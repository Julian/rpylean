"""
The kernel: terms as flat records in unmanaged memory, addressed by
integer handles, and the checker that reduces, infers and compares them.

The `W_Expr` tree is the parsed representation: it is what the garbage
collector traces, so every reduction product that lives in it is
re-traced on every major collection for as long as it is retained. Here
a term is instead a *record*: a fixed run of machine words in an
untraced array, named by an integer *handle*. Records are hash-consed,
so structurally equal terms have equal handles and syntactic equality
is an integer comparison. Leaves that carry no sub-terms (constants,
sorts, variables, literals) stay `W_Expr` objects referenced from a
side table; they are canonicalised by content on the way in, which is
what makes handle equality meaningful.

A store is per declaration: the working set of one check, emptied
for the next when the check ends.
"""

from rpython.rlib.objectmodel import always_inline, newlist_hint, we_are_translated
from rpython.rlib.rarithmetic import intmask, r_uint
from rpython.rlib.rstack import stack_almost_full
from rpython.rtyper.lltypesystem import lltype, rffi

from rpython.rlib.rbigint import rbigint

from rpylean._eval import eval_closed_scalar
from rpylean.exceptions import (
    HeartbeatExceeded,
    InvalidProjection,
    LooseBoundVariable,
)
from rpylean.objects import (
    HINT_ABBREV,
    NAT,
    NAT_ZERO,
    PROP,
    STRING,
    Name,
    W_App,
    W_BVar,
    W_Const,
    W_Constructor,
    W_DeepRecursion,
    W_Definition,
    W_ForAll,
    W_FVar,
    W_Inductive,
    W_Lambda,
    W_Let,
    W_LitNat,
    W_LitStr,
    W_NotAFunction,
    W_NotAProp,
    W_NotASort,
    W_Proj,
    W_Recursor,
    W_Sort,
    W_TypeError,
    W_LEVEL_ZERO,
    _BOOL_FALSE,
    _BOOL_TRUE,
    _NAT_REC_NAME,
    _NAT_SUCC_NAME,
    _mk_w_litnat,
    apply_const_level_params,
    find_decl,
    get_decl,
    is_nat_binop,
    name_dict,
    nat_binop_value,
    syntactic_eq,
)


# ---- Handles --------------------------------------------------------------
#
# A handle is a tagged machine int. Bit 0 set: a leaf, index `h >> 1`
# into the leaf table. Bit 0 clear and non-zero: a record, index
# `(h >> 1) - 1`. Zero never names anything, so it doubles as the empty
# marker of every table.

INVALID = 0


@always_inline
def is_leaf(h):
    return (h & 1) == 1


@always_inline
def leaf_index(h):
    return h >> 1


@always_inline
def rec_index(h):
    return (h >> 1) - 1


@always_inline
def rec_handle(i):
    return (i + 1) << 1


@always_inline
def leaf_handle(j):
    return (j << 1) | 1


# ---- Records --------------------------------------------------------------
#
# Five words per record: kind, three kind-specific fields, and `meta`,
# which packs `loose_bvar_range << 1 | has_fvar` exactly as a
# `W_Expr`'s `_packed` upper half does.

KIND_APP = 1      # a = fn, b = arg
KIND_LAMBDA = 2   # a = binder type, b = body; info = the Binder
KIND_FORALL = 3   # a = binder type, b = body; info = the Binder
KIND_PROJ = 4     # a = struct, b = (name_id << 32) | field_index; info = name_id
KIND_LET = 5      # a = type, b = PAIR(value, body); info = the let Name
KIND_PAIR = 6     # a = value, b = body (auxiliary to KIND_LET)

REC_WORDS = 4
F_KM = 0
F_A = 1
F_B = 2
F_INFO = 3
_KIND_MASK = 7
_PROJ_SHIFT = 32
_PROJ_MASK = (1 << _PROJ_SHIFT) - 1

# Per-record memo slots (parallel to the records, 0 = not yet known).
MEMO_SLOTS = 5
M_WHNF_CORE = 0
M_WHNF = 1
M_INFER = 2
M_INFER_CHECKED = 3
M_WHNF_CORE_CHEAP = 4

_SIGNED_ARRAY = rffi.CArray(lltype.Signed)
_NO_INFO = -1


def _alloc_words(n):
    return lltype.malloc(_SIGNED_ARRAY, n, flavor='raw', zero=True)


def _free_words(arr):
    lltype.free(arr, flavor='raw')


def _zero_words(arr, n):
    """Zero ``arr``'s first ``n`` words."""
    if n <= 0:
        return
    if we_are_translated():
        rffi.c_memset(
            rffi.cast(rffi.VOIDP, arr), 0, n * rffi.sizeof(lltype.Signed),
        )
    else:
        i = 0
        while i < n:
            arr[i] = 0
            i += 1


def _grow_words(arr, used, cap):
    """A fresh array of ``cap`` words holding ``arr``'s first ``used``
    words; ``arr`` is freed."""
    new = _alloc_words(cap)
    if we_are_translated():
        rffi.c_memcpy(
            rffi.cast(rffi.VOIDP, new), rffi.cast(rffi.CONST_VOIDP, arr),
            used * rffi.sizeof(lltype.Signed),
        )
    else:
        i = 0
        while i < used:
            new[i] = arr[i]
            i += 1
    _free_words(arr)
    return new


@always_inline
def _spread(k):
    # Single-multiply SplitMix finalizer: mixes high bits (handles shifted by
    # 38) and low bits (depths) into every bit with half the latency of fmix64.
    x = r_uint(k)
    x = (x ^ (x >> 30)) * r_uint(0xbf58476d1ce4e5b9)
    x ^= x >> 27
    return intmask(x)


@always_inline
def _hash_rec(kind, a, b):
    """64-bit hash for a record ``(kind, a, b)``. Low bits index `table`,
    upper 31 bits form the collision-filtering tag packed into `table[i]`."""
    x = (
        (r_uint(a) * r_uint(0x9e3779b97f4a7c15))
        ^ (r_uint(b) * r_uint(0xbf58476d1ce4e5b9))
        ^ (r_uint(kind) * r_uint(0x94d049bb133111eb))
    )
    x ^= x >> 32
    return intmask(x)


_TABLE_SLOT_MASK = 0xFFFFFFFF
_TABLE_TAG_MASK = 0x7FFFFFFF
_BVAR_ARR_LEN = 256
_STORE_KEEP_CAP = 1 << 17


@always_inline
def _pack_key(h, other, depth):
    """
    ``(h, other, depth)`` as one map key, or 0 when a component is too
    large to pack (the caller then skips the memo for this call).
    Handles get 25 bits each, the depth 13; ``h`` is never 0, so the
    key is never 0.
    """
    if h >= (1 << 25) or other >= (1 << 25) or depth >= (1 << 13):
        return 0
    return (h << 38) | (other << 13) | depth


_ITE_NAME = Name.simple("ite")
_DITE_NAME = Name.simple("dite")
_COND_NAME = Name.simple("cond")
_BOOL_AND_NAME = Name.from_str("Bool.and")
_BOOL_OR_NAME = Name.from_str("Bool.or")
_BOOL_NOT_NAME = Name.from_str("Bool.not")
_AND_NAME = Name.simple("and")
_OR_NAME = Name.simple("or")

#: How many records a declaration's store holds before the types of
#: heavy terms under binders are inferred without substituting into
#: them. Few declarations get there, and those that don't are spared
#: finding out what is heavy.
_OPEN_RECORDS = 1 << 17

#: How many nodes make a term heavy: one whose type is inferred without
#: substituting into it (see `Machine._infer_open`).
_HEAVY = 256

#: How many slots a `SubstMemo` may have. A substitution memo only
#: pays for itself while a lookup is cheaper than redoing the work,
#: which it stops being once the table has outgrown the caches.
_MEMO_LIMIT = 1 << 18

#: Maximum entries cleared via the sparse dirty list in `IntMap.clear()`
#: before falling back to a full array memset.
_DIRTY_CAP = 4096

#: The depths a `SubstMemo` remembers beyond what packs into a word.
_WIDE_DEPTH_BITS = 24
_WIDE_DEPTH = 1 << _WIDE_DEPTH_BITS


def _canonical_const(const):
    """
    ``const`` with its universe levels in normal form, so constants at
    equal universes written differently share one leaf.
    """
    c = const._canonical
    if c is not None:
        return c
    levels = const.levels
    changed = False
    normalized = []
    for level in levels:
        n = level.normalize()
        if n is not level:
            changed = True
        normalized.append(n)
    c = const if not changed else const.name.const(normalized)
    const._canonical = c
    c._canonical = c
    return c


def _canonical_sort(sort):
    """``sort`` with its level in normal form (see `_canonical_const`)."""
    c = sort._canonical
    if c is not None:
        return c
    n = sort.level.normalize()
    c = sort if n is sort.level else n.sort()
    sort._canonical = c
    c._canonical = c
    return c


class IntMap(object):
    """
    An open-addressed int -> int map in unmanaged memory. Keys must be
    non-zero (zero marks an empty slot). Key and value are interleaved in
    a single array so probes touch one cache line, and small populations
    clear via a dirty-offset list without `memset` or shrink/grow churn.
    """

    _attrs_ = [
        'entries', 'dirty', '_dirty_count', 'mask', 'size',
        'initial', 'keep_cap', 'limit',
    ]

    def __init__(self, capacity=1 << 10, keep_cap=1 << 15):
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.initial = cap
        self.keep_cap = keep_cap if keep_cap >= cap else cap
        self.limit = 0
        self.entries = _alloc_words(cap << 1)
        self.dirty = _alloc_words(_DIRTY_CAP)
        self._dirty_count = 0
        self.mask = cap - 1
        self.size = 0

    def clear(self):
        """Forget every entry, clearing sparsely when small and keeping up
        to ``keep_cap`` slots allocated to avoid repeated grow/shrink churn."""
        sz = self.size
        if sz == 0:
            self._dirty_count = 0
            return
        cap = self.mask + 1
        if cap > self.keep_cap and sz * 8 < cap:
            _free_words(self.entries)
            cap = self.keep_cap
            self.entries = _alloc_words(cap << 1)
            self.mask = cap - 1
        elif self._dirty_count >= 0:
            entries = self.entries
            dirty = self.dirty
            dc = self._dirty_count
            i = 0
            while i < dc:
                entries[dirty[i]] = 0
                i += 1
        else:
            _zero_words(self.entries, cap << 1)
        self.size = 0
        self._dirty_count = 0

    def get(self, key, default):
        assert key != 0
        mask = self.mask
        entries = self.entries
        i = _spread(key) & mask
        while True:
            off = i << 1
            k = entries[off]
            if k == key:
                return entries[off + 1]
            if k == 0:
                return default
            i = (i + 1) & mask

    def set(self, key, val):
        assert key != 0
        if (self.size + 1) * 2 > self.mask + 1:
            self._grow()
        mask = self.mask
        entries = self.entries
        i = _spread(key) & mask
        while True:
            off = i << 1
            k = entries[off]
            if k == key:
                entries[off + 1] = val
                return
            if k == 0:
                entries[off] = key
                entries[off + 1] = val
                dc = self._dirty_count
                if dc >= 0:
                    if dc < _DIRTY_CAP:
                        self.dirty[dc] = off
                        self._dirty_count = dc + 1
                    else:
                        self._dirty_count = -1
                self.size += 1
                return
            i = (i + 1) & mask

    def _grow(self):
        old_cap = self.mask + 1
        if self.limit > 0 and old_cap >= self.limit:
            # Only ever a way to skip work already done: start over
            # rather than outgrow the caches.
            _zero_words(self.entries, old_cap << 1)
            self.size = 0
            self._dirty_count = 0
            return
        old_entries = self.entries
        cap = old_cap * 2
        entries = _alloc_words(cap << 1)
        mask = cap - 1
        i = 0
        end = old_cap << 1
        while i < end:
            k = old_entries[i]
            if k != 0:
                j = _spread(k) & mask
                while entries[j << 1] != 0:
                    j = (j + 1) & mask
                off = j << 1
                entries[off] = k
                entries[off + 1] = old_entries[i + 1]
            i += 2
        self.entries = entries
        self.mask = mask
        self._dirty_count = -1
        _free_words(old_entries)

    def free(self):
        if self.mask >= 0:
            _free_words(self.entries)
            _free_words(self.dirty)
            self.mask = -1
            self.size = 0
            self._dirty_count = 0


class PairMap(object):
    """
    An open-addressed (int, int) -> int map in unmanaged memory. The
    first half of a key must be non-zero (zero marks an empty slot).
    """

    _attrs_ = ['keys', 'vals', 'mask', 'size', 'initial', 'limit']

    def __init__(self, capacity=1 << 10):
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.initial = cap
        self.limit = 0
        self.keys = _alloc_words(cap * 2)
        self.vals = _alloc_words(cap)
        self.mask = cap - 1
        self.size = 0

    def clear(self):
        """Forget every entry, and most of the room a few were left."""
        cap = self.mask + 1
        if cap > self.initial and self.size * 8 < cap:
            _free_words(self.keys)
            _free_words(self.vals)
            cap = self.initial
            self.keys = _alloc_words(cap * 2)
            self.vals = _alloc_words(cap)
            self.mask = cap - 1
        elif self.size > 0:
            _zero_words(self.keys, cap * 2)
        self.size = 0

    def get(self, k1, k2, default):
        assert k1 != 0
        mask = self.mask
        keys = self.keys
        i = _spread(k1 ^ _spread(k2)) & mask
        while True:
            k = keys[i * 2]
            if k == k1 and keys[i * 2 + 1] == k2:
                return self.vals[i]
            if k == 0:
                return default
            i = (i + 1) & mask

    def set(self, k1, k2, val):
        assert k1 != 0
        if (self.size + 1) * 2 > self.mask + 1:
            self._grow()
        mask = self.mask
        keys = self.keys
        i = _spread(k1 ^ _spread(k2)) & mask
        while True:
            k = keys[i * 2]
            if k == k1 and keys[i * 2 + 1] == k2:
                self.vals[i] = val
                return
            if k == 0:
                keys[i * 2] = k1
                keys[i * 2 + 1] = k2
                self.vals[i] = val
                self.size += 1
                return
            i = (i + 1) & mask

    def _grow(self):
        if self.limit > 0 and self.mask + 1 >= self.limit:
            # Only ever a way to skip work already done: start over
            # rather than outgrow the caches.
            _zero_words(self.keys, (self.mask + 1) * 2)
            self.size = 0
            return
        old_keys = self.keys
        old_vals = self.vals
        old_cap = self.mask + 1
        cap = old_cap * 2
        keys = _alloc_words(cap * 2)
        vals = _alloc_words(cap)
        mask = cap - 1
        i = 0
        while i < old_cap:
            k1 = old_keys[i * 2]
            if k1 != 0:
                k2 = old_keys[i * 2 + 1]
                j = _spread(k1 ^ _spread(k2)) & mask
                while keys[j * 2] != 0:
                    j = (j + 1) & mask
                keys[j * 2] = k1
                keys[j * 2 + 1] = k2
                vals[j] = old_vals[i]
            i += 1
        self.keys = keys
        self.vals = vals
        self.mask = mask
        _free_words(old_keys)
        _free_words(old_vals)

    def free(self):
        if self.mask >= 0:
            _free_words(self.keys)
            _free_words(self.vals)
            self.mask = -1
            self.size = 0


class SubstMemo(IntMap):
    """
    What a substitution made of a record: ``(h, other, depth)`` to the
    result, with ``other`` whatever the substitution is of (a handle,
    or a count) and 0 for a triple not yet seen. Triples small enough
    to pack into one word, which nearly all are, are the `IntMap`'s own
    entries; the rest go to a map keyed on two words.
    """

    _attrs_ = ['wide']

    def __init__(self, capacity):
        IntMap.__init__(self, capacity)
        self.limit = _MEMO_LIMIT
        self.wide = None

    def get_wide(self, h, other, depth):
        wide = self.wide
        if wide is None or depth >= _WIDE_DEPTH:
            return 0
        return wide.get(h, (other << _WIDE_DEPTH_BITS) | depth, 0)

    def set_wide(self, h, other, depth, val):
        if depth >= _WIDE_DEPTH:
            return
        wide = self.wide
        if wide is None:
            wide = self.wide = PairMap(1 << 10)
            wide.limit = _MEMO_LIMIT
        wide.set(h, (other << _WIDE_DEPTH_BITS) | depth, val)

    def clear(self):
        IntMap.clear(self)
        if self.wide is not None:
            self.wide.free()
            self.wide = None

    def count(self):
        wide = self.wide
        if wide is None:
            return self.size
        return self.size + wide.size

    def free(self):
        IntMap.free(self)
        if self.wide is not None:
            self.wide.free()
            self.wide = None


class TermStore(object):
    """
    The record arena for one declaration's check: records, the consing
    table over them, the leaf table, and the memoised boundary to and
    from `W_Expr` in both directions.
    """

    _attrs_ = [
        'tc',
        'recs', 'memos', 'nrecs', 'cap',
        'table', 'tmask',
        'leaves', 'leaf_meta', 'leaf_bvar', 'leaf_whnf', 'leaf_infer',
        'leaf_checked', 'leaf_delta', 'nleaves', 'leaf_cap',
        'infos', 'names', '_name_ids',
        '_bvar_arr', '_bvar_max', '_bvar_leaves', '_leaf_uid', '_content_leaves',
        '_import_memo', '_import_spine', 'rec_node', 'nodes',
        '_inst_memo', '_shift_memo', '_bind_memo', '_multi_memo',
        '_bindm_memo', '_call_memo',
        '_freed', 'initial_cap',
    ]

    def __init__(self, tc, capacity=1 << 14):
        self.tc = tc
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.initial_cap = cap
        self._alloc_records(cap)
        #: Leaves by index; `leaf_meta` / `leaf_bvar` mirror the two
        #: facts the machine reads on hot paths so it need not touch the
        #: object: the packed meta word, and the de Bruijn index for a
        #: bound variable (-1 otherwise).
        self.leaf_cap = 1 << 10
        self.leaf_meta = _alloc_words(self.leaf_cap)
        self.leaf_bvar = _alloc_words(self.leaf_cap)
        self.leaf_whnf = _alloc_words(self.leaf_cap)
        #: A leaf's inferred type (0 = not yet), and whether that type
        #: was produced in check mode (a constant's reference check has
        #: run).
        self.leaf_infer = _alloc_words(self.leaf_cap)
        self.leaf_checked = _alloc_words(self.leaf_cap)
        #: Delta-unfolded handle for a constant leaf (0 = uncached, -1 = none).
        self.leaf_delta = _alloc_words(self.leaf_cap)
        #: Flat array for small bound-variable leaf handles (`id < 256`).
        self._bvar_arr = _alloc_words(_BVAR_ARR_LEN)
        self._bvar_max = 0
        #: Per-declaration `W_Expr._uid + 1 -> leaf handle` fast cache.
        self._leaf_uid = IntMap(1 << 11, keep_cap=1 << 14)
        self._import_memo = IntMap(1 << 13)
        self._import_spine = []
        self._inst_memo = SubstMemo(1 << 12)
        self._shift_memo = SubstMemo(1 << 10)
        self._bind_memo = SubstMemo(1 << 10)
        self._multi_memo = SubstMemo(1 << 11)
        self._bindm_memo = SubstMemo(1 << 10)
        #: L1-resident scratch memo cleared after each one-shot multi-subst.
        self._call_memo = IntMap(1 << 11, keep_cap=1 << 14)
        self._freed = False
        self._forget()

    def _alloc_records(self, cap):
        self.cap = cap
        self.recs = _alloc_words(cap << 2)
        self.memos = _alloc_words(cap * MEMO_SLOTS)
        #: record index -> 1 + its index in `nodes`, or 0: the `W_Expr`
        #: a record was imported from or exported to
        self.rec_node = _alloc_words(cap)
        self.table = _alloc_words(cap * 2)
        self.tmask = cap * 2 - 1

    def _free_records(self):
        _free_words(self.recs)
        _free_words(self.rec_node)
        _free_words(self.memos)
        _free_words(self.table)

    def _forget(self):
        """Start over on everything the garbage collector looks after."""
        self.nrecs = 0
        self.nleaves = 0
        self.leaves = []
        #: Binder infos (`Binder`s, for the name and style) and
        #: `Name`s (for projections and lets), by `F_INFO` index.
        self.infos = []
        self.names = []
        self._name_ids = name_dict()
        self._bvar_leaves = {}
        self._content_leaves = {}
        self.nodes = []

    def reset(self):
        """
        Empty the store for another declaration, keeping its memory:
        nearly every declaration is small, and allocating and growing
        a store for each costs more than checking most of them does.
        What is cleared is what was used, not what there is room for.
        """
        n = self.nrecs
        keep_cap = _STORE_KEEP_CAP if _STORE_KEEP_CAP >= self.initial_cap else self.initial_cap
        if self.cap > keep_cap and n * 8 < self.cap:
            self._free_records()
            self._alloc_records(keep_cap)
        else:
            self._clear_table(n)
            _zero_words(self.memos, n * MEMO_SLOTS)
            _zero_words(self.rec_node, n)
        leaves = self.nleaves
        _zero_words(self.leaf_whnf, leaves)
        _zero_words(self.leaf_infer, leaves)
        _zero_words(self.leaf_checked, leaves)
        _zero_words(self.leaf_delta, leaves)
        if self._bvar_max > 0:
            _zero_words(self._bvar_arr, self._bvar_max)
            self._bvar_max = 0
        self._leaf_uid.clear()
        self._import_memo.clear()
        self._inst_memo.clear()
        self._shift_memo.clear()
        self._bind_memo.clear()
        self._multi_memo.clear()
        self._bindm_memo.clear()
        self._call_memo.clear()
        self._forget()

    def _clear_table(self, n):
        table = self.table
        tmask = self.tmask
        if n * 16 > tmask:
            _zero_words(table, tmask + 1)
            return
        recs = self.recs
        idx = n - 1
        while idx >= 0:
            base = idx << 2
            hh = _hash_rec(recs[base] & _KIND_MASK, recs[base + F_A], recs[base + F_B])
            expected = (((hh >> 32) & _TABLE_TAG_MASK) << 32) | (idx + 1)
            i = hh & tmask
            while table[i] != expected:
                i = (i + 1) & tmask
            table[i] = 0
            idx -= 1

    # ---- lifecycle -------------------------------------------------------

    def free(self):
        if self._freed:
            return
        self._freed = True
        self._free_records()
        _free_words(self.leaf_meta)
        _free_words(self.leaf_bvar)
        _free_words(self.leaf_whnf)
        _free_words(self.leaf_infer)
        _free_words(self.leaf_checked)
        _free_words(self.leaf_delta)
        _free_words(self._bvar_arr)
        self._leaf_uid.free()
        self._import_memo.free()
        self._inst_memo.free()
        self._shift_memo.free()
        self._bind_memo.free()
        self._multi_memo.free()
        self._bindm_memo.free()
        self._call_memo.free()

    # ---- record access ---------------------------------------------------

    @always_inline
    def kind(self, h):
        if is_leaf(h):
            return 0
        return self.recs[rec_index(h) << 2] & _KIND_MASK

    @always_inline
    def field_a(self, h):
        return self.recs[(rec_index(h) << 2) + F_A]

    @always_inline
    def field_b(self, h):
        return self.recs[(rec_index(h) << 2) + F_B]

    @always_inline
    def proj_index(self, h):
        return self.recs[(rec_index(h) << 2) + F_B] & _PROJ_MASK

    @always_inline
    def meta(self, h):
        if is_leaf(h):
            return self.leaf_meta[leaf_index(h)]
        return self.recs[rec_index(h) << 2] >> 3

    @always_inline
    def loose_bvar_range(self, h):
        return self.meta(h) >> 1

    @always_inline
    def has_fvar(self, h):
        return (self.meta(h) & 1) != 0

    @always_inline
    def info(self, h):
        return self.recs[(rec_index(h) << 2) + F_INFO]

    @always_inline
    def memo(self, h, slot):
        return self.memos[rec_index(h) * MEMO_SLOTS + slot]

    @always_inline
    def set_memo(self, h, slot, value):
        self.memos[rec_index(h) * MEMO_SLOTS + slot] = value

    def binder_of(self, h):
        """The `Binder` recorded for a lambda or forall record."""
        return self.infos[self.info(h)]

    def name_of(self, h):
        """The `Name` recorded for a projection or let record."""
        return self.names[self.info(h)]

    def leaf(self, h):
        """The `W_Expr` a leaf handle names."""
        return self.leaves[leaf_index(h)]

    def bvar_id(self, h):
        """The de Bruijn index of a bound-variable leaf, else -1."""
        if not is_leaf(h):
            return -1
        return self.leaf_bvar[leaf_index(h)]

    # ---- consing ---------------------------------------------------------

    def _meta_for(self, kind, a, b):
        if kind == KIND_APP or kind == KIND_PAIR:
            ma = self.meta(a)
            mb = self.meta(b)
            la = ma & ~1
            lb = mb & ~1
            return (la if la > lb else lb) | ((ma | mb) & 1)
        if kind == KIND_LAMBDA or kind == KIND_FORALL:
            la = self.loose_bvar_range(a)
            lb = self.loose_bvar_range(b) - 1
            if lb < 0:
                lb = 0
            loose = la if la > lb else lb
            fvar = self.has_fvar(a) or self.has_fvar(b)
            return (loose << 1) | (1 if fvar else 0)
        if kind == KIND_PROJ:
            return self.meta(a)
        assert kind == KIND_LET
        la = self.loose_bvar_range(a)
        lv = self.loose_bvar_range(self.field_a(b))
        lb = self.loose_bvar_range(self.field_b(b)) - 1
        if lb < 0:
            lb = 0
        loose = la
        if lv > loose:
            loose = lv
        if lb > loose:
            loose = lb
        fvar = self.has_fvar(a) or self.has_fvar(b)
        return (loose << 1) | (1 if fvar else 0)

    def cons_app(self, fn, arg):
        """Dedicated fast path for `KIND_APP` records."""
        recs = self.recs
        table = self.table
        tmask = self.tmask
        hh = _hash_rec(KIND_APP, fn, arg)
        tag = (hh >> 32) & _TABLE_TAG_MASK
        i = hh & tmask
        while True:
            entry = table[i]
            if entry == 0:
                break
            if (entry >> 32) == tag:
                slot = entry & _TABLE_SLOT_MASK
                base = (slot - 1) << 2
                if ((recs[base] & _KIND_MASK) == KIND_APP
                        and recs[base + F_A] == fn and recs[base + F_B] == arg):
                    return rec_handle(slot - 1)
            i = (i + 1) & tmask
        idx = self.nrecs
        if idx == self.cap:
            self._grow_records()
            recs = self.recs
        ma = self.meta(fn)
        mb = self.meta(arg)
        la = ma & ~1
        lb = mb & ~1
        meta = (la if la > lb else lb) | ((ma | mb) & 1)
        base = idx << 2
        recs[base] = (meta << 3) | KIND_APP
        recs[base + F_A] = fn
        recs[base + F_B] = arg
        recs[base + F_INFO] = _NO_INFO
        self.nrecs = idx + 1
        if (idx + 1) * 2 > self.tmask + 1:
            self._rehash()
        else:
            self.table[i] = (tag << 32) | (idx + 1)
        return rec_handle(idx)

    def cons(self, kind, a, b, info=_NO_INFO):
        """
        The record ``(kind, a, b)``, creating it if new. ``info`` is
        not part of the identity: the first recorded binder or name
        stands for every later alpha-equal request.
        """
        recs = self.recs
        table = self.table
        tmask = self.tmask
        hh = _hash_rec(kind, a, b)
        tag = (hh >> 32) & _TABLE_TAG_MASK
        i = hh & tmask
        while True:
            entry = table[i]
            if entry == 0:
                break
            if (entry >> 32) == tag:
                slot = entry & _TABLE_SLOT_MASK
                base = (slot - 1) << 2
                if ((recs[base] & _KIND_MASK) == kind
                        and recs[base + F_A] == a and recs[base + F_B] == b):
                    return rec_handle(slot - 1)
            i = (i + 1) & tmask
        idx = self.nrecs
        if idx == self.cap:
            self._grow_records()
            recs = self.recs
        meta = self._meta_for(kind, a, b)
        base = idx << 2
        recs[base] = (meta << 3) | kind
        recs[base + F_A] = a
        recs[base + F_B] = b
        recs[base + F_INFO] = info
        self.nrecs = idx + 1
        if (idx + 1) * 2 > self.tmask + 1:
            self._rehash()
        else:
            self.table[i] = (tag << 32) | (idx + 1)
        return rec_handle(idx)

    def _grow_records(self):
        n = self.nrecs
        cap = self.cap * 2
        self.recs = _grow_words(self.recs, n << 2, cap << 2)
        self.rec_node = _grow_words(self.rec_node, n, cap)
        self.memos = _grow_words(self.memos, n * MEMO_SLOTS, cap * MEMO_SLOTS)
        self.cap = cap

    def _rehash(self):
        _free_words(self.table)
        cap = (self.tmask + 1) * 2
        table = _alloc_words(cap)
        tmask = cap - 1
        recs = self.recs
        idx = 0
        while idx < self.nrecs:
            base = idx << 2
            hh = _hash_rec(recs[base] & _KIND_MASK, recs[base + F_A], recs[base + F_B])
            i = hh & tmask
            while table[i] != 0:
                i = (i + 1) & tmask
            table[i] = (((hh >> 32) & _TABLE_TAG_MASK) << 32) | (idx + 1)
            idx += 1
        self.table = table
        self.tmask = tmask

    def app(self, fn, arg):
        return self.cons_app(fn, arg)

    def lam(self, binder, type, body):
        return self.cons(KIND_LAMBDA, type, body, self._info_index(binder))

    def forall(self, binder, type, body):
        return self.cons(KIND_FORALL, type, body, self._info_index(binder))

    def proj(self, struct_name, field_index, struct):
        name_id = self._name_index(struct_name)
        packed = (name_id << _PROJ_SHIFT) | (field_index & _PROJ_MASK)
        return self.cons(KIND_PROJ, struct, packed, name_id)

    def let(self, name, type, value, body):
        pair = self.cons(KIND_PAIR, value, body)
        return self.cons(KIND_LET, type, pair, self._name_index(name))

    def _info_index(self, binder):
        i = len(self.infos)
        self.infos.append(binder)
        return i

    def _name_index(self, name):
        i = self._name_ids.get(name, -1)
        if i >= 0:
            return i
        i = len(self.names)
        self.names.append(name)
        self._name_ids[name] = i
        return i

    # ---- leaves ----------------------------------------------------------

    def _new_leaf(self, e, bvar):
        j = self.nleaves
        if j == self.leaf_cap:
            cap = self.leaf_cap * 2
            self.leaf_meta = _grow_words(self.leaf_meta, j, cap)
            self.leaf_bvar = _grow_words(self.leaf_bvar, j, cap)
            self.leaf_whnf = _grow_words(self.leaf_whnf, j, cap)
            self.leaf_infer = _grow_words(self.leaf_infer, j, cap)
            self.leaf_checked = _grow_words(self.leaf_checked, j, cap)
            self.leaf_delta = _grow_words(self.leaf_delta, j, cap)
            self.leaf_cap = cap
        self.leaves.append(e)
        self.leaf_meta[j] = (e._packed >> 32) & 0x3FFFFFFF
        self.leaf_bvar[j] = bvar
        self.nleaves = j + 1
        return leaf_handle(j)

    def bvar(self, id):
        if 0 <= id < _BVAR_ARR_LEN:
            h = self._bvar_arr[id]
            if h != 0:
                return h
            h = self._new_leaf(W_BVar(id), id)
            self._bvar_arr[id] = h
            if id + 1 > self._bvar_max:
                self._bvar_max = id + 1
            return h
        h = self._bvar_leaves.get(id, 0)
        if h != 0:
            return h
        h = self._new_leaf(W_BVar(id), id)
        self._bvar_leaves[id] = h
        return h

    def has_fvar_leaf(self, fvar):
        """Whether the free variable ``fvar`` already has a leaf."""
        return self._leaf_uid.get(fvar._uid + 1, 0) != 0

    def leaf_for(self, e):
        """
        The canonical leaf handle for the leaf ``e``: bound
        variables by index, free variables by identity, everything else
        by content.
        """
        cls = e.__class__
        if cls is W_BVar:
            assert isinstance(e, W_BVar)
            id = e.id
            if 0 <= id < _BVAR_ARR_LEN:
                h = self._bvar_arr[id]
                if h != 0:
                    return h
                h = self._new_leaf(e, id)
                self._bvar_arr[id] = h
                if id + 1 > self._bvar_max:
                    self._bvar_max = id + 1
                return h
            h = self._bvar_leaves.get(id, 0)
            if h != 0:
                return h
            h = self._new_leaf(e, id)
            self._bvar_leaves[id] = h
            return h
        uid_key = e._uid + 1
        h = self._leaf_uid.get(uid_key, 0)
        if h != 0:
            return h
        if cls is W_FVar:
            h = self._new_leaf(e, -1)
            self._leaf_uid.set(uid_key, h)
            return h
        orig = e
        if cls is W_Const:
            assert isinstance(e, W_Const)
            e = _canonical_const(e)
        elif cls is W_Sort:
            assert isinstance(e, W_Sort)
            e = _canonical_sort(e)
        if e is not orig:
            h = self._leaf_uid.get(e._uid + 1, 0)
            if h != 0:
                self._leaf_uid.set(uid_key, h)
                return h
        key = e.hash()
        bucket = self._content_leaves.get(key, None)
        if bucket is None:
            bucket = []
            self._content_leaves[key] = bucket
        else:
            for h in bucket:
                if syntactic_eq(self.leaves[leaf_index(h)], e):
                    self._leaf_uid.set(uid_key, h)
                    if e is not orig:
                        self._leaf_uid.set(e._uid + 1, h)
                    return h
        h = self._new_leaf(e, -1)
        bucket.append(h)
        self._leaf_uid.set(uid_key, h)
        if e is not orig:
            self._leaf_uid.set(e._uid + 1, h)
        return h

    # ---- spines ----------------------------------------------------------

    def head(self, h):
        """The head of the application spine ``h``."""
        recs = self.recs
        while (h & 1) == 0:
            base = rec_index(h) << 2
            if (recs[base] & _KIND_MASK) != KIND_APP:
                break
            h = recs[base + F_A]
        return h

    def unapp(self, h):
        """
        ``(head, args)`` for the spine ``h``, args outermost-first (the
        last argument first), as `W_Expr.unapp` returns them.
        """
        args = newlist_hint(4)
        recs = self.recs
        while (h & 1) == 0:
            base = rec_index(h) << 2
            if (recs[base] & _KIND_MASK) != KIND_APP:
                break
            args.append(recs[base + F_B])
            h = recs[base + F_A]
        return h, args

    def apply(self, fn, args, start, stop):
        """``fn`` applied to ``args[start:stop]``, left to right."""
        i = start
        while i < stop:
            fn = self.cons_app(fn, args[i])
            i += 1
        return fn

    def apply_rev(self, fn, args, hi):
        """``fn`` applied to ``args[hi]``, ``args[hi-1]``, … ``args[0]``:
        re-applies an outermost-first arg list up to index ``hi``."""
        i = hi
        while i >= 0:
            fn = self.cons_app(fn, args[i])
            i -= 1
        return fn

    def const_leaf(self, h):
        """The `W_Const` a leaf handle names, or ``None``."""
        if not is_leaf(h):
            return None
        e = self.leaves[leaf_index(h)]
        if isinstance(e, W_Const):
            return e
        return None

    def litnat_leaf(self, h):
        """The `W_LitNat` a leaf handle names, or ``None``."""
        if not is_leaf(h):
            return None
        e = self.leaves[leaf_index(h)]
        if isinstance(e, W_LitNat):
            return e
        return None

    # ---- substitution ----------------------------------------------------

    def instantiate(self, h, sub, depth=0, rdepth=0):
        """
        ``h`` with ``sub`` substituted for the bound variable ``depth``
        and every looser bound variable moved down by one (the binder
        that bound it is gone).
        """
        if self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            # Only a bound variable has a loose range, so this is one,
            # at or above `depth`.
            id = self.leaf_bvar[leaf_index(h)]
            if id == depth:
                return sub if depth == 0 else self.shift(sub, depth, 0)
            return self.bvar(id - 1)
        key = _pack_key(h, sub, depth)
        if key != 0:
            r = self._inst_memo.get(key, 0)
        else:
            r = self._inst_memo.get_wide(h, sub, depth)
        if r != 0:
            return r
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("instantiate")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        nr = rdepth + 1
        if kind == KIND_APP:
            if self.loose_bvar_range(a) <= depth:
                na = a
            elif is_leaf(a):
                aid = self.leaf_bvar[leaf_index(a)]
                if aid == depth:
                    na = sub if depth == 0 else self.shift(sub, depth, 0)
                else:
                    na = self.bvar(aid - 1)
            else:
                na = self.instantiate(a, sub, depth, nr)
            if self.loose_bvar_range(b) <= depth:
                nb = b
            elif is_leaf(b):
                bid = self.leaf_bvar[leaf_index(b)]
                if bid == depth:
                    nb = sub if depth == 0 else self.shift(sub, depth, 0)
                else:
                    nb = self.bvar(bid - 1)
            else:
                nb = self.instantiate(b, sub, depth, nr)
            if na == a and nb == b:
                r = h
            else:
                r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if self.loose_bvar_range(a) <= depth else self.instantiate(a, sub, depth, nr)
            nb = b if self.loose_bvar_range(b) <= depth + 1 else self.instantiate(b, sub, depth + 1, nr)
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self.instantiate(a, sub, depth, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self.instantiate(a, sub, depth, nr)
            nv = self.instantiate(value, sub, depth, nr)
            nbody = self.instantiate(body, sub, depth + 1, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if key != 0:
            self._inst_memo.set(key, r)
        else:
            self._inst_memo.set_wide(h, sub, depth, r)
        return r

    def instantiate_multi(self, h, substs, depth=0):
        """
        ``h`` with ``substs[i]`` substituted for the bound variable
        ``depth + i`` for every ``i``, all at once, and every looser
        bound variable moved down by ``len(substs)``.

        Uses the L1-resident one-shot `_call_memo` (cleared on return) so
        no `KIND_PAIR` chain records are consed and no declaration-wide
        multi-substitution table grows out of L1/L2 cache.
        """
        n = len(substs)
        if n == 1:
            return self.instantiate(h, substs[0], depth)
        if n == 0 or self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = self.leaf_bvar[leaf_index(h)]
            rel = id - depth
            if rel < n:
                return substs[rel] if depth == 0 else self.shift(substs[rel], depth, 0)
            return self.bvar(id - n)
        memo = self._call_memo
        try:
            return self._inst_multi_oneshot(h, substs, n, depth, memo, 0)
        finally:
            memo.clear()

    def _inst_multi_oneshot(self, h, substs, n, depth, memo, rdepth):
        if self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = self.leaf_bvar[leaf_index(h)]
            rel = id - depth
            if rel < n:
                return substs[rel] if depth == 0 else self.shift(substs[rel], depth, 0)
            return self.bvar(id - n)
        if depth < (1 << 16) and h < (1 << 46):
            key = (h << 16) | depth
            r = memo.get(key, 0)
            if r != 0:
                return r
        else:
            key = 0
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("instantiate_multi")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        nr = rdepth + 1
        if kind == KIND_APP:
            if self.loose_bvar_range(a) <= depth:
                na = a
            elif is_leaf(a):
                aid = self.leaf_bvar[leaf_index(a)]
                arel = aid - depth
                if arel < n:
                    na = substs[arel] if depth == 0 else self.shift(substs[arel], depth, 0)
                else:
                    na = self.bvar(aid - n)
            else:
                na = self._inst_multi_oneshot(a, substs, n, depth, memo, nr)
            if self.loose_bvar_range(b) <= depth:
                nb = b
            elif is_leaf(b):
                bid = self.leaf_bvar[leaf_index(b)]
                brel = bid - depth
                if brel < n:
                    nb = substs[brel] if depth == 0 else self.shift(substs[brel], depth, 0)
                else:
                    nb = self.bvar(bid - n)
            else:
                nb = self._inst_multi_oneshot(b, substs, n, depth, memo, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if self.loose_bvar_range(a) <= depth else self._inst_multi_oneshot(a, substs, n, depth, memo, nr)
            nb = b if self.loose_bvar_range(b) <= depth + 1 else self._inst_multi_oneshot(b, substs, n, depth + 1, memo, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self._inst_multi_oneshot(a, substs, n, depth, memo, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_oneshot(a, substs, n, depth, memo, nr)
            nv = self._inst_multi_oneshot(value, substs, n, depth, memo, nr)
            nbody = self._inst_multi_oneshot(body, substs, n, depth + 1, memo, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if key != 0:
            memo.set(key, r)
        return r

    def instantiate_multi_rev(self, h, substs, count, depth=0):
        """
        Like `instantiate_multi`, but reads the first ``count`` entries of
        ``substs`` in reverse order (oldest-first: ``substs[count - 1]``
        replaces ``bvar(depth)``, ``substs[0]`` replaces ``bvar(depth + count - 1)``),
        avoiding list reversal and slice copies.
        """
        if count == 1:
            return self.instantiate(h, substs[0], depth)
        if count == 0 or self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = self.leaf_bvar[leaf_index(h)]
            rel = id - depth
            if rel < count:
                sub = substs[count - 1 - rel]
                return sub if depth == 0 else self.shift(sub, depth, 0)
            return self.bvar(id - count)
        memo = self._call_memo
        try:
            return self._inst_multi_rev_oneshot(h, substs, count, depth, memo, 0)
        finally:
            memo.clear()

    def _inst_multi_rev_oneshot(self, h, substs, n, depth, memo, rdepth):
        if self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = self.leaf_bvar[leaf_index(h)]
            rel = id - depth
            if rel < n:
                sub = substs[n - 1 - rel]
                return sub if depth == 0 else self.shift(sub, depth, 0)
            return self.bvar(id - n)
        if depth < (1 << 16) and h < (1 << 46):
            key = (h << 16) | depth
            r = memo.get(key, 0)
            if r != 0:
                return r
        else:
            key = 0
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("instantiate_multi")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        nr = rdepth + 1
        if kind == KIND_APP:
            if self.loose_bvar_range(a) <= depth:
                na = a
            elif is_leaf(a):
                aid = self.leaf_bvar[leaf_index(a)]
                arel = aid - depth
                if arel < n:
                    asub = substs[n - 1 - arel]
                    na = asub if depth == 0 else self.shift(asub, depth, 0)
                else:
                    na = self.bvar(aid - n)
            else:
                na = self._inst_multi_rev_oneshot(a, substs, n, depth, memo, nr)
            if self.loose_bvar_range(b) <= depth:
                nb = b
            elif is_leaf(b):
                bid = self.leaf_bvar[leaf_index(b)]
                brel = bid - depth
                if brel < n:
                    bsub = substs[n - 1 - brel]
                    nb = bsub if depth == 0 else self.shift(bsub, depth, 0)
                else:
                    nb = self.bvar(bid - n)
            else:
                nb = self._inst_multi_rev_oneshot(b, substs, n, depth, memo, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if self.loose_bvar_range(a) <= depth else self._inst_multi_rev_oneshot(a, substs, n, depth, memo, nr)
            nb = b if self.loose_bvar_range(b) <= depth + 1 else self._inst_multi_rev_oneshot(b, substs, n, depth + 1, memo, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self._inst_multi_rev_oneshot(a, substs, n, depth, memo, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_rev_oneshot(a, substs, n, depth, memo, nr)
            nv = self._inst_multi_rev_oneshot(value, substs, n, depth, memo, nr)
            nbody = self._inst_multi_rev_oneshot(body, substs, n, depth + 1, memo, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if key != 0:
            memo.set(key, r)
        return r

    def _instantiate_multi(self, h, substs, chain, depth, rdepth=0):
        if self.loose_bvar_range(h) <= depth:
            return h
        n = len(substs)
        if is_leaf(h):
            id = self.leaf_bvar[leaf_index(h)]
            rel = id - depth
            if rel < n:
                return substs[rel] if depth == 0 else self.shift(substs[rel], depth, 0)
            return self.bvar(id - n)
        key = _pack_key(h, chain, depth)
        if key != 0:
            r = self._multi_memo.get(key, 0)
        else:
            r = self._multi_memo.get_wide(h, chain, depth)
        if r != 0:
            return r
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("instantiate_multi")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        nr = rdepth + 1
        if kind == KIND_APP:
            na = self._instantiate_multi(a, substs, chain, depth, nr)
            nb = self._instantiate_multi(b, substs, chain, depth, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = self._instantiate_multi(a, substs, chain, depth, nr)
            nb = self._instantiate_multi(b, substs, chain, depth + 1, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self._instantiate_multi(a, substs, chain, depth, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._instantiate_multi(a, substs, chain, depth, nr)
            nv = self._instantiate_multi(value, substs, chain, depth, nr)
            nbody = self._instantiate_multi(body, substs, chain, depth + 1, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if key != 0:
            self._multi_memo.set(key, r)
        else:
            self._multi_memo.set_wide(h, chain, depth, r)
        return r

    def shift(self, h, count, depth=0, rdepth=0):
        """
        ``h`` with every bound variable at or above ``depth`` moved up
        by ``count`` (it is being placed under ``count`` more binders).
        """
        if count == 0 or self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            return self.bvar(self.leaf_bvar[leaf_index(h)] + count)
        key = _pack_key(h, count, depth)
        if key != 0:
            r = self._shift_memo.get(key, 0)
        else:
            r = self._shift_memo.get_wide(h, count, depth)
        if r != 0:
            return r
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("shift")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        nr = rdepth + 1
        if kind == KIND_APP:
            na = a if self.loose_bvar_range(a) <= depth else self.shift(a, count, depth, nr)
            nb = b if self.loose_bvar_range(b) <= depth else self.shift(b, count, depth, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            r = self.cons(
                kind, self.shift(a, count, depth, nr),
                self.shift(b, count, depth + 1, nr), info,
            )
        elif kind == KIND_PROJ:
            r = self.cons(
                KIND_PROJ, self.shift(a, count, depth, nr), b, info,
            )
        else:
            assert kind == KIND_LET
            pair = self.cons(
                KIND_PAIR, self.shift(self.field_a(b), count, depth, nr),
                self.shift(self.field_b(b), count, depth + 1, nr),
            )
            r = self.cons(KIND_LET, self.shift(a, count, depth, nr), pair, info)
        if key != 0:
            self._shift_memo.set(key, r)
        else:
            self._shift_memo.set_wide(h, count, depth, r)
        return r

    def bind_fvar(self, h, fvar, depth=0):
        """
        ``h`` with the free variable leaf ``fvar`` abstracted to the
        bound variable ``depth``: the inverse of opening a binder.
        """
        if not self.has_fvar(h):
            return h
        if is_leaf(h):
            if h == fvar:
                return self.bvar(depth)
            return h
        key = _pack_key(h, fvar, depth)
        if key != 0:
            r = self._bind_memo.get(key, 0)
        else:
            r = self._bind_memo.get_wide(h, fvar, depth)
        if r != 0:
            return r
        if stack_almost_full():
            raise W_DeepRecursion("bind_fvar")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        if kind == KIND_APP:
            na = self.bind_fvar(a, fvar, depth)
            nb = self.bind_fvar(b, fvar, depth)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = self.bind_fvar(a, fvar, depth)
            nb = self.bind_fvar(b, fvar, depth + 1)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self.bind_fvar(a, fvar, depth)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self.bind_fvar(a, fvar, depth)
            nv = self.bind_fvar(value, fvar, depth)
            nbody = self.bind_fvar(body, fvar, depth + 1)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if key != 0:
            self._bind_memo.set(key, r)
        else:
            self._bind_memo.set_wide(h, fvar, depth, r)
        return r

    def chain(self, handles):
        """The record chain standing for the list ``handles`` (at least
        two of them), for keying memos on a list."""
        n = len(handles)
        chain = handles[n - 1]
        i = n - 2
        while i >= 0:
            chain = self.cons(KIND_PAIR, handles[i], chain)
            i -= 1
        return chain

    def bind_fvars(self, h, fvars, depth=0):
        """
        ``h`` with the free variables ``fvars`` (in binding order)
        abstracted in one pass: the last becomes the bound variable
        ``depth``, the first ``depth + len(fvars) - 1``.
        """
        n = len(fvars)
        if n == 1:
            return self.bind_fvar(h, fvars[0], depth)
        if n == 0 or not self.has_fvar(h):
            return h
        return self._bind_fvars(h, fvars, self.chain(fvars), depth)

    def _bind_fvars(self, h, fvars, chain, depth):
        if not self.has_fvar(h):
            return h
        n = len(fvars)
        if is_leaf(h):
            j = 0
            while j < n:
                if fvars[j] == h:
                    return self.bvar(depth + n - 1 - j)
                j += 1
            return h
        key = _pack_key(h, chain, depth)
        if key != 0:
            r = self._bindm_memo.get(key, 0)
        else:
            r = self._bindm_memo.get_wide(h, chain, depth)
        if r != 0:
            return r
        if stack_almost_full():
            raise W_DeepRecursion("bind_fvars")
        recs = self.recs
        base = rec_index(h) << 2
        kind = recs[base] & _KIND_MASK
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = recs[base + F_INFO]
        if kind == KIND_APP:
            na = self._bind_fvars(a, fvars, chain, depth)
            nb = self._bind_fvars(b, fvars, chain, depth)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = self._bind_fvars(a, fvars, chain, depth)
            nb = self._bind_fvars(b, fvars, chain, depth + 1)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self._bind_fvars(a, fvars, chain, depth)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._bind_fvars(a, fvars, chain, depth)
            nv = self._bind_fvars(value, fvars, chain, depth)
            nbody = self._bind_fvars(body, fvars, chain, depth + 1)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if key != 0:
            self._bindm_memo.set(key, r)
        else:
            self._bindm_memo.set_wide(h, chain, depth, r)
        return r

    def sort_leaf(self, h):
        """The `W_Sort` a leaf handle names, or ``None``."""
        if not is_leaf(h):
            return None
        e = self.leaves[leaf_index(h)]
        if isinstance(e, W_Sort):
            return e
        return None

    # ---- boundary --------------------------------------------------------

    def node_of(self, h):
        """The `W_Expr` the record ``h`` was imported from or exported
        to, or ``None``."""
        i = self.rec_node[rec_index(h)]
        if i == 0:
            return None
        return self.nodes[i - 1]

    def set_node(self, h, e):
        self.nodes.append(e)
        self.rec_node[rec_index(h)] = len(self.nodes)

    def import_term(self, e, rdepth=0):
        """The handle for the term ``e``, memoised per `W_Expr`."""
        memo = self._import_memo
        h = memo.get(e._uid + 1, 0)
        if h != 0:
            return h
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("import_term")
        cls = e.__class__
        nr = rdepth + 1
        if cls is W_App:
            assert isinstance(e, W_App)
            fn = e.fn
            if not isinstance(fn, W_App):
                head = self.cons_app(
                    self.import_term(fn, nr), self.import_term(e.arg, nr),
                )
                memo.set(e._uid + 1, head)
                self.set_node(head, e)
                return head
            # Walk the spine down to the first already-imported node
            # (or the head) using the shared `_import_spine` buffer, then
            # fold applications back up, memoising every spine node.
            spine = self._import_spine
            mark = len(spine)
            try:
                cur = e
                head = 0
                while True:
                    if not isinstance(cur, W_App):
                        head = self.import_term(cur, nr)
                        break
                    hh = memo.get(cur._uid + 1, 0)
                    if hh != 0:
                        head = hh
                        break
                    spine.append(cur)
                    cur = cur.fn
                while len(spine) > mark:
                    app = spine.pop()
                    head = self.cons_app(head, self.import_term(app.arg, nr))
                    memo.set(app._uid + 1, head)
                    self.set_node(head, app)
                return head
            finally:
                while len(spine) > mark:
                    spine.pop()
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(e, W_Lambda) or isinstance(e, W_ForAll)
            binder = e.binder
            type = self.import_term(binder.type, nr)
            body = self.import_term(e.body, nr)
            if cls is W_Lambda:
                h = self.lam(binder, type, body)
            else:
                h = self.forall(binder, type, body)
        elif cls is W_Proj:
            assert isinstance(e, W_Proj)
            h = self.proj(
                e.struct_name, e.field_index, self.import_term(e.struct_expr, nr),
            )
        elif cls is W_Let:
            assert isinstance(e, W_Let)
            h = self.let(
                e.name,
                self.import_term(e.type, nr),
                self.import_term(e.value, nr),
                self.import_term(e.body, nr),
            )
        else:
            h = self.leaf_for(e)
            memo.set(e._uid + 1, h)
            return h
        memo.set(e._uid + 1, h)
        self.set_node(h, e)
        return h

    def import_const_term(self, const, decl, target):
        """Import ``target`` (a declaration's type, body, or recursor rule)
        instantiated with ``const.levels`` directly into record handles,
        avoiding intermediate `W_Expr` tree allocation."""
        params = decl.levels
        n = len(params)
        if n == 0 or not target.has_level_param():
            return self.import_term(target)
        clevels = const.levels
        if len(clevels) != n:
            raise RuntimeError(
                "W_Const.infer: expected %s levels, got %s"
                % (n, len(clevels)),
            )
        # Identity instantiation (e.g. polymorphic decl referring to another
        # at the same universe params): reuse `_import_memo` directly.
        identity = True
        i = 0
        while i < n:
            if clevels[i] is not params[i].as_level_param():
                identity = False
                break
            i += 1
        if identity:
            return self.import_term(target)
        memo = self._call_memo
        try:
            return self._import_with_levels(target, params, clevels, memo, 0)
        finally:
            memo.clear()

    def _import_with_levels(self, e, params, clevels, memo, rdepth):
        if not e.has_level_param():
            return self.import_term(e, rdepth)
        h = memo.get(e._uid + 1, 0)
        if h != 0:
            return h
        if (rdepth & 31) == 0 and stack_almost_full():
            raise W_DeepRecursion("import_term")
        cls = e.__class__
        nr = rdepth + 1
        if cls is W_App:
            assert isinstance(e, W_App)
            fn = e.fn
            if not isinstance(fn, W_App):
                fn_h = (
                    self._import_with_levels(fn, params, clevels, memo, nr)
                    if fn.has_level_param()
                    else self.import_term(fn, nr)
                )
                arg = e.arg
                arg_h = (
                    self._import_with_levels(arg, params, clevels, memo, nr)
                    if arg.has_level_param()
                    else self.import_term(arg, nr)
                )
                head = self.cons_app(fn_h, arg_h)
                memo.set(e._uid + 1, head)
                return head
            spine = self._import_spine
            mark = len(spine)
            try:
                cur = e
                head = 0
                while True:
                    if not cur.has_level_param():
                        head = self.import_term(cur, nr)
                        break
                    if not isinstance(cur, W_App):
                        head = self._import_with_levels(
                            cur, params, clevels, memo, nr,
                        )
                        break
                    hh = memo.get(cur._uid + 1, 0)
                    if hh != 0:
                        head = hh
                        break
                    spine.append(cur)
                    cur = cur.fn
                while len(spine) > mark:
                    app = spine.pop()
                    arg = app.arg
                    arg_h = (
                        self._import_with_levels(arg, params, clevels, memo, nr)
                        if arg.has_level_param()
                        else self.import_term(arg, nr)
                    )
                    head = self.cons_app(head, arg_h)
                    memo.set(app._uid + 1, head)
                return head
            finally:
                while len(spine) > mark:
                    spine.pop()
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(e, W_Lambda) or isinstance(e, W_ForAll)
            binder = e.binder
            type_h = self._import_with_levels(
                binder.type, params, clevels, memo, nr,
            )
            body_h = self._import_with_levels(
                e.body, params, clevels, memo, nr,
            )
            if cls is W_Lambda:
                h = self.lam(binder, type_h, body_h)
            else:
                h = self.forall(binder, type_h, body_h)
        elif cls is W_Proj:
            assert isinstance(e, W_Proj)
            h = self.proj(
                e.struct_name, e.field_index,
                self._import_with_levels(
                    e.struct_expr, params, clevels, memo, nr,
                ),
            )
        elif cls is W_Let:
            assert isinstance(e, W_Let)
            h = self.let(
                e.name,
                self._import_with_levels(e.type, params, clevels, memo, nr),
                self._import_with_levels(e.value, params, clevels, memo, nr),
                self._import_with_levels(e.body, params, clevels, memo, nr),
            )
        elif cls is W_Const:
            assert isinstance(e, W_Const)
            lvls = e.levels
            leaf_e = e
            if lvls:
                changed = False
                new_lvls = []
                for lvl in lvls:
                    nl = (
                        lvl.subst_levels_lists(params, clevels)
                        if lvl.has_param else lvl
                    )
                    if nl is not lvl:
                        changed = True
                    new_lvls.append(nl)
                if changed:
                    leaf_e = e.name.const(new_lvls)
            h = self.leaf_for(leaf_e)
        elif cls is W_Sort:
            assert isinstance(e, W_Sort)
            leaf_e = e
            if e.level.has_param:
                nl = e.level.subst_levels_lists(params, clevels)
                if nl is not e.level:
                    leaf_e = nl.sort()
            h = self.leaf_for(leaf_e)
        else:
            h = self.leaf_for(e)
        memo.set(e._uid + 1, h)
        return h

    def export_term(self, h):
        """The `W_Expr` for ``h``, memoised per record."""
        if is_leaf(h):
            return self.leaves[leaf_index(h)]
        cached = self.node_of(h)
        if cached is not None:
            return cached
        if stack_almost_full():
            raise W_DeepRecursion("export_term")
        kind = self.kind(h)
        if kind == KIND_APP:
            args = []
            cur = h
            head = None
            while True:
                if self.kind(cur) != KIND_APP:
                    head = self.export_term(cur)
                    break
                cached = self.node_of(cur)
                if cached is not None:
                    head = cached
                    break
                args.append(cur)
                cur = self.field_a(cur)
            assert head is not None
            i = len(args) - 1
            while i >= 0:
                app = args[i]
                head = W_App(head, self.export_term(self.field_b(app)))
                self.set_node(app, head)
                i -= 1
            return head
        if kind == KIND_LAMBDA or kind == KIND_FORALL:
            binder = self.binder_of(h).with_type(
                self.export_term(self.field_a(h)),
            )
            body = self.export_term(self.field_b(h))
            if kind == KIND_LAMBDA:
                e = W_Lambda(binder, body)
            else:
                e = W_ForAll(binder, body)
        elif kind == KIND_PROJ:
            e = W_Proj(
                self.name_of(h), self.proj_index(h),
                self.export_term(self.field_a(h)),
            )
        else:
            assert kind == KIND_LET
            pair = self.field_b(h)
            e = W_Let(
                self.name_of(h),
                self.export_term(self.field_a(h)),
                self.export_term(self.field_a(pair)),
                self.export_term(self.field_b(pair)),
            )
        self.set_node(h, e)
        return e


class Machine(object):
    """
    A declaration checker over handles.

    Every step mirrors Lean's kernel: `whnf_core` is beta / zeta /
    projection / iota / quot only, `whnf` adds native Nat arithmetic
    and one delta layer per iteration, `def_eq` runs the same sequence
    of checks in the same order, and `infer` opens each binder with one
    canonical free variable per binder record.
    """

    _attrs_ = [
        'tc', 'store', '_rule_memo', '_fvars', '_opened',
        '_open_memo', '_heavy', '_budget',
        '_eqv', '_neq', '_failed',
        'h_prop', 'h_true', 'h_false', 'h_nat', 'h_nat_zero', 'h_string',
    ]

    _LAZY_DELTA_MAX_ITER = 100000

    def __init__(self, tc):
        self.tc = tc
        self.store = TermStore(tc)
        #: (heavy open record, context chain and mode) -> its type there
        self._open_memo = PairMap(1 << 8)
        #: open record -> 1 if light, 2 if heavy
        self._heavy = IntMap(1 << 8)
        self._budget = 0
        #: (rec const leaf index, ctor leaf index) -> rule rhs handle
        self._rule_memo = IntMap(1 << 8, keep_cap=1 << 12)
        #: (binder record, domain) -> the free-variable leaf opening it
        self._fvars = IntMap(1 << 8, keep_cap=1 << 13)
        #: proven-def-eq forest over handles (handle -> parent)
        self._eqv = IntMap(1 << 10)
        #: pairs proven NOT def-eq
        self._neq = IntMap(1 << 10)
        #: pairs whose same-head argument comparison failed (symmetric)
        self._failed = IntMap(1 << 8)
        self._forget()

    def _forget(self):
        """Start over on everything the garbage collector looks after."""
        store = self.store
        #: uids of binders' own free variables already opening a binder
        self._opened = {}
        self.h_prop = store.leaf_for(PROP)
        self.h_true = store.leaf_for(_BOOL_TRUE)
        self.h_false = store.leaf_for(_BOOL_FALSE)
        self.h_nat = store.leaf_for(NAT)
        self.h_nat_zero = store.leaf_for(NAT_ZERO)
        self.h_string = store.leaf_for(STRING)

    def _census(self):
        store = self.store
        tracer = self.tc.tracer
        if tracer.recording:
            tracer.census(
                store.nrecs, store.nleaves, store._inst_memo.count(),
                store._shift_memo.count(), store._bind_memo.count(),
                self._eqv.size, self._neq.size, self._failed.size,
            )

    def reset(self):
        """Empty the machine for another declaration, keeping its memory."""
        self.store.reset()
        self._rule_memo.clear()
        self._fvars.clear()
        self._eqv.clear()
        self._neq.clear()
        self._failed.clear()
        self._open_memo.clear()
        self._heavy.clear()
        self._forget()

    def free(self):
        self.store.free()
        self._rule_memo.free()
        self._fvars.free()
        self._eqv.free()
        self._neq.free()
        self._failed.free()
        self._open_memo.free()
        self._heavy.free()

    def _decl(self, const):
        return find_decl(self.tc.declarations, const.name)

    def export(self, h):
        return self.store.export_term(h)

    # ---- whnf ------------------------------------------------------------

    def whnf_core(self, h, cheap_proj=False, traced=True):
        """
        Weak head normal form without unfolding definitions: beta, zeta,
        projection of a constructor, iota and quot only. With
        ``cheap_proj`` the struct of a projection is itself only taken
        to whnf_core, never evaluated; the first pass of def_eq uses
        that so two projections are compared before either struct is
        unfolded through its definitions. A tracer that writes sees
        each form the term takes unless ``traced`` is off, as it is for
        the reduction of an application's head on the way to its own.
        """
        store = self.store
        tc = self.tc
        tracer = tc.tracer
        writes = traced and tracer.recording and tracer.writes
        if is_leaf(h):
            if writes:
                tracer.whnf_step(self.export(h), tc.declarations)
            return h
        slot = M_WHNF_CORE_CHEAP if cheap_proj else M_WHNF_CORE
        cached = store.memo(h, slot)
        if cached != 0:
            return cached
        # A term already known to be in full WHNF is whnf_core-normal
        # either way, and a full whnf_core result is a cheap one too.
        cached = store.memo(h, M_WHNF)
        if cached == h:
            return h
        if cheap_proj:
            cached = store.memo(h, M_WHNF_CORE)
            if cached == h:
                return h
        if stack_almost_full():
            raise W_DeepRecursion("whnf_core")
        start = h
        while True:
            tc.tick_wall_time()
            if writes:
                tracer.whnf_step(self.export(h), tc.declarations)
            next = self._whnf_core_step(h, cheap_proj)
            if next == 0:
                break
            h = next
            if not writes:
                if is_leaf(h):
                    break
                cached = store.memo(h, slot)
                if cached != 0:
                    h = cached
                    break
        store.set_memo(start, slot, h)
        return h

    def _beta_spine(self, head, args):
        """Multi-arg beta-reduce a leading `KIND_LAMBDA` telescope ``head``
        applied to ``args`` (outermost-first) in a single substitution pass."""
        store = self.store
        n = len(args)
        k = 0
        body = head
        while k < n and store.kind(body) == KIND_LAMBDA:
            body = store.field_b(body)
            k += 1
        if self.tc.tracer.recording:
            j = 0
            while j < k:
                self.tc.tracer.beta()
                j += 1
        if store.loose_bvar_range(body) == 0:
            res = body
        elif is_leaf(body):
            bid = store.leaf_bvar[leaf_index(body)]
            if bid < k:
                res = args[n - k + bid]
            else:
                res = store.bvar(bid - k)
        elif k == 1:
            res = store.instantiate(body, args[n - 1], 0)
        elif k == n:
            res = store.instantiate_multi(body, args, 0)
        else:
            start = n - k
            assert start >= 0
            res = store.instantiate_multi(body, args[start:n], 0)
        return store.apply_rev(res, args, n - 1 - k)

    def _whnf_core_step(self, h, cheap_proj):
        """One whnf_core step of ``h``, or 0 when there is none."""
        store = self.store
        kind = store.kind(h)
        if kind == KIND_APP:
            head = h
            while store.kind(head) == KIND_APP:
                head = store.field_a(head)
            hk = store.kind(head)
            if hk == 0:
                const = store.const_leaf(head)
                if const is None:
                    return 0
                decl = self._decl(const)
                if decl is not None:
                    dkind = decl.w_kind
                    if isinstance(dkind, W_Recursor):
                        _, args = store.unapp(h)
                        return self._try_iota_spine(
                            head, const, decl, dkind, args,
                        )
                if const.name.syntactic_eq(W_App._QUOT_LIFT):
                    _, args = store.unapp(h)
                    return self._try_quot_lift_spine(args)
                return 0
            if hk == KIND_LAMBDA:
                _, args = store.unapp(h)
                return self._beta_spine(head, args)
            if hk == KIND_PROJ or hk == KIND_LET:
                head_w = self.whnf_core(head, cheap_proj, False)
                if head_w == head:
                    return 0
                _, args = store.unapp(h)
                if (store.kind(head_w) == KIND_LAMBDA
                        and not (self.tc.tracer.recording
                                 and self.tc.tracer.writes)):
                    return self._beta_spine(head_w, args)
                return store.apply_rev(head_w, args, len(args) - 1)
            return 0
        if kind == KIND_LET:
            pair = store.field_b(h)
            return store.instantiate(store.field_b(pair), store.field_a(pair), 0)
        if kind == KIND_PROJ:
            return self.try_proj(h, cheap_proj)
        return 0

    def whnf(self, h):
        """Weak head normal form, unfolding definitions as needed."""
        store = self.store
        if is_leaf(h):
            cached = store.leaf_whnf[leaf_index(h)]
        else:
            cached = store.memo(h, M_WHNF)
        if cached != 0:
            return cached
        start = h
        while True:
            h = self.whnf_core(h)
            if store.kind(h) == KIND_APP:
                reduced = self.try_reduce_nat(h)
                if reduced != 0:
                    h = reduced
                    continue
            unfolded = self.try_unfold_head(h)
            if unfolded == 0:
                break
            h = unfolded
        if is_leaf(start):
            store.leaf_whnf[leaf_index(start)] = h
        else:
            store.set_memo(start, M_WHNF, h)
        return h

    def try_unfold_head(self, h):
        """``h`` with its head constant unfolded one definition layer and
        the spine re-applied (beta-reducing leading lambdas when not writing
        traces), or 0 when the head isn't unfoldable."""
        store = self.store
        head = store.head(h)
        const = store.const_leaf(head)
        if const is None:
            return 0
        val = self._delta_value(head, const)
        if val == 0:
            return 0
        if h == head:
            return val
        _, args = store.unapp(h)
        if (store.kind(val) == KIND_LAMBDA
                and not (self.tc.tracer.recording and self.tc.tracer.writes)):
            return self._beta_spine(val, args)
        return store.apply_rev(val, args, len(args) - 1)

    def _delta_kind(self, head):
        """The `W_Definition` a delta-reducible head names, or None."""
        const = self.store.const_leaf(head)
        if const is None:
            return None
        decl = self._decl(const)
        if decl is None:
            return None
        kind = decl.w_kind
        if not isinstance(kind, W_Definition):
            return None
        if kind.get_delta_reduce_target() is None:
            return None
        return kind

    def _delta_value(self, head, const):
        store = self.store
        j = leaf_index(head)
        cached = store.leaf_delta[j]
        if cached != 0:
            return cached if cached > 0 else 0
        decl = self._decl(const)
        val = 0
        if decl is not None and isinstance(decl.w_kind, W_Definition):
            target = decl.w_kind.get_delta_reduce_target()
            if target is not None:
                if self.tc.tracer.recording:
                    self.tc.tracer.delta(const.name)
                val = store.import_const_term(const, decl, target)
        store.leaf_delta[j] = val if val > 0 else -1
        return val

    def _whnf_nat_arg(self, arg):
        """Evaluate an argument of a native Nat binary op to WHNF, using the
        meta-traced evaluator for closed non-literal terms."""
        store = self.store
        if store.litnat_leaf(arg) is not None or arg == self.h_nat_zero:
            return arg
        if not self.tc.tracer.recording:
            if is_leaf(arg):
                cached = store.leaf_whnf[leaf_index(arg)]
                if cached != 0:
                    return cached
                const = store.const_leaf(arg)
                if const is not None and self._delta_value(arg, const) != 0:
                    ev = eval_closed_scalar(self, arg)
                    if ev != 0:
                        store.leaf_whnf[leaf_index(arg)] = ev
                        return ev
            elif not store.has_fvar(arg) and store.loose_bvar_range(arg) == 0:
                cached = store.memo(arg, M_WHNF)
                if cached != 0:
                    return cached
                cheap = self.try_reduce_nat_cheap(arg)
                if cheap != 0:
                    store.set_memo(arg, M_WHNF, cheap)
                    return cheap
                ev = eval_closed_scalar(self, arg)
                if ev != 0:
                    store.set_memo(arg, M_WHNF, ev)
                    return ev
        return self.whnf(arg)

    def try_reduce_nat(self, h):
        """Native evaluation of a binary Nat op on literal arguments, or
        0 when ``h`` isn't one."""
        store = self.store
        fn = store.field_a(h)
        if store.kind(fn) != KIND_APP:
            return 0
        head = store.field_a(fn)
        if store.kind(head) == KIND_APP:
            return 0
        const = store.const_leaf(head)
        if const is None or not is_nat_binop(const.name):
            return 0
        v1 = self._nat_value(self._whnf_nat_arg(store.field_b(fn)))
        if v1 is None:
            return 0
        v2 = self._nat_value(self._whnf_nat_arg(store.field_b(h)))
        if v2 is None:
            return 0
        result = nat_binop_value(const.name, v1, v2)
        if result is None:
            return 0
        if self.tc.tracer.recording:
            self.tc.tracer.nat_reduce(const.name)
        return store.leaf_for(result)

    def _nat_value_cheap(self, h):
        """The Nat value of ``h`` if it is already a syntactic literal,
        `Nat.zero`, or `Nat.succ` chain without unfolding definitions."""
        store = self.store
        succs = 0
        while True:
            lit = store.litnat_leaf(h)
            if lit is not None:
                return lit.val.add(rbigint.fromint(succs))
            const = store.const_leaf(h)
            if const is not None:
                if const.name.syntactic_eq(NAT_ZERO.name):
                    return rbigint.fromint(succs)
                return None
            if store.kind(h) == KIND_APP:
                head = store.const_leaf(store.field_a(h))
                if head is not None and head.name.syntactic_eq(_NAT_SUCC_NAME):
                    succs += 1
                    h = store.field_b(h)
                    continue
            return None

    def try_reduce_nat_cheap(self, h):
        """Native evaluation of a binary Nat op only when both arguments
        are already syntactic Nat numerals (never unfolding definitions)."""
        store = self.store
        fn = store.field_a(h)
        if store.kind(fn) != KIND_APP:
            return 0
        head = store.field_a(fn)
        if store.kind(head) == KIND_APP:
            return 0
        const = store.const_leaf(head)
        if const is None or not is_nat_binop(const.name):
            return 0
        v1 = self._nat_value_cheap(store.field_b(fn))
        if v1 is None:
            return 0
        v2 = self._nat_value_cheap(store.field_b(h))
        if v2 is None:
            return 0
        result = nat_binop_value(const.name, v1, v2)
        if result is None:
            return 0
        if self.tc.tracer.recording:
            self.tc.tracer.nat_reduce(const.name)
        return store.leaf_for(result)

    def _nat_value(self, h):
        """The Nat value of a WHNF ``h`` (a literal, `Nat.zero`, or
        `Nat.succ` of such), or ``None``."""
        store = self.store
        succs = 0
        while True:
            lit = store.litnat_leaf(h)
            if lit is not None:
                return lit.val.add(rbigint.fromint(succs))
            const = store.const_leaf(h)
            if const is not None:
                if const.name.syntactic_eq(NAT_ZERO.name):
                    return rbigint.fromint(succs)
                return None
            if store.kind(h) == KIND_APP:
                head = store.const_leaf(store.field_a(h))
                if head is not None and head.name.syntactic_eq(_NAT_SUCC_NAME):
                    succs += 1
                    h = self.whnf(store.field_b(h))
                    continue
            return None

    def _is_nat_zero(self, h):
        store = self.store
        lit = store.litnat_leaf(h)
        if lit is not None:
            return lit.val.eq(rbigint.fromint(0))
        const = store.const_leaf(h)
        if const is not None:
            return const.name.syntactic_eq(NAT_ZERO.name)
        return False

    def _nat_succ_pred(self, h):
        """The predecessor of a syntactic `Nat.succ pred` / non-zero
        literal, or 0."""
        store = self.store
        lit = store.litnat_leaf(h)
        if lit is not None:
            if lit.val.eq(rbigint.fromint(0)):
                return 0
            return store.leaf_for(_mk_w_litnat(lit.val.sub(rbigint.fromint(1))))
        if store.kind(h) == KIND_APP:
            head = store.const_leaf(store.field_a(h))
            if head is not None and head.name.syntactic_eq(_NAT_SUCC_NAME):
                return store.field_b(h)
        return 0

    def try_proj(self, h, cheap_proj=False):
        """Projection of a constructor application, or 0."""
        store = self.store
        if cheap_proj:
            struct = self.whnf_core(store.field_a(h), True)
        else:
            struct = self.whnf(store.field_a(h))
        lit = None
        if is_leaf(struct):
            e = store.leaf(struct)
            if isinstance(e, W_LitStr):
                lit = e
        if lit is not None:
            struct = self.whnf(store.import_term(lit.build_str_expr()))
        head, args = store.unapp(struct)
        const = store.const_leaf(head)
        if const is None:
            return 0
        decl = self._decl(const)
        if decl is None:
            return 0
        kind = decl.w_kind
        if not isinstance(kind, W_Constructor):
            return 0
        idx = kind.num_params + store.proj_index(h)
        n = len(args)
        if idx < n:
            # args are outermost-first: field i of a left-to-right list
            # sits at n - 1 - i.
            return args[n - 1 - idx]
        return 0

    def _try_quot_lift_spine(self, args):
        """``Quot.lift α r β f h (Quot.mk r a) extra... ⇒ f a extra...``, or 0."""
        store = self.store
        n = len(args)
        if n < 6:
            return 0
        mk = self.whnf(args[n - 6])
        mk_head, mk_args = store.unapp(mk)
        mk_const = store.const_leaf(mk_head)
        if mk_const is None or len(mk_args) != 3:
            return 0
        if not mk_const.name.syntactic_eq(W_App._QUOT_MK):
            return 0
        res = store.cons_app(args[n - 4], mk_args[0])
        return store.apply_rev(res, args, n - 7)

    def _try_iota_spine(self, target, const, decl, rec, args):
        """One recursor iota step on ``target`` applied to ``args``, or 0."""
        store = self.store
        tc = self.tc
        n_args = len(args)
        skip = rec.num_params + rec.num_indices + rec.num_minors + rec.num_motives
        major_idx = n_args - 1 - skip
        if major_idx < 0:
            return 0

        # `Nat.rec motive zero succ (literal N)` in one step.
        if const.name.syntactic_eq(_NAT_REC_NAME):
            lit = store.litnat_leaf(args[major_idx])
            if lit is not None:
                if tc.tracer.recording:
                    tc.tracer.iota(const.name)
                succ_case = args[major_idx + 1]
                zero_case = args[major_idx + 2]
                motive = args[major_idx + 3]
                if lit.val.eq(rbigint.fromint(0)):
                    res = zero_case
                else:
                    pred = store.leaf_for(
                        _mk_w_litnat(lit.val.sub(rbigint.fromint(1))),
                    )
                    rec_at_pred = store.cons_app(
                        store.cons_app(
                            store.cons_app(
                                store.cons_app(target, motive), zero_case,
                            ),
                            succ_case,
                        ),
                        pred,
                    )
                    res = store.cons_app(
                        store.cons_app(succ_case, pred), rec_at_pred,
                    )
                return store.apply_rev(res, args, major_idx - 1)

        major = self.whnf(args[major_idx])

        if rec.k == 1:
            major = self._to_cnstr_when_k(rec, args, major)
            if major == 0:
                return 0

        lit = store.litnat_leaf(major)
        if lit is not None:
            major = store.import_term(lit.one_step_constructor())
        else:
            expanded = self._to_cnstr_when_structure(decl, rec, major)
            if expanded != 0:
                major = expanded

        ctor_head, ctor_args = store.unapp(major)
        ctor = store.const_leaf(ctor_head)
        if ctor is None:
            return 0
        rule = rec.rule_for_ctor(ctor.name)
        if rule is None:
            return 0
        ctor_decl = find_decl(tc.declarations, rule.ctor_name)
        if ctor_decl is None or not ctor_decl.w_kind.is_constructor():
            return 0
        ctor_kind = ctor_decl.w_kind
        assert isinstance(ctor_kind, W_Constructor)

        rhs = self._rule_rhs(target, const, ctor_head, rule)
        # Collect rhs arguments left-to-right: params, motives, minors,
        # constructor fields, then anything following the major premise.
        total = rec.num_params + rec.num_motives + rec.num_minors
        assert total >= 0
        rhs_args = []
        i = n_args - 1
        stop = n_args - total
        while i >= stop:
            rhs_args.append(args[i])
            i -= 1
        n_ctor = len(ctor_args)
        i = n_ctor - 1 - ctor_kind.num_params
        stop = n_ctor - 1 - (ctor_kind.num_params + rule.num_fields)
        while i > stop and i >= 0:
            rhs_args.append(ctor_args[i])
            i -= 1
        i = major_idx - 1
        while i >= 0:
            rhs_args.append(args[i])
            i -= 1

        if tc.tracer.recording:
            tc.tracer.iota(const.name)

        # Directly beta-reduce `rhs`'s leading lambda telescope in one
        # pass instead of building throwaway `KIND_APP` records.
        m = len(rhs_args)
        k = 0
        body = rhs
        while k < m and store.kind(body) == KIND_LAMBDA:
            body = store.field_b(body)
            k += 1
        if k == 0:
            result = body
        else:
            if tc.tracer.recording:
                j = 0
                while j < k:
                    tc.tracer.beta()
                    j += 1
            if store.loose_bvar_range(body) == 0:
                result = body
            elif is_leaf(body):
                bid = store.leaf_bvar[leaf_index(body)]
                if bid < k:
                    result = rhs_args[k - 1 - bid]
                else:
                    result = store.bvar(bid - k)
            elif k == 1:
                result = store.instantiate(body, rhs_args[0], 0)
            else:
                result = store.instantiate_multi_rev(body, rhs_args, k, 0)
        j = k
        while j < m:
            result = store.cons_app(result, rhs_args[j])
            j += 1
        return result

    def _rule_rhs(self, target, const, ctor_head, rule):
        key = ((leaf_index(target) + 1) << 30) | leaf_index(ctor_head)
        rhs = self._rule_memo.get(key, 0)
        if rhs != 0:
            return rhs
        rhs = self.store.import_const_term(
            const, get_decl(self.tc.declarations, const.name), rule.rhs,
        )
        self._rule_memo.set(key, rhs)
        return rhs

    def _to_cnstr_when_k(self, rec, args, major):
        """
        K-like reduction: the major premise of a recursor for a
        single-constructor inductive whose type matches the
        constructor's is replaced by that constructor. 0 when the
        conditions don't hold (no iota).
        """
        store = self.store
        tc = self.tc
        tracer = tc.tracer
        old_ty = self.whnf(self.infer(major, False))
        old_const = store.const_leaf(store.head(old_ty))
        if old_const is None:
            if tracer.recording:
                tracer.klike_bail_head()
            return 0
        if len(rec.all) != 1:
            if tracer.recording:
                tracer.klike_bail_mutual()
            return 0
        ind_kind = get_decl(tc.declarations, rec.all[0]).w_kind
        assert isinstance(ind_kind, W_Inductive)
        if len(ind_kind.ctor_names) != 1:
            if tracer.recording:
                tracer.klike_bail_ctors()
            return 0
        ctor_decl = ind_kind.constructor_decls(tc.declarations)[0]
        ctor_kind = ctor_decl.w_kind
        assert isinstance(ctor_kind, W_Constructor)
        ctor = store.leaf_for(ctor_decl.name.const(old_const.levels))
        n = len(args)
        i = n - 1
        stop = n - 1 - ctor_kind.num_params
        while i > stop and i >= 0:
            ctor = store.cons_app(ctor, args[i])
            i -= 1
        new_ty = self.infer(ctor, False)
        if not self.def_eq(old_ty, new_ty):
            if tracer.recording:
                tracer.klike_bail_defeq()
            return 0
        if tracer.recording:
            tracer.klike_fired()
        return ctor

    def _to_cnstr_when_structure(self, rec_decl, rec, major):
        """
        A stuck major of non-recursive-structure type, eta-expanded to
        its constructor applied to its projections so the rule can
        fire; 0 when that doesn't apply.
        """
        store = self.store
        tc = self.tc
        induct_name = rec.major_induct_name(rec_decl.type)
        if induct_name is None:
            return 0
        ind_decl = find_decl(tc.declarations, induct_name)
        if ind_decl is None:
            return 0
        ind = ind_decl.w_kind
        if not isinstance(ind, W_Inductive):
            return 0
        if not ind.is_non_recursive_structure():
            return 0
        head_const = store.const_leaf(store.head(major))
        if head_const is not None:
            head_decl = find_decl(tc.declarations, head_const.name)
            if head_decl is not None and head_decl.w_kind.is_constructor():
                return 0
        e_type = self.whnf(self.infer(major, False))
        type_head, type_args = store.unapp(e_type)
        type_const = store.const_leaf(type_head)
        if type_const is None:
            return 0
        if not type_const.name.syntactic_eq(induct_name):
            return 0
        ctor_decl = ind.constructor_decls(tc.declarations)[0]
        ctor_kind = ctor_decl.w_kind
        assert isinstance(ctor_kind, W_Constructor)
        num_params = ctor_kind.num_params
        n = len(type_args)
        if n < num_params:
            return 0
        result = store.leaf_for(ctor_decl.name.const(type_const.levels))
        i = n - 1
        stop = n - 1 - num_params
        while i > stop:
            result = store.cons_app(result, type_args[i])
            i -= 1
        for i in range(ctor_kind.num_fields):
            result = store.cons_app(
                result, store.proj(induct_name, i, major),
            )
        return result

    # ---- inference -------------------------------------------------------

    def fvar_for(self, h):
        """The canonical free variable opening the binder record ``h``,
        whose domain is closed."""
        return self.fvar_for_domain(h, self.store.field_a(h))

    def fvar_for_domain(self, h, domain):
        """
        The canonical free variable opening the binder record ``h``
        when its domain, with the enclosing binders' variables
        substituted in, is ``domain``.
        """
        key = self._pair_key(h, domain)
        if key != 0:
            fv = self._fvars.get(key, 0)
            if fv != 0:
                return fv
        store = self.store
        binder = store.binder_of(h)
        own = binder.fvar()
        if own._uid in self._opened or store.has_fvar_leaf(own):
            fv = store.leaf_for(W_FVar(binder))
        else:
            # The binder's own variable serves its first opening, so an
            # error in it is marked where whoever opens the binder
            # outside the machine (the printer, say) puts the variable.
            self._opened[own._uid] = None
            fv = store.leaf_for(own)
        j = leaf_index(fv)
        store.leaf_infer[j] = domain
        store.leaf_checked[j] = 1
        if key != 0:
            self._fvars.set(key, fv)
        return fv

    def infer(self, h, check):
        """
        The type of ``h``. In ``check`` mode every application argument
        is checked against its domain, every binder type against being a
        sort, every let value against its type, and every constant
        against the declaration order and safety; otherwise the term is
        trusted to be well-typed and only the type is computed.
        """
        store = self.store
        if is_leaf(h):
            j = leaf_index(h)
            t = store.leaf_infer[j]
            if t != 0:
                if check and store.leaf_checked[j] == 0:
                    self._check_leaf(h)
                return t
            return self._infer_leaf(h, check)
        t = store.memo(h, M_INFER_CHECKED)
        if t != 0:
            return t
        if not check:
            t = store.memo(h, M_INFER)
            if t != 0:
                return t
        if stack_almost_full():
            raise W_DeepRecursion("infer")
        kind = store.kind(h)
        if kind == KIND_APP:
            t = self._infer_app(h, check)
        elif kind == KIND_LAMBDA:
            if store.nrecs >= _OPEN_RECORDS and self._is_heavy(h):
                t = self._infer_open_lambda(h, [], 0, check)
            else:
                t = self._infer_lambda(h, check)
        elif kind == KIND_FORALL:
            if store.nrecs >= _OPEN_RECORDS and self._is_heavy(h):
                t = self._infer_open_forall(h, [], 0, check)
            else:
                t = self._infer_forall(h, check)
        elif kind == KIND_LET:
            if store.nrecs >= _OPEN_RECORDS and self._is_heavy(h):
                t = self._infer_open_let(h, [], 0, check)
            else:
                t = self._infer_let(h, check)
        elif kind == KIND_PROJ:
            t = self._infer_proj(h, [], 0, check)
        else:
            raise RuntimeError("infer: internal pair record")
        if check:
            store.set_memo(h, M_INFER_CHECKED, t)
        store.set_memo(h, M_INFER, t)
        return t

    # Under the binders of a heavy term nothing is substituted into it:
    # its loose bound variables are read off a context instead,
    # innermost first, of what each stands for (the free variable
    # opening a binder, or a let's value). `chain` is the context as a
    # record chain, for keying what has been inferred under it. A
    # subterm is given its context's entries only where a type comes to
    # depend on it, or once it is light: substituting into a light term
    # is cheap, and what is inferred of the result is shared with its
    # every other occurrence, at whatever depth.

    def _is_heavy(self, h):
        """Whether ``h`` has `_HEAVY` nodes or more, as a tree."""
        self._budget = _HEAVY
        self._spend(h)
        return self._budget <= 0

    def _spend(self, h):
        self._budget -= 1
        if self._budget <= 0 or is_leaf(h):
            return
        store = self.store
        self._spend(store.field_a(h))
        if self._budget > 0 and store.kind(h) != KIND_PROJ:
            self._spend(store.field_b(h))

    def _is_heavy_memoised(self, h):
        known = self._heavy.get(h, 0)
        if known == 0:
            known = 2 if self._is_heavy(h) else 1
            self._heavy.set(h, known)
        return known == 2

    def _push(self, ctx, chain, entry):
        """Extend the context innermost; the extended context's chain."""
        if ctx:
            chain = self.store.cons(KIND_PAIR, entry, chain)
        else:
            chain = entry
        ctx.insert(0, entry)
        return chain

    def _pop(self, ctx, count):
        while count > 0:
            ctx.pop(0)
            count -= 1

    def _materialize(self, h, ctx, chain):
        """``h`` with the context substituted for its loose variables."""
        store = self.store
        if store.loose_bvar_range(h) == 0:
            return h
        if len(ctx) == 1:
            return store.instantiate(h, ctx[0], 0)
        return store._instantiate_multi(h, ctx, chain, 0)

    def _infer_open(self, h, ctx, chain, check):
        """The type of ``h`` with the context standing for its loose
        bound variables."""
        store = self.store
        if store.loose_bvar_range(h) == 0:
            return self.infer(h, check)
        if is_leaf(h):
            return self.infer(ctx[store.leaf_bvar[leaf_index(h)]], check)
        if not self._is_heavy_memoised(h):
            return self.infer(self._materialize(h, ctx, chain), check)
        memo = self._open_memo
        t = memo.get(h, (chain << 1) | 1, 0)
        if t != 0:
            return t
        if not check:
            t = memo.get(h, chain << 1, 0)
            if t != 0:
                return t
        if stack_almost_full():
            raise W_DeepRecursion("infer")
        kind = store.kind(h)
        if kind == KIND_APP:
            t = self._infer_open_app(h, ctx, chain, check)
        elif kind == KIND_LAMBDA:
            t = self._infer_open_lambda(h, ctx, chain, check)
        elif kind == KIND_FORALL:
            t = self._infer_open_forall(h, ctx, chain, check)
        elif kind == KIND_LET:
            t = self._infer_open_let(h, ctx, chain, check)
        elif kind == KIND_PROJ:
            t = self._infer_proj(h, ctx, chain, check)
        else:
            raise RuntimeError("infer: internal pair record")
        if check:
            memo.set(h, (chain << 1) | 1, t)
        else:
            memo.set(h, chain << 1, t)
        return t

    def _infer_open_app(self, h, ctx, chain, check):
        store = self.store
        tc = self.tc
        head, args = store.unapp(h)
        fn_type = self._infer_open(head, ctx, chain, check)
        n = len(args)
        i = n - 1
        while i >= 0:
            arg = args[i]
            if store.kind(fn_type) != KIND_FORALL:
                fn_type_whnf = self.whnf(fn_type)
                if store.kind(fn_type_whnf) != KIND_FORALL:
                    closed = [
                        self._materialize(each, ctx, chain) for each in args
                    ]
                    self._not_a_function(
                        self._materialize(head, ctx, chain), closed, i,
                        fn_type,
                    )
                fn_type = fn_type_whnf
            if check:
                arg_type = self._infer_open(arg, ctx, chain, True)
                domain = store.field_a(fn_type)
                tracing = tc.tracer.recording
                if tracing:
                    tc.tracer.begin_argcheck()
                ok = self.def_eq(domain, arg_type)
                if tracing:
                    tc.tracer.end_argcheck(self._head_label(head), n - 1 - i)
                if not ok:
                    raise W_TypeError(
                        tc,
                        self.export(self._materialize(arg, ctx, chain)),
                        self.export(domain),
                        inferred_type=self.export(arg_type),
                    )
            body = store.field_b(fn_type)
            if store.loose_bvar_range(body) > 0:
                fn_type = store.instantiate(
                    body, self._materialize(arg, ctx, chain), 0,
                )
            else:
                fn_type = body
            i -= 1
        return fn_type

    def _infer_open_lambda(self, h, ctx, chain, check):
        store = self.store
        records = []
        domains = []
        fvars = []
        e = h
        while store.kind(e) == KIND_LAMBDA:
            domain = self._materialize(store.field_a(e), ctx, chain)
            if check:
                self._ensure_sort(domain, True)
            fvar = self.fvar_for_domain(e, domain)
            records.append(e)
            domains.append(domain)
            fvars.append(fvar)
            chain = self._push(ctx, chain, fvar)
            e = store.field_b(e)
        r = self._cheap_beta(self._infer_open(e, ctx, chain, check))
        n = len(fvars)
        self._pop(ctx, n)
        # Close the telescope back up as a Pi: the body type over all
        # the variables, each domain over the variables before it.
        r = store.bind_fvars(r, fvars, 0)
        i = n - 1
        while i >= 0:
            domain = store.bind_fvars(domains[i], fvars[:i], 0)
            r = store.cons(KIND_FORALL, domain, r, store.info(records[i]))
            i -= 1
        return r

    def _infer_open_forall(self, h, ctx, chain, check):
        store = self.store
        levels = []
        e = h
        while store.kind(e) == KIND_FORALL:
            domain = self._materialize(store.field_a(e), ctx, chain)
            levels.append(self._ensure_sort(domain, check))
            chain = self._push(ctx, chain, self.fvar_for_domain(e, domain))
            e = store.field_b(e)
        t = self._infer_open(e, ctx, chain, check)
        sort = store.sort_leaf(self.whnf(t))
        if sort is None:
            raise W_NotASort(
                self.tc,
                self.export(self._materialize(e, ctx, chain)),
                inferred_type=self.export(t),
            )
        self._pop(ctx, len(levels))
        level = sort.level
        i = len(levels) - 1
        while i >= 0:
            level = levels[i].imax(level)
            i -= 1
        return store.leaf_for(level.sort())

    def _infer_open_let(self, h, ctx, chain, check):
        store = self.store
        pushed = 0
        while store.kind(h) == KIND_LET:
            pair = store.field_b(h)
            value = self._materialize(store.field_a(pair), ctx, chain)
            if check:
                type_h = self._materialize(store.field_a(h), ctx, chain)
                self._ensure_sort(type_h, True)
                value_type = self.infer(value, True)
                if not self.def_eq(value_type, type_h):
                    raise W_TypeError(
                        self.tc, self.export(value), self.export(type_h),
                        inferred_type=self.export(value_type),
                    )
            chain = self._push(ctx, chain, value)
            pushed += 1
            h = store.field_b(pair)
        t = self._infer_open(h, ctx, chain, check)
        self._pop(ctx, pushed)
        return t

    def _check_leaf(self, h):
        store = self.store
        tc = self.tc
        e = store.leaf(h)
        if isinstance(e, W_Const):
            tc.check_reference(e, get_decl(tc.declarations, e.name))
            for lvl in e.levels:
                if lvl.has_param:
                    tc.check_level(lvl)
        elif isinstance(e, W_Sort):
            if e.level.has_param:
                tc.check_level(e.level)
        store.leaf_checked[leaf_index(h)] = 1

    def _infer_leaf(self, h, check):
        store = self.store
        tc = self.tc
        j = leaf_index(h)
        e = store.leaf(h)
        if isinstance(e, W_Const):
            decl = get_decl(tc.declarations, e.name)
            if check:
                tc.check_reference(e, decl)
                for lvl in e.levels:
                    if lvl.has_param:
                        tc.check_level(lvl)
                store.leaf_checked[j] = 1
            t = store.import_const_term(e, decl, decl.type)
        elif isinstance(e, W_Sort):
            if check:
                if e.level.has_param:
                    tc.check_level(e.level)
                store.leaf_checked[j] = 1
            t = store.leaf_for(e.level.succ().sort())
        elif isinstance(e, W_LitNat):
            t = self.h_nat
            store.leaf_checked[j] = 1
        elif isinstance(e, W_LitStr):
            t = self.h_string
            store.leaf_checked[j] = 1
        elif isinstance(e, W_FVar):
            t = store.import_term(e.binder.type)
            store.leaf_checked[j] = 1
        else:
            raise LooseBoundVariable(store.leaf_bvar[j])
        store.leaf_infer[j] = t
        return t

    def _ensure_sort(self, h, check):
        """The level of the sort ``h`` has as its type."""
        t = self.infer(h, check)
        t_whnf = self.whnf(t)
        sort = self.store.sort_leaf(t_whnf)
        if sort is None:
            raise W_NotASort(self.tc, self.export(h), inferred_type=self.export(t))
        return sort.level

    def _infer_app(self, h, check):
        store = self.store
        tc = self.tc
        head, args = store.unapp(h)
        fn_type = self.infer(head, check)
        n = len(args)
        if not check:
            return self._infer_app_only(head, args, fn_type)
        pending = []
        i = n - 1
        while i >= 0:
            arg = args[i]
            if store.kind(fn_type) != KIND_FORALL:
                if pending:
                    fn_type = store.instantiate_multi_rev(
                        fn_type, pending, len(pending), 0,
                    )
                    pending = []
                fn_type = self.whnf(fn_type)
                if store.kind(fn_type) != KIND_FORALL:
                    self._not_a_function(head, args, i, fn_type)
            arg_type = self.infer(arg, True)
            domain = store.field_a(fn_type)
            plen = len(pending)
            if plen > 0 and store.loose_bvar_range(domain) > 0:
                if is_leaf(domain):
                    bid = store.leaf_bvar[leaf_index(domain)]
                    if bid < plen:
                        domain = pending[plen - 1 - bid]
                    else:
                        domain = store.bvar(bid - plen)
                elif plen == 1:
                    domain = store.instantiate(domain, pending[0], 0)
                else:
                    domain = store.instantiate_multi_rev(
                        domain, pending, plen, 0,
                    )
            tracing = tc.tracer.recording
            if tracing:
                tc.tracer.begin_argcheck()
            ok = self.def_eq(domain, arg_type)
            if tracing:
                tc.tracer.end_argcheck(self._head_label(head), n - 1 - i)
            if not ok:
                raise W_TypeError(
                    tc, self.export(arg), self.export(domain),
                    inferred_type=self.export(arg_type),
                )
            fn_type = store.field_b(fn_type)
            if store.loose_bvar_range(fn_type) == 0:
                if pending:
                    pending = []
            else:
                pending.append(arg)
            i -= 1
        if pending:
            fn_type = store.instantiate_multi_rev(
                fn_type, pending, len(pending), 0,
            )
        return fn_type

    def _infer_app_only(self, head, args, fn_type):
        """
        The type of ``head args`` given ``head``'s type, trusting the
        arguments. Walks straight through a Pi telescope's bodies and
        substitutes the pending arguments in one pass only when it has
        to reduce, so a well-typed n-ary application costs one
        substitution rather than n.
        """
        store = self.store
        n = len(args)
        pending = []
        i = n - 1
        while i >= 0:
            arg = args[i]
            if store.kind(fn_type) != KIND_FORALL:
                if pending:
                    fn_type = store.instantiate_multi_rev(
                        fn_type, pending, len(pending), 0,
                    )
                    pending = []
                fn_type = self.whnf(fn_type)
                if store.kind(fn_type) != KIND_FORALL:
                    self._not_a_function(head, args, i, fn_type)
            fn_type = store.field_b(fn_type)
            if store.loose_bvar_range(fn_type) == 0:
                if pending:
                    pending = []
            else:
                pending.append(arg)
            i -= 1
        if pending:
            fn_type = store.instantiate_multi_rev(
                fn_type, pending, len(pending), 0,
            )
        return fn_type

    def _not_a_function(self, head, args, i, fn_type):
        store = self.store
        spine = head
        j = len(args) - 1
        while j > i:
            spine = store.cons_app(spine, args[j])
            j -= 1
        raise W_NotAFunction(
            self.tc, self.export(spine), inferred_type=self.export(fn_type),
        )

    def _open_telescope(self, h, kind, check):
        """
        Open every leading binder of the given kind at once: returns
        ``(records, domains, fvars, body)`` with the domains and the
        body instantiated with the free variables of the binders
        before them. In check mode each domain is checked to be a sort.
        """
        store = self.store
        records = []
        domains = []
        fvars = []
        e = h
        while store.kind(e) == kind:
            domain = store.field_a(e)
            n = len(fvars)
            if n > 0 and store.loose_bvar_range(domain) > 0:
                domain = store.instantiate_multi_rev(domain, fvars, n, 0)
            if check:
                self._ensure_sort(domain, True)
            fvar = self.fvar_for_domain(e, domain)
            records.append(e)
            domains.append(domain)
            fvars.append(fvar)
            e = store.field_b(e)
        body = store.instantiate_multi_rev(e, fvars, len(fvars), 0)
        return records, domains, fvars, body

    def _infer_lambda(self, h, check):
        store = self.store
        records, domains, fvars, body = self._open_telescope(h, KIND_LAMBDA, check)
        r = self._cheap_beta(self.infer(body, check))
        # Close the telescope back up as a Pi: the body type over all
        # the variables, each domain over the variables before it.
        n = len(fvars)
        r = store.bind_fvars(r, fvars, 0)
        i = n - 1
        while i >= 0:
            domain = store.bind_fvars(domains[i], fvars[:i], 0)
            r = store.cons(KIND_FORALL, domain, r, store.info(records[i]))
            i -= 1
        return r

    def _infer_forall(self, h, check):
        store = self.store
        records, domains, fvars, body = self._open_telescope(h, KIND_FORALL, False)
        levels = []
        for domain in domains:
            levels.append(self._ensure_sort(domain, check))
        level = self._ensure_sort(body, check)
        i = len(levels) - 1
        while i >= 0:
            level = levels[i].imax(level)
            i -= 1
        return store.leaf_for(level.sort())

    def _cheap_beta(self, h):
        """
        Beta-reduce a head lambda application only when that costs
        nothing: the lambda's body ignores its arguments, or is just
        one of them.
        """
        store = self.store
        if store.kind(h) != KIND_APP:
            return h
        head, args = store.unapp(h)
        if store.kind(head) != KIND_LAMBDA:
            return h
        n = len(args)
        i = 0
        fn = head
        while store.kind(fn) == KIND_LAMBDA and i < n:
            i += 1
            fn = store.field_b(fn)
        if store.loose_bvar_range(fn) == 0:
            return store.apply_rev(fn, args, n - 1 - i)
        idx = store.bvar_id(fn)
        if idx >= 0 and idx < i:
            # args are outermost-first: the j-th consumed argument (in
            # application order) is args[n - 1 - j]; bvar idx names
            # the (i - 1 - idx)-th consumed one.
            return store.apply_rev(args[n - 1 - (i - 1 - idx)], args, n - 1 - i)
        return h

    def _infer_let(self, h, check):
        store = self.store
        type_h = store.field_a(h)
        pair = store.field_b(h)
        value = store.field_a(pair)
        body = store.field_b(pair)
        if check:
            self._ensure_sort(type_h, True)
            value_type = self.infer(value, True)
            if not self.def_eq(value_type, type_h):
                raise W_TypeError(
                    self.tc, self.export(value), self.export(type_h),
                    inferred_type=self.export(value_type),
                )
        return self.infer(store.instantiate(body, value, 0), check)

    def _infer_proj(self, h, ctx, chain, check):
        store = self.store
        tc = self.tc
        struct = store.field_a(h)
        field_index = store.proj_index(h)
        struct_name = store.name_of(h)
        struct_type = self.whnf(self._infer_open(struct, ctx, chain, check))
        type_head, type_args = store.unapp(struct_type)

        struct_decl = find_decl(tc.declarations, struct_name)
        if struct_decl is None:
            raise InvalidProjection.unknown_structure(
                struct_name, field_index, self.export(self._materialize(struct, ctx, chain)),
            )
        head_const = store.const_leaf(type_head)
        if head_const is None:
            raise InvalidProjection.not_a_structure_type(
                struct_name, field_index, self.export(self._materialize(struct, ctx, chain)),
            )
        if not head_const.is_named(struct_name):
            raise InvalidProjection.mismatched_structure(
                struct_name, field_index, head_const.name, self.export(self._materialize(struct, ctx, chain)),
            )
        struct_kind = struct_decl.w_kind
        if not isinstance(struct_kind, W_Inductive):
            raise InvalidProjection.not_an_inductive(
                struct_name, field_index, self.export(self._materialize(struct, ctx, chain)),
            )
        if len(struct_kind.ctor_names) != 1:
            raise InvalidProjection.not_a_structure(
                struct_name, field_index, len(struct_kind.ctor_names),
                self.export(self._materialize(struct, ctx, chain)),
            )
        ind_type = self.whnf(
            store.import_const_term(head_const, struct_decl, struct_decl.type),
        )
        ind_sort = store.sort_leaf(ind_type)
        is_prop_type = ind_sort is not None and ind_sort.level.eq(W_LEVEL_ZERO)

        ctor_decl = struct_kind.constructor_decls(tc.declarations)[0]
        ctor_type = store.import_const_term(
            head_const, ctor_decl, ctor_decl.type,
        )
        # Type arguments left to right.
        i = len(type_args) - 1
        while i >= 0:
            ctor_type = self.whnf(ctor_type)
            if store.kind(ctor_type) != KIND_FORALL:
                raise InvalidProjection.out_of_bounds(
                    struct_name, field_index, 0, self.export(self._materialize(struct, ctx, chain)),
                )
            ctor_type = store.instantiate(store.field_b(ctor_type), type_args[i], 0)
            i -= 1
        i = -1
        for i in range(field_index):
            ctor_type = self.whnf(ctor_type)
            if store.kind(ctor_type) != KIND_FORALL:
                raise InvalidProjection.out_of_bounds(
                    struct_name, field_index, i + 1, self.export(self._materialize(struct, ctx, chain)),
                )
            body = store.field_b(ctor_type)
            if store.loose_bvar_range(body) > 0:
                if is_prop_type:
                    if not self._is_prop(store.field_a(ctor_type), check):
                        raise InvalidProjection.non_prop_field(
                            struct_name, field_index, self.export(self._materialize(struct, ctx, chain)),
                        )
                ctor_type = store.instantiate(
                    body,
                    store.proj(
                        struct_name, i,
                        self._materialize(struct, ctx, chain),
                    ),
                    0,
                )
            else:
                ctor_type = body
        ctor_type = self.whnf(ctor_type)
        if store.kind(ctor_type) != KIND_FORALL:
            raise InvalidProjection.out_of_bounds(
                struct_name, field_index, i + 1, self.export(self._materialize(struct, ctx, chain)),
            )
        field_type = store.field_a(ctor_type)
        if is_prop_type:
            if not self._is_prop(field_type, check):
                raise InvalidProjection.non_prop_field(
                    struct_name, field_index, self.export(self._materialize(struct, ctx, chain)),
                )
        return field_type

    def _is_prop(self, h, check):
        """Whether the type ``h`` lives in `Prop`."""
        sort = self.store.sort_leaf(self.whnf(self.infer(h, check)))
        return sort is not None and sort.level.eq(W_LEVEL_ZERO)

    # ---- definitional equality --------------------------------------------

    def _find(self, h):
        eqv = self._eqv
        if eqv.size == 0:
            return h
        root = h
        while True:
            parent = eqv.get(root, 0)
            if parent == 0:
                break
            root = parent
        cur = h
        while cur != root:
            parent = eqv.get(cur, 0)
            eqv.set(cur, root)
            cur = parent
        return root

    def _union(self, h1, h2):
        r1 = self._find(h1)
        r2 = self._find(h2)
        if r1 != r2:
            self._eqv.set(r1, r2)

    @staticmethod
    def _pair_key(h1, h2):
        if h1 >= (1 << 31) or h2 >= (1 << 31):
            return 0
        return (h1 << 31) | h2

    def def_eq(self, h1, h2):
        """Whether ``h1`` and ``h2`` are definitionally equal."""
        tc = self.tc
        env = tc.env
        max_heartbeat = env.max_heartbeat
        if max_heartbeat > 0 or env.count_heartbeats:
            tc.heartbeat += 1
            if max_heartbeat > 0 and tc.heartbeat > max_heartbeat:
                raise HeartbeatExceeded(tc.decl, tc.heartbeat, max_heartbeat)
        tc.tick_wall_time()
        tracer = tc.tracer
        tracing = tracer.recording
        if tracing:
            # Rendering both sides is only worth it when the tracer
            # writes them out; a counting tracer just takes the tally.
            if tracer.writes:
                tracer.enter(self.export(h1), self.export(h2), tc.declarations)
            else:
                tracer.counted_enter()
        if h1 == h2:
            if tracing:
                tracer.identity_hit()
                return self._traced_result(True)
            return True
        if self._eqv.size > 0 and self._find(h1) == self._find(h2):
            if tracing:
                tracer.eqv_hit()
                return self._traced_result(True)
            return True
        key = self._pair_key(h1, h2)
        if self._neq.size > 0 and key != 0 and self._neq.get(key, 0) != 0:
            if tracing:
                return self._traced_result(False)
            return False
        store = self.store
        if (self._eqv.size > 0
                and store.kind(h1) == KIND_APP
                and store.kind(h2) == KIND_APP):
            if self._spine_cheap_eq(h1, h2):
                self._union(h1, h2)
                if tracing:
                    tracer.eqv_hit()
                    return self._traced_result(True)
                return True
        if stack_almost_full():
            raise W_DeepRecursion("def_eq")
        result = self._def_eq_uncached(h1, h2)
        if result:
            self._union(h1, h2)
        elif key != 0:
            self._neq.set(key, 1)
            key2 = self._pair_key(h2, h1)
            if key2 != 0:
                self._neq.set(key2, 1)
        if tracing:
            return self._traced_result(result)
        return result

    def _traced_result(self, result):
        tracer = self.tc.tracer
        if tracer.writes:
            return tracer.result(result)
        return tracer.counted_result(result)

    def _spine_cheap_eq(self, h1, h2):
        store = self.store
        while True:
            a1 = store.field_b(h1)
            a2 = store.field_b(h2)
            if a1 != a2 and self._find(a1) != self._find(a2):
                return False
            f1 = store.field_a(h1)
            f2 = store.field_a(h2)
            if f1 == f2:
                return True
            app1 = store.kind(f1) == KIND_APP
            app2 = store.kind(f2) == KIND_APP
            if app1 and app2:
                h1 = f1
                h2 = f2
                continue
            if app1 or app2:
                return False
            return self._find(f1) == self._find(f2)

    def _head_label(self, h):
        """A short label for a comparison histogram: the head constant's
        name, or the kind of the head."""
        store = self.store
        head = store.head(h)
        const = store.const_leaf(head)
        if const is not None:
            return const.name.str()
        kind = store.kind(head)
        if kind == 0:
            e = store.leaf(head)
            if isinstance(e, W_FVar):
                return "<fvar>"
            if isinstance(e, W_Sort):
                return "<sort>"
            return "<lit>"
        if kind == KIND_LAMBDA:
            return "<lambda>"
        if kind == KIND_FORALL:
            return "<pi>"
        if kind == KIND_PROJ:
            return "<proj " + store.name_of(head).str() + ">"
        return "<let>"

    def _is_scalar_target(self, h):
        if h == self.h_true or h == self.h_false or h == self.h_nat_zero:
            return True
        return self.store.litnat_leaf(h) is not None

    def _is_closed_compound(self, h):
        if is_leaf(h):
            return False
        return (
            not self.store.has_fvar(h)
            and self.store.loose_bvar_range(h) == 0
        )

    def _def_eq_uncached(self, h1, h2):
        store = self.store
        tracer = self.tc.tracer
        # Closed-term call-by-need fast path: when comparing a closed
        # compound term against a Bool or Nat scalar (e.g. `decide +kernel`
        # or `beta-ladder`), evaluate it in the meta-traced abstract machine
        # before eager substitution touches it.
        if not tracer.recording:
            if (self._is_scalar_target(h2) and self._is_closed_compound(h1)
                    and self._nat_succ_pred(h1) == 0):
                ev = eval_closed_scalar(self, h1)
                if ev != 0:
                    if ev == h2:
                        return True
                    h1 = ev
            elif (self._is_scalar_target(h1) and self._is_closed_compound(h2)
                    and self._nat_succ_pred(h2) == 0):
                ev = eval_closed_scalar(self, h2)
                if ev != 0:
                    if ev == h1:
                        return True
                    h2 = ev
        h1 = self.whnf_core(h1, True)
        h2 = self.whnf_core(h2, True)
        if h1 == h2:
            return True

        # Proof irrelevance, before any unfolding.
        t1 = self.infer(h1, False)
        s1 = self.infer(t1, False)
        if s1 != self.h_prop:
            s1 = self.whnf(s1)
        if s1 == self.h_prop:
            t2 = self.infer(h2, False)
            s2 = self.infer(t2, False)
            if s2 != self.h_prop:
                s2 = self.whnf(s2)
            if s2 == self.h_prop:
                if self.def_eq(t1, t2):
                    if tracer.recording:
                        tracer.pi_hit()
                    return True

        offset = self._def_eq_offset(h1, h2)
        if offset == _OFFSET_TRUE:
            return True
        if offset == _OFFSET_FALSE:
            return False

        if h2 == self.h_true:
            if self.whnf(h1) == self.h_true:
                return True
        elif h1 == self.h_true:
            if self.whnf(h2) == self.h_true:
                return True

        status, h1, h2 = self._try_lazy_delta(h1, h2)
        if status == _LD_TRUE:
            return True
        if h1 == h2:
            return True
        # Before evaluating projected structures in full, try matching two
        # projections (bare or applied) of the same struct/field lazily.
        if self._def_eq_proj_lazy(h1, h2):
            return True
        # Now with projections evaluated in full: if that changes either
        # side, start the comparison over on the new forms.
        n1 = self.whnf_core(h1)
        n2 = self.whnf_core(h2)
        if n1 != h1 or n2 != h2:
            return self.def_eq(n1, n2)
        return self._def_eq_core(h1, h2)

    def _proj_lazy_eq(self, h1, h2, rem, depth):
        """Bounded cheap definitional equality check for two projected
        structures (no full projection reduction, no unbounded recursion).
        Uses a single shared step budget ``rem`` across all recursive calls
        so wide Mathlib typeclass diamonds never branch exponentially.
        Returns ``(ok, remaining_budget)``."""
        store = self.store
        while True:
            if h1 == h2 or (self._eqv.size > 0 and self._find(h1) == self._find(h2)):
                return True, rem
            h1 = self.whnf_core(h1, True)
            h2 = self.whnf_core(h2, True)
            if h1 == h2 or (self._eqv.size > 0 and self._find(h1) == self._find(h2)):
                return True, rem
            head1 = store.head(h1)
            head2 = store.head(h2)
            if depth > 0 and self._same_const(head1, head2):
                _, args1 = store.unapp(h1)
                _, args2 = store.unapp(h2)
                if len(args1) == len(args2):
                    all_eq = True
                    j = len(args1) - 1
                    while j >= 0:
                        if args1[j] != args2[j]:
                            ok, rem = self._proj_lazy_eq(
                                args1[j], args2[j], rem, depth - 1,
                            )
                            if not ok:
                                all_eq = False
                                break
                        j -= 1
                    if all_eq:
                        self._union(h1, h2)
                        return True, rem
            if rem <= 0:
                return False, 0
            kind1 = self._delta_kind(head1)
            kind2 = self._delta_kind(head2)
            if kind1 is None and kind2 is None:
                return False, rem
            rem -= 1
            if kind1 is None:
                new2 = self.try_unfold_head(h2)
                if new2 == 0:
                    return False, rem
                h2 = new2
            elif kind2 is None:
                new1 = self.try_unfold_head(h1)
                if new1 == 0:
                    return False, rem
                h1 = new1
            else:
                hint1 = kind1.hint
                hint2 = kind2.hint
                if (hint1 == HINT_ABBREV and hint2 != HINT_ABBREV) or hint1 > hint2:
                    new1 = self.try_unfold_head(h1)
                    if new1 == 0:
                        return False, rem
                    h1 = new1
                elif (hint2 == HINT_ABBREV and hint1 != HINT_ABBREV) or hint2 > hint1:
                    new2 = self.try_unfold_head(h2)
                    if new2 == 0:
                        return False, rem
                    h2 = new2
                else:
                    new1 = self.try_unfold_head(h1)
                    new2 = self.try_unfold_head(h2)
                    if new1 == 0 and new2 == 0:
                        return False, rem
                    if new1 != 0:
                        h1 = new1
                    if new2 != 0:
                        h2 = new2

    def _def_eq_proj_lazy(self, h1, h2):
        """Compare two bare or applied projections of the same structure
        and field using a bounded cheap check on their underlying structures
        before forcing full projection reduction."""
        store = self.store
        k1 = store.kind(h1)
        k2 = store.kind(h2)
        if k1 == KIND_PROJ and k2 == KIND_PROJ:
            if store.field_b(h1) == store.field_b(h2):
                if self._failed_before(h1, h2):
                    return False
                ok, _ = self._proj_lazy_eq(
                    store.field_a(h1), store.field_a(h2), 8, 3,
                )
                if ok:
                    return True
                self._cache_failure(h1, h2)
            return False
        if k1 == KIND_APP and k2 == KIND_APP:
            head1 = store.head(h1)
            head2 = store.head(h2)
            if (store.kind(head1) == KIND_PROJ
                    and store.kind(head2) == KIND_PROJ
                    and store.field_b(head1) == store.field_b(head2)):
                if self._failed_before(h1, h2) or self._failed_before(head1, head2):
                    return False
                _, args1 = store.unapp(h1)
                _, args2 = store.unapp(h2)
                if len(args1) != len(args2):
                    return False
                ok, rem = self._proj_lazy_eq(
                    store.field_a(head1), store.field_a(head2), 8, 3,
                )
                if not ok:
                    self._cache_failure(head1, head2)
                    return False
                self._union(head1, head2)
                j = len(args1) - 1
                while j >= 0:
                    if args1[j] != args2[j]:
                        ok, rem = self._proj_lazy_eq(args1[j], args2[j], rem, 2)
                        if not ok:
                            self._cache_failure(h1, h2)
                            return False
                    j -= 1
                return True
        return False

    def _def_eq_offset(self, h1, h2):
        store = self.store
        while True:
            lit1 = store.litnat_leaf(h1)
            lit2 = store.litnat_leaf(h2)
            if lit1 is not None and lit2 is not None:
                if lit1.val.eq(lit2.val):
                    return _OFFSET_TRUE
                return _OFFSET_FALSE
            z1 = self._is_nat_zero(h1)
            z2 = self._is_nat_zero(h2)
            if z1 and z2:
                return _OFFSET_TRUE
            pred1 = self._nat_succ_pred(h1)
            if pred1 == 0:
                if z1 and self._nat_succ_pred(h2) != 0:
                    return _OFFSET_FALSE
                return _OFFSET_UNDEF
            pred2 = self._nat_succ_pred(h2)
            if pred2 == 0:
                if z2:
                    return _OFFSET_FALSE
                return _OFFSET_UNDEF
            self.tc.tick_wall_time()
            h1 = pred1
            h2 = pred2

    def _unfold_or_nat(self, h):
        """Try native Nat arithmetic before delta-unfolding a closed Nat op."""
        store = self.store
        if store.kind(h) == KIND_APP and not store.has_fvar(h):
            reduced = self.try_reduce_nat(h)
            if reduced != 0:
                return reduced
        return self.try_unfold_head(h)

    def _is_closed_ite(self, h, head):
        """Whether ``h`` is a fully-applied `ite`/`dite` whose `Decidable`
        instance argument is closed (no free variables), so unfolding it
        can take a branch without reducing an open condition."""
        store = self.store
        if store.kind(h) != KIND_APP:
            return False
        const = store.const_leaf(head)
        if const is None:
            return False
        name = const.name
        if not (name.syntactic_eq(_ITE_NAME) or name.syntactic_eq(_DITE_NAME)):
            return False
        _, args = store.unapp(h)
        n = len(args)
        if n < 5:
            return False
        inst_idx = n - 3
        assert inst_idx >= 0
        return not store.has_fvar(args[inst_idx])

    def _is_short_circuit_bool(self, head):
        const = self.store.const_leaf(head)
        if const is None:
            return False
        name = const.name
        return (
            name.syntactic_eq(_BOOL_AND_NAME)
            or name.syntactic_eq(_BOOL_OR_NAME)
            or name.syntactic_eq(_AND_NAME)
            or name.syntactic_eq(_OR_NAME)
        )

    def _bool_arg0_reducible(self, fn):
        """Whether the first argument of a 2-arg boolean op ``(op a) b``
        is a concrete Bool constructor or a reducible boolean combinator."""
        store = self.store
        arg0 = store.field_b(fn)
        if arg0 == self.h_true or arg0 == self.h_false:
            return True
        c = store.const_leaf(store.head(arg0))
        if c is None:
            return False
        name = c.name
        return (
            name.syntactic_eq(_BOOL_AND_NAME)
            or name.syntactic_eq(_BOOL_OR_NAME)
            or name.syntactic_eq(_AND_NAME)
            or name.syntactic_eq(_OR_NAME)
            or name.syntactic_eq(_BOOL_NOT_NAME)
            or name.syntactic_eq(_ITE_NAME)
            or name.syntactic_eq(_DITE_NAME)
            or name.syntactic_eq(_COND_NAME)
        )

    def _is_nat_binop_head(self, head):
        const = self.store.const_leaf(head)
        return const is not None and is_nat_binop(const.name)

    def _try_lazy_delta(self, h1, h2):
        store = self.store
        for _ in range(self._LAZY_DELTA_MAX_ITER):
            if h1 == h2:
                return _LD_TRUE, h1, h2
            peeled = False
            while True:
                lit1 = store.litnat_leaf(h1)
                lit2 = store.litnat_leaf(h2)
                if lit1 is not None and lit2 is not None:
                    if lit1.val.eq(lit2.val):
                        return _LD_TRUE, h1, h2
                    break
                pred1 = self._nat_succ_pred(h1)
                if pred1 == 0:
                    break
                pred2 = self._nat_succ_pred(h2)
                if pred2 == 0:
                    break
                self.tc.tick_wall_time()
                h1 = pred1
                h2 = pred2
                peeled = True
            if peeled:
                h1 = self.whnf_core(h1, True)
                h2 = self.whnf_core(h2, True)
                if h1 == h2:
                    return _LD_TRUE, h1, h2

            if not store.has_fvar(h1) and not store.has_fvar(h2):
                if store.kind(h1) == KIND_APP:
                    reduced = self.try_reduce_nat_cheap(h1)
                    if reduced != 0:
                        h1 = reduced
                        continue
                if store.kind(h2) == KIND_APP:
                    reduced = self.try_reduce_nat_cheap(h2)
                    if reduced != 0:
                        h2 = reduced
                        continue

            head1 = store.head(h1)
            head2 = store.head(h2)
            kind1 = self._delta_kind(head1)
            kind2 = self._delta_kind(head2)
            if kind1 is None and kind2 is None:
                return _LD_UNDEF, h1, h2

            if kind1 is None:
                new2 = self._unfold_or_nat(h2)
                if new2 == 0:
                    return _LD_UNDEF, h1, h2
                if store.kind(head1) == KIND_PROJ:
                    c2 = self.whnf_core(new2, True)
                    if self._def_eq_proj_lazy(h1, c2):
                        return _LD_TRUE, h1, c2
                    h2 = self.whnf_core(c2)
                else:
                    h2 = self.whnf_core(new2)
                continue
            if kind2 is None:
                new1 = self._unfold_or_nat(h1)
                if new1 == 0:
                    return _LD_UNDEF, h1, h2
                if store.kind(head2) == KIND_PROJ:
                    c1 = self.whnf_core(new1, True)
                    if self._def_eq_proj_lazy(c1, h2):
                        return _LD_TRUE, c1, h2
                    h1 = self.whnf_core(c1)
                else:
                    h1 = self.whnf_core(new1)
                continue

            hint1 = kind1.hint
            hint2 = kind2.hint
            if hint1 == HINT_ABBREV and hint2 != HINT_ABBREV:
                new1 = self._unfold_or_nat(h1)
                if new1 == 0:
                    return _LD_UNDEF, h1, h2
                h1 = self.whnf_core(new1)
                continue
            if hint2 == HINT_ABBREV and hint1 != HINT_ABBREV:
                new2 = self._unfold_or_nat(h2)
                if new2 == 0:
                    return _LD_UNDEF, h1, h2
                h2 = self.whnf_core(new2)
                continue

            # Unfold a closed-condition `ite`/`dite` before an unrelated
            # regular definition so taking a branch (e.g.
            # `if true = true then big else other = big`) resolves without
            # evaluating the taken branch.
            ite1 = self._is_closed_ite(h1, head1)
            ite2 = self._is_closed_ite(h2, head2)
            if ite1 and not ite2:
                new1 = self.try_unfold_head(h1)
                if new1 != 0:
                    h1 = self.whnf_core(new1)
                    continue
            if ite2 and not ite1:
                new2 = self.try_unfold_head(h2)
                if new2 != 0:
                    h2 = self.whnf_core(new2)
                    continue

            if hint1 >= 0 and self._same_const(head1, head2):
                # Short-circuit `Bool.and`/`Bool.or` when the first argument
                # is already a concrete Bool or boolean combinator, instead of
                # comparing potentially expensive discarded second arguments.
                skip_same_head = False
                if (self._is_short_circuit_bool(head1)
                        and store.kind(h1) == KIND_APP
                        and store.kind(h2) == KIND_APP):
                    fn1 = store.field_a(h1)
                    fn2 = store.field_a(h2)
                    if (store.kind(fn1) == KIND_APP
                            and store.kind(fn2) == KIND_APP
                            and (self._bool_arg0_reducible(fn1)
                                 or self._bool_arg0_reducible(fn2))):
                        skip_same_head = True
                if not skip_same_head:
                    args1 = store.unapp(h1)[1]
                    args2 = store.unapp(h2)[1]
                    if len(args1) == len(args2):
                        if not self._failed_before(h1, h2):
                            all_eq = True
                            j = len(args1) - 1
                            while j >= 0:
                                if not self.def_eq(args1[j], args2[j]):
                                    all_eq = False
                                    break
                                j -= 1
                            if all_eq:
                                return _LD_TRUE, h1, h2
                            self._cache_failure(h1, h2)

            # Unfold a regular non-Nat-binop definition before forcing native
            # Nat reduction on the other side's potentially expensive args
            # (e.g. `[slowA, 1].sum = slowA + (1 + 0)`).
            nat1 = self._is_nat_binop_head(head1)
            nat2 = self._is_nat_binop_head(head2)
            if nat2 and not nat1:
                new1 = self.try_unfold_head(h1)
                if new1 != 0:
                    h1 = self.whnf_core(new1)
                    continue
            if nat1 and not nat2:
                new2 = self.try_unfold_head(h2)
                if new2 != 0:
                    h2 = self.whnf_core(new2)
                    continue

            if hint1 > hint2:
                new1 = self._unfold_or_nat(h1)
                if new1 == 0:
                    return _LD_UNDEF, h1, h2
                h1 = self.whnf_core(new1)
                continue
            if hint1 < hint2:
                new2 = self._unfold_or_nat(h2)
                if new2 == 0:
                    return _LD_UNDEF, h1, h2
                h2 = self.whnf_core(new2)
                continue

            new1 = self._unfold_or_nat(h1)
            new2 = self._unfold_or_nat(h2)
            if new1 == 0 and new2 == 0:
                return _LD_UNDEF, h1, h2
            if new1 != 0 and new2 != 0:
                c1 = self.whnf_core(new1, True)
                c2 = self.whnf_core(new2, True)
                if c1 == c2 or self._def_eq_proj_lazy(c1, c2):
                    return _LD_TRUE, c1, c2
                h1 = self.whnf_core(c1)
                h2 = self.whnf_core(c2)
            elif new1 != 0:
                h1 = self.whnf_core(new1)
            elif new2 != 0:
                h2 = self.whnf_core(new2)
        return _LD_UNDEF, h1, h2

    def _same_const(self, head1, head2):
        """Whether two constant heads name the same declaration at
        universes that are equal, if not identical, level expressions."""
        if head1 == head2:
            return True
        c1 = self.store.const_leaf(head1)
        c2 = self.store.const_leaf(head2)
        if c1 is None or c2 is None:
            return False
        return c1.name.syntactic_eq(c2.name) and c1.def_eq(c2)

    def _failed_before(self, h1, h2):
        if self._failed.size == 0:
            return False
        key = self._pair_key(h1, h2)
        return key != 0 and self._failed.get(key, 0) != 0

    def _cache_failure(self, h1, h2):
        key = self._pair_key(h1, h2)
        if key != 0:
            self._failed.set(key, 1)
        key = self._pair_key(h2, h1)
        if key != 0:
            self._failed.set(key, 1)

    def _def_eq_core(self, h1, h2):
        store = self.store
        kind1 = store.kind(h1)
        kind2 = store.kind(h2)
        if kind1 == 0 and kind2 == 0:
            e1 = store.leaf(h1)
            e2 = store.leaf(h2)
            cls1 = e1.__class__
            if cls1 is e2.__class__:
                if cls1 is W_LitNat or cls1 is W_LitStr:
                    # Distinct canonical literal leaves are unequal.
                    return False
                if cls1 is W_Sort:
                    assert isinstance(e1, W_Sort)
                    assert isinstance(e2, W_Sort)
                    if e1.level.eq(e2.level):
                        return True
                elif cls1 is W_Const:
                    assert isinstance(e1, W_Const)
                    assert isinstance(e2, W_Const)
                    if e1.name.syntactic_eq(e2.name) and e1.def_eq(e2):
                        return True
                # Free variables are canonical by identity: unequal.
        elif kind1 == kind2:
            if kind1 == KIND_APP:
                if self._def_eq_app(h1, h2):
                    return True
            elif kind1 == KIND_LAMBDA or kind1 == KIND_FORALL:
                if self._def_eq_binders(h1, h2):
                    return True
            elif kind1 == KIND_PROJ:
                if (store.field_b(h1) == store.field_b(h2)
                        and self.def_eq(store.field_a(h1), store.field_a(h2))):
                    return True

        eta2 = self.try_eta_expand(h1, h2)
        if eta2 != 0:
            return self.def_eq(h1, eta2)
        eta1 = self.try_eta_expand(h2, h1)
        if eta1 != 0:
            return self.def_eq(eta1, h2)

        if self.try_struct_eta(h1, h2):
            return True
        if self.try_struct_eta(h2, h1):
            return True

        if self.def_eq_unit(h1, h2):
            return True

        lit1 = store.litnat_leaf(h1)
        if lit1 is not None:
            return self.def_eq(
                store.import_term(lit1.one_step_constructor()), h2,
            )
        lit2 = store.litnat_leaf(h2)
        if lit2 is not None:
            return self.def_eq(
                h1, store.import_term(lit2.one_step_constructor()),
            )
        if is_leaf(h1):
            s1 = store.leaf(h1)
            if isinstance(s1, W_LitStr):
                return self.def_eq(
                    store.import_term(s1.build_str_expr()), h2,
                )
        if is_leaf(h2):
            s2 = store.leaf(h2)
            if isinstance(s2, W_LitStr):
                return self.def_eq(
                    h1, store.import_term(s2.build_str_expr()),
                )
        return False

    def _def_eq_app(self, h1, h2):
        store = self.store
        fn1 = store.field_a(h1)
        if store.kind(fn1) == KIND_LAMBDA:
            if self.def_eq(store.instantiate(store.field_b(fn1), store.field_b(h1), 0), h2):
                return True
        fn2 = store.field_a(h2)
        if store.kind(fn2) == KIND_LAMBDA:
            if self.def_eq(h1, store.instantiate(store.field_b(fn2), store.field_b(h2), 0)):
                return True
        args1 = []
        args2 = []
        while store.kind(h1) == KIND_APP and store.kind(h2) == KIND_APP:
            args1.append(store.field_b(h1))
            args2.append(store.field_b(h2))
            h1 = store.field_a(h1)
            h2 = store.field_a(h2)
        if not self.def_eq(h1, h2):
            return False
        if len(args1) != len(args2):
            return False
        i = len(args1) - 1
        while i >= 0:
            if not self.def_eq(args1[i], args2[i]):
                return False
            i -= 1
        return True

    def _def_eq_binders(self, h1, h2):
        store = self.store
        if not self.def_eq(store.field_a(h1), store.field_a(h2)):
            return False
        fvar = self.fvar_for(h1)
        return self.def_eq(
            store.instantiate(store.field_b(h1), fvar, 0),
            store.instantiate(store.field_b(h2), fvar, 0),
        )

    def try_eta_expand(self, h1, h2):
        """``fun x => h2 x`` when ``h1`` is a lambda and ``h2`` is not
        but has a function type; 0 otherwise."""
        store = self.store
        if store.kind(h1) != KIND_LAMBDA or store.kind(h2) == KIND_LAMBDA:
            return 0
        t2 = self.whnf(self.infer(h2, False))
        if store.kind(t2) != KIND_FORALL:
            return 0
        body = store.cons_app(store.shift(h2, 1, 0), store.bvar(0))
        return store.cons(KIND_LAMBDA, store.field_a(t2), body, store.info(t2))

    def try_struct_eta(self, ctor_side, other_side):
        """``S.mk (S.p₁ x) … (S.pₙ x) ≟ x``."""
        store = self.store
        tc = self.tc
        head, args = store.unapp(ctor_side)
        const = store.const_leaf(head)
        if const is None:
            return False
        ctor_decl = self._decl(const)
        if ctor_decl is None:
            return False
        ctor_kind = ctor_decl.w_kind
        if not isinstance(ctor_kind, W_Constructor):
            return False
        num_params = ctor_kind.num_params
        num_fields = ctor_kind.num_fields
        n = len(args)
        if n != num_params + num_fields:
            return False
        ctor_ty = self.whnf(self.infer(ctor_side, False))
        result_const = store.const_leaf(store.head(ctor_ty))
        if result_const is None:
            return False
        struct_name = result_const.name
        ind_decl = find_decl(tc.declarations, struct_name)
        if ind_decl is None or not isinstance(ind_decl.w_kind, W_Inductive):
            return False
        ind = ind_decl.w_kind
        assert isinstance(ind, W_Inductive)
        if not ind.is_non_recursive_structure():
            return False
        if not self.def_eq(ctor_ty, self.infer(other_side, False)):
            return False
        i = 0
        while i < num_fields:
            proj = store.proj(struct_name, i, other_side)
            if not self.def_eq(proj, args[n - 1 - (num_params + i)]):
                return False
            i += 1
        return True

    def def_eq_unit(self, h1, h2):
        store = self.store
        tc = self.tc
        t1 = self.whnf(self.infer(h1, False))
        const = store.const_leaf(store.head(t1))
        if const is None:
            return False
        decl = self._decl(const)
        if decl is None:
            return False
        ind = decl.w_kind
        if not isinstance(ind, W_Inductive):
            return False
        if not ind.is_non_recursive_structure():
            return False
        if ind.num_indices != 0:
            return False
        first_ctor = ind.constructor_decls(tc.declarations)[0].w_kind
        assert isinstance(first_ctor, W_Constructor)
        if first_ctor.num_fields != 0:
            return False
        return self.def_eq(t1, self.infer(h2, False))

    # ---- checking --------------------------------------------------------

    def check_value(self, type, value, prop):
        """
        Check a definition-like declaration: ``type`` must be a sort (a
        proposition when ``prop``, for a theorem) and ``value`` must
        have that type. Returns ``None`` when accepted, a `W_CheckError`
        when rejected.
        """
        store = self.store
        tc = self.tc
        if value.loose_bvar_range() > 0:
            raise LooseBoundVariable(value.loose_bvar_range() - 1)
        ty = store.import_term(type)
        val = store.import_term(value)
        ty_ty = self.infer(ty, True)
        ty_ty_whnf = self.whnf(ty_ty)
        sort = store.sort_leaf(ty_ty_whnf)
        if sort is None:
            return W_NotASort(tc, type, inferred_type=self.export(ty_ty), name=None)
        if prop and not sort.level.eq(W_LEVEL_ZERO):
            return W_NotAProp(tc, type, inferred_sort=sort, name=None)
        val_ty = self.infer(val, True)
        if tc.tracer.recording:
            tc.tracer.phase("infer value")
        ok = self.def_eq(ty, val_ty)
        if tc.tracer.recording:
            tc.tracer.phase("def_eq type")
        if not ok:
            return W_TypeError(tc, value, type, inferred_type=self.export(val_ty))
        return None


_OFFSET_UNDEF = 0
_OFFSET_TRUE = 1
_OFFSET_FALSE = 2
_LD_TRUE = 1
_LD_UNDEF = 0


class _Spare(object):
    """The machine of the last declaration checked, emptied."""

    def __init__(self):
        self.machine = None


_SPARE = _Spare()


def acquire(tc):
    """A machine for ``tc``'s declaration: the spare one, if there is one."""
    machine = _SPARE.machine
    if machine is None:
        return Machine(tc)
    _SPARE.machine = None
    machine.tc = tc
    machine.store.tc = tc
    return machine


def release(machine):
    """Hand back a machine whose declaration has been checked."""
    machine._census()
    if _SPARE.machine is None:
        machine.reset()
        _SPARE.machine = machine
    else:
        machine.free()
