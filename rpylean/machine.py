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

from rpython.rlib.objectmodel import always_inline, dont_inline, newlist_hint, we_are_translated
from rpython.rlib.rarithmetic import intmask, r_uint
from rpython.rlib.rstack import stack_almost_full
from rpython.rtyper.lltypesystem import lltype, rffi

from rpython.rlib.rbigint import rbigint

from rpylean._eval import eval_closed_scalar
from rpylean.exceptions import (
    InvalidProjection,
    LooseBoundVariable,
)
from rpylean.objects import (
    HINT_ABBREV,
    NAT,
    NAT_ZERO,
    PROP,
    SAFETY_SAFE,
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
    W_LevelParam,
    W_LevelSucc,
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
    _PROP_MASK_DONE,
    _PROP_MASK_PLANS,
    _expr_has_bvar_lt,
    _mk_w_const1,
    _mk_w_const2,
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
_INFO_MASK = 0xFFFFFF
_SIZE_SHIFT = 24
_HEAVY_ENC = 255
_PROJ_SHIFT = 10
_PROJ_MASK = (1 << _PROJ_SHIFT) - 1
_PROJ_OVF_NAME = _PROJ_MASK
_PROJ_OVF_BASE = _PROJ_OVF_NAME << _PROJ_SHIFT

# Per-record memo slots (parallel to the records, 0 = not yet known).
MEMO_SLOTS = 6
M_WHNF_CORE = 0
M_WHNF = 1
M_INFER = 2
M_CHECKED_GEN = 3
M_WHNF_CORE_CHEAP = 4
M_EQV = 5
#: High bit set in `M_WHNF_CORE_CHEAP` on a `_LF_DELTA` `KIND_APP` record to
#: cache its one-step `try_unfold_head` result. Any record carrying this tag is
#: a delta-headed `KIND_APP` and therefore already in `whnf_core` normal form
#: (both full and cheap).
_UNFOLD_TAG = 0x80000000
_UNFOLD_MASK = 0x7FFFFFFF

_SIGNED_ARRAY = rffi.CArray(lltype.Signed)
_U32_ARRAY = rffi.CArray(rffi.UINT)
_I32_ARRAY = rffi.CArray(rffi.INT)
_NO_INFO = 0


@always_inline
def _u32(x):
    return rffi.cast(rffi.UINT, x)


@always_inline
def _i32(x):
    return rffi.cast(rffi.INT, x)


@always_inline
def _s32(x):
    return rffi.cast(lltype.Signed, x)


@always_inline
def _si32(x):
    return rffi.cast(lltype.Signed, x)


def _alloc_u32(n):
    return lltype.malloc(_U32_ARRAY, n, flavor='raw', zero=True)


def _alloc_u32_uninit(n):
    return lltype.malloc(_U32_ARRAY, n, flavor='raw', zero=False)


def _free_u32(arr):
    lltype.free(arr, flavor='raw')


def _zero_u32(arr, n):
    """Zero ``arr``'s first ``n`` 32-bit entries."""
    if n <= 0:
        return
    if we_are_translated():
        rffi.c_memset(
            rffi.cast(rffi.VOIDP, arr), 0, n * rffi.sizeof(rffi.UINT),
        )
    else:
        z = _u32(0)
        i = 0
        while i < n:
            arr[i] = z
            i += 1


def _grow_u32(arr, used, cap):
    """A fresh 32-bit array of ``cap`` entries holding ``arr``'s first
    ``used`` entries; ``arr`` is freed."""
    new = _alloc_u32(cap)
    if we_are_translated():
        rffi.c_memcpy(
            rffi.cast(rffi.VOIDP, new), rffi.cast(rffi.CONST_VOIDP, arr),
            used * rffi.sizeof(rffi.UINT),
        )
    else:
        i = 0
        while i < used:
            new[i] = arr[i]
            i += 1
    _free_u32(arr)
    return new


def _grow_u32_uninit(arr, used, cap):
    """Like `_grow_u32`, leaving entries `[used:cap]` uninitialized."""
    new = _alloc_u32_uninit(cap)
    if we_are_translated():
        rffi.c_memcpy(
            rffi.cast(rffi.VOIDP, new), rffi.cast(rffi.CONST_VOIDP, arr),
            used * rffi.sizeof(rffi.UINT),
        )
    else:
        i = 0
        while i < used:
            new[i] = arr[i]
            i += 1
    _free_u32(arr)
    return new


def _alloc_i32(n):
    return lltype.malloc(_I32_ARRAY, n, flavor='raw', zero=True)


def _free_i32(arr):
    lltype.free(arr, flavor='raw')


def _zero_i32(arr, n):
    if n <= 0:
        return
    if we_are_translated():
        rffi.c_memset(
            rffi.cast(rffi.VOIDP, arr), 0, n * rffi.sizeof(rffi.INT),
        )
    else:
        z = _i32(0)
        i = 0
        while i < n:
            arr[i] = z
            i += 1


def _grow_i32(arr, used, cap):
    new = _alloc_i32(cap)
    if we_are_translated():
        rffi.c_memcpy(
            rffi.cast(rffi.VOIDP, new), rffi.cast(rffi.CONST_VOIDP, arr),
            used * rffi.sizeof(rffi.INT),
        )
    else:
        i = 0
        while i < used:
            new[i] = arr[i]
            i += 1
    _free_i32(arr)
    return new


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
_APP_PACK_LIMIT = 1 << 21
_APP_SLOT_MASK = (1 << 21) - 1
_OTHER_PACK_LIMIT = 1 << 20
_OTHER_SLOT_MASK = (1 << 20) - 1
_U32_KEY_LIMIT = 1 << 31
_U32_VAL_MASK = 0xFFFFFFFF
_CACHE_GEN_LIMIT = 1 << 31
_BVAR_ARR_LEN = 256
_LGEN_SIZE = 512
_LGEN_MASK = _LGEN_SIZE - 1


@dont_inline
def _check_stack_store(label):
    if stack_almost_full():
        raise W_DeepRecursion(label)


def _subst_level_fast(lvl, params, clevels):
    """Fast level substitution for `W_LevelParam` without virtual dispatch."""
    if not lvl.has_param:
        return lvl
    if lvl.__class__ is W_LevelParam:
        assert isinstance(lvl, W_LevelParam)
        lname = lvl.name
        n = len(params)
        if n == 1:
            return clevels[0] if lname is params[0] else lvl
        if n == 2:
            if lname is params[0]:
                return clevels[0]
            if lname is params[1]:
                return clevels[1]
            return lvl
        i = 0
        while i < n:
            if lname is params[i]:
                return clevels[i]
            i += 1
        return lvl
    return lvl.subst_levels_lists(params, clevels)


def _level_subst_eq(lvl, params, clevels, target_lvl):
    """Whether substituting ``params -> clevels`` in ``lvl`` produces a level
    semantically equal to ``target_lvl``, avoiding `W_LevelSucc` allocation on
    common `Type u` / `Sort (u + 1)` comparisons."""
    while lvl.__class__ is W_LevelSucc and target_lvl.__class__ is W_LevelSucc:
        assert isinstance(lvl, W_LevelSucc)
        assert isinstance(target_lvl, W_LevelSucc)
        lvl = lvl.parent
        target_lvl = target_lvl.parent
    sub = _subst_level_fast(lvl, params, clevels)
    return sub is target_lvl or sub.eq(target_lvl)


class _CacheGen(object):
    _attrs_ = ['count']

    def __init__(self):
        self.count = 0


_CACHE_GEN = _CacheGen()


@always_inline
def _next_cache_gen():
    g = _CACHE_GEN.count + 1
    if g < _CACHE_GEN_LIMIT:
        _CACHE_GEN.count = g
        return g
    return -1
_LF_CLASSIFIED = 1
_LF_RECURSOR = 2
_LF_QUOT_LIFT = 4
_LF_DELTA = 8
_LF_CTOR = 16
_LF_NAT_BINOP = 32
_LF_ITE = 64
_LF_SHORT_BOOL = 128
_LF_BOOL_ARG0 = 256
_LF_NAT_SUCC = 512
_LF_NAT_ZERO = 1024
_LF_HINT_SHIFT = 16
_LF_HINT_OVF = 65535
#: Tag bits (60..61) of `TermStore.leaf_delta_body[j]` for fast unfolds that
#: bypass `import_const_term` and `instantiate`:
#:   0 = generic stripped body `(arity << 32) | body_handle`
#:   1 = identity/arg-picker `λ... => BVar(b)`: `_DB_BVAR_TAG | (m << 32) | b`
#:   2 = projection `λ... => Proj(S, idx, BVar(b))`:
#:       `_DB_PROJ_TAG | (m << 52) | (b << 44) | (name_id << 24) | proj_packed`
_DB_TAG_SHIFT = 60
_DB_BVAR_TAG = 1 << 60
_DB_PROJ_TAG = 2 << 60
_STORE_KEEP_CAP = 1 << 18
_WARM_MAX_RECS = 196608
_WARM_MAX_LEAVES = 1 << 16
_WARM_MAX_EQV = 1 << 17
_WARM_MAX_NEQ = 1 << 17
_WARM_MAX_FAILED = 1 << 17
#: Sentinel stored in `leaf_checked` and `M_CHECKED_GEN` for closed ground
#: leaves/records proven well-typed under `SAFETY_SAFE`, `group < 0`, zero
#: `W_LevelParam`s, and `decl.index < current.index`. Valid across all
#: subsequent monotonic warm declarations even after `check_gen` bumps.
_CHECKED_PERM = 0x7FFFFFFF
#: Sentinel stored in `TermStore.leaf_infer[j]` after a `W_Const` leaf has been
#: checked once via the AST-direct `_infer_app` path. Single-use constants
#: (~78% of `_infer_leaf` records) never import their `decl.type`, while a
#: second application promotes the constant into `TermStore` for fast flat
#: `u32` checking and `_infer_app_expected_pat` reuse.
_LEAF_INFER_SEEN = 0x7FFFFFFF


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
    n = len(levels)
    normalized = None
    i = 0
    while i < n:
        level = levels[i]
        nl = level.normalize()
        if nl is not level:
            if normalized is None:
                normalized = list(levels)
            normalized[i] = nl
        i += 1
    c = const if normalized is None else const.name.const(normalized)
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

    @always_inline
    def get(self, key, default):
        if not we_are_translated():
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
        if not we_are_translated():
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


class IntSet(object):
    """
    A compact 8-byte/slot open-addressed set of non-zero signed 64-bit keys
    (16 entries per 128-byte cache line), with sparse clearing and an optional
    capacity limit for pure caches like `Machine._neq` and `Machine._failed`.
    """

    _attrs_ = [
        'entries', 'dirty', '_dirty_count', 'mask', 'size',
        'initial', 'keep_cap', 'limit',
    ]

    def __init__(self, capacity=1 << 10, keep_cap=1 << 15, limit=0):
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.initial = cap
        self.keep_cap = keep_cap if keep_cap >= cap else cap
        self.limit = limit
        self.entries = _alloc_words(cap)
        self.dirty = _alloc_words(_DIRTY_CAP)
        self._dirty_count = 0
        self.mask = cap - 1
        self.size = 0

    def clear(self):
        sz = self.size
        if sz == 0:
            self._dirty_count = 0
            return
        cap = self.mask + 1
        if cap > self.keep_cap and sz * 8 < cap:
            _free_words(self.entries)
            cap = self.keep_cap
            self.entries = _alloc_words(cap)
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
            _zero_words(self.entries, cap)
        self.size = 0
        self._dirty_count = 0

    @always_inline
    def contains(self, key):
        if not we_are_translated():
            assert key != 0
        mask = self.mask
        entries = self.entries
        i = _spread(key) & mask
        while True:
            k = entries[i]
            if k == key:
                return True
            if k == 0:
                return False
            i = (i + 1) & mask

    def add(self, key):
        if not we_are_translated():
            assert key != 0
        if (self.size + 1) * 2 > self.mask + 1:
            self._grow()
        mask = self.mask
        entries = self.entries
        i = _spread(key) & mask
        while True:
            k = entries[i]
            if k == key:
                return
            if k == 0:
                entries[i] = key
                dc = self._dirty_count
                if dc >= 0:
                    if dc < _DIRTY_CAP:
                        self.dirty[dc] = i
                        self._dirty_count = dc + 1
                    else:
                        self._dirty_count = -1
                self.size += 1
                return
            i = (i + 1) & mask

    def _grow(self):
        old_cap = self.mask + 1
        if self.limit > 0 and old_cap >= self.limit:
            _zero_words(self.entries, old_cap)
            self.size = 0
            self._dirty_count = 0
            return
        old_entries = self.entries
        cap = old_cap * 2
        entries = _alloc_words(cap)
        mask = cap - 1
        i = 0
        while i < old_cap:
            k = old_entries[i]
            if k != 0:
                j = _spread(k) & mask
                while entries[j] != 0:
                    j = (j + 1) & mask
                entries[j] = k
            i += 1
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


class U32Map(object):
    """
    A compact 8-byte/slot open-addressed map for positive 31-bit keys ->
    unsigned 32-bit values (`(key << 32) | val`). Halves cache footprint
    versus `IntMap` (16 entries per 128-byte cache line), falling back
    losslessly to a lazy `IntMap` for out-of-range keys or values.
    """

    _attrs_ = [
        'entries', 'dirty', '_dirty_count', 'mask', 'size',
        'initial', 'keep_cap', 'overflow',
    ]

    def __init__(self, capacity=1 << 10, keep_cap=1 << 15):
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.initial = cap
        self.keep_cap = keep_cap if keep_cap >= cap else cap
        self.entries = _alloc_words(cap)
        self.dirty = _alloc_words(_DIRTY_CAP)
        self._dirty_count = 0
        self.mask = cap - 1
        self.size = 0
        self.overflow = None

    def clear(self):
        if self.overflow is not None:
            self.overflow.clear()
        sz = self.size
        if sz == 0:
            self._dirty_count = 0
            return
        cap = self.mask + 1
        if cap > self.keep_cap and sz * 8 < cap:
            _free_words(self.entries)
            cap = self.keep_cap
            self.entries = _alloc_words(cap)
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
            _zero_words(self.entries, cap)
        self.size = 0
        self._dirty_count = 0

    @dont_inline
    def _get_overflow(self, key, default):
        if self.overflow is not None:
            return self.overflow.get(key, default)
        return default

    @always_inline
    def get(self, key, default):
        if not we_are_translated():
            assert key > 0
        if key >= _U32_KEY_LIMIT:
            return self._get_overflow(key, default)
        mask = self.mask
        entries = self.entries
        i = _spread(key) & mask
        while True:
            entry = entries[i]
            if (entry >> 32) == key:
                return entry & _U32_VAL_MASK
            if entry == 0:
                return default
            i = (i + 1) & mask

    @dont_inline
    def _set_overflow(self, key, val):
        ov = self.overflow
        if ov is None:
            ov = self.overflow = IntMap(1 << 8)
        ov.set(key, val)

    def set(self, key, val):
        if not we_are_translated():
            assert key > 0
            assert 0 <= val <= _U32_VAL_MASK
        if key >= _U32_KEY_LIMIT:
            self._set_overflow(key, val)
            return
        if (self.size + 1) * 2 > self.mask + 1:
            self._grow()
        mask = self.mask
        entries = self.entries
        packed = (key << 32) | val
        i = _spread(key) & mask
        while True:
            entry = entries[i]
            if (entry >> 32) == key:
                entries[i] = packed
                return
            if entry == 0:
                entries[i] = packed
                dc = self._dirty_count
                if dc >= 0:
                    if dc < _DIRTY_CAP:
                        self.dirty[dc] = i
                        self._dirty_count = dc + 1
                    else:
                        self._dirty_count = -1
                self.size += 1
                return
            i = (i + 1) & mask

    def _grow(self):
        old_cap = self.mask + 1
        old_entries = self.entries
        cap = old_cap * 2
        entries = _alloc_words(cap)
        mask = cap - 1
        i = 0
        while i < old_cap:
            entry = old_entries[i]
            if entry != 0:
                j = _spread(entry >> 32) & mask
                while entries[j] != 0:
                    j = (j + 1) & mask
                entries[j] = entry
            i += 1
        self.entries = entries
        self.mask = mask
        self._dirty_count = -1
        _free_words(old_entries)

    def free(self):
        if self.overflow is not None:
            self.overflow.free()
            self.overflow = None
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
        'app_table', 'app_mask', 'napps', '_app_limit', 'app_wide', 'app_wide_mask',
        'table', 'tmask', 'nother', '_other_limit',
        'call_slot', '_call_epoch',
        '_spine_buf', '_spine_cap', '_spine_top',
        '_subst_stack', '_subst_cap', '_subst_top',
        'leaves', 'leaf_decl', 'leaf_meta', 'leaf_whnf', 'leaf_infer',
        'leaf_checked', 'leaf_delta', 'leaf_delta_body',
        'leaf_next', 'leaf_eqv', 'leaf_head_kind', 'leaf_prop_mask',
        'nleaves', 'leaf_cap',
        'infos', 'names', '_name_ids', '_proj_overflow',
        '_bvar_arr', '_bvar_max', '_bvar_leaves', '_fvar_uid', '_content_head',
        '_store_gen', '_import_spine', '_import_spine_len',
        '_fvar_gens', '_fvar_gens_len', '_fvar_base_gen', '_fvar_multi',
        '_lgen1_p', '_lgen1_l', '_lgen1_g', '_lgen1_dirty',
        '_lgen2_p0', '_lgen2_p1', '_lgen2_l0', '_lgen2_l1', '_lgen2_g', '_lgen2_dirty',
        '_lgenN_p', '_lgenN_l', '_lgenN_g', '_lgenN_dirty',
        'rec_node', '_rec_node_dirty', 'nodes', 'record_nodes',
        '_inst_memo', '_shift_memo', '_bind_memo', '_multi_memo',
        '_call_memo', '_bind_lo', '_bind_span', '_inst_all_closed',
        '_freed', 'initial_cap',
    ]

    def __init__(self, tc, capacity=1 << 14):
        self.tc = tc
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.initial_cap = cap
        self._call_epoch = 1
        self._alloc_records(cap)
        self._spine_cap = 4096
        self._spine_buf = _alloc_u32_uninit(self._spine_cap)
        self._spine_top = 0
        self._subst_cap = 4096
        self._subst_stack = _alloc_u32_uninit(self._subst_cap)
        self._subst_top = 0
        self._bind_lo = 0
        self._bind_span = r_uint(0)
        self._inst_all_closed = -1
        #: Leaves by index; `leaf_meta` mirrors `(loose_bvar_range << 1) | has_fvar`
        #: in 32 bits (for a `W_BVar(id)`, `leaf_meta == (id + 1) << 1 > 1`, so
        #: `id == (leaf_meta >> 1) - 1` without a separate `leaf_bvar` array).
        self.leaf_cap = 1 << 10
        self.leaf_meta = _alloc_u32_uninit(self.leaf_cap)
        self.leaf_whnf = _alloc_u32(self.leaf_cap)
        #: A leaf's inferred type (0 = not yet), and the `check_gen` under
        #: which its reference check ran.
        self.leaf_infer = _alloc_u32(self.leaf_cap)
        self.leaf_checked = _alloc_u32(self.leaf_cap)
        #: Delta-unfolded handle for a constant leaf (0 = uncached, -1 = none).
        self.leaf_delta = _alloc_i32(self.leaf_cap)
        #: Stripped delta-unfold body for an applied constant leaf:
        #: 0 = uncached, -1 = none, else `(arity << 32) | body_handle` after
        #: peeling all leading `W_Lambda` binders without importing their types.
        self.leaf_delta_body = _alloc_words(self.leaf_cap)
        #: Collision chain for unmanaged `_content_head` leaf interning.
        self.leaf_next = _alloc_u32(self.leaf_cap)
        #: Union-find parent handle for proven-def-eq leaves (0 = root).
        self.leaf_eqv = _alloc_u32(self.leaf_cap)
        #: Packed classification flags & definition hint (`_LF_*`).
        self.leaf_head_kind = _alloc_u32(self.leaf_cap)
        #: Per-leaf bitmask of argument positions (0..61) whose domain lives
        #: in `Prop`, with `_PROP_MASK_DONE` (bit 62) marking computed entries.
        self.leaf_prop_mask = _alloc_words(self.leaf_cap)
        #: Flat array for small bound-variable leaf handles (`id < 256`).
        self._bvar_arr = _alloc_words(_BVAR_ARR_LEN)
        self._bvar_max = 0
        #: Per-store `W_FVar._uid -> leaf handle` map (preserves FVar identity
        #: even when multiple `TermStore`s coexist).
        self._fvar_uid = U32Map(1 << 8, keep_cap=1 << 12)
        #: `(e.hash() & 0x7FFFFFFF or 1) -> first canonical leaf handle`.
        self._content_head = U32Map(1 << 11, keep_cap=1 << 15)
        #: Unique generation tag stamping `W_Expr._cache` for this store epoch.
        self._store_gen = _next_cache_gen()
        self._import_spine = []
        self._import_spine_len = 0
        self._fvar_gens = [0] * 64
        self._fvar_gens_len = 0
        self._fvar_base_gen = 0
        self._fvar_multi = None
        #: Direct-mapped per-epoch level-substitution generation caches so
        #: polymorphic DAG subterms shared across declarations at the same
        #: concrete universe levels reuse `W_Expr._cache` hits.
        self._lgen1_p = [None] * _LGEN_SIZE
        self._lgen1_l = [None] * _LGEN_SIZE
        self._lgen1_g = _alloc_words(_LGEN_SIZE)
        self._lgen1_dirty = False
        self._lgen2_p0 = [None] * _LGEN_SIZE
        self._lgen2_p1 = [None] * _LGEN_SIZE
        self._lgen2_l0 = [None] * _LGEN_SIZE
        self._lgen2_l1 = [None] * _LGEN_SIZE
        self._lgen2_g = _alloc_words(_LGEN_SIZE)
        self._lgen2_dirty = False
        self._lgenN_p = [None] * _LGEN_SIZE
        self._lgenN_l = [None] * _LGEN_SIZE
        self._lgenN_g = _alloc_words(_LGEN_SIZE)
        self._lgenN_dirty = False
        self.record_nodes = True
        self._inst_memo = SubstMemo(1 << 12)
        self._shift_memo = SubstMemo(1 << 10)
        self._bind_memo = SubstMemo(1 << 10)
        self._multi_memo = SubstMemo(1 << 11)
        #: Scratch memo for rare multi-depth collisions in one-shot substitutions.
        self._call_memo = IntMap(1 << 11, keep_cap=1 << 14)
        self._freed = False
        self._forget()

    def _alloc_records(self, cap):
        self.cap = cap
        self.recs = _alloc_u32_uninit(cap << 2)
        self.memos = _alloc_u32(cap * MEMO_SLOTS)
        #: record index -> 1 + its index in `nodes`, or 0: lazily allocated
        #: only when `record_nodes` or `export_term` actually records a node.
        self.rec_node = lltype.nullptr(_U32_ARRAY)
        self._rec_node_dirty = False
        #: Single-word generation-stamped scratch memo for one-shot
        #: substitutions: `(((epoch << 8) | depth) << 32) | handle`.
        self.call_slot = _alloc_words(cap)
        #: Dedicated single-word `(fn:21 | arg:21 | slot:21)` hash table for
        #: `KIND_APP` records (8 bytes/slot, zero `recs[]` loads on hit),
        #: promoted to interleaved 16-byte `app_wide` if handles exceed 2^21.
        app_cap = cap * 2
        self.app_table = _alloc_words(app_cap)
        self.app_mask = app_cap - 1
        self._app_limit = _APP_PACK_LIMIT
        self.app_wide = lltype.nullptr(_SIGNED_ARRAY)
        self.app_wide_mask = 0
        #: Hash table for non-`KIND_APP` records (lambda/forall/proj/let/pair),
        #: single-word packed `(kind:3 | a:20 | b:20 | slot:20)` below 2^20.
        other_cap = cap >> 1
        if other_cap < 64:
            other_cap = 64
        self.table = _alloc_words(other_cap)
        self.tmask = other_cap - 1
        self._other_limit = _OTHER_PACK_LIMIT

    def _free_records(self):
        _free_u32(self.recs)
        if self.rec_node:
            _free_u32(self.rec_node)
            self.rec_node = lltype.nullptr(_U32_ARRAY)
        self._rec_node_dirty = False
        _free_u32(self.memos)
        _free_words(self.call_slot)
        if self.app_table:
            _free_words(self.app_table)
        if self.app_wide:
            _free_words(self.app_wide)
        _free_words(self.table)

    def _forget(self):
        """Start over on everything the garbage collector looks after."""
        self.nrecs = 0
        self.napps = 0
        self.nother = 0
        self.nleaves = 0
        lhint = self.leaf_cap if self.leaf_cap <= 8192 else 8192
        self.leaves = newlist_hint(lhint)
        self.leaf_decl = newlist_hint(lhint)
        #: Binder infos (`Binder`s, for the name and style) and
        #: `Name`s (for projections and lets), by `F_INFO` index.
        self.infos = newlist_hint(1024)
        self.names = []
        self._name_ids = name_dict()
        self._proj_overflow = []
        self._bvar_leaves = {}
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
        if (self._app_limit == 0
                or self._other_limit == 0
                or (self.cap > keep_cap and n * 8 < self.cap)
                or (self.app_mask + 1 > keep_cap * 2 and self.napps * 8 < self.app_mask + 1)):
            self._free_records()
            self._alloc_records(keep_cap)
            self._call_epoch = 1
        else:
            self._clear_app_table(n)
            self._clear_table(n)
            _zero_u32(self.memos, n * MEMO_SLOTS)
            if self._rec_node_dirty:
                _zero_u32(self.rec_node, n)
                self._rec_node_dirty = False
            if self._call_epoch >= (1 << 22):
                _zero_words(self.call_slot, self.cap)
                self._call_epoch = 1
            else:
                self._call_epoch += 1
        self._spine_top = 0
        self._subst_top = 0
        leaves = self.nleaves
        _zero_u32(self.leaf_whnf, leaves)
        _zero_u32(self.leaf_infer, leaves)
        _zero_u32(self.leaf_checked, leaves)
        _zero_i32(self.leaf_delta, leaves)
        _zero_words(self.leaf_delta_body, leaves)
        _zero_u32(self.leaf_next, leaves)
        _zero_u32(self.leaf_eqv, leaves)
        _zero_u32(self.leaf_head_kind, leaves)
        _zero_words(self.leaf_prop_mask, leaves)
        if self._bvar_max > 0:
            _zero_words(self._bvar_arr, self._bvar_max)
            self._bvar_max = 0
        self._fvar_uid.clear()
        self._content_head.clear()
        self._store_gen = _next_cache_gen()
        self.clear_fvar_gens()
        if self._lgen1_dirty:
            p = self._lgen1_p
            l = self._lgen1_l
            i = 0
            while i < _LGEN_SIZE:
                p[i] = None
                l[i] = None
                i += 1
            self._lgen1_dirty = False
        if self._lgen2_dirty:
            p0 = self._lgen2_p0
            p1 = self._lgen2_p1
            l0 = self._lgen2_l0
            l1 = self._lgen2_l1
            i = 0
            while i < _LGEN_SIZE:
                p0[i] = None
                p1[i] = None
                l0[i] = None
                l1[i] = None
                i += 1
            self._lgen2_dirty = False
        if self._lgenN_dirty:
            pn = self._lgenN_p
            ln = self._lgenN_l
            i = 0
            while i < _LGEN_SIZE:
                pn[i] = None
                ln[i] = None
                i += 1
            self._lgenN_dirty = False
        self._inst_memo.clear()
        self._shift_memo.clear()
        self._bind_memo.clear()
        self._multi_memo.clear()
        self._call_memo.clear()
        self._forget()

    def _clear_app_table(self, n):
        app_table = self.app_table
        amask = self.app_mask
        if self.napps * 16 > amask:
            _zero_words(app_table, amask + 1)
            return
        recs = self.recs
        idx = n - 1
        while idx >= 0:
            base = idx << 2
            if (_s32(recs[base]) & _KIND_MASK) == KIND_APP:
                pair = (_s32(recs[base + F_A]) << 21) | _s32(recs[base + F_B])
                expected = (pair << 21) | (idx + 1)
                i = _spread(pair) & amask
                while app_table[i] != expected:
                    i = (i + 1) & amask
                app_table[i] = 0
            idx -= 1

    def _clear_table(self, n):
        table = self.table
        tmask = self.tmask
        if self.nother * 16 > tmask:
            _zero_words(table, tmask + 1)
            return
        recs = self.recs
        idx = n - 1
        while idx >= 0:
            base = idx << 2
            kind = _s32(recs[base]) & _KIND_MASK
            if kind != KIND_APP:
                key = (
                    (kind << 40)
                    | (_s32(recs[base + F_A]) << 20)
                    | _s32(recs[base + F_B])
                )
                expected = (key << 20) | (idx + 1)
                i = _spread(key) & tmask
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
        _free_u32(self._spine_buf)
        _free_u32(self._subst_stack)
        _free_u32(self.leaf_meta)
        _free_u32(self.leaf_whnf)
        _free_u32(self.leaf_infer)
        _free_u32(self.leaf_checked)
        _free_i32(self.leaf_delta)
        _free_words(self.leaf_delta_body)
        _free_u32(self.leaf_next)
        _free_u32(self.leaf_eqv)
        _free_u32(self.leaf_head_kind)
        _free_words(self.leaf_prop_mask)
        _free_words(self._bvar_arr)
        _free_words(self._lgen1_g)
        _free_words(self._lgen2_g)
        _free_words(self._lgenN_g)
        self._fvar_uid.free()
        self._content_head.free()
        self._inst_memo.free()
        self._shift_memo.free()
        self._bind_memo.free()
        self._multi_memo.free()
        self._call_memo.free()

    # ---- record access ---------------------------------------------------

    @always_inline
    def kind(self, h):
        if is_leaf(h):
            return 0
        return _s32(self.recs[rec_index(h) << 2]) & _KIND_MASK

    @always_inline
    def field_a(self, h):
        return _s32(self.recs[(rec_index(h) << 2) + F_A])

    @always_inline
    def field_b(self, h):
        return _s32(self.recs[(rec_index(h) << 2) + F_B])

    @always_inline
    def proj_index(self, h):
        packed = _s32(self.recs[(rec_index(h) << 2) + F_B])
        if packed >= _PROJ_OVF_BASE:
            return self._proj_overflow[packed - _PROJ_OVF_BASE][1]
        return packed & _PROJ_MASK

    @always_inline
    def meta(self, h):
        if is_leaf(h):
            return _s32(self.leaf_meta[leaf_index(h)])
        return _s32(self.recs[rec_index(h) << 2]) >> 3

    @always_inline
    def loose_bvar_range(self, h):
        return self.meta(h) >> 1

    @always_inline
    def has_fvar(self, h):
        return (self.meta(h) & 1) != 0

    @always_inline
    def info(self, h):
        return _s32(self.recs[(rec_index(h) << 2) + F_INFO]) & _INFO_MASK

    @always_inline
    def is_heavy(self, h):
        return (
            not is_leaf(h)
            and (_s32(self.recs[(rec_index(h) << 2) + F_INFO]) >> _SIZE_SHIFT) == _HEAVY_ENC
        )

    @always_inline
    def memo(self, h, slot):
        return _s32(self.memos[rec_index(h) * MEMO_SLOTS + slot])

    @always_inline
    def set_memo(self, h, slot, value):
        self.memos[rec_index(h) * MEMO_SLOTS + slot] = _u32(value)

    @always_inline
    def eqv_get(self, h):
        if is_leaf(h):
            return _s32(self.leaf_eqv[leaf_index(h)])
        return _s32(self.memos[rec_index(h) * MEMO_SLOTS + M_EQV])

    @always_inline
    def eqv_set(self, h, parent):
        if is_leaf(h):
            self.leaf_eqv[leaf_index(h)] = _u32(parent)
        else:
            self.memos[rec_index(h) * MEMO_SLOTS + M_EQV] = _u32(parent)

    def binder_of(self, h):
        """The `Binder` recorded for a lambda or forall record."""
        return self.infos[self.info(h)]

    def name_of(self, h):
        """The `Name` recorded for a projection or let record."""
        return self.names[self.info(h)]

    def leaf(self, h):
        """The `W_Expr` a leaf handle names."""
        return self.leaves[leaf_index(h)]

    @always_inline
    def bvar_id(self, h):
        """The de Bruijn index of a bound-variable leaf, else -1."""
        if not is_leaf(h):
            return -1
        m = _s32(self.leaf_meta[leaf_index(h)])
        return (m >> 1) - 1 if m > 1 else -1

    # ---- consing ---------------------------------------------------------

    @always_inline
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
        """Dedicated fast path for `KIND_APP` records with single-word packed
        `(fn:21 | arg:21 | slot:21)` lookup (8 bytes/slot, zero `recs[]` load
        on hit), promoting losslessly to 16-byte `app_wide` above 2^21."""
        if (fn | arg) >= self._app_limit:
            return self._cons_app_wide(fn, arg)
        pair = (fn << 21) | arg
        app_table = self.app_table
        amask = self.app_mask
        i = _spread(pair) & amask
        while True:
            entry = app_table[i]
            if (entry >> 21) == pair:
                return (entry & _APP_SLOT_MASK) << 1
            if entry == 0:
                return self._cons_app_miss(fn, arg, pair, i)
            i = (i + 1) & amask

    @dont_inline
    def _cons_app_miss(self, fn, arg, pair, i):
        idx = self.nrecs
        if idx + 1 >= _APP_PACK_LIMIT:
            return self._cons_app_wide(fn, arg)
        if idx == self.cap:
            self._grow_records()
        recs = self.recs
        if is_leaf(fn):
            ma = _s32(self.leaf_meta[leaf_index(fn)])
            ea = 0
        else:
            fbase = rec_index(fn) << 2
            ma = _s32(recs[fbase]) >> 3
            ea = _s32(recs[fbase + F_INFO]) >> _SIZE_SHIFT
        if is_leaf(arg):
            mb = _s32(self.leaf_meta[leaf_index(arg)])
            eb = 0
        else:
            abase = rec_index(arg) << 2
            mb = _s32(recs[abase]) >> 3
            eb = _s32(recs[abase + F_INFO]) >> _SIZE_SHIFT
        la = ma & ~1
        lb = mb & ~1
        meta = (la if la > lb else lb) | ((ma | mb) & 1)
        sz = ea + eb + 2
        if sz > _HEAVY_ENC:
            sz = _HEAVY_ENC
        base = idx << 2
        recs[base] = _u32((meta << 3) | KIND_APP)
        recs[base + F_A] = _u32(fn)
        recs[base + F_B] = _u32(arg)
        recs[base + F_INFO] = _u32(sz << _SIZE_SHIFT)
        self.nrecs = idx + 1
        napps = self.napps + 1
        self.napps = napps
        if napps * 2 > self.app_mask + 1:
            self._rehash_apps()
        else:
            self.app_table[i] = (pair << 21) | (idx + 1)
        return rec_handle(idx)

    @dont_inline
    def _promote_apps_to_wide(self):
        wcap = self.app_mask + 1
        while wcap < self.napps * 2 + 2:
            wcap *= 2
        app_wide = _alloc_words(wcap << 1)
        wmask = wcap - 1
        recs = self.recs
        idx = 0
        n = self.nrecs
        while idx < n:
            base = idx << 2
            if (_s32(recs[base]) & _KIND_MASK) == KIND_APP:
                key = (_s32(recs[base + F_A]) << 32) | _s32(recs[base + F_B])
                i = _spread(key) & wmask
                while app_wide[i << 1] != 0:
                    i = (i + 1) & wmask
                p = i << 1
                app_wide[p] = key
                app_wide[p + 1] = rec_handle(idx)
            idx += 1
        _free_words(self.app_table)
        self.app_table = lltype.nullptr(_SIGNED_ARRAY)
        self.app_mask = 0
        self._app_limit = 0
        self.app_wide = app_wide
        self.app_wide_mask = wmask

    @dont_inline
    def _rehash_app_wide(self):
        _free_words(self.app_wide)
        wcap = (self.app_wide_mask + 1) * 2
        app_wide = _alloc_words(wcap << 1)
        wmask = wcap - 1
        recs = self.recs
        idx = 0
        n = self.nrecs
        while idx < n:
            base = idx << 2
            if (_s32(recs[base]) & _KIND_MASK) == KIND_APP:
                key = (_s32(recs[base + F_A]) << 32) | _s32(recs[base + F_B])
                i = _spread(key) & wmask
                while app_wide[i << 1] != 0:
                    i = (i + 1) & wmask
                p = i << 1
                app_wide[p] = key
                app_wide[p + 1] = rec_handle(idx)
            idx += 1
        self.app_wide = app_wide
        self.app_wide_mask = wmask

    @dont_inline
    def _cons_app_promote_and_insert(self, fn, arg):
        self._promote_apps_to_wide()
        key = (fn << 32) | arg
        app_wide = self.app_wide
        wmask = self.app_wide_mask
        i = _spread(key) & wmask
        while True:
            p = i << 1
            k = app_wide[p]
            if k == key:
                return app_wide[p + 1]
            if k == 0:
                return self._cons_app_wide_miss(fn, arg, key, i)
            i = (i + 1) & wmask

    @dont_inline
    def _cons_app_wide(self, fn, arg):
        if self._app_limit != 0:
            return self._cons_app_promote_and_insert(fn, arg)
        key = (fn << 32) | arg
        app_wide = self.app_wide
        wmask = self.app_wide_mask
        i = _spread(key) & wmask
        while True:
            p = i << 1
            k = app_wide[p]
            if k == key:
                return app_wide[p + 1]
            if k == 0:
                return self._cons_app_wide_miss(fn, arg, key, i)
            i = (i + 1) & wmask

    @dont_inline
    def _cons_app_wide_miss(self, fn, arg, key, i):
        idx = self.nrecs
        if idx == self.cap:
            self._grow_records()
        recs = self.recs
        if is_leaf(fn):
            ma = _s32(self.leaf_meta[leaf_index(fn)])
            ea = 0
        else:
            fbase = rec_index(fn) << 2
            ma = _s32(recs[fbase]) >> 3
            ea = _s32(recs[fbase + F_INFO]) >> _SIZE_SHIFT
        if is_leaf(arg):
            mb = _s32(self.leaf_meta[leaf_index(arg)])
            eb = 0
        else:
            abase = rec_index(arg) << 2
            mb = _s32(recs[abase]) >> 3
            eb = _s32(recs[abase + F_INFO]) >> _SIZE_SHIFT
        la = ma & ~1
        lb = mb & ~1
        meta = (la if la > lb else lb) | ((ma | mb) & 1)
        sz = ea + eb + 2
        if sz > _HEAVY_ENC:
            sz = _HEAVY_ENC
        base = idx << 2
        recs[base] = _u32((meta << 3) | KIND_APP)
        recs[base + F_A] = _u32(fn)
        recs[base + F_B] = _u32(arg)
        recs[base + F_INFO] = _u32(sz << _SIZE_SHIFT)
        self.nrecs = idx + 1
        h = rec_handle(idx)
        napps = self.napps + 1
        self.napps = napps
        if napps * 2 > self.app_wide_mask + 1:
            self._rehash_app_wide()
        else:
            p = i << 1
            app_wide = self.app_wide
            app_wide[p] = key
            app_wide[p + 1] = h
        return h

    @always_inline
    def cons(self, kind, a, b, info=_NO_INFO):
        """
        The record ``(kind, a, b)``, creating it if new. ``info`` is
        not part of the identity: the first recorded binder or name
        stands for every later alpha-equal request.
        """
        if kind == KIND_APP:
            return self.cons_app(a, b)
        return self._cons_general(kind, a, b, info)

    @always_inline
    def _size_enc_for(self, kind, a, b):
        recs = self.recs
        ea = 0 if is_leaf(a) else (_s32(recs[(rec_index(a) << 2) + F_INFO]) >> _SIZE_SHIFT)
        if kind == KIND_PROJ:
            sz = ea + 1
        else:
            eb = 0 if is_leaf(b) else (_s32(recs[(rec_index(b) << 2) + F_INFO]) >> _SIZE_SHIFT)
            sz = ea + eb + 2
        return _HEAVY_ENC if sz > _HEAVY_ENC else sz

    def _cons_general(self, kind, a, b, info):
        """Dedicated single-word packed `(kind:3 | a:20 | b:20 | slot:20)`
        hash table for non-`KIND_APP` records (zero `recs[]` load on hit),
        promoting losslessly to tag+`recs[]` mode above 2^20."""
        if (a | b) >= self._other_limit:
            return self._cons_general_wide(kind, a, b, info)
        key = (kind << 40) | (a << 20) | b
        table = self.table
        tmask = self.tmask
        i = _spread(key) & tmask
        while True:
            entry = table[i]
            if (entry >> 20) == key:
                return (entry & _OTHER_SLOT_MASK) << 1
            if entry == 0:
                return self._cons_general_miss(kind, a, b, info, key, i)
            i = (i + 1) & tmask

    @dont_inline
    def _cons_general_miss(self, kind, a, b, info, key, i, binder=None):
        idx = self.nrecs
        if idx + 1 >= _OTHER_PACK_LIMIT:
            return self._cons_general_wide(kind, a, b, info, binder)
        if binder is not None:
            info = self._info_index(binder)
        if idx == self.cap:
            self._grow_records()
        meta = self._meta_for(kind, a, b)
        sz = self._size_enc_for(kind, a, b)
        base = idx << 2
        recs = self.recs
        recs[base] = _u32((meta << 3) | kind)
        recs[base + F_A] = _u32(a)
        recs[base + F_B] = _u32(b)
        recs[base + F_INFO] = _u32((sz << _SIZE_SHIFT) | (info & _INFO_MASK))
        self.nrecs = idx + 1
        nother = self.nother + 1
        self.nother = nother
        if nother * 2 > self.tmask + 1:
            self._rehash()
        else:
            self.table[i] = (key << 20) | (idx + 1)
        return rec_handle(idx)

    @dont_inline
    def _promote_other_to_wide(self):
        cap = self.tmask + 1
        while cap < self.nother * 2 + 2:
            cap *= 2
        table = _alloc_words(cap)
        tmask = cap - 1
        recs = self.recs
        idx = 0
        n = self.nrecs
        while idx < n:
            base = idx << 2
            kind = _s32(recs[base]) & _KIND_MASK
            if kind != KIND_APP:
                hh = _hash_rec(
                    kind, _s32(recs[base + F_A]), _s32(recs[base + F_B]),
                )
                i = hh & tmask
                while table[i] != 0:
                    i = (i + 1) & tmask
                table[i] = (((hh >> 32) & _TABLE_TAG_MASK) << 32) | (idx + 1)
            idx += 1
        _free_words(self.table)
        self.table = table
        self.tmask = tmask
        self._other_limit = 0

    @dont_inline
    def _rehash_wide(self):
        _free_words(self.table)
        cap = (self.tmask + 1) * 2
        table = _alloc_words(cap)
        tmask = cap - 1
        recs = self.recs
        idx = 0
        n = self.nrecs
        while idx < n:
            base = idx << 2
            kind = _s32(recs[base]) & _KIND_MASK
            if kind != KIND_APP:
                hh = _hash_rec(
                    kind, _s32(recs[base + F_A]), _s32(recs[base + F_B]),
                )
                i = hh & tmask
                while table[i] != 0:
                    i = (i + 1) & tmask
                table[i] = (((hh >> 32) & _TABLE_TAG_MASK) << 32) | (idx + 1)
            idx += 1
        self.table = table
        self.tmask = tmask

    @dont_inline
    def _cons_general_wide(self, kind, a, b, info, binder=None):
        if self._other_limit != 0:
            self._promote_other_to_wide()
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
                if ((_s32(recs[base]) & _KIND_MASK) == kind
                        and _s32(recs[base + F_A]) == a
                        and _s32(recs[base + F_B]) == b):
                    return rec_handle(slot - 1)
            i = (i + 1) & tmask
        if binder is not None:
            info = self._info_index(binder)
        idx = self.nrecs
        if idx == self.cap:
            self._grow_records()
            recs = self.recs
        meta = self._meta_for(kind, a, b)
        sz = self._size_enc_for(kind, a, b)
        base = idx << 2
        recs[base] = _u32((meta << 3) | kind)
        recs[base + F_A] = _u32(a)
        recs[base + F_B] = _u32(b)
        recs[base + F_INFO] = _u32((sz << _SIZE_SHIFT) | (info & _INFO_MASK))
        self.nrecs = idx + 1
        nother = self.nother + 1
        self.nother = nother
        if nother * 2 > tmask + 1:
            self._rehash_wide()
        else:
            table[i] = (tag << 32) | (idx + 1)
        return rec_handle(idx)

    def _grow_records(self):
        n = self.nrecs
        cap = self.cap * 2
        self.recs = _grow_u32_uninit(self.recs, n << 2, cap << 2)
        if self.rec_node:
            if self._rec_node_dirty:
                self.rec_node = _grow_u32(self.rec_node, n, cap)
            else:
                _free_u32(self.rec_node)
                self.rec_node = lltype.nullptr(_U32_ARRAY)
        self.memos = _grow_u32(self.memos, n * MEMO_SLOTS, cap * MEMO_SLOTS)
        self.call_slot = _grow_words(self.call_slot, n, cap)
        self.cap = cap

    def _rehash_apps(self):
        _free_words(self.app_table)
        cap = (self.app_mask + 1) * 2
        app_table = _alloc_words(cap)
        amask = cap - 1
        recs = self.recs
        idx = 0
        n = self.nrecs
        while idx < n:
            base = idx << 2
            if (_s32(recs[base]) & _KIND_MASK) == KIND_APP:
                pair = (_s32(recs[base + F_A]) << 21) | _s32(recs[base + F_B])
                i = _spread(pair) & amask
                while app_table[i] != 0:
                    i = (i + 1) & amask
                app_table[i] = (pair << 21) | (idx + 1)
            idx += 1
        self.app_table = app_table
        self.app_mask = amask

    def _rehash(self):
        _free_words(self.table)
        cap = (self.tmask + 1) * 2
        table = _alloc_words(cap)
        tmask = cap - 1
        recs = self.recs
        idx = 0
        n = self.nrecs
        while idx < n:
            base = idx << 2
            kind = _s32(recs[base]) & _KIND_MASK
            if kind != KIND_APP:
                key = (
                    (kind << 40)
                    | (_s32(recs[base + F_A]) << 20)
                    | _s32(recs[base + F_B])
                )
                i = _spread(key) & tmask
                while table[i] != 0:
                    i = (i + 1) & tmask
                table[i] = (key << 20) | (idx + 1)
            idx += 1
        self.table = table
        self.tmask = tmask

    def app(self, fn, arg):
        return self.cons_app(fn, arg)

    def _cons_binder(self, kind, binder, a, b):
        if (a | b) >= self._other_limit:
            return self._cons_general_wide(kind, a, b, 0, binder)
        key = (kind << 40) | (a << 20) | b
        table = self.table
        tmask = self.tmask
        i = _spread(key) & tmask
        while True:
            entry = table[i]
            if (entry >> 20) == key:
                return (entry & _OTHER_SLOT_MASK) << 1
            if entry == 0:
                return self._cons_general_miss(kind, a, b, 0, key, i, binder)
            i = (i + 1) & tmask

    @dont_inline
    def _cons_let_wide(self, name, a, pair):
        return self._cons_general_wide(KIND_LET, a, pair, self._name_index(name))

    @dont_inline
    def _cons_let_miss(self, name, a, pair, key, i):
        return self._cons_general_miss(
            KIND_LET, a, pair, self._name_index(name), key, i,
        )

    @always_inline
    def lam(self, binder, type, body):
        return self._cons_binder(KIND_LAMBDA, binder, type, body)

    @always_inline
    def forall(self, binder, type, body):
        return self._cons_binder(KIND_FORALL, binder, type, body)

    def _proj_pack(self, name_id, field_index):
        if name_id < _PROJ_OVF_NAME and 0 <= field_index <= _PROJ_MASK:
            return (name_id << _PROJ_SHIFT) | field_index
        ov = self._proj_overflow
        ov_idx = -1
        for k in range(len(ov)):
            pair = ov[k]
            if pair[0] == name_id and pair[1] == field_index:
                ov_idx = k
                break
        if ov_idx < 0:
            ov_idx = len(ov)
            ov.append((name_id, field_index))
        return _PROJ_OVF_BASE + ov_idx

    def proj(self, struct_name, field_index, struct):
        name_id = self._name_index(struct_name)
        packed = self._proj_pack(name_id, field_index)
        return self.cons(KIND_PROJ, struct, packed, name_id)

    def let(self, name, type, value, body):
        pair = self.cons(KIND_PAIR, value, body)
        if (type | pair) >= self._other_limit:
            return self._cons_let_wide(name, type, pair)
        key = (KIND_LET << 40) | (type << 20) | pair
        table = self.table
        tmask = self.tmask
        i = _spread(key) & tmask
        while True:
            entry = table[i]
            if (entry >> 20) == key:
                return (entry & _OTHER_SLOT_MASK) << 1
            if entry == 0:
                return self._cons_let_miss(name, type, pair, key, i)
            i = (i + 1) & tmask

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

    def _new_leaf(self, e):
        j = self.nleaves
        if j == self.leaf_cap:
            cap = self.leaf_cap * 2
            self.leaf_meta = _grow_u32_uninit(self.leaf_meta, j, cap)
            self.leaf_whnf = _grow_u32(self.leaf_whnf, j, cap)
            self.leaf_infer = _grow_u32(self.leaf_infer, j, cap)
            self.leaf_checked = _grow_u32(self.leaf_checked, j, cap)
            self.leaf_delta = _grow_i32(self.leaf_delta, j, cap)
            self.leaf_delta_body = _grow_words(self.leaf_delta_body, j, cap)
            self.leaf_next = _grow_u32(self.leaf_next, j, cap)
            self.leaf_eqv = _grow_u32(self.leaf_eqv, j, cap)
            self.leaf_head_kind = _grow_u32(self.leaf_head_kind, j, cap)
            self.leaf_prop_mask = _grow_words(self.leaf_prop_mask, j, cap)
            self.leaf_cap = cap
        self.leaves.append(e)
        self.leaf_decl.append(None)
        self.leaf_meta[j] = _u32((e._packed >> 32) & 0x3FFFFFFF)
        self.leaf_head_kind[j] = _u32(
            0 if e.__class__ is W_Const else _LF_CLASSIFIED,
        )
        self.nleaves = j + 1
        return leaf_handle(j)

    def bvar(self, id):
        if 0 <= id < _BVAR_ARR_LEN:
            h = self._bvar_arr[id]
            if h != 0:
                return h
            h = self._new_leaf(W_BVar(id))
            self._bvar_arr[id] = h
            if id + 1 > self._bvar_max:
                self._bvar_max = id + 1
            return h
        h = self._bvar_leaves.get(id, 0)
        if h != 0:
            return h
        h = self._new_leaf(W_BVar(id))
        self._bvar_leaves[id] = h
        return h

    def has_fvar_leaf(self, fvar):
        """Whether the free variable ``fvar`` already has a leaf."""
        assert isinstance(fvar, W_FVar)
        gen = self._store_gen
        if (fvar._cache >> 32) == gen:
            return True
        return self._fvar_uid.get(fvar._uid, 0) != 0

    def _new_fvar_leaf(self, fvar):
        """Register a free variable known not to have a leaf in this store yet."""
        assert isinstance(fvar, W_FVar)
        h = self._new_leaf(fvar)
        self._fvar_uid.set(fvar._uid, h)
        gen = self._store_gen
        if gen > 0:
            fvar._cache = (gen << 32) | h
        return h

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
                h = self._new_leaf(e)
                self._bvar_arr[id] = h
                if id + 1 > self._bvar_max:
                    self._bvar_max = id + 1
                return h
            h = self._bvar_leaves.get(id, 0)
            if h != 0:
                return h
            h = self._new_leaf(e)
            self._bvar_leaves[id] = h
            return h
        gen = self._store_gen
        c = e._cache
        if (c >> 32) == gen:
            return c & _TABLE_SLOT_MASK
        if cls is W_FVar:
            assert isinstance(e, W_FVar)
            uid_key = e._uid
            h = self._fvar_uid.get(uid_key, 0)
            if h == 0:
                h = self._new_leaf(e)
                self._fvar_uid.set(uid_key, h)
            if gen > 0:
                e._cache = (gen << 32) | h
            return h
        orig = e
        if cls is W_Const:
            assert isinstance(e, W_Const)
            e = _canonical_const(e)
        elif cls is W_Sort:
            assert isinstance(e, W_Sort)
            e = _canonical_sort(e)
        if e is not orig:
            ec = e._cache
            if (ec >> 32) == gen:
                h = ec & _TABLE_SLOT_MASK
                if gen > 0:
                    orig._cache = ec
                return h
        h31 = e.hash() & 0x7FFFFFFF
        key = h31 if h31 != 0 else 1
        head = self._content_head.get(key, 0)
        cur = head
        while cur != 0:
            j = leaf_index(cur)
            if syntactic_eq(self.leaves[j], e):
                if gen > 0:
                    tagged = (gen << 32) | cur
                    orig._cache = tagged
                    if e is not orig:
                        e._cache = tagged
                return cur
            cur = _s32(self.leaf_next[j])
        h = self._new_leaf(e)
        self.leaf_next[leaf_index(h)] = _u32(head)
        self._content_head.set(key, h)
        if gen > 0:
            tagged = (gen << 32) | h
            orig._cache = tagged
            if e is not orig:
                e._cache = tagged
        return h

    def _const_leaf1(self, name, l0):
        """Canonical leaf handle for `W_Const(name, [l0])`, probing the store's
        `_content_head` directly to avoid `_CONST_CACHE` probes and `W_Const`
        allocations on hits."""
        nl0 = l0._normal
        if nl0 is None:
            nl0 = l0.normalize()
        h31 = (
            ((((name.hash() * 1000003) ^ nl0.hash()) * 1000003) ^ 0xC057)
            & 0x7FFFFFFF
        )
        key = h31 if h31 != 0 else 1
        cur = self._content_head.get(key, 0)
        while cur != 0:
            j = leaf_index(cur)
            le = self.leaves[j]
            if le.__class__ is W_Const:
                assert isinstance(le, W_Const)
                if le.name is name:
                    el = le.levels
                    if len(el) == 1 and el[0] is nl0:
                        return cur
            cur = _s32(self.leaf_next[j])
        return self._const_leaf1_miss(name, nl0)

    @dont_inline
    def _const_leaf1_miss(self, name, nl0):
        return self.leaf_for(_mk_w_const1(name, nl0))

    def _const_leaf2(self, name, l0, l1):
        """Canonical leaf handle for `W_Const(name, [l0, l1])` without
        allocating a `W_Const` or probing `_CONST_CACHE` on hits."""
        nl0 = l0._normal
        if nl0 is None:
            nl0 = l0.normalize()
        nl1 = l1._normal
        if nl1 is None:
            nl1 = l1.normalize()
        h31 = (
            ((((((name.hash() * 1000003) ^ nl0.hash()) * 1000003) ^ nl1.hash())
              * 1000003) ^ 0xC057)
            & 0x7FFFFFFF
        )
        key = h31 if h31 != 0 else 1
        cur = self._content_head.get(key, 0)
        while cur != 0:
            j = leaf_index(cur)
            le = self.leaves[j]
            if le.__class__ is W_Const:
                assert isinstance(le, W_Const)
                if le.name is name:
                    el = le.levels
                    if len(el) == 2 and el[0] is nl0 and el[1] is nl1:
                        return cur
            cur = _s32(self.leaf_next[j])
        return self._const_leaf2_miss(name, nl0, nl1)

    @dont_inline
    def _const_leaf2_miss(self, name, nl0, nl1):
        return self.leaf_for(_mk_w_const2(name, nl0, nl1))

    # ---- spines ----------------------------------------------------------

    def head(self, h):
        """The head of the application spine ``h``."""
        recs = self.recs
        while (h & 1) == 0:
            base = rec_index(h) << 2
            if (_s32(recs[base]) & _KIND_MASK) != KIND_APP:
                break
            h = _s32(recs[base + F_A])
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
            if (_s32(recs[base]) & _KIND_MASK) != KIND_APP:
                break
            args.append(_s32(recs[base + F_B]))
            h = _s32(recs[base + F_A])
        return h, args

    @dont_inline
    def _grow_spine(self, top):
        new_cap = self._spine_cap * 2
        buf = _grow_u32_uninit(self._spine_buf, top, new_cap)
        self._spine_buf = buf
        self._spine_cap = new_cap
        return buf

    @dont_inline
    def _unapp_push_grow(self, h, top):
        recs = self.recs
        buf = self._grow_spine(top)
        cap = self._spine_cap
        while (h & 1) == 0:
            base = rec_index(h) << 2
            if (_s32(recs[base]) & _KIND_MASK) != KIND_APP:
                break
            if top == cap:
                buf = self._grow_spine(top)
                cap = self._spine_cap
            buf[top] = recs[base + F_B]
            top += 1
            h = _s32(recs[base + F_A])
        self._spine_top = top
        return h

    def unapp_push(self, h):
        """Push the application spine of ``h`` onto `_spine_buf` outermost-first
        and return the head handle. Caller captures ``mark = store._spine_top``
        before calling, reads ``count = store._spine_top - mark``, and restores
        via ``unapp_pop(mark)``."""
        recs = self.recs
        top = self._spine_top
        buf = self._spine_buf
        cap = self._spine_cap
        while (h & 1) == 0:
            base = rec_index(h) << 2
            if (_s32(recs[base]) & _KIND_MASK) != KIND_APP:
                break
            if top == cap:
                return self._unapp_push_grow(h, top)
            buf[top] = recs[base + F_B]
            top += 1
            h = _s32(recs[base + F_A])
        self._spine_top = top
        return h

    @always_inline
    def unapp_pop(self, mark):
        self._spine_top = mark

    def ensure_spine_room(self, count):
        top = self._spine_top
        while top + count > self._spine_cap:
            self._grow_spine(top)

    @always_inline
    def spine_arg(self, idx):
        return _s32(self._spine_buf[idx])

    def spine_push(self, h):
        top = self._spine_top
        if top == self._spine_cap:
            buf = self._grow_spine(top)
        else:
            buf = self._spine_buf
        buf[top] = _u32(h)
        self._spine_top = top + 1

    def apply_buf_rev(self, fn, mark, hi):
        """``fn`` applied to `_spine_buf[mark + hi]`, …, `_spine_buf[mark]`."""
        buf = self._spine_buf
        i = hi
        while i >= 0:
            fn = self.cons_app(fn, _s32(buf[mark + i]))
            i -= 1
        return fn

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

    @always_inline
    def _next_call_epoch(self):
        gen = self._call_epoch + 1
        if gen >= (1 << 23):
            _zero_words(self.call_slot, self.cap)
            gen = 1
        self._call_epoch = gen
        return gen

    @always_inline
    def _buf_all_closed(self, buf, start, n):
        i = 0
        while i < n:
            if self.loose_bvar_range(_s32(buf[start + i])) != 0:
                return False
            i += 1
        return True

    @always_inline
    def _list_all_closed(self, substs, n):
        i = 0
        while i < n:
            if self.loose_bvar_range(substs[i]) != 0:
                return False
            i += 1
        return True

    def instantiate(self, h, sub, depth=0):
        """
        ``h`` with ``sub`` substituted for the bound variable ``depth``
        and every looser bound variable moved down by one (the binder
        that bound it is gone).
        """
        if self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = (_s32(self.leaf_meta[leaf_index(h)]) >> 1) - 1
            if id == depth:
                return sub if (depth == 0 or self.loose_bvar_range(sub) == 0) else self.shift(sub, depth, 0)
            return self.bvar(id - 1)
        key = _pack_key(h, sub, depth)
        if key != 0:
            r = self._inst_memo.get(key, 0)
        else:
            r = self._inst_memo.get_wide(h, sub, depth)
        if r != 0:
            return r
        gen = self._next_call_epoch()
        try:
            if depth == 0:
                r = self._inst_d0(h, sub, gen << 8, 0)
            else:
                r = self._inst_oneshot(
                    h, sub, depth, gen, self.loose_bvar_range(sub) == 0, 0,
                )
        finally:
            self._subst_top = 0
            if self._call_memo.size > 0:
                self._call_memo.clear()
        if key != 0:
            self._inst_memo.set(key, r)
        else:
            self._inst_memo.set_wide(h, sub, depth, r)
        return r

    def _inst_d0(self, h, sub, tag, rdepth):
        if is_leaf(h):
            m = _s32(self.leaf_meta[leaf_index(h)])
            if m <= 1:
                return h
            id = (m >> 1) - 1
            return sub if id == 0 else self.bvar(id - 1)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if hdr < 16:
            return h
        call_slot = self.call_slot
        entry = call_slot[ri]
        if (entry >> 32) == tag:
            return entry & _TABLE_SLOT_MASK
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                am = _s32(self.leaf_meta[leaf_index(a)])
                if am <= 1:
                    na = a
                else:
                    aid = (am >> 1) - 1
                    na = sub if aid == 0 else self.bvar(aid - 1)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if ahdr < 16:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_d0(a, sub, tag, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    while True:
                        if is_leaf(cur):
                            cm = _s32(self.leaf_meta[leaf_index(cur)])
                            if cm <= 1:
                                na = cur
                            else:
                                cid = (cm >> 1) - 1
                                na = sub if cid == 0 else self.bvar(cid - 1)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if chdr < 16:
                            na = cur
                            break
                        centry = call_slot[cri]
                        if (centry >> 32) == tag:
                            na = centry & _TABLE_SLOT_MASK
                            break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_d0(cur, sub, tag, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cri)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        nri = _s32(self._subst_stack[stop])
                        recs = self.recs
                        old_b = _s32(recs[(nri << 2) + F_B])
                        if is_leaf(old_b):
                            bm2 = _s32(self.leaf_meta[leaf_index(old_b)])
                            if bm2 <= 1:
                                nb2 = old_b
                            else:
                                bid2 = (bm2 >> 1) - 1
                                nb2 = sub if bid2 == 0 else self.bvar(bid2 - 1)
                        else:
                            bri2 = rec_index(old_b)
                            if _s32(recs[bri2 << 2]) < 16:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2]
                                if (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_d0(old_b, sub, tag, nr)
                        na = self.cons_app(na, nb2)
                        self.call_slot[nri] = (tag << 32) | na
                    self._subst_top = smark
            if is_leaf(b):
                bm = _s32(self.leaf_meta[leaf_index(b)])
                if bm <= 1:
                    nb = b
                else:
                    bid = (bm >> 1) - 1
                    nb = sub if bid == 0 else self.bvar(bid - 1)
            else:
                bri = rec_index(b)
                if _s32(self.recs[bri << 2]) < 16:
                    nb = b
                else:
                    bentry = self.call_slot[bri]
                    if (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_d0(b, sub, tag, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                am = _s32(self.leaf_meta[leaf_index(a)])
                if am <= 1:
                    na = a
                else:
                    aid = (am >> 1) - 1
                    na = sub if aid == 0 else self.bvar(aid - 1)
            else:
                ari = rec_index(a)
                if _s32(recs[ari << 2]) < 16:
                    na = a
                else:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_d0(a, sub, tag, nr)
            if self.loose_bvar_range(b) <= 1:
                nb = b
            else:
                nb = self._inst_oneshot(
                    b, sub, 1, tag >> 8, self.loose_bvar_range(sub) == 0, nr,
                )
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_d0(a, sub, tag, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_d0(a, sub, tag, nr)
            nv = self._inst_d0(value, sub, tag, nr)
            if self.loose_bvar_range(body) <= 1:
                nbody = body
            else:
                nbody = self._inst_oneshot(
                    body, sub, 1, tag >> 8, self.loose_bvar_range(sub) == 0, nr,
                )
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        self.call_slot[ri] = (tag << 32) | r
        return r

    def _inst_oneshot(self, h, sub, depth, gen, sub_closed, rdepth):
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            if id == depth:
                return sub if sub_closed else self.shift(sub, depth, 0)
            return self.bvar(id - 1)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        if depth < 256:
            tag = (gen << 8) | depth
            entry = self.call_slot[ri]
            if (entry >> 32) == tag:
                return entry & _TABLE_SLOT_MASK
            if (entry >> 40) == gen:
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        else:
            tag = 0
            if depth < (1 << 16):
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    if aid == depth:
                        na = sub if sub_closed else self.shift(sub, depth, 0)
                    else:
                        na = self.bvar(aid - 1)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = self.call_slot[ari] if tag != 0 else 0
                    if tag != 0 and (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_oneshot(a, sub, depth, gen, sub_closed, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    call_slot = self.call_slot
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                if cid == depth:
                                    na = sub if sub_closed else self.shift(sub, depth, 0)
                                else:
                                    na = self.bvar(cid - 1)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        if tag != 0:
                            centry = call_slot[cri]
                            if (centry >> 32) == tag:
                                na = centry & _TABLE_SLOT_MASK
                                break
                            if (centry >> 40) == gen:
                                cr = self._call_memo.get((cur << 16) | depth, 0)
                                if cr != 0:
                                    na = cr
                                    break
                        elif depth < (1 << 16):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_oneshot(cur, sub, depth, gen, sub_closed, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        nri = rec_index(node)
                        recs = self.recs
                        nbase = nri << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                if bid2 == depth:
                                    nb2 = sub if sub_closed else self.shift(sub, depth, 0)
                                else:
                                    nb2 = self.bvar(bid2 - 1)
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) >> 4) <= depth:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2] if tag != 0 else 0
                                if tag != 0 and (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_oneshot(old_b, sub, depth, gen, sub_closed, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        if tag != 0:
                            call_slot = self.call_slot
                            if (call_slot[nri] >> 40) != gen:
                                call_slot[nri] = (tag << 32) | na
                            else:
                                self._call_memo.set((node << 16) | depth, na)
                        elif depth < (1 << 16):
                            self._call_memo.set((node << 16) | depth, na)
                    self._subst_top = smark
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    if bid == depth:
                        nb = sub if sub_closed else self.shift(sub, depth, 0)
                    else:
                        nb = self.bvar(bid - 1)
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) >> 4) <= depth:
                    nb = b
                else:
                    bentry = self.call_slot[bri] if tag != 0 else 0
                    if tag != 0 and (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_oneshot(b, sub, depth, gen, sub_closed, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    if aid == depth:
                        na = sub if sub_closed else self.shift(sub, depth, 0)
                    else:
                        na = self.bvar(aid - 1)
            else:
                ari = rec_index(a)
                if (_s32(recs[ari << 2]) >> 4) <= depth:
                    na = a
                else:
                    aentry = self.call_slot[ari] if tag != 0 else 0
                    if tag != 0 and (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_oneshot(a, sub, depth, gen, sub_closed, nr)
            d1 = depth + 1
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= d1:
                    nb = b
                else:
                    bid = blo - 1
                    if bid == d1:
                        nb = sub if sub_closed else self.shift(sub, d1, 0)
                    else:
                        nb = self.bvar(bid - 1)
            else:
                nb = b if (_s32(self.recs[rec_index(b) << 2]) >> 4) <= d1 else self._inst_oneshot(b, sub, d1, gen, sub_closed, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_oneshot(a, sub, depth, gen, sub_closed, nr)
            r = h if na == a else self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_oneshot(a, sub, depth, gen, sub_closed, nr)
            nv = self._inst_oneshot(value, sub, depth, gen, sub_closed, nr)
            nbody = self._inst_oneshot(body, sub, depth + 1, gen, sub_closed, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        if tag != 0:
            call_slot = self.call_slot
            if (call_slot[ri] >> 40) != gen:
                call_slot[ri] = (tag << 32) | r
            else:
                self._call_memo.set((h << 16) | depth, r)
        elif depth < (1 << 16):
            self._call_memo.set((h << 16) | depth, r)
        return r

    def instantiate_multi(self, h, substs, depth=0):
        """
        ``h`` with ``substs[i]`` substituted for the bound variable
        ``depth + i`` for every ``i``, all at once, and every looser
        bound variable moved down by ``len(substs)``.
        """
        n = len(substs)
        if n == 1:
            return self.instantiate(h, substs[0], depth)
        if n == 0 or self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = (_s32(self.leaf_meta[leaf_index(h)]) >> 1) - 1
            rel = id - depth
            if rel < n:
                s = substs[rel]
                return s if (depth == 0 or self.loose_bvar_range(s) == 0) else self.shift(s, depth, 0)
            return self.bvar(id - n)
        gen = self._next_call_epoch()
        try:
            return self._inst_multi_oneshot(
                h, substs, n, depth, gen, self._list_all_closed(substs, n), 0,
            )
        finally:
            self._subst_top = 0
            if self._call_memo.size > 0:
                self._call_memo.clear()

    def _inst_multi_oneshot(self, h, substs, n, depth, gen, all_closed, rdepth):
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            rel = id - depth
            if rel < n:
                s = substs[rel]
                return s if (all_closed or depth == 0) else self.shift(s, depth, 0)
            return self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        if depth < 256:
            tag = (gen << 8) | depth
            entry = self.call_slot[ri]
            if (entry >> 32) == tag:
                return entry & _TABLE_SLOT_MASK
            if (entry >> 40) == gen:
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        else:
            tag = 0
            if depth < (1 << 16):
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    if arel < n:
                        asub = substs[arel]
                        na = asub if (all_closed or depth == 0) else self.shift(asub, depth, 0)
                    else:
                        na = self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    if tag != 0 and (self.call_slot[ari] >> 32) == tag:
                        na = self.call_slot[ari] & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_oneshot(a, substs, n, depth, gen, all_closed, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    call_slot = self.call_slot
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                crel = cid - depth
                                if crel < n:
                                    csub = substs[crel]
                                    na = csub if (all_closed or depth == 0) else self.shift(csub, depth, 0)
                                else:
                                    na = self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        if tag != 0:
                            centry = call_slot[cri]
                            if (centry >> 32) == tag:
                                na = centry & _TABLE_SLOT_MASK
                                break
                            if (centry >> 40) == gen:
                                cr = self._call_memo.get((cur << 16) | depth, 0)
                                if cr != 0:
                                    na = cr
                                    break
                        elif depth < (1 << 16):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_oneshot(cur, substs, n, depth, gen, all_closed, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    self._subst_top = stop
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        self._subst_top = stop
                        nri = rec_index(node)
                        recs = self.recs
                        nbase = nri << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                brel2 = bid2 - depth
                                if brel2 < n:
                                    bsub2 = substs[brel2]
                                    nb2 = bsub2 if (all_closed or depth == 0) else self.shift(bsub2, depth, 0)
                                else:
                                    nb2 = self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) >> 4) <= depth:
                                nb2 = old_b
                            elif tag != 0 and (self.call_slot[bri2] >> 32) == tag:
                                nb2 = self.call_slot[bri2] & _TABLE_SLOT_MASK
                            else:
                                nb2 = self._inst_multi_oneshot(old_b, substs, n, depth, gen, all_closed, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        if tag != 0:
                            call_slot = self.call_slot
                            if (call_slot[nri] >> 40) != gen:
                                call_slot[nri] = (tag << 32) | na
                            else:
                                self._call_memo.set((node << 16) | depth, na)
                        elif depth < (1 << 16):
                            self._call_memo.set((node << 16) | depth, na)
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - depth
                    if brel < n:
                        bsub = substs[brel]
                        nb = bsub if (all_closed or depth == 0) else self.shift(bsub, depth, 0)
                    else:
                        nb = self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) >> 4) <= depth:
                    nb = b
                elif tag != 0 and (self.call_slot[bri] >> 32) == tag:
                    nb = self.call_slot[bri] & _TABLE_SLOT_MASK
                else:
                    nb = self._inst_multi_oneshot(b, substs, n, depth, gen, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if self.loose_bvar_range(a) <= depth else self._inst_multi_oneshot(a, substs, n, depth, gen, all_closed, nr)
            nb = b if self.loose_bvar_range(b) <= depth + 1 else self._inst_multi_oneshot(b, substs, n, depth + 1, gen, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_oneshot(a, substs, n, depth, gen, all_closed, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_oneshot(a, substs, n, depth, gen, all_closed, nr)
            nv = self._inst_multi_oneshot(value, substs, n, depth, gen, all_closed, nr)
            nbody = self._inst_multi_oneshot(body, substs, n, depth + 1, gen, all_closed, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        if tag != 0:
            call_slot = self.call_slot
            if (call_slot[ri] >> 40) != gen:
                call_slot[ri] = (tag << 32) | r
            else:
                self._call_memo.set((h << 16) | depth, r)
        elif depth < (1 << 16):
            self._call_memo.set((h << 16) | depth, r)
        return r

    @dont_inline
    def inst_eq_buf(self, pat, start, n, target):
        """Return True only when ``instantiate_multi_buf(pat, start, n, 0)``
        would produce the exact handle ``target``, without allocating records
        or probing consing tables. Bounded by a step budget so heavily shared
        DAGs fall back cleanly to memoized instantiation."""
        return self._inst_eq_d0(pat, self._spine_buf, start, n, target, 512) >= 0

    @dont_inline
    def ast_inst_eq_buf(self, pat, params, clevels, start, n, target):
        """Return True only when instantiating raw AST ``pat`` with universe
        levels ``params -> clevels`` and ``_spine_buf[start:start+n]`` produces
        a term structurally equal to handle ``target`` (modulo binder names/info),
        without importing ``pat`` or allocating any `TermStore` records."""
        return self._ast_inst_eq(
            pat, params, clevels, self._spine_buf, start, n, target, 0, 512,
        ) >= 0

    def _ast_inst_eq(self, pat, params, clevels, buf, start, n, target, depth, budget):
        if not pat.has_level_param() and pat.loose_bvar_range() <= depth:
            c = pat._cache
            if (c >> 32) == self._store_gen:
                return budget if (c & _TABLE_SLOT_MASK) == target else -1
        cls = pat.__class__
        if cls is W_BVar:
            assert isinstance(pat, W_BVar)
            bid = pat.id
            if bid < depth:
                if (is_leaf(target)
                        and _s32(self.leaf_meta[leaf_index(target)]) == ((bid + 1) << 1)):
                    return budget
                return -1
            rel = bid - depth
            if rel < n:
                sub = _s32(buf[start + rel])
                if sub == target and (depth == 0 or self.loose_bvar_range(sub) == 0):
                    return budget
                return -1
            if (is_leaf(target)
                    and _s32(self.leaf_meta[leaf_index(target)]) == ((bid - n + 1) << 1)):
                return budget
            return -1
        recs = self.recs
        leaf_meta = self.leaf_meta
        if cls is W_App:
            if is_leaf(target):
                return -1
            tbase = rec_index(target) << 2
            if (_s32(recs[tbase]) & _KIND_MASK) != KIND_APP:
                return -1
            cur = pat
            while True:
                if budget <= 0:
                    return -1
                budget -= 1
                assert isinstance(cur, W_App)
                pa = cur.arg
                tb = _s32(recs[tbase + F_B])
                if pa.__class__ is W_BVar:
                    assert isinstance(pa, W_BVar)
                    bid = pa.id
                    if bid < depth:
                        if not (is_leaf(tb)
                                and _s32(leaf_meta[leaf_index(tb)]) == ((bid + 1) << 1)):
                            return -1
                    else:
                        rel = bid - depth
                        if rel < n:
                            sub = _s32(buf[start + rel])
                            if sub != tb or (depth > 0 and self.loose_bvar_range(sub) != 0):
                                return -1
                        elif not (is_leaf(tb)
                                  and _s32(leaf_meta[leaf_index(tb)]) == ((bid - n + 1) << 1)):
                            return -1
                else:
                    budget = self._ast_inst_eq(
                        pa, params, clevels, buf, start, n, tb, depth, budget,
                    )
                    if budget < 0:
                        return -1
                pf = cur.fn
                ta = _s32(recs[tbase + F_A])
                if pf.__class__ is W_App:
                    if is_leaf(ta):
                        return -1
                    tbase = rec_index(ta) << 2
                    if (_s32(recs[tbase]) & _KIND_MASK) != KIND_APP:
                        return -1
                    cur = pf
                    continue
                return self._ast_inst_eq(
                    pf, params, clevels, buf, start, n, ta, depth, budget,
                )
        if cls is W_Const:
            if not is_leaf(target):
                return -1
            te = self.leaves[leaf_index(target)]
            if te.__class__ is not W_Const:
                return -1
            assert isinstance(pat, W_Const)
            assert isinstance(te, W_Const)
            if not pat.name.syntactic_eq(te.name):
                return -1
            plvls = pat.levels
            tlvls = te.levels
            nl = len(plvls)
            if nl != len(tlvls):
                return -1
            if nl == 0:
                return budget
            if not pat.has_level_param():
                k = 0
                while k < nl:
                    if plvls[k] is not tlvls[k] and not plvls[k].eq(tlvls[k]):
                        return -1
                    k += 1
                return budget
            k = 0
            while k < nl:
                if not _level_subst_eq(plvls[k], params, clevels, tlvls[k]):
                    return -1
                k += 1
            return budget
        if cls is W_Sort:
            if not is_leaf(target):
                return -1
            te = self.leaves[leaf_index(target)]
            if te.__class__ is not W_Sort:
                return -1
            assert isinstance(pat, W_Sort)
            assert isinstance(te, W_Sort)
            if _level_subst_eq(pat.level, params, clevels, te.level):
                return budget
            return -1
        if cls is W_ForAll or cls is W_Lambda:
            if is_leaf(target) or budget <= 0:
                return -1
            budget -= 1
            tbase = rec_index(target) << 2
            want = KIND_FORALL if cls is W_ForAll else KIND_LAMBDA
            if (_s32(recs[tbase]) & _KIND_MASK) != want:
                return -1
            assert isinstance(pat, W_ForAll) or isinstance(pat, W_Lambda)
            budget = self._ast_inst_eq(
                pat.binder.type, params, clevels, buf, start, n,
                _s32(recs[tbase + F_A]), depth, budget,
            )
            if budget < 0:
                return -1
            return self._ast_inst_eq(
                pat.body, params, clevels, buf, start, n,
                _s32(recs[tbase + F_B]), depth + 1, budget,
            )
        if cls is W_Proj:
            if is_leaf(target) or budget <= 0:
                return -1
            budget -= 1
            tbase = rec_index(target) << 2
            if (_s32(recs[tbase]) & _KIND_MASK) != KIND_PROJ:
                return -1
            assert isinstance(pat, W_Proj)
            if self.proj_index(target) != pat.field_index:
                return -1
            if not self.name_of(target).syntactic_eq(pat.struct_name):
                return -1
            return self._ast_inst_eq(
                pat.struct_expr, params, clevels, buf, start, n,
                _s32(recs[tbase + F_A]), depth, budget,
            )
        if cls is W_Let:
            if is_leaf(target) or budget <= 0:
                return -1
            budget -= 1
            tbase = rec_index(target) << 2
            if (_s32(recs[tbase]) & _KIND_MASK) != KIND_LET:
                return -1
            assert isinstance(pat, W_Let)
            budget = self._ast_inst_eq(
                pat.type, params, clevels, buf, start, n,
                _s32(recs[tbase + F_A]), depth, budget,
            )
            if budget < 0:
                return -1
            tpair = _s32(recs[tbase + F_B])
            budget = self._ast_inst_eq(
                pat.value, params, clevels, buf, start, n,
                self.field_a(tpair), depth, budget,
            )
            if budget < 0:
                return -1
            return self._ast_inst_eq(
                pat.body, params, clevels, buf, start, n,
                self.field_b(tpair), depth + 1, budget,
            )
        if cls is W_LitNat or cls is W_LitStr:
            if not is_leaf(target):
                return -1
            if pat.syntactic_eq(self.leaves[leaf_index(target)]):
                return budget
            return -1
        return -1

    def _inst_eq_d0(self, pat, buf, start, n, target, budget):
        recs = self.recs
        leaf_meta = self.leaf_meta
        if is_leaf(pat):
            pm = _s32(leaf_meta[leaf_index(pat)])
            if pm <= 1:
                return budget if pat == target else -1
            bid = (pm >> 1) - 1
            if bid < n:
                return budget if _s32(buf[start + bid]) == target else -1
            if (is_leaf(target)
                    and _s32(leaf_meta[leaf_index(target)]) == ((bid - n + 1) << 1)):
                return budget
            return -1
        pbase = rec_index(pat) << 2
        phdr = _s32(recs[pbase])
        if phdr < 16:
            return budget if pat == target else -1
        if is_leaf(target):
            return -1
        tbase = rec_index(target) << 2
        thdr = _s32(recs[tbase])
        pkind = phdr & _KIND_MASK
        if pkind != (thdr & _KIND_MASK):
            return -1
        if pkind == KIND_APP:
            while True:
                if budget <= 0:
                    return -1
                budget -= 1
                pb = _s32(recs[pbase + F_B])
                tb = _s32(recs[tbase + F_B])
                if is_leaf(pb):
                    pm = _s32(leaf_meta[leaf_index(pb)])
                    if pm <= 1:
                        if pb != tb:
                            return -1
                    else:
                        bid = (pm >> 1) - 1
                        if bid < n:
                            if _s32(buf[start + bid]) != tb:
                                return -1
                        else:
                            if (not is_leaf(tb)
                                    or _s32(leaf_meta[leaf_index(tb)]) != ((bid - n + 1) << 1)):
                                return -1
                else:
                    if _s32(recs[rec_index(pb) << 2]) < 16:
                        if pb != tb:
                            return -1
                    else:
                        budget = self._inst_eq_d0(pb, buf, start, n, tb, budget)
                        if budget < 0:
                            return -1
                pa = _s32(recs[pbase + F_A])
                ta = _s32(recs[tbase + F_A])
                if is_leaf(pa):
                    pm = _s32(leaf_meta[leaf_index(pa)])
                    if pm <= 1:
                        return budget if pa == ta else -1
                    bid = (pm >> 1) - 1
                    if bid < n:
                        return budget if _s32(buf[start + bid]) == ta else -1
                    if (is_leaf(ta)
                            and _s32(leaf_meta[leaf_index(ta)]) == ((bid - n + 1) << 1)):
                        return budget
                    return -1
                pbase = rec_index(pa) << 2
                pahdr = _s32(recs[pbase])
                if pahdr < 16:
                    return budget if pa == ta else -1
                if is_leaf(ta):
                    return -1
                tbase = rec_index(ta) << 2
                tahdr = _s32(recs[tbase])
                pk = pahdr & _KIND_MASK
                if pk != (tahdr & _KIND_MASK):
                    return -1
                if pk == KIND_APP:
                    continue
                return self._inst_eq_d0(pa, buf, start, n, ta, budget)
        if budget <= 0:
            return -1
        budget -= 1
        if pkind == KIND_LAMBDA or pkind == KIND_FORALL:
            budget = self._inst_eq_d0(
                _s32(recs[pbase + F_A]), buf, start, n,
                _s32(recs[tbase + F_A]), budget,
            )
            if budget < 0:
                return -1
            pb = _s32(recs[pbase + F_B])
            tb = _s32(recs[tbase + F_B])
            if self.loose_bvar_range(pb) <= 1:
                return budget if pb == tb else -1
            return self._inst_eq_depth(pb, buf, start, n, tb, 1, budget)
        if pkind == KIND_PROJ:
            if _s32(recs[pbase + F_B]) != _s32(recs[tbase + F_B]):
                return -1
            return self._inst_eq_d0(
                _s32(recs[pbase + F_A]), buf, start, n,
                _s32(recs[tbase + F_A]), budget,
            )
        assert pkind == KIND_LET
        budget = self._inst_eq_d0(
            _s32(recs[pbase + F_A]), buf, start, n,
            _s32(recs[tbase + F_A]), budget,
        )
        if budget < 0:
            return -1
        ppair = _s32(recs[pbase + F_B])
        tpair = _s32(recs[tbase + F_B])
        budget = self._inst_eq_d0(
            self.field_a(ppair), buf, start, n,
            self.field_a(tpair), budget,
        )
        if budget < 0:
            return -1
        pbody = self.field_b(ppair)
        tbody = self.field_b(tpair)
        if self.loose_bvar_range(pbody) <= 1:
            return budget if pbody == tbody else -1
        return self._inst_eq_depth(pbody, buf, start, n, tbody, 1, budget)

    def _inst_eq_depth(self, pat, buf, start, n, target, depth, budget):
        recs = self.recs
        leaf_meta = self.leaf_meta
        if is_leaf(pat):
            lo = _s32(leaf_meta[leaf_index(pat)]) >> 1
            if lo <= depth:
                return budget if pat == target else -1
            id = lo - 1
            rel = id - depth
            if rel < n:
                sub = _s32(buf[start + rel])
                if sub == target and self.loose_bvar_range(sub) == 0:
                    return budget
                return -1
            if (is_leaf(target)
                    and _s32(leaf_meta[leaf_index(target)]) == ((id - n + 1) << 1)):
                return budget
            return -1
        pbase = rec_index(pat) << 2
        phdr = _s32(recs[pbase])
        if (phdr >> 4) <= depth:
            return budget if pat == target else -1
        if is_leaf(target):
            return -1
        tbase = rec_index(target) << 2
        thdr = _s32(recs[tbase])
        pkind = phdr & _KIND_MASK
        if pkind != (thdr & _KIND_MASK):
            return -1
        if pkind == KIND_APP:
            while True:
                if budget <= 0:
                    return -1
                budget -= 1
                pb = _s32(recs[pbase + F_B])
                tb = _s32(recs[tbase + F_B])
                if is_leaf(pb):
                    lo = _s32(leaf_meta[leaf_index(pb)]) >> 1
                    if lo <= depth:
                        if pb != tb:
                            return -1
                    else:
                        id = lo - 1
                        rel = id - depth
                        if rel < n:
                            sub = _s32(buf[start + rel])
                            if sub != tb or self.loose_bvar_range(sub) != 0:
                                return -1
                        else:
                            if (not is_leaf(tb)
                                    or _s32(leaf_meta[leaf_index(tb)]) != ((id - n + 1) << 1)):
                                return -1
                else:
                    if (_s32(recs[rec_index(pb) << 2]) >> 4) <= depth:
                        if pb != tb:
                            return -1
                    else:
                        budget = self._inst_eq_depth(pb, buf, start, n, tb, depth, budget)
                        if budget < 0:
                            return -1
                pa = _s32(recs[pbase + F_A])
                ta = _s32(recs[tbase + F_A])
                if is_leaf(pa):
                    lo = _s32(leaf_meta[leaf_index(pa)]) >> 1
                    if lo <= depth:
                        return budget if pa == ta else -1
                    id = lo - 1
                    rel = id - depth
                    if rel < n:
                        sub = _s32(buf[start + rel])
                        if sub == ta and self.loose_bvar_range(sub) == 0:
                            return budget
                        return -1
                    if (is_leaf(ta)
                            and _s32(leaf_meta[leaf_index(ta)]) == ((id - n + 1) << 1)):
                        return budget
                    return -1
                pbase = rec_index(pa) << 2
                pahdr = _s32(recs[pbase])
                if (pahdr >> 4) <= depth:
                    return budget if pa == ta else -1
                if is_leaf(ta):
                    return -1
                tbase = rec_index(ta) << 2
                tahdr = _s32(recs[tbase])
                pk = pahdr & _KIND_MASK
                if pk != (tahdr & _KIND_MASK):
                    return -1
                if pk == KIND_APP:
                    continue
                return self._inst_eq_depth(pa, buf, start, n, ta, depth, budget)
        if budget <= 0:
            return -1
        budget -= 1
        if pkind == KIND_LAMBDA or pkind == KIND_FORALL:
            budget = self._inst_eq_depth(
                _s32(recs[pbase + F_A]), buf, start, n,
                _s32(recs[tbase + F_A]), depth, budget,
            )
            if budget < 0:
                return -1
            pb = _s32(recs[pbase + F_B])
            tb = _s32(recs[tbase + F_B])
            if self.loose_bvar_range(pb) <= depth + 1:
                return budget if pb == tb else -1
            return self._inst_eq_depth(pb, buf, start, n, tb, depth + 1, budget)
        if pkind == KIND_PROJ:
            if _s32(recs[pbase + F_B]) != _s32(recs[tbase + F_B]):
                return -1
            return self._inst_eq_depth(
                _s32(recs[pbase + F_A]), buf, start, n,
                _s32(recs[tbase + F_A]), depth, budget,
            )
        assert pkind == KIND_LET
        budget = self._inst_eq_depth(
            _s32(recs[pbase + F_A]), buf, start, n,
            _s32(recs[tbase + F_A]), depth, budget,
        )
        if budget < 0:
            return -1
        ppair = _s32(recs[pbase + F_B])
        tpair = _s32(recs[tbase + F_B])
        budget = self._inst_eq_depth(
            self.field_a(ppair), buf, start, n,
            self.field_a(tpair), depth, budget,
        )
        if budget < 0:
            return -1
        pbody = self.field_b(ppair)
        tbody = self.field_b(tpair)
        if self.loose_bvar_range(pbody) <= depth + 1:
            return budget if pbody == tbody else -1
        return self._inst_eq_depth(pbody, buf, start, n, tbody, depth + 1, budget)

    def inst_eq_inst_buf(self, p1, s1, n1, p2, s2, n2):
        """Return True only when ``instantiate_multi_buf(p1, s1, n1, 0)`` and
        ``instantiate_multi_buf(p2, s2, n2, 0)`` would produce the exact same
        handle, without allocating records or probing consing tables. Bounded
        by a step budget so heavily shared DAGs fall back cleanly."""
        return self._inst_eq_inst_d0(
            p1, self._spine_buf, s1, n1, p2, s2, n2, 512,
        ) >= 0

    def _inst_eq_inst_d0(self, p1, buf, s1, n1, p2, s2, n2, budget):
        recs = self.recs
        leaf_meta = self.leaf_meta
        v1 = 0
        b1 = 0
        h1 = 0
        if is_leaf(p1):
            pm1 = _s32(leaf_meta[leaf_index(p1)])
            if pm1 <= 1:
                v1 = p1
            else:
                bid1 = (pm1 >> 1) - 1
                if bid1 < n1:
                    v1 = _s32(buf[s1 + bid1])
                else:
                    if not is_leaf(p2):
                        return -1
                    pm2 = _s32(leaf_meta[leaf_index(p2)])
                    if pm2 <= 1:
                        return -1
                    bid2 = (pm2 >> 1) - 1
                    tmeta = (bid1 - n1 + 1) << 1
                    if bid2 < n2:
                        v2 = _s32(buf[s2 + bid2])
                        if is_leaf(v2) and _s32(leaf_meta[leaf_index(v2)]) == tmeta:
                            return budget
                        return -1
                    return budget if (bid1 - n1) == (bid2 - n2) else -1
        else:
            b1 = rec_index(p1) << 2
            h1 = _s32(recs[b1])
            if h1 < 16:
                v1 = p1
        if v1 != 0:
            if is_leaf(p2):
                pm2 = _s32(leaf_meta[leaf_index(p2)])
                if pm2 <= 1:
                    return budget if v1 == p2 else -1
                bid2 = (pm2 >> 1) - 1
                if bid2 < n2:
                    return budget if v1 == _s32(buf[s2 + bid2]) else -1
                if (is_leaf(v1)
                        and _s32(leaf_meta[leaf_index(v1)]) == ((bid2 - n2 + 1) << 1)):
                    return budget
                return -1
            if _s32(recs[rec_index(p2) << 2]) < 16:
                return budget if v1 == p2 else -1
            return self._inst_eq_d0(p2, buf, s2, n2, v1, budget)
        # p1 is an open record (`b1`, `h1` already loaded).
        if is_leaf(p2):
            pm2 = _s32(leaf_meta[leaf_index(p2)])
            if pm2 <= 1:
                return -1
            bid2 = (pm2 >> 1) - 1
            if bid2 < n2:
                return self._inst_eq_d0(p1, buf, s1, n1, _s32(buf[s2 + bid2]), budget)
            return -1
        b2 = rec_index(p2) << 2
        h2 = _s32(recs[b2])
        if h2 < 16:
            return self._inst_eq_d0(p1, buf, s1, n1, p2, budget)
        k1 = h1 & _KIND_MASK
        if k1 != (h2 & _KIND_MASK):
            return -1
        if k1 == KIND_APP:
            while True:
                if budget <= 0:
                    return -1
                budget -= 1
                pb1 = _s32(recs[b1 + F_B])
                pb2 = _s32(recs[b2 + F_B])
                if is_leaf(pb1) and is_leaf(pb2):
                    pm1 = _s32(leaf_meta[leaf_index(pb1)])
                    pm2 = _s32(leaf_meta[leaf_index(pb2)])
                    if pm1 > 1 and pm2 > 1:
                        bid1 = (pm1 >> 1) - 1
                        bid2 = (pm2 >> 1) - 1
                        if bid1 < n1 and bid2 < n2:
                            if _s32(buf[s1 + bid1]) != _s32(buf[s2 + bid2]):
                                return -1
                        else:
                            budget = self._inst_eq_inst_d0(
                                pb1, buf, s1, n1, pb2, s2, n2, budget,
                            )
                            if budget < 0:
                                return -1
                    elif pm1 <= 1 and pm2 <= 1:
                        if pb1 != pb2:
                            return -1
                    else:
                        budget = self._inst_eq_inst_d0(
                            pb1, buf, s1, n1, pb2, s2, n2, budget,
                        )
                        if budget < 0:
                            return -1
                else:
                    budget = self._inst_eq_inst_d0(
                        pb1, buf, s1, n1, pb2, s2, n2, budget,
                    )
                    if budget < 0:
                        return -1
                pa1 = _s32(recs[b1 + F_A])
                pa2 = _s32(recs[b2 + F_A])
                if not is_leaf(pa1) and not is_leaf(pa2):
                    nb1 = rec_index(pa1) << 2
                    nb2 = rec_index(pa2) << 2
                    nh1 = _s32(recs[nb1])
                    nh2 = _s32(recs[nb2])
                    if nh1 >= 16 and nh2 >= 16:
                        nk1 = nh1 & _KIND_MASK
                        if nk1 != (nh2 & _KIND_MASK):
                            return -1
                        if nk1 == KIND_APP:
                            b1 = nb1
                            b2 = nb2
                            continue
                elif pa1 == pa2 and is_leaf(pa1):
                    if _s32(leaf_meta[leaf_index(pa1)]) <= 1:
                        return budget
                return self._inst_eq_inst_d0(
                    pa1, buf, s1, n1, pa2, s2, n2, budget,
                )
        if budget <= 0:
            return -1
        budget -= 1
        if k1 == KIND_LAMBDA or k1 == KIND_FORALL:
            budget = self._inst_eq_inst_d0(
                _s32(recs[b1 + F_A]), buf, s1, n1,
                _s32(recs[b2 + F_A]), s2, n2, budget,
            )
            if budget < 0:
                return -1
            pb1 = _s32(recs[b1 + F_B])
            pb2 = _s32(recs[b2 + F_B])
            if self.loose_bvar_range(pb1) <= 1 and self.loose_bvar_range(pb2) <= 1:
                return budget if pb1 == pb2 else -1
            return self._inst_eq_inst_depth(
                pb1, buf, s1, n1, pb2, s2, n2, 1, budget,
            )
        if k1 == KIND_PROJ:
            if _s32(recs[b1 + F_B]) != _s32(recs[b2 + F_B]):
                return -1
            return self._inst_eq_inst_d0(
                _s32(recs[b1 + F_A]), buf, s1, n1,
                _s32(recs[b2 + F_A]), s2, n2, budget,
            )
        assert k1 == KIND_LET
        budget = self._inst_eq_inst_d0(
            _s32(recs[b1 + F_A]), buf, s1, n1,
            _s32(recs[b2 + F_A]), s2, n2, budget,
        )
        if budget < 0:
            return -1
        pp1 = _s32(recs[b1 + F_B])
        pp2 = _s32(recs[b2 + F_B])
        budget = self._inst_eq_inst_d0(
            self.field_a(pp1), buf, s1, n1,
            self.field_a(pp2), s2, n2, budget,
        )
        if budget < 0:
            return -1
        pbody1 = self.field_b(pp1)
        pbody2 = self.field_b(pp2)
        if self.loose_bvar_range(pbody1) <= 1 and self.loose_bvar_range(pbody2) <= 1:
            return budget if pbody1 == pbody2 else -1
        return self._inst_eq_inst_depth(
            pbody1, buf, s1, n1, pbody2, s2, n2, 1, budget,
        )

    def _inst_eq_inst_depth(self, p1, buf, s1, n1, p2, s2, n2, depth, budget):
        recs = self.recs
        leaf_meta = self.leaf_meta
        v1 = 0
        b1 = 0
        h1 = 0
        if is_leaf(p1):
            lo1 = _s32(leaf_meta[leaf_index(p1)]) >> 1
            if lo1 <= depth:
                v1 = p1
            else:
                id1 = lo1 - 1
                rel1 = id1 - depth
                if rel1 < n1:
                    sub1 = _s32(buf[s1 + rel1])
                    if self.loose_bvar_range(sub1) != 0:
                        return -1
                    v1 = sub1
                else:
                    if not is_leaf(p2):
                        return -1
                    lo2 = _s32(leaf_meta[leaf_index(p2)]) >> 1
                    if lo2 <= depth:
                        return -1
                    id2 = lo2 - 1
                    rel2 = id2 - depth
                    if rel2 < n2:
                        return -1
                    return budget if (id1 - n1) == (id2 - n2) else -1
        else:
            b1 = rec_index(p1) << 2
            h1 = _s32(recs[b1])
            if (h1 >> 4) <= depth:
                v1 = p1
        if v1 != 0:
            return self._inst_eq_depth(p2, buf, s2, n2, v1, depth, budget)
        if is_leaf(p2):
            lo2 = _s32(leaf_meta[leaf_index(p2)]) >> 1
            if lo2 <= depth:
                return -1
            id2 = lo2 - 1
            rel2 = id2 - depth
            if rel2 < n2:
                sub2 = _s32(buf[s2 + rel2])
                if self.loose_bvar_range(sub2) != 0:
                    return -1
                return self._inst_eq_depth(p1, buf, s1, n1, sub2, depth, budget)
            return -1
        b2 = rec_index(p2) << 2
        h2 = _s32(recs[b2])
        if (h2 >> 4) <= depth:
            return self._inst_eq_depth(p1, buf, s1, n1, p2, depth, budget)
        k1 = h1 & _KIND_MASK
        if k1 != (h2 & _KIND_MASK):
            return -1
        if k1 == KIND_APP:
            while True:
                if budget <= 0:
                    return -1
                budget -= 1
                budget = self._inst_eq_inst_depth(
                    _s32(recs[b1 + F_B]), buf, s1, n1,
                    _s32(recs[b2 + F_B]), s2, n2, depth, budget,
                )
                if budget < 0:
                    return -1
                pa1 = _s32(recs[b1 + F_A])
                pa2 = _s32(recs[b2 + F_A])
                if not is_leaf(pa1) and not is_leaf(pa2):
                    nb1 = rec_index(pa1) << 2
                    nb2 = rec_index(pa2) << 2
                    nh1 = _s32(recs[nb1])
                    nh2 = _s32(recs[nb2])
                    if (nh1 >> 4) > depth and (nh2 >> 4) > depth:
                        nk1 = nh1 & _KIND_MASK
                        if nk1 != (nh2 & _KIND_MASK):
                            return -1
                        if nk1 == KIND_APP:
                            b1 = nb1
                            b2 = nb2
                            continue
                return self._inst_eq_inst_depth(
                    pa1, buf, s1, n1, pa2, s2, n2, depth, budget,
                )
        if budget <= 0:
            return -1
        budget -= 1
        if k1 == KIND_LAMBDA or k1 == KIND_FORALL:
            budget = self._inst_eq_inst_depth(
                _s32(recs[b1 + F_A]), buf, s1, n1,
                _s32(recs[b2 + F_A]), s2, n2, depth, budget,
            )
            if budget < 0:
                return -1
            pb1 = _s32(recs[b1 + F_B])
            pb2 = _s32(recs[b2 + F_B])
            if (self.loose_bvar_range(pb1) <= depth + 1
                    and self.loose_bvar_range(pb2) <= depth + 1):
                return budget if pb1 == pb2 else -1
            return self._inst_eq_inst_depth(
                pb1, buf, s1, n1, pb2, s2, n2, depth + 1, budget,
            )
        if k1 == KIND_PROJ:
            if _s32(recs[b1 + F_B]) != _s32(recs[b2 + F_B]):
                return -1
            return self._inst_eq_inst_depth(
                _s32(recs[b1 + F_A]), buf, s1, n1,
                _s32(recs[b2 + F_A]), s2, n2, depth, budget,
            )
        assert k1 == KIND_LET
        budget = self._inst_eq_inst_depth(
            _s32(recs[b1 + F_A]), buf, s1, n1,
            _s32(recs[b2 + F_A]), s2, n2, depth, budget,
        )
        if budget < 0:
            return -1
        pp1 = _s32(recs[b1 + F_B])
        pp2 = _s32(recs[b2 + F_B])
        budget = self._inst_eq_inst_depth(
            self.field_a(pp1), buf, s1, n1,
            self.field_a(pp2), s2, n2, depth, budget,
        )
        if budget < 0:
            return -1
        pbody1 = self.field_b(pp1)
        pbody2 = self.field_b(pp2)
        if (self.loose_bvar_range(pbody1) <= depth + 1
                and self.loose_bvar_range(pbody2) <= depth + 1):
            return budget if pbody1 == pbody2 else -1
        return self._inst_eq_inst_depth(
            pbody1, buf, s1, n1, pbody2, s2, n2, depth + 1, budget,
        )

    def instantiate_multi_buf(self, h, start, count, depth=0):
        """
        Like `instantiate_multi`, reading ``count`` substitutes directly from
        ``self._spine_buf[start + rel]`` (zero list allocation or slice copy).
        """
        buf = self._spine_buf
        if count == 1:
            return self.instantiate(h, _s32(buf[start]), depth)
        if count == 0 or self.loose_bvar_range(h) <= depth:
            return h
        if is_leaf(h):
            id = (_s32(self.leaf_meta[leaf_index(h)]) >> 1) - 1
            rel = id - depth
            if rel < count:
                sub = _s32(buf[start + rel])
                return sub if (depth == 0 or self.loose_bvar_range(sub) == 0) else self.shift(sub, depth, 0)
            return self.bvar(id - count)
        gen = self._next_call_epoch()
        self._inst_all_closed = -1
        try:
            if depth == 0:
                return self._inst_multi_buf_d0(h, buf, start, count, gen << 8, 0)
            ac = self._buf_all_closed(buf, start, count)
            if ac and depth < 256:
                return self._inst_multi_buf_closed(
                    h, buf, start, count, (gen << 8) | depth, 0,
                )
            return self._inst_multi_buf_oneshot(
                h, buf, start, count, depth, gen, ac, 0,
            )
        finally:
            self._subst_top = 0
            if self._call_memo.size > 0:
                self._call_memo.clear()

    def _inst_multi_buf_d0(self, h, buf, start, n, tag, rdepth):
        if is_leaf(h):
            m = _s32(self.leaf_meta[leaf_index(h)])
            if m <= 1:
                return h
            id = (m >> 1) - 1
            return _s32(buf[start + id]) if id < n else self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if hdr < 16:
            return h
        call_slot = self.call_slot
        entry = call_slot[ri]
        if (entry >> 32) == tag:
            return entry & _TABLE_SLOT_MASK
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                am = _s32(self.leaf_meta[leaf_index(a)])
                if am <= 1:
                    na = a
                else:
                    aid = (am >> 1) - 1
                    na = _s32(buf[start + aid]) if aid < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if ahdr < 16:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_buf_d0(a, buf, start, n, tag, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    while True:
                        if is_leaf(cur):
                            cm = _s32(self.leaf_meta[leaf_index(cur)])
                            if cm <= 1:
                                na = cur
                            else:
                                cid = (cm >> 1) - 1
                                na = _s32(buf[start + cid]) if cid < n else self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if chdr < 16:
                            na = cur
                            break
                        centry = call_slot[cri]
                        if (centry >> 32) == tag:
                            na = centry & _TABLE_SLOT_MASK
                            break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_buf_d0(cur, buf, start, n, tag, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cri)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        nri = _s32(self._subst_stack[stop])
                        recs = self.recs
                        old_b = _s32(recs[(nri << 2) + F_B])
                        if is_leaf(old_b):
                            bm2 = _s32(self.leaf_meta[leaf_index(old_b)])
                            if bm2 <= 1:
                                nb2 = old_b
                            else:
                                bid2 = (bm2 >> 1) - 1
                                nb2 = _s32(buf[start + bid2]) if bid2 < n else self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if _s32(recs[bri2 << 2]) < 16:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2]
                                if (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_multi_buf_d0(old_b, buf, start, n, tag, nr)
                        na = self.cons_app(na, nb2)
                        self.call_slot[nri] = (tag << 32) | na
                    self._subst_top = smark
            if is_leaf(b):
                bm = _s32(self.leaf_meta[leaf_index(b)])
                if bm <= 1:
                    nb = b
                else:
                    bid = (bm >> 1) - 1
                    nb = _s32(buf[start + bid]) if bid < n else self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if _s32(self.recs[bri << 2]) < 16:
                    nb = b
                else:
                    bentry = self.call_slot[bri]
                    if (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_multi_buf_d0(b, buf, start, n, tag, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                am = _s32(self.leaf_meta[leaf_index(a)])
                if am <= 1:
                    na = a
                else:
                    aid = (am >> 1) - 1
                    na = _s32(buf[start + aid]) if aid < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                if _s32(recs[ari << 2]) < 16:
                    na = a
                else:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_buf_d0(a, buf, start, n, tag, nr)
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= 1:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - 1
                    if brel < n:
                        bsub = _s32(buf[start + brel])
                        nb = bsub if self.loose_bvar_range(bsub) == 0 else self.shift(bsub, 1, 0)
                    else:
                        nb = self.bvar(bid - n)
            elif (_s32(self.recs[rec_index(b) << 2]) >> 4) <= 1:
                nb = b
            else:
                ac = self._inst_all_closed
                if ac < 0:
                    ac = 1 if self._buf_all_closed(buf, start, n) else 0
                    self._inst_all_closed = ac
                if ac != 0:
                    nb = self._inst_multi_buf_closed(
                        b, buf, start, n, tag | 1, nr,
                    )
                else:
                    nb = self._inst_multi_buf_oneshot(
                        b, buf, start, n, 1, tag >> 8, False, nr,
                    )
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_buf_d0(a, buf, start, n, tag, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_buf_d0(a, buf, start, n, tag, nr)
            nv = self._inst_multi_buf_d0(value, buf, start, n, tag, nr)
            if self.loose_bvar_range(body) <= 1:
                nbody = body
            else:
                ac = self._inst_all_closed
                if ac < 0:
                    ac = 1 if self._buf_all_closed(buf, start, n) else 0
                    self._inst_all_closed = ac
                if ac != 0:
                    nbody = self._inst_multi_buf_closed(
                        body, buf, start, n, tag | 1, nr,
                    )
                else:
                    nbody = self._inst_multi_buf_oneshot(
                        body, buf, start, n, 1, tag >> 8, False, nr,
                    )
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        self.call_slot[ri] = (tag << 32) | r
        return r

    def _inst_multi_buf_closed(self, h, buf, start, n, tag, rdepth):
        """Hot specialization of `_inst_multi_buf_oneshot` when all substitutes
        are closed (`loose_bvar_range == 0`) and `1 <= depth < 256`, packing
        `(gen << 8) | depth` into `tag` to minimize live registers and spills."""
        depth = tag & 0xFF
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            rel = id - depth
            return _s32(buf[start + rel]) if rel < n else self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        call_slot = self.call_slot
        entry = call_slot[ri]
        if (entry >> 32) == tag:
            return entry & _TABLE_SLOT_MASK
        if (entry >> 40) == (tag >> 8):
            r = self._call_memo.get((h << 16) | depth, 0)
            if r != 0:
                return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    na = _s32(buf[start + arel]) if arel < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_buf_closed(a, buf, start, n, tag, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                crel = cid - depth
                                na = _s32(buf[start + crel]) if crel < n else self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        centry = call_slot[cri]
                        if (centry >> 32) == tag:
                            na = centry & _TABLE_SLOT_MASK
                            break
                        if (centry >> 40) == (tag >> 8):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_buf_closed(cur, buf, start, n, tag, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cri)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        nri = _s32(self._subst_stack[stop])
                        recs = self.recs
                        old_b = _s32(recs[(nri << 2) + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                brel2 = bid2 - depth
                                nb2 = _s32(buf[start + brel2]) if brel2 < n else self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) >> 4) <= depth:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2]
                                if (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_multi_buf_closed(old_b, buf, start, n, tag, nr)
                        na = self.cons_app(na, nb2)
                        call_slot = self.call_slot
                        if (call_slot[nri] >> 40) != (tag >> 8):
                            call_slot[nri] = (tag << 32) | na
                        else:
                            self._call_memo.set((rec_handle(nri) << 16) | depth, na)
                    self._subst_top = smark
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - depth
                    nb = _s32(buf[start + brel]) if brel < n else self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) >> 4) <= depth:
                    nb = b
                else:
                    bentry = self.call_slot[bri]
                    if (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_multi_buf_closed(b, buf, start, n, tag, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    na = _s32(buf[start + arel]) if arel < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                if (_s32(recs[ari << 2]) >> 4) <= depth:
                    na = a
                else:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_buf_closed(a, buf, start, n, tag, nr)
            d1 = depth + 1
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= d1:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - d1
                    nb = _s32(buf[start + brel]) if brel < n else self.bvar(bid - n)
            elif (_s32(self.recs[rec_index(b) << 2]) >> 4) <= d1:
                nb = b
            elif d1 < 256:
                nb = self._inst_multi_buf_closed(b, buf, start, n, tag + 1, nr)
            else:
                nb = self._inst_multi_buf_oneshot(b, buf, start, n, d1, tag >> 8, True, nr)
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_buf_closed(a, buf, start, n, tag, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_buf_closed(a, buf, start, n, tag, nr)
            nv = self._inst_multi_buf_closed(value, buf, start, n, tag, nr)
            d1 = depth + 1
            if self.loose_bvar_range(body) <= d1:
                nbody = body
            elif d1 < 256:
                nbody = self._inst_multi_buf_closed(body, buf, start, n, tag + 1, nr)
            else:
                nbody = self._inst_multi_buf_oneshot(body, buf, start, n, d1, tag >> 8, True, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        call_slot = self.call_slot
        if (call_slot[ri] >> 40) != (tag >> 8):
            call_slot[ri] = (tag << 32) | r
        else:
            self._call_memo.set((h << 16) | depth, r)
        return r

    @dont_inline
    def _inst_multi_buf_oneshot(self, h, buf, start, n, depth, gen, all_closed, rdepth):
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            rel = id - depth
            if rel < n:
                sub = _s32(buf[start + rel])
                return sub if all_closed else self.shift(sub, depth, 0)
            return self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        if depth < 256:
            tag = (gen << 8) | depth
            entry = self.call_slot[ri]
            if (entry >> 32) == tag:
                return entry & _TABLE_SLOT_MASK
            if (entry >> 40) == gen:
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        else:
            tag = 0
            if depth < (1 << 16):
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    if arel < n:
                        asub = _s32(buf[start + arel])
                        na = asub if all_closed else self.shift(asub, depth, 0)
                    else:
                        na = self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = self.call_slot[ari] if tag != 0 else 0
                    if tag != 0 and (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_buf_oneshot(a, buf, start, n, depth, gen, all_closed, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    call_slot = self.call_slot
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                crel = cid - depth
                                if crel < n:
                                    csub = _s32(buf[start + crel])
                                    na = csub if all_closed else self.shift(csub, depth, 0)
                                else:
                                    na = self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        if tag != 0:
                            centry = call_slot[cri]
                            if (centry >> 32) == tag:
                                na = centry & _TABLE_SLOT_MASK
                                break
                            if (centry >> 40) == gen:
                                cr = self._call_memo.get((cur << 16) | depth, 0)
                                if cr != 0:
                                    na = cr
                                    break
                        elif depth < (1 << 16):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_buf_oneshot(cur, buf, start, n, depth, gen, all_closed, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        nri = rec_index(node)
                        recs = self.recs
                        nbase = nri << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                brel2 = bid2 - depth
                                if brel2 < n:
                                    bsub2 = _s32(buf[start + brel2])
                                    nb2 = bsub2 if all_closed else self.shift(bsub2, depth, 0)
                                else:
                                    nb2 = self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) >> 4) <= depth:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2] if tag != 0 else 0
                                if tag != 0 and (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_multi_buf_oneshot(old_b, buf, start, n, depth, gen, all_closed, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        if tag != 0:
                            call_slot = self.call_slot
                            if (call_slot[nri] >> 40) != gen:
                                call_slot[nri] = (tag << 32) | na
                            else:
                                self._call_memo.set((node << 16) | depth, na)
                        elif depth < (1 << 16):
                            self._call_memo.set((node << 16) | depth, na)
                    self._subst_top = smark
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - depth
                    if brel < n:
                        bsub = _s32(buf[start + brel])
                        nb = bsub if all_closed else self.shift(bsub, depth, 0)
                    else:
                        nb = self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) >> 4) <= depth:
                    nb = b
                else:
                    bentry = self.call_slot[bri] if tag != 0 else 0
                    if tag != 0 and (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_multi_buf_oneshot(b, buf, start, n, depth, gen, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    if arel < n:
                        asub = _s32(buf[start + arel])
                        na = asub if all_closed else self.shift(asub, depth, 0)
                    else:
                        na = self.bvar(aid - n)
            else:
                ari = rec_index(a)
                if (_s32(recs[ari << 2]) >> 4) <= depth:
                    na = a
                else:
                    aentry = self.call_slot[ari] if tag != 0 else 0
                    if tag != 0 and (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_buf_oneshot(a, buf, start, n, depth, gen, all_closed, nr)
            d1 = depth + 1
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= d1:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - d1
                    if brel < n:
                        bsub = _s32(buf[start + brel])
                        nb = bsub if all_closed else self.shift(bsub, d1, 0)
                    else:
                        nb = self.bvar(bid - n)
            else:
                nb = b if (_s32(self.recs[rec_index(b) << 2]) >> 4) <= d1 else self._inst_multi_buf_oneshot(b, buf, start, n, d1, gen, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_buf_oneshot(a, buf, start, n, depth, gen, all_closed, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_buf_oneshot(a, buf, start, n, depth, gen, all_closed, nr)
            nv = self._inst_multi_buf_oneshot(value, buf, start, n, depth, gen, all_closed, nr)
            nbody = self._inst_multi_buf_oneshot(body, buf, start, n, depth + 1, gen, all_closed, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        if tag != 0:
            call_slot = self.call_slot
            if (call_slot[ri] >> 40) != gen:
                call_slot[ri] = (tag << 32) | r
            else:
                self._call_memo.set((h << 16) | depth, r)
        elif depth < (1 << 16):
            self._call_memo.set((h << 16) | depth, r)
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
            id = (_s32(self.leaf_meta[leaf_index(h)]) >> 1) - 1
            rel = id - depth
            if rel < count:
                sub = substs[count - 1 - rel]
                return sub if (depth == 0 or self.loose_bvar_range(sub) == 0) else self.shift(sub, depth, 0)
            return self.bvar(id - count)
        gen = self._next_call_epoch()
        self._inst_all_closed = -1
        try:
            if depth == 0:
                return self._inst_multi_rev_d0(h, substs, count, gen << 8, 0)
            ac = self._list_all_closed(substs, count)
            if ac and depth < 256:
                return self._inst_multi_rev_closed(
                    h, substs, count, (gen << 8) | depth, 0,
                )
            return self._inst_multi_rev_oneshot(
                h, substs, count, depth, gen, ac, 0,
            )
        finally:
            self._subst_top = 0
            if self._call_memo.size > 0:
                self._call_memo.clear()

    def _inst_multi_rev_d0(self, h, substs, n, tag, rdepth):
        if is_leaf(h):
            m = _s32(self.leaf_meta[leaf_index(h)])
            if m <= 1:
                return h
            id = (m >> 1) - 1
            return substs[n - 1 - id] if id < n else self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if hdr < 16:
            return h
        call_slot = self.call_slot
        entry = call_slot[ri]
        if (entry >> 32) == tag:
            return entry & _TABLE_SLOT_MASK
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                am = _s32(self.leaf_meta[leaf_index(a)])
                if am <= 1:
                    na = a
                else:
                    aid = (am >> 1) - 1
                    na = substs[n - 1 - aid] if aid < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if ahdr < 16:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_rev_d0(a, substs, n, tag, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    while True:
                        if is_leaf(cur):
                            cm = _s32(self.leaf_meta[leaf_index(cur)])
                            if cm <= 1:
                                na = cur
                            else:
                                cid = (cm >> 1) - 1
                                na = substs[n - 1 - cid] if cid < n else self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if chdr < 16:
                            na = cur
                            break
                        centry = call_slot[cri]
                        if (centry >> 32) == tag:
                            na = centry & _TABLE_SLOT_MASK
                            break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_rev_d0(cur, substs, n, tag, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cri)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        nri = _s32(self._subst_stack[stop])
                        recs = self.recs
                        old_b = _s32(recs[(nri << 2) + F_B])
                        if is_leaf(old_b):
                            bm2 = _s32(self.leaf_meta[leaf_index(old_b)])
                            if bm2 <= 1:
                                nb2 = old_b
                            else:
                                bid2 = (bm2 >> 1) - 1
                                nb2 = substs[n - 1 - bid2] if bid2 < n else self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if _s32(recs[bri2 << 2]) < 16:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2]
                                if (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_multi_rev_d0(old_b, substs, n, tag, nr)
                        na = self.cons_app(na, nb2)
                        self.call_slot[nri] = (tag << 32) | na
                    self._subst_top = smark
            if is_leaf(b):
                bm = _s32(self.leaf_meta[leaf_index(b)])
                if bm <= 1:
                    nb = b
                else:
                    bid = (bm >> 1) - 1
                    nb = substs[n - 1 - bid] if bid < n else self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if _s32(self.recs[bri << 2]) < 16:
                    nb = b
                else:
                    bentry = self.call_slot[bri]
                    if (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_multi_rev_d0(b, substs, n, tag, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                am = _s32(self.leaf_meta[leaf_index(a)])
                if am <= 1:
                    na = a
                else:
                    aid = (am >> 1) - 1
                    na = substs[n - 1 - aid] if aid < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                if _s32(recs[ari << 2]) < 16:
                    na = a
                else:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_rev_d0(a, substs, n, tag, nr)
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= 1:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - 1
                    if brel < n:
                        bsub = substs[n - 1 - brel]
                        nb = bsub if self.loose_bvar_range(bsub) == 0 else self.shift(bsub, 1, 0)
                    else:
                        nb = self.bvar(bid - n)
            elif (_s32(self.recs[rec_index(b) << 2]) >> 4) <= 1:
                nb = b
            else:
                ac = self._inst_all_closed
                if ac < 0:
                    ac = 1 if self._list_all_closed(substs, n) else 0
                    self._inst_all_closed = ac
                if ac != 0:
                    nb = self._inst_multi_rev_closed(
                        b, substs, n, tag | 1, nr,
                    )
                else:
                    nb = self._inst_multi_rev_oneshot(
                        b, substs, n, 1, tag >> 8, False, nr,
                    )
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_rev_d0(a, substs, n, tag, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_rev_d0(a, substs, n, tag, nr)
            nv = self._inst_multi_rev_d0(value, substs, n, tag, nr)
            if self.loose_bvar_range(body) <= 1:
                nbody = body
            else:
                ac = self._inst_all_closed
                if ac < 0:
                    ac = 1 if self._list_all_closed(substs, n) else 0
                    self._inst_all_closed = ac
                if ac != 0:
                    nbody = self._inst_multi_rev_closed(
                        body, substs, n, tag | 1, nr,
                    )
                else:
                    nbody = self._inst_multi_rev_oneshot(
                        body, substs, n, 1, tag >> 8, False, nr,
                    )
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        self.call_slot[ri] = (tag << 32) | r
        return r

    def _inst_multi_rev_closed(self, h, substs, n, tag, rdepth):
        """Hot specialization of `_inst_multi_rev_oneshot` when all substitutes
        are closed (`loose_bvar_range == 0`) and `1 <= depth < 256`."""
        depth = tag & 0xFF
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            rel = id - depth
            return substs[n - 1 - rel] if rel < n else self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        call_slot = self.call_slot
        entry = call_slot[ri]
        if (entry >> 32) == tag:
            return entry & _TABLE_SLOT_MASK
        if (entry >> 40) == (tag >> 8):
            r = self._call_memo.get((h << 16) | depth, 0)
            if r != 0:
                return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    na = substs[n - 1 - arel] if arel < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_rev_closed(a, substs, n, tag, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                crel = cid - depth
                                na = substs[n - 1 - crel] if crel < n else self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        centry = call_slot[cri]
                        if (centry >> 32) == tag:
                            na = centry & _TABLE_SLOT_MASK
                            break
                        if (centry >> 40) == (tag >> 8):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_rev_closed(cur, substs, n, tag, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cri)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        nri = _s32(self._subst_stack[stop])
                        recs = self.recs
                        old_b = _s32(recs[(nri << 2) + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                brel2 = bid2 - depth
                                nb2 = substs[n - 1 - brel2] if brel2 < n else self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) >> 4) <= depth:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2]
                                if (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_multi_rev_closed(old_b, substs, n, tag, nr)
                        na = self.cons_app(na, nb2)
                        call_slot = self.call_slot
                        if (call_slot[nri] >> 40) != (tag >> 8):
                            call_slot[nri] = (tag << 32) | na
                        else:
                            self._call_memo.set((rec_handle(nri) << 16) | depth, na)
                    self._subst_top = smark
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - depth
                    nb = substs[n - 1 - brel] if brel < n else self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) >> 4) <= depth:
                    nb = b
                else:
                    bentry = self.call_slot[bri]
                    if (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_multi_rev_closed(b, substs, n, tag, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    na = substs[n - 1 - arel] if arel < n else self.bvar(aid - n)
            else:
                ari = rec_index(a)
                if (_s32(recs[ari << 2]) >> 4) <= depth:
                    na = a
                else:
                    aentry = call_slot[ari]
                    if (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_rev_closed(a, substs, n, tag, nr)
            d1 = depth + 1
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= d1:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - d1
                    nb = substs[n - 1 - brel] if brel < n else self.bvar(bid - n)
            elif (_s32(self.recs[rec_index(b) << 2]) >> 4) <= d1:
                nb = b
            elif d1 < 256:
                nb = self._inst_multi_rev_closed(b, substs, n, tag + 1, nr)
            else:
                nb = self._inst_multi_rev_oneshot(b, substs, n, d1, tag >> 8, True, nr)
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_rev_closed(a, substs, n, tag, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_rev_closed(a, substs, n, tag, nr)
            nv = self._inst_multi_rev_closed(value, substs, n, tag, nr)
            d1 = depth + 1
            if self.loose_bvar_range(body) <= d1:
                nbody = body
            elif d1 < 256:
                nbody = self._inst_multi_rev_closed(body, substs, n, tag + 1, nr)
            else:
                nbody = self._inst_multi_rev_oneshot(body, substs, n, d1, tag >> 8, True, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        call_slot = self.call_slot
        if (call_slot[ri] >> 40) != (tag >> 8):
            call_slot[ri] = (tag << 32) | r
        else:
            self._call_memo.set((h << 16) | depth, r)
        return r

    @dont_inline
    def _inst_multi_rev_oneshot(self, h, substs, n, depth, gen, all_closed, rdepth):
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            rel = id - depth
            if rel < n:
                sub = substs[n - 1 - rel]
                return sub if all_closed else self.shift(sub, depth, 0)
            return self.bvar(id - n)
        ri = rec_index(h)
        recs = self.recs
        base = ri << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        if depth < 256:
            tag = (gen << 8) | depth
            entry = self.call_slot[ri]
            if (entry >> 32) == tag:
                return entry & _TABLE_SLOT_MASK
            if (entry >> 40) == gen:
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        else:
            tag = 0
            if depth < (1 << 16):
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    if arel < n:
                        asub = substs[n - 1 - arel]
                        na = asub if all_closed else self.shift(asub, depth, 0)
                    else:
                        na = self.bvar(aid - n)
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    aentry = self.call_slot[ari] if tag != 0 else 0
                    if tag != 0 and (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_rev_oneshot(a, substs, n, depth, gen, all_closed, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    call_slot = self.call_slot
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                crel = cid - depth
                                if crel < n:
                                    csub = substs[n - 1 - crel]
                                    na = csub if all_closed else self.shift(csub, depth, 0)
                                else:
                                    na = self.bvar(cid - n)
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        if tag != 0:
                            centry = call_slot[cri]
                            if (centry >> 32) == tag:
                                na = centry & _TABLE_SLOT_MASK
                                break
                            if (centry >> 40) == gen:
                                cr = self._call_memo.get((cur << 16) | depth, 0)
                                if cr != 0:
                                    na = cr
                                    break
                        elif depth < (1 << 16):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._inst_multi_rev_oneshot(cur, substs, n, depth, gen, all_closed, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        nri = rec_index(node)
                        recs = self.recs
                        nbase = nri << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                brel2 = bid2 - depth
                                if brel2 < n:
                                    bsub2 = substs[n - 1 - brel2]
                                    nb2 = bsub2 if all_closed else self.shift(bsub2, depth, 0)
                                else:
                                    nb2 = self.bvar(bid2 - n)
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) >> 4) <= depth:
                                nb2 = old_b
                            else:
                                bentry2 = self.call_slot[bri2] if tag != 0 else 0
                                if tag != 0 and (bentry2 >> 32) == tag:
                                    nb2 = bentry2 & _TABLE_SLOT_MASK
                                else:
                                    self._subst_top = stop
                                    nb2 = self._inst_multi_rev_oneshot(old_b, substs, n, depth, gen, all_closed, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        if tag != 0:
                            call_slot = self.call_slot
                            if (call_slot[nri] >> 40) != gen:
                                call_slot[nri] = (tag << 32) | na
                            else:
                                self._call_memo.set((node << 16) | depth, na)
                        elif depth < (1 << 16):
                            self._call_memo.set((node << 16) | depth, na)
                    self._subst_top = smark
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - depth
                    if brel < n:
                        bsub = substs[n - 1 - brel]
                        nb = bsub if all_closed else self.shift(bsub, depth, 0)
                    else:
                        nb = self.bvar(bid - n)
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) >> 4) <= depth:
                    nb = b
                else:
                    bentry = self.call_slot[bri] if tag != 0 else 0
                    if tag != 0 and (bentry >> 32) == tag:
                        nb = bentry & _TABLE_SLOT_MASK
                    else:
                        nb = self._inst_multi_rev_oneshot(b, substs, n, depth, gen, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    if arel < n:
                        asub = substs[n - 1 - arel]
                        na = asub if all_closed else self.shift(asub, depth, 0)
                    else:
                        na = self.bvar(aid - n)
            else:
                ari = rec_index(a)
                if (_s32(recs[ari << 2]) >> 4) <= depth:
                    na = a
                else:
                    aentry = self.call_slot[ari] if tag != 0 else 0
                    if tag != 0 and (aentry >> 32) == tag:
                        na = aentry & _TABLE_SLOT_MASK
                    else:
                        na = self._inst_multi_rev_oneshot(a, substs, n, depth, gen, all_closed, nr)
            d1 = depth + 1
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= d1:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - d1
                    if brel < n:
                        bsub = substs[n - 1 - brel]
                        nb = bsub if all_closed else self.shift(bsub, d1, 0)
                    else:
                        nb = self.bvar(bid - n)
            else:
                nb = b if (_s32(self.recs[rec_index(b) << 2]) >> 4) <= d1 else self._inst_multi_rev_oneshot(b, substs, n, d1, gen, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, _s32(self.recs[(ri << 2) + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._inst_multi_rev_oneshot(a, substs, n, depth, gen, all_closed, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[(ri << 2) + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._inst_multi_rev_oneshot(a, substs, n, depth, gen, all_closed, nr)
            nv = self._inst_multi_rev_oneshot(value, substs, n, depth, gen, all_closed, nr)
            nbody = self._inst_multi_rev_oneshot(body, substs, n, depth + 1, gen, all_closed, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[(ri << 2) + F_INFO]))
        if tag != 0:
            call_slot = self.call_slot
            if (call_slot[ri] >> 40) != gen:
                call_slot[ri] = (tag << 32) | r
            else:
                self._call_memo.set((h << 16) | depth, r)
        elif depth < (1 << 16):
            self._call_memo.set((h << 16) | depth, r)
        return r

    def instantiate_multi_ctx(self, h, substs, chain):
        """Memoised multi-substitution for open-context materialization."""
        if self.loose_bvar_range(h) == 0:
            return h
        n = len(substs)
        if is_leaf(h):
            id = (_s32(self.leaf_meta[leaf_index(h)]) >> 1) - 1
            return substs[id] if id < n else self.bvar(id - n)
        key = _pack_key(h, chain, 0)
        if key != 0:
            r = self._multi_memo.get(key, 0)
        else:
            r = self._multi_memo.get_wide(h, chain, 0)
        if r != 0:
            return r
        smark = self._subst_top
        all_closed = self._list_all_closed(substs, n)
        try:
            return self._instantiate_multi(h, substs, n, chain, 0, all_closed, 0)
        finally:
            self._subst_top = smark

    def _instantiate_multi(self, h, substs, n, chain, depth, all_closed, rdepth):
        if is_leaf(h):
            lo = _s32(self.leaf_meta[leaf_index(h)]) >> 1
            if lo <= depth:
                return h
            id = lo - 1
            rel = id - depth
            if rel < n:
                s = substs[rel]
                return s if (all_closed or depth == 0) else self.shift(s, depth, 0)
            return self.bvar(id - n)
        recs = self.recs
        base = rec_index(h) << 2
        hdr = _s32(recs[base])
        if (hdr >> 4) <= depth:
            return h
        key = _pack_key(h, chain, depth)
        if key != 0:
            r = self._multi_memo.get(key, 0)
        else:
            r = self._multi_memo.get_wide(h, chain, depth)
        if r != 0:
            return r
        if (rdepth & 31) == 31:
            _check_stack_store("instantiate_multi")
        kind = hdr & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                if alo <= depth:
                    na = a
                else:
                    aid = alo - 1
                    arel = aid - depth
                    if arel < n:
                        sa = substs[arel]
                        na = sa if (all_closed or depth == 0) else self.shift(sa, depth, 0)
                    else:
                        na = self.bvar(aid - n)
            else:
                ahdr = _s32(recs[rec_index(a) << 2])
                if (ahdr >> 4) <= depth:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    akey = _pack_key(a, chain, depth)
                    ar = self._multi_memo.get(akey, 0) if akey != 0 else 0
                    na = ar if ar != 0 else self._instantiate_multi(a, substs, n, chain, depth, all_closed, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    while True:
                        if is_leaf(cur):
                            clo = _s32(self.leaf_meta[leaf_index(cur)]) >> 1
                            if clo <= depth:
                                na = cur
                            else:
                                cid = clo - 1
                                crel = cid - depth
                                if crel < n:
                                    cs = substs[crel]
                                    na = cs if (all_closed or depth == 0) else self.shift(cs, depth, 0)
                                else:
                                    na = self.bvar(cid - n)
                            break
                        cbase = rec_index(cur) << 2
                        chdr = _s32(recs[cbase])
                        if (chdr >> 4) <= depth:
                            na = cur
                            break
                        ckey = _pack_key(cur, chain, depth)
                        if ckey != 0:
                            cr = self._multi_memo.get(ckey, 0)
                        else:
                            cr = self._multi_memo.get_wide(cur, chain, depth)
                        if cr != 0:
                            na = cr
                            break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._instantiate_multi(cur, substs, n, chain, depth, all_closed, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[cbase + F_A])
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        recs = self.recs
                        nbase = rec_index(node) << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            blo2 = _s32(self.leaf_meta[leaf_index(old_b)]) >> 1
                            if blo2 <= depth:
                                nb2 = old_b
                            else:
                                bid2 = blo2 - 1
                                brel2 = bid2 - depth
                                if brel2 < n:
                                    sb2 = substs[brel2]
                                    nb2 = sb2 if (all_closed or depth == 0) else self.shift(sb2, depth, 0)
                                else:
                                    nb2 = self.bvar(bid2 - n)
                        elif (_s32(recs[rec_index(old_b) << 2]) >> 4) <= depth:
                            nb2 = old_b
                        else:
                            bkey2 = _pack_key(old_b, chain, depth)
                            br2 = self._multi_memo.get(bkey2, 0) if bkey2 != 0 else 0
                            if br2 != 0:
                                nb2 = br2
                            else:
                                self._subst_top = stop
                                nb2 = self._instantiate_multi(old_b, substs, n, chain, depth, all_closed, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        nkey = _pack_key(node, chain, depth)
                        if nkey != 0:
                            self._multi_memo.set(nkey, na)
                        else:
                            self._multi_memo.set_wide(node, chain, depth, na)
                    self._subst_top = smark
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                if blo <= depth:
                    nb = b
                else:
                    bid = blo - 1
                    brel = bid - depth
                    if brel < n:
                        sb = substs[brel]
                        nb = sb if (all_closed or depth == 0) else self.shift(sb, depth, 0)
                    else:
                        nb = self.bvar(bid - n)
            elif (_s32(self.recs[rec_index(b) << 2]) >> 4) <= depth:
                nb = b
            else:
                bkey = _pack_key(b, chain, depth)
                br = self._multi_memo.get(bkey, 0) if bkey != 0 else 0
                nb = br if br != 0 else self._instantiate_multi(b, substs, n, chain, depth, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if self.loose_bvar_range(a) <= depth else self._instantiate_multi(a, substs, n, chain, depth, all_closed, nr)
            nb = b if self.loose_bvar_range(b) <= depth + 1 else self._instantiate_multi(b, substs, n, chain, depth + 1, all_closed, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, _s32(self.recs[base + F_INFO]))
        elif kind == KIND_PROJ:
            na = self._instantiate_multi(a, substs, n, chain, depth, all_closed, nr)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, _s32(self.recs[base + F_INFO]))
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._instantiate_multi(a, substs, n, chain, depth, all_closed, nr)
            nv = self._instantiate_multi(value, substs, n, chain, depth, all_closed, nr)
            nbody = self._instantiate_multi(body, substs, n, chain, depth + 1, all_closed, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, _s32(self.recs[base + F_INFO]))
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
            return self.bvar(((_s32(self.leaf_meta[leaf_index(h)]) >> 1) - 1) + count)
        key = _pack_key(h, count, depth)
        if key != 0:
            r = self._shift_memo.get(key, 0)
        else:
            r = self._shift_memo.get_wide(h, count, depth)
        if r != 0:
            return r
        if (rdepth & 31) == 31:
            _check_stack_store("shift")
        recs = self.recs
        base = rec_index(h) << 2
        kind = _s32(recs[base]) & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        info = _s32(recs[base + F_INFO])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                alo = _s32(self.leaf_meta[leaf_index(a)]) >> 1
                na = a if alo <= depth else self.bvar(alo - 1 + count)
            elif (_s32(recs[rec_index(a) << 2]) >> 4) <= depth:
                na = a
            else:
                na = self.shift(a, count, depth, nr)
            if is_leaf(b):
                blo = _s32(self.leaf_meta[leaf_index(b)]) >> 1
                nb = b if blo <= depth else self.bvar(blo - 1 + count)
            elif (_s32(self.recs[rec_index(b) << 2]) >> 4) <= depth:
                nb = b
            else:
                nb = self.shift(b, count, depth, nr)
            r = self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if self.loose_bvar_range(a) <= depth else self.shift(a, count, depth, nr)
            nb = b if self.loose_bvar_range(b) <= depth + 1 else self.shift(b, count, depth + 1, nr)
            r = self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            r = self.cons(
                KIND_PROJ, self.shift(a, count, depth, nr), b, info,
            )
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = a if self.loose_bvar_range(a) <= depth else self.shift(a, count, depth, nr)
            nv = value if self.loose_bvar_range(value) <= depth else self.shift(value, count, depth, nr)
            nbody = body if self.loose_bvar_range(body) <= depth + 1 else self.shift(body, count, depth + 1, nr)
            pair = self.cons(KIND_PAIR, nv, nbody)
            r = self.cons(KIND_LET, na, pair, info)
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
        gen = self._next_call_epoch()
        try:
            r = self._bind_fvar_oneshot(h, fvar, depth, gen, 0)
        finally:
            self._subst_top = 0
            if self._call_memo.size > 0:
                self._call_memo.clear()
        if key != 0:
            self._bind_memo.set(key, r)
        else:
            self._bind_memo.set_wide(h, fvar, depth, r)
        return r

    def _bind_fvar_oneshot(self, h, fvar, depth, gen, rdepth):
        if not self.has_fvar(h):
            return h
        if is_leaf(h):
            return self.bvar(depth) if h == fvar else h
        ri = rec_index(h)
        if depth < 256:
            tag = (gen << 8) | depth
            entry = self.call_slot[ri]
            if (entry >> 32) == tag:
                return entry & _TABLE_SLOT_MASK
            if (entry >> 40) == gen:
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        else:
            tag = 0
            if depth < (1 << 16):
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        if (rdepth & 31) == 31:
            _check_stack_store("bind_fvar")
        recs = self.recs
        base = ri << 2
        kind = _s32(recs[base]) & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        info = _s32(recs[base + F_INFO])
        nr = rdepth + 1
        if kind == KIND_APP:
            if is_leaf(a):
                na = self.bvar(depth) if a == fvar else a
            else:
                ahdr = _s32(recs[rec_index(a) << 2])
                if (ahdr & 8) == 0:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    na = self._bind_fvar_oneshot(a, fvar, depth, gen, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    call_slot = self.call_slot
                    while True:
                        if is_leaf(cur):
                            na = self.bvar(depth) if cur == fvar else cur
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr & 8) == 0:
                            na = cur
                            break
                        if tag != 0:
                            centry = call_slot[cri]
                            if (centry >> 32) == tag:
                                na = centry & _TABLE_SLOT_MASK
                                break
                            if (centry >> 40) == gen:
                                cr = self._call_memo.get((cur << 16) | depth, 0)
                                if cr != 0:
                                    na = cr
                                    break
                        elif depth < (1 << 16):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._bind_fvar_oneshot(cur, fvar, depth, gen, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    self._subst_top = stop
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        self._subst_top = stop
                        nri = rec_index(node)
                        recs = self.recs
                        nbase = nri << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            nb2 = self.bvar(depth) if old_b == fvar else old_b
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) & 8) == 0:
                                nb2 = old_b
                            elif tag != 0 and (self.call_slot[bri2] >> 32) == tag:
                                nb2 = self.call_slot[bri2] & _TABLE_SLOT_MASK
                            else:
                                nb2 = self._bind_fvar_oneshot(old_b, fvar, depth, gen, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        if tag != 0:
                            call_slot = self.call_slot
                            if (call_slot[nri] >> 40) != gen:
                                call_slot[nri] = (tag << 32) | na
                            else:
                                self._call_memo.set((node << 16) | depth, na)
                        elif depth < (1 << 16):
                            self._call_memo.set((node << 16) | depth, na)
            if is_leaf(b):
                nb = self.bvar(depth) if b == fvar else b
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) & 8) == 0:
                    nb = b
                elif tag != 0 and (self.call_slot[bri] >> 32) == tag:
                    nb = self.call_slot[bri] & _TABLE_SLOT_MASK
                else:
                    nb = self._bind_fvar_oneshot(b, fvar, depth, gen, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if not self.has_fvar(a) else self._bind_fvar_oneshot(a, fvar, depth, gen, nr)
            nb = b if not self.has_fvar(b) else self._bind_fvar_oneshot(b, fvar, depth + 1, gen, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self._bind_fvar_oneshot(a, fvar, depth, gen, nr)
            r = h if na == a else self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._bind_fvar_oneshot(a, fvar, depth, gen, nr)
            nv = self._bind_fvar_oneshot(value, fvar, depth, gen, nr)
            nbody = self._bind_fvar_oneshot(body, fvar, depth + 1, gen, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if tag != 0:
            call_slot = self.call_slot
            if (call_slot[ri] >> 40) != gen:
                call_slot[ri] = (tag << 32) | r
            else:
                self._call_memo.set((h << 16) | depth, r)
        elif depth < (1 << 16):
            self._call_memo.set((h << 16) | depth, r)
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

    def bind_fvars(self, h, fvars, depth=0, count=-1):
        """
        ``h`` with the first ``count`` free variables in ``fvars`` (in binding
        order) abstracted in one pass: ``fvars[count - 1]`` becomes ``depth``,
        ``fvars[0]`` becomes ``depth + count - 1``.
        """
        n = len(fvars) if count < 0 else count
        if n == 1:
            return self.bind_fvar(h, fvars[0], depth)
        if n == 0 or not self.has_fvar(h):
            return h
        if is_leaf(h):
            j = 0
            while j < n:
                if fvars[j] == h:
                    return self.bvar(depth + n - 1 - j)
                j += 1
            return h
        lo = fvars[0]
        hi = lo
        j = 1
        while j < n:
            fj = fvars[j]
            if fj < lo:
                lo = fj
            elif fj > hi:
                hi = fj
            j += 1
        self._bind_lo = lo
        self._bind_span = r_uint(hi - lo)
        gen = self._next_call_epoch()
        try:
            return self._bind_fvars_oneshot(h, fvars, n, depth, gen, 0)
        finally:
            self._subst_top = 0
            if self._call_memo.size > 0:
                self._call_memo.clear()

    def _bind_fvars_oneshot(self, h, fvars, n, depth, gen, rdepth):
        if is_leaf(h):
            if r_uint(h - self._bind_lo) <= self._bind_span:
                j = 0
                while j < n:
                    if fvars[j] == h:
                        return self.bvar(depth + n - 1 - j)
                    j += 1
            return h
        if not self.has_fvar(h):
            return h
        ri = rec_index(h)
        if depth < 256:
            tag = (gen << 8) | depth
            entry = self.call_slot[ri]
            if (entry >> 32) == tag:
                return entry & _TABLE_SLOT_MASK
            if (entry >> 40) == gen:
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        else:
            tag = 0
            if depth < (1 << 16):
                r = self._call_memo.get((h << 16) | depth, 0)
                if r != 0:
                    return r
        if (rdepth & 31) == 31:
            _check_stack_store("bind_fvars")
        recs = self.recs
        base = ri << 2
        kind = _s32(recs[base]) & _KIND_MASK
        a = _s32(recs[base + F_A])
        b = _s32(recs[base + F_B])
        info = _s32(recs[base + F_INFO])
        nr = rdepth + 1
        if kind == KIND_APP:
            bind_lo = self._bind_lo
            bind_span = self._bind_span
            if is_leaf(a):
                na = a
                if r_uint(a - bind_lo) <= bind_span:
                    j = 0
                    while j < n:
                        if fvars[j] == a:
                            na = self.bvar(depth + n - 1 - j)
                            break
                        j += 1
            else:
                ari = rec_index(a)
                ahdr = _s32(recs[ari << 2])
                if (ahdr & 8) == 0:
                    na = a
                elif (ahdr & _KIND_MASK) != KIND_APP:
                    if tag != 0 and (self.call_slot[ari] >> 32) == tag:
                        na = self.call_slot[ari] & _TABLE_SLOT_MASK
                    else:
                        na = self._bind_fvars_oneshot(a, fvars, n, depth, gen, nr)
                else:
                    smark = self._subst_top
                    stop = smark
                    cur = a
                    call_slot = self.call_slot
                    while True:
                        if is_leaf(cur):
                            na = cur
                            if r_uint(cur - bind_lo) <= bind_span:
                                j = 0
                                while j < n:
                                    if fvars[j] == cur:
                                        na = self.bvar(depth + n - 1 - j)
                                        break
                                    j += 1
                            break
                        cri = rec_index(cur)
                        chdr = _s32(recs[cri << 2])
                        if (chdr & 8) == 0:
                            na = cur
                            break
                        if tag != 0:
                            centry = call_slot[cri]
                            if (centry >> 32) == tag:
                                na = centry & _TABLE_SLOT_MASK
                                break
                            if (centry >> 40) == gen:
                                cr = self._call_memo.get((cur << 16) | depth, 0)
                                if cr != 0:
                                    na = cr
                                    break
                        elif depth < (1 << 16):
                            cr = self._call_memo.get((cur << 16) | depth, 0)
                            if cr != 0:
                                na = cr
                                break
                        if (chdr & _KIND_MASK) != KIND_APP:
                            self._subst_top = stop
                            na = self._bind_fvars_oneshot(cur, fvars, n, depth, gen, nr)
                            break
                        if stop == self._subst_cap:
                            ncap = self._subst_cap * 2
                            self._subst_stack = _grow_u32_uninit(self._subst_stack, stop, ncap)
                            self._subst_cap = ncap
                        self._subst_stack[stop] = _u32(cur)
                        stop += 1
                        cur = _s32(recs[(cri << 2) + F_A])
                    self._subst_top = stop
                    while stop > smark:
                        stop -= 1
                        node = _s32(self._subst_stack[stop])
                        self._subst_top = stop
                        nri = rec_index(node)
                        recs = self.recs
                        nbase = nri << 2
                        old_a = _s32(recs[nbase + F_A])
                        old_b = _s32(recs[nbase + F_B])
                        if is_leaf(old_b):
                            nb2 = old_b
                            if r_uint(old_b - bind_lo) <= bind_span:
                                j = 0
                                while j < n:
                                    if fvars[j] == old_b:
                                        nb2 = self.bvar(depth + n - 1 - j)
                                        break
                                    j += 1
                        else:
                            bri2 = rec_index(old_b)
                            if (_s32(recs[bri2 << 2]) & 8) == 0:
                                nb2 = old_b
                            elif tag != 0 and (self.call_slot[bri2] >> 32) == tag:
                                nb2 = self.call_slot[bri2] & _TABLE_SLOT_MASK
                            else:
                                nb2 = self._bind_fvars_oneshot(old_b, fvars, n, depth, gen, nr)
                        na = node if (na == old_a and nb2 == old_b) else self.cons_app(na, nb2)
                        if tag != 0:
                            call_slot = self.call_slot
                            if (call_slot[nri] >> 40) != gen:
                                call_slot[nri] = (tag << 32) | na
                            else:
                                self._call_memo.set((node << 16) | depth, na)
                        elif depth < (1 << 16):
                            self._call_memo.set((node << 16) | depth, na)
            if is_leaf(b):
                nb = b
                if r_uint(b - bind_lo) <= bind_span:
                    j = 0
                    while j < n:
                        if fvars[j] == b:
                            nb = self.bvar(depth + n - 1 - j)
                            break
                        j += 1
            else:
                bri = rec_index(b)
                if (_s32(self.recs[bri << 2]) & 8) == 0:
                    nb = b
                elif tag != 0 and (self.call_slot[bri] >> 32) == tag:
                    nb = self.call_slot[bri] & _TABLE_SLOT_MASK
                else:
                    nb = self._bind_fvars_oneshot(b, fvars, n, depth, gen, nr)
            r = h if (na == a and nb == b) else self.cons_app(na, nb)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = a if not self.has_fvar(a) else self._bind_fvars_oneshot(a, fvars, n, depth, gen, nr)
            nb = b if not self.has_fvar(b) else self._bind_fvars_oneshot(b, fvars, n, depth + 1, gen, nr)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, info)
        elif kind == KIND_PROJ:
            na = self._bind_fvars_oneshot(a, fvars, n, depth, gen, nr)
            r = h if na == a else self.cons(KIND_PROJ, na, b, info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self._bind_fvars_oneshot(a, fvars, n, depth, gen, nr)
            nv = self._bind_fvars_oneshot(value, fvars, n, depth, gen, nr)
            nbody = self._bind_fvars_oneshot(body, fvars, n, depth + 1, gen, nr)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody)
                r = self.cons(KIND_LET, na, pair, info)
        if tag != 0:
            call_slot = self.call_slot
            if (call_slot[ri] >> 40) != gen:
                call_slot[ri] = (tag << 32) | r
            else:
                self._call_memo.set((h << 16) | depth, r)
        elif depth < (1 << 16):
            self._call_memo.set((h << 16) | depth, r)
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
        if not self._rec_node_dirty:
            return None
        i = _s32(self.rec_node[rec_index(h)])
        if i == 0:
            return None
        return self.nodes[i - 1]

    def set_node(self, h, e):
        if not self.rec_node:
            self.rec_node = _alloc_u32(self.cap)
        self._rec_node_dirty = True
        self.nodes.append(e)
        self.rec_node[rec_index(h)] = _u32(len(self.nodes))

    @dont_inline
    def _clear_import_spine(self, mark):
        spine = self._import_spine
        top = self._import_spine_len
        while top > mark:
            top -= 1
            spine[top] = None
        self._import_spine_len = mark

    def import_term(self, e):
        """The handle for the term ``e``, memoised intrusively on `W_Expr._cache`."""
        gen = self._store_gen
        c = e._cache
        if (c >> 32) == gen:
            return c & _TABLE_SLOT_MASK
        mark = self._import_spine_len
        try:
            return self._import_rec(e, gen, 0)
        finally:
            if self._import_spine_len > mark:
                self._clear_import_spine(mark)

    def _import_rec(self, e, gen, rdepth):
        c = e._cache
        if (c >> 32) == gen:
            return c & _TABLE_SLOT_MASK
        cls = e.__class__
        if cls is W_BVar:
            assert isinstance(e, W_BVar)
            id = e.id
            if 0 <= id < _BVAR_ARR_LEN:
                h = self._bvar_arr[id]
                if h != 0:
                    return h
                h = self._new_leaf(e)
                self._bvar_arr[id] = h
                if id + 1 > self._bvar_max:
                    self._bvar_max = id + 1
                return h
            return self.leaf_for(e)
        if (rdepth & 31) == 31:
            _check_stack_store("import_term")
        nr = rdepth + 1
        if cls is W_App:
            assert isinstance(e, W_App)
            fn = e.fn
            fc = fn._cache
            if (fc >> 32) == gen:
                fn_h = fc & _TABLE_SLOT_MASK
            elif not isinstance(fn, W_App):
                fn_h = self._import_rec(fn, gen, nr)
            else:
                fn_h = 0
            if fn_h != 0:
                arg = e.arg
                ac = arg._cache
                if (ac >> 32) == gen:
                    arg_h = ac & _TABLE_SLOT_MASK
                elif arg.__class__ is W_BVar:
                    assert isinstance(arg, W_BVar)
                    bid = arg.id
                    if 0 <= bid < _BVAR_ARR_LEN:
                        arg_h = self._bvar_arr[bid]
                        if arg_h == 0:
                            arg_h = self._new_leaf(arg)
                            self._bvar_arr[bid] = arg_h
                            if bid + 1 > self._bvar_max:
                                self._bvar_max = bid + 1
                    else:
                        arg_h = self.leaf_for(arg)
                else:
                    arg_h = self._import_rec(arg, gen, nr)
                head = self.cons_app(fn_h, arg_h)
                if gen > 0:
                    e._cache = (gen << 32) | head
                if self.record_nodes:
                    self.set_node(head, e)
                return head
            # Walk the spine down to the first already-imported node
            # (or the head) using the cursor-indexed `_import_spine` buffer,
            # then fold applications back up. Cleanup on exception happens
            # once at the outer `import_term` / `import_const_term` frame.
            spine = self._import_spine
            mark = self._import_spine_len
            top = mark
            assert top >= 0
            if top < len(spine):
                spine[top] = e
            else:
                spine.append(e)
            top += 1
            cur = fn
            head = 0
            while True:
                if not isinstance(cur, W_App):
                    self._import_spine_len = top
                    cc = cur._cache
                    if (cc >> 32) == gen:
                        head = cc & _TABLE_SLOT_MASK
                    else:
                        head = self._import_rec(cur, gen, nr)
                    break
                cc = cur._cache
                if (cc >> 32) == gen:
                    head = cc & _TABLE_SLOT_MASK
                    break
                assert top >= 0
                if top < len(spine):
                    spine[top] = cur
                else:
                    spine.append(cur)
                top += 1
                cur = cur.fn
            while top > mark:
                top -= 1
                assert top >= 0
                app = spine[top]
                spine[top] = None
                arg = app.arg
                ac = arg._cache
                if (ac >> 32) == gen:
                    arg_h = ac & _TABLE_SLOT_MASK
                elif arg.__class__ is W_BVar:
                    assert isinstance(arg, W_BVar)
                    bid = arg.id
                    if 0 <= bid < _BVAR_ARR_LEN:
                        arg_h = self._bvar_arr[bid]
                        if arg_h == 0:
                            arg_h = self._new_leaf(arg)
                            self._bvar_arr[bid] = arg_h
                            if bid + 1 > self._bvar_max:
                                self._bvar_max = bid + 1
                    else:
                        arg_h = self.leaf_for(arg)
                else:
                    self._import_spine_len = top
                    arg_h = self._import_rec(arg, gen, nr)
                head = self.cons_app(head, arg_h)
                if gen > 0:
                    app._cache = (gen << 32) | head
                if self.record_nodes:
                    self.set_node(head, app)
            self._import_spine_len = mark
            return head
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(e, W_Lambda) or isinstance(e, W_ForAll)
            binder = e.binder
            btype = binder.type
            tc = btype._cache
            type = (
                tc & _TABLE_SLOT_MASK
                if (tc >> 32) == gen
                else self._import_rec(btype, gen, nr)
            )
            ebody = e.body
            bc = ebody._cache
            body = (
                bc & _TABLE_SLOT_MASK
                if (bc >> 32) == gen
                else self._import_rec(ebody, gen, nr)
            )
            if cls is W_Lambda:
                h = self.lam(binder, type, body)
            else:
                h = self.forall(binder, type, body)
        elif cls is W_Proj:
            assert isinstance(e, W_Proj)
            h = self.proj(
                e.struct_name, e.field_index, self._import_rec(e.struct_expr, gen, nr),
            )
        elif cls is W_Let:
            assert isinstance(e, W_Let)
            h = self.let(
                e.name,
                self._import_rec(e.type, gen, nr),
                self._import_rec(e.value, gen, nr),
                self._import_rec(e.body, gen, nr),
            )
        else:
            return self.leaf_for(e)
        if gen > 0:
            e._cache = (gen << 32) | h
        if self.record_nodes:
            self.set_node(h, e)
        return h

    def clear_fvar_gens(self):
        n = self._fvar_gens_len
        if n > 0:
            gens = self._fvar_gens
            i = 0
            while i < n:
                gens[i] = 0
                i += 1
            self._fvar_gens_len = 0
        self._fvar_base_gen = 0
        if self._fvar_multi is not None:
            self._fvar_multi = None

    def _fvar_gen_for_depth(self, depth):
        gens = self._fvar_gens
        while depth >= len(gens):
            gens.append(0)
        g = gens[depth]
        if g == 0:
            g = _next_cache_gen()
            gens[depth] = g
            if depth + 1 > self._fvar_gens_len:
                self._fvar_gens_len = depth + 1
        return g

    def _fvar_cache_put(self, e, depth, dgen, h):
        if dgen > 0:
            base = self._fvar_base_gen
            if base > 0 and (e._cache >> 32) >= base and (e._cache >> 32) != dgen:
                mm = self._fvar_multi
                if mm is None:
                    mm = self._fvar_multi = {}
                mm[(e, depth)] = h
                return
            e._cache = (dgen << 32) | h

    def import_term_fvars(self, e, fvars, nf, fgen):
        """Import ``e`` while substituting outer telescope bound variables
        ``BVar(k) -> fvars[nf - 1 - k]`` (all closed `W_FVar` leaves) directly
        on the AST, avoiding allocating throwaway `BVar`-bearing records."""
        if nf == 0 or e.loose_bvar_range() == 0:
            return self.import_term(e)
        if e.__class__ is W_BVar:
            assert isinstance(e, W_BVar)
            bid = e.id
            return fvars[nf - 1 - bid] if bid < nf else self.bvar(bid - nf)
        if fgen > 0:
            c = e._cache
            if (c >> 32) == fgen:
                return c & _TABLE_SLOT_MASK
            if self._fvar_base_gen == 0:
                self._fvar_base_gen = fgen
        mark = self._import_spine_len
        try:
            return self._import_fvars_rec(e, fvars, nf, 0, fgen, 0)
        finally:
            if self._import_spine_len > mark:
                self._clear_import_spine(mark)

    def _import_fvars_rec(self, e, fvars, nf, depth, dgen, rdepth):
        sgen = self._store_gen
        if e.loose_bvar_range() <= depth:
            c = e._cache
            if (c >> 32) == sgen:
                return c & _TABLE_SLOT_MASK
            return self._import_rec(e, sgen, rdepth)
        if dgen > 0:
            c = e._cache
            if (c >> 32) == dgen:
                return c & _TABLE_SLOT_MASK
            mm = self._fvar_multi
            if mm is not None:
                mh = mm.get((e, depth), 0)
                if mh != 0:
                    return mh
        if (rdepth & 31) == 31:
            _check_stack_store("import_term")
        cls = e.__class__
        nr = rdepth + 1
        if cls is W_BVar:
            assert isinstance(e, W_BVar)
            rel = e.id - depth
            if rel < nf:
                return fvars[nf - 1 - rel]
            return self.bvar(e.id - nf)
        if cls is W_App:
            assert isinstance(e, W_App)
            fn = e.fn
            fn_h = 0
            if fn.loose_bvar_range() <= depth:
                fc = fn._cache
                if (fc >> 32) == sgen:
                    fn_h = fc & _TABLE_SLOT_MASK
                else:
                    fn_h = self._import_rec(fn, sgen, nr)
            elif dgen > 0 and (fn._cache >> 32) == dgen:
                fn_h = fn._cache & _TABLE_SLOT_MASK
            elif not isinstance(fn, W_App):
                if fn.__class__ is W_BVar:
                    assert isinstance(fn, W_BVar)
                    rel = fn.id - depth
                    fn_h = fvars[nf - 1 - rel] if rel < nf else self.bvar(fn.id - nf)
                else:
                    fn_h = self._import_fvars_rec(fn, fvars, nf, depth, dgen, nr)
            if fn_h != 0:
                arg = e.arg
                if arg.loose_bvar_range() <= depth:
                    ac = arg._cache
                    if (ac >> 32) == sgen:
                        arg_h = ac & _TABLE_SLOT_MASK
                    elif arg.__class__ is W_BVar:
                        assert isinstance(arg, W_BVar)
                        bid = arg.id
                        if 0 <= bid < _BVAR_ARR_LEN:
                            arg_h = self._bvar_arr[bid]
                            if arg_h == 0:
                                arg_h = self._new_leaf(arg)
                                self._bvar_arr[bid] = arg_h
                                if bid + 1 > self._bvar_max:
                                    self._bvar_max = bid + 1
                        else:
                            arg_h = self.leaf_for(arg)
                    else:
                        arg_h = self._import_rec(arg, sgen, nr)
                elif arg.__class__ is W_BVar:
                    assert isinstance(arg, W_BVar)
                    rel = arg.id - depth
                    arg_h = fvars[nf - 1 - rel] if rel < nf else self.bvar(arg.id - nf)
                elif dgen > 0 and (arg._cache >> 32) == dgen:
                    arg_h = arg._cache & _TABLE_SLOT_MASK
                else:
                    arg_h = self._import_fvars_rec(arg, fvars, nf, depth, dgen, nr)
                head = self.cons_app(fn_h, arg_h)
                if dgen > 0:
                    if (self._fvar_base_gen > 0
                            and (e._cache >> 32) >= self._fvar_base_gen
                            and (e._cache >> 32) != dgen):
                        self._fvar_cache_put(e, depth, dgen, head)
                    else:
                        e._cache = (dgen << 32) | head
                return head
            spine = self._import_spine
            mark = self._import_spine_len
            top = mark
            assert top >= 0
            if top < len(spine):
                spine[top] = e
            else:
                spine.append(e)
            top += 1
            cur = fn
            head = 0
            while True:
                if cur.loose_bvar_range() <= depth:
                    self._import_spine_len = top
                    cc = cur._cache
                    head = (
                        cc & _TABLE_SLOT_MASK
                        if (cc >> 32) == sgen
                        else self._import_rec(cur, sgen, nr)
                    )
                    break
                if dgen > 0 and (cur._cache >> 32) == dgen:
                    head = cur._cache & _TABLE_SLOT_MASK
                    break
                if self._fvar_multi is not None:
                    mh = self._fvar_multi.get((cur, depth), 0)
                    if mh != 0:
                        head = mh
                        break
                if not isinstance(cur, W_App):
                    if cur.__class__ is W_BVar:
                        assert isinstance(cur, W_BVar)
                        rel = cur.id - depth
                        head = fvars[nf - 1 - rel] if rel < nf else self.bvar(cur.id - nf)
                    else:
                        self._import_spine_len = top
                        head = self._import_fvars_rec(cur, fvars, nf, depth, dgen, nr)
                    break
                assert top >= 0
                if top < len(spine):
                    spine[top] = cur
                else:
                    spine.append(cur)
                top += 1
                cur = cur.fn
            while top > mark:
                top -= 1
                assert top >= 0
                app = spine[top]
                spine[top] = None
                arg = app.arg
                if arg.loose_bvar_range() <= depth:
                    ac = arg._cache
                    if (ac >> 32) == sgen:
                        arg_h = ac & _TABLE_SLOT_MASK
                    elif arg.__class__ is W_BVar:
                        assert isinstance(arg, W_BVar)
                        bid = arg.id
                        if 0 <= bid < _BVAR_ARR_LEN:
                            arg_h = self._bvar_arr[bid]
                            if arg_h == 0:
                                arg_h = self._new_leaf(arg)
                                self._bvar_arr[bid] = arg_h
                                if bid + 1 > self._bvar_max:
                                    self._bvar_max = bid + 1
                        else:
                            arg_h = self.leaf_for(arg)
                    else:
                        self._import_spine_len = top
                        arg_h = self._import_rec(arg, sgen, nr)
                elif arg.__class__ is W_BVar:
                    assert isinstance(arg, W_BVar)
                    rel = arg.id - depth
                    arg_h = fvars[nf - 1 - rel] if rel < nf else self.bvar(arg.id - nf)
                elif dgen > 0 and (arg._cache >> 32) == dgen:
                    arg_h = arg._cache & _TABLE_SLOT_MASK
                else:
                    self._import_spine_len = top
                    arg_h = self._import_fvars_rec(arg, fvars, nf, depth, dgen, nr)
                head = self.cons_app(head, arg_h)
                if dgen > 0:
                    if (self._fvar_base_gen > 0
                            and (app._cache >> 32) >= self._fvar_base_gen
                            and (app._cache >> 32) != dgen):
                        self._fvar_cache_put(app, depth, dgen, head)
                    else:
                        app._cache = (dgen << 32) | head
            self._import_spine_len = mark
            return head
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(e, W_Lambda) or isinstance(e, W_ForAll)
            binder = e.binder
            btype = binder.type
            if btype.loose_bvar_range() <= depth:
                tc = btype._cache
                type_h = (
                    tc & _TABLE_SLOT_MASK
                    if (tc >> 32) == sgen
                    else self._import_rec(btype, sgen, nr)
                )
            else:
                type_h = self._import_fvars_rec(btype, fvars, nf, depth, dgen, nr)
            ebody = e.body
            ndepth = depth + 1
            if ebody.loose_bvar_range() <= ndepth:
                bc = ebody._cache
                body_h = (
                    bc & _TABLE_SLOT_MASK
                    if (bc >> 32) == sgen
                    else self._import_rec(ebody, sgen, nr)
                )
            else:
                ndgen = self._fvar_gen_for_depth(ndepth)
                body_h = self._import_fvars_rec(ebody, fvars, nf, ndepth, ndgen, nr)
            if cls is W_Lambda:
                h = self.lam(binder, type_h, body_h)
            else:
                h = self.forall(binder, type_h, body_h)
        elif cls is W_Proj:
            assert isinstance(e, W_Proj)
            h = self.proj(
                e.struct_name, e.field_index,
                self._import_fvars_rec(e.struct_expr, fvars, nf, depth, dgen, nr),
            )
        elif cls is W_Let:
            assert isinstance(e, W_Let)
            et = e.type
            if et.loose_bvar_range() <= depth:
                tc = et._cache
                th = (
                    tc & _TABLE_SLOT_MASK
                    if (tc >> 32) == sgen
                    else self._import_rec(et, sgen, nr)
                )
            else:
                th = self._import_fvars_rec(et, fvars, nf, depth, dgen, nr)
            ev = e.value
            if ev.loose_bvar_range() <= depth:
                vc = ev._cache
                vh = (
                    vc & _TABLE_SLOT_MASK
                    if (vc >> 32) == sgen
                    else self._import_rec(ev, sgen, nr)
                )
            else:
                vh = self._import_fvars_rec(ev, fvars, nf, depth, dgen, nr)
            eb = e.body
            ndepth = depth + 1
            if eb.loose_bvar_range() <= ndepth:
                bc = eb._cache
                bh = (
                    bc & _TABLE_SLOT_MASK
                    if (bc >> 32) == sgen
                    else self._import_rec(eb, sgen, nr)
                )
            else:
                ndgen = self._fvar_gen_for_depth(ndepth)
                bh = self._import_fvars_rec(eb, fvars, nf, ndepth, ndgen, nr)
            h = self.let(e.name, th, vh, bh)
        else:
            return self.leaf_for(e)
        if dgen > 0:
            if (self._fvar_base_gen > 0
                    and (e._cache >> 32) >= self._fvar_base_gen
                    and (e._cache >> 32) != dgen):
                self._fvar_cache_put(e, depth, dgen, h)
            else:
                e._cache = (dgen << 32) | h
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
        # at the same universe params): reuse `_store_gen` directly.
        identity = True
        i = 0
        while i < n:
            cl = clevels[i]
            if not cl.has_param or cl is not params[i].as_level_param():
                identity = False
                break
            i += 1
        if identity:
            return self.import_term(target)
        if n == 1:
            p0 = params[0]
            l0 = clevels[0]
            slot = ((p0.hash() * 1000003) ^ l0.hash()) & _LGEN_MASK
            if self._lgen1_p[slot] is p0 and self._lgen1_l[slot] is l0:
                lgen = self._lgen1_g[slot]
            else:
                lgen = _next_cache_gen()
                if lgen > 0:
                    self._lgen1_p[slot] = p0
                    self._lgen1_l[slot] = l0
                    self._lgen1_g[slot] = lgen
                    self._lgen1_dirty = True
        elif n == 2:
            p0 = params[0]
            p1 = params[1]
            l0 = clevels[0]
            l1 = clevels[1]
            hh = ((p0.hash() * 1000003) ^ p1.hash()) * 1000003
            hh = ((hh ^ l0.hash()) * 1000003) ^ l1.hash()
            slot = hh & _LGEN_MASK
            if (self._lgen2_p0[slot] is p0
                    and self._lgen2_p1[slot] is p1
                    and self._lgen2_l0[slot] is l0
                    and self._lgen2_l1[slot] is l1):
                lgen = self._lgen2_g[slot]
            else:
                lgen = _next_cache_gen()
                if lgen > 0:
                    self._lgen2_p0[slot] = p0
                    self._lgen2_p1[slot] = p1
                    self._lgen2_l0[slot] = l0
                    self._lgen2_l1[slot] = l1
                    self._lgen2_g[slot] = lgen
                    self._lgen2_dirty = True
        else:
            hh = n
            i = 0
            while i < n:
                hh = ((hh * 1000003) ^ params[i].hash()) * 1000003 ^ clevels[i].hash()
                i += 1
            slot = hh & _LGEN_MASK
            cp = self._lgenN_p[slot]
            cl = self._lgenN_l[slot]
            hit = False
            if cp is not None and cl is not None and len(cp) == n:
                hit = True
                i = 0
                while i < n:
                    if cp[i] is not params[i] or cl[i] is not clevels[i]:
                        hit = False
                        break
                    i += 1
            if hit:
                lgen = self._lgenN_g[slot]
            else:
                lgen = _next_cache_gen()
                if lgen > 0:
                    self._lgenN_p[slot] = params
                    self._lgenN_l[slot] = clevels
                    self._lgenN_g[slot] = lgen
                    self._lgenN_dirty = True
        mark = self._import_spine_len
        try:
            return self._import_with_levels(target, params, clevels, lgen, 0)
        finally:
            if self._import_spine_len > mark:
                self._clear_import_spine(mark)

    def _import_with_levels(self, e, params, clevels, lgen, rdepth):
        sgen = self._store_gen
        if not e.has_level_param():
            c = e._cache
            if (c >> 32) == sgen:
                return c & _TABLE_SLOT_MASK
            return self._import_rec(e, sgen, rdepth)
        c = e._cache
        if (c >> 32) == lgen:
            return c & _TABLE_SLOT_MASK
        if (rdepth & 31) == 31:
            _check_stack_store("import_term")
        cls = e.__class__
        nr = rdepth + 1
        if cls is W_App:
            assert isinstance(e, W_App)
            fn = e.fn
            fn_h = 0
            if fn.has_level_param():
                fc = fn._cache
                if (fc >> 32) == lgen:
                    fn_h = fc & _TABLE_SLOT_MASK
                elif not isinstance(fn, W_App):
                    fn_h = self._import_with_levels(fn, params, clevels, lgen, nr)
            else:
                fc = fn._cache
                if (fc >> 32) == sgen:
                    fn_h = fc & _TABLE_SLOT_MASK
                else:
                    fn_h = self._import_rec(fn, sgen, nr)
            if fn_h != 0:
                arg = e.arg
                if arg.has_level_param():
                    ac = arg._cache
                    arg_h = (
                        ac & _TABLE_SLOT_MASK
                        if (ac >> 32) == lgen
                        else self._import_with_levels(arg, params, clevels, lgen, nr)
                    )
                else:
                    ac = arg._cache
                    if (ac >> 32) == sgen:
                        arg_h = ac & _TABLE_SLOT_MASK
                    elif arg.__class__ is W_BVar:
                        assert isinstance(arg, W_BVar)
                        bid = arg.id
                        if 0 <= bid < _BVAR_ARR_LEN:
                            arg_h = self._bvar_arr[bid]
                            if arg_h == 0:
                                arg_h = self._new_leaf(arg)
                                self._bvar_arr[bid] = arg_h
                                if bid + 1 > self._bvar_max:
                                    self._bvar_max = bid + 1
                        else:
                            arg_h = self.leaf_for(arg)
                    else:
                        arg_h = self._import_rec(arg, sgen, nr)
                head = self.cons_app(fn_h, arg_h)
                if lgen > 0:
                    e._cache = (lgen << 32) | head
                return head
            spine = self._import_spine
            mark = self._import_spine_len
            top = mark
            assert top >= 0
            if top < len(spine):
                spine[top] = e
            else:
                spine.append(e)
            top += 1
            cur = fn
            head = 0
            while True:
                if not cur.has_level_param():
                    self._import_spine_len = top
                    cc = cur._cache
                    head = (
                        cc & _TABLE_SLOT_MASK
                        if (cc >> 32) == sgen
                        else self._import_rec(cur, sgen, nr)
                    )
                    break
                if not isinstance(cur, W_App):
                    self._import_spine_len = top
                    cc = cur._cache
                    head = (
                        cc & _TABLE_SLOT_MASK
                        if (cc >> 32) == lgen
                        else self._import_with_levels(
                            cur, params, clevels, lgen, nr,
                        )
                    )
                    break
                cc = cur._cache
                if (cc >> 32) == lgen:
                    head = cc & _TABLE_SLOT_MASK
                    break
                assert top >= 0
                if top < len(spine):
                    spine[top] = cur
                else:
                    spine.append(cur)
                top += 1
                cur = cur.fn
            while top > mark:
                top -= 1
                assert top >= 0
                app = spine[top]
                spine[top] = None
                arg = app.arg
                if arg.has_level_param():
                    ac = arg._cache
                    if (ac >> 32) == lgen:
                        arg_h = ac & _TABLE_SLOT_MASK
                    else:
                        self._import_spine_len = top
                        arg_h = self._import_with_levels(
                            arg, params, clevels, lgen, nr,
                        )
                else:
                    ac = arg._cache
                    if (ac >> 32) == sgen:
                        arg_h = ac & _TABLE_SLOT_MASK
                    elif arg.__class__ is W_BVar:
                        assert isinstance(arg, W_BVar)
                        bid = arg.id
                        if 0 <= bid < _BVAR_ARR_LEN:
                            arg_h = self._bvar_arr[bid]
                            if arg_h == 0:
                                arg_h = self._new_leaf(arg)
                                self._bvar_arr[bid] = arg_h
                                if bid + 1 > self._bvar_max:
                                    self._bvar_max = bid + 1
                        else:
                            arg_h = self.leaf_for(arg)
                    else:
                        self._import_spine_len = top
                        arg_h = self._import_rec(arg, sgen, nr)
                head = self.cons_app(head, arg_h)
                if lgen > 0:
                    app._cache = (lgen << 32) | head
            self._import_spine_len = mark
            return head
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(e, W_Lambda) or isinstance(e, W_ForAll)
            binder = e.binder
            btype = binder.type
            if btype.has_level_param():
                tc = btype._cache
                type_h = (
                    tc & _TABLE_SLOT_MASK
                    if (tc >> 32) == lgen
                    else self._import_with_levels(btype, params, clevels, lgen, nr)
                )
            else:
                tc = btype._cache
                type_h = (
                    tc & _TABLE_SLOT_MASK
                    if (tc >> 32) == sgen
                    else self._import_rec(btype, sgen, nr)
                )
            ebody = e.body
            if ebody.has_level_param():
                bc = ebody._cache
                body_h = (
                    bc & _TABLE_SLOT_MASK
                    if (bc >> 32) == lgen
                    else self._import_with_levels(ebody, params, clevels, lgen, nr)
                )
            else:
                bc = ebody._cache
                body_h = (
                    bc & _TABLE_SLOT_MASK
                    if (bc >> 32) == sgen
                    else self._import_rec(ebody, sgen, nr)
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
                    e.struct_expr, params, clevels, lgen, nr,
                ),
            )
        elif cls is W_Let:
            assert isinstance(e, W_Let)
            h = self.let(
                e.name,
                self._import_with_levels(e.type, params, clevels, lgen, nr),
                self._import_with_levels(e.value, params, clevels, lgen, nr),
                self._import_with_levels(e.body, params, clevels, lgen, nr),
            )
        elif cls is W_Const:
            assert isinstance(e, W_Const)
            lvls = e.levels
            nlvls = len(lvls)
            h = 0
            leaf_e = e
            if nlvls == 1:
                l0 = lvls[0]
                if l0.has_param:
                    if l0.__class__ is W_LevelParam and len(params) == 1:
                        assert isinstance(l0, W_LevelParam)
                        nl0 = clevels[0] if l0.name is params[0] else l0
                    else:
                        nl0 = _subst_level_fast(l0, params, clevels)
                    if nl0 is not l0:
                        h = self._const_leaf1(e.name, nl0)
            elif nlvls == 2:
                l0 = lvls[0]
                l1 = lvls[1]
                nl0 = _subst_level_fast(l0, params, clevels) if l0.has_param else l0
                nl1 = _subst_level_fast(l1, params, clevels) if l1.has_param else l1
                if nl0 is not l0 or nl1 is not l1:
                    h = self._const_leaf2(e.name, nl0, nl1)
            elif nlvls > 2:
                new_lvls = None
                i = 0
                while i < nlvls:
                    lvl = lvls[i]
                    nl = _subst_level_fast(lvl, params, clevels)
                    if nl is not lvl:
                        if new_lvls is None:
                            new_lvls = list(lvls)
                        new_lvls[i] = nl
                    i += 1
                if new_lvls is not None:
                    leaf_e = e.name.const(new_lvls)
            if h == 0:
                lc = leaf_e._cache
                if (lc >> 32) == sgen:
                    h = lc & _TABLE_SLOT_MASK
                else:
                    h = self.leaf_for(leaf_e)
        elif cls is W_Sort:
            assert isinstance(e, W_Sort)
            leaf_e = e
            lvl = e.level
            if lvl.has_param:
                if lvl.__class__ is W_LevelParam and len(params) == 1:
                    assert isinstance(lvl, W_LevelParam)
                    nl = clevels[0] if lvl.name is params[0] else lvl
                else:
                    nl = _subst_level_fast(lvl, params, clevels)
                if nl is not lvl:
                    leaf_e = nl.sort()
            lc = leaf_e._cache
            if (lc >> 32) == sgen:
                h = lc & _TABLE_SLOT_MASK
            else:
                h = self.leaf_for(leaf_e)
        else:
            h = self.leaf_for(e)
        if lgen > 0:
            e._cache = (lgen << 32) | h
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
        'tc', 'store', '_rule_memo', '_fvars', '_top_fvars',
        '_open_memo', '_decl_start_recs',
        '_eqv_count', '_neq', '_failed',
        '_ld_h1', '_ld_h2', '_proj_rem',
        '_def_eq_hooked', '_stack_tick', '_fvar_reused',
        'check_gen', '_last_env', '_is_clean', 'recheck_on_error',
        '_warm_max_index', '_warm_levels', '_warm_safe_cohort',
        '_can_perm', '_saw_nonperm',
        '_proj_field_cache', '_proj_fidxs', '_proj_fidx_top', '_proj_popped',
        'h_prop', 'h_true', 'h_false', 'h_nat', 'h_nat_zero', 'h_string',
    ]

    _LAZY_DELTA_MAX_ITER = 100000

    def __init__(self, tc):
        self.tc = tc
        self.store = TermStore(tc)
        #: (heavy open record, context chain and mode) -> its type there
        self._open_memo = PairMap(1 << 8)
        self._open_memo.limit = _MEMO_LIMIT
        self._decl_start_recs = 0
        #: (rec const leaf index, ctor leaf index) -> rule rhs handle
        self._rule_memo = IntMap(1 << 8, keep_cap=1 << 12)
        #: (const leaf index, depth, fidx chain) -> imported raw field handle
        self._proj_field_cache = IntMap(1 << 8, keep_cap=1 << 12)
        #: Re-entrant stack of pending projection field indices for `try_proj`.
        self._proj_fidxs = [0] * 32
        self._proj_fidx_top = 0
        self._proj_popped = 0
        #: (binder record, domain) -> the free-variable leaf opening it
        self._fvars = IntMap(1 << 8, keep_cap=1 << 13)
        #: (top-level telescope idx + 1, domain) -> canonical FVar leaf
        self._top_fvars = IntMap(1 << 8, keep_cap=1 << 12)
        #: number of union-find merges recorded in `store.memos[M_EQV]`/`leaf_eqv`
        self._eqv_count = 0
        #: pairs proven NOT def-eq (packed symmetric keys, 8 B/slot, capped at 32 MiB)
        self._neq = IntSet(1 << 10, limit=1 << 22)
        #: pairs whose same-head argument comparison failed (symmetric, 8 B/slot)
        self._failed = IntSet(1 << 8, limit=1 << 22)
        #: Out-slots for `_try_lazy_delta` and `_proj_lazy_eq` (zero-tuple return)
        self._ld_h1 = 0
        self._ld_h2 = 0
        self._proj_rem = 0
        self._def_eq_hooked = tc.def_eq_hooked
        self._stack_tick = 0
        self._fvar_reused = False
        #: Generation tag for `check=True` memos so warm cross-declaration
        #: caches re-verify reference ordering, safety, and universe params
        #: on every declaration while reusing pure whnf/infer/def_eq memos.
        self.check_gen = 1
        self._last_env = tc.env
        self._is_clean = True
        self.recheck_on_error = False
        self._warm_max_index = -1
        self._warm_levels = None
        self._warm_safe_cohort = False
        self._can_perm = False
        self._saw_nonperm = False
        self._forget()

    @dont_inline
    def _check_stack_slow(self, label):
        if stack_almost_full():
            raise W_DeepRecursion(label)

    def is_warm_ready(self):
        """Whether this machine is small enough to stay warm for another
        declaration without growing unboundedly."""
        store = self.store
        return (
            store.nrecs < _WARM_MAX_RECS
            and store.nleaves < _WARM_MAX_LEAVES
            and self._eqv_count < _WARM_MAX_EQV
            and self._neq.size < _WARM_MAX_NEQ
            and self._failed.size < _WARM_MAX_FAILED
            and self.check_gen < 0x70000000
        )

    def _forget(self):
        """Start over on everything the garbage collector looks after."""
        store = self.store
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
                self._eqv_count, self._neq.size, self._failed.size,
            )

    def reset(self):
        """Empty the machine for another declaration, keeping its memory."""
        self.store.reset()
        self.store.record_nodes = True
        self._rule_memo.clear()
        self._proj_field_cache.clear()
        self._proj_fidx_top = 0
        self._fvars.clear()
        self._top_fvars.clear()
        self._eqv_count = 0
        self._neq.clear()
        self._failed.clear()
        self._open_memo.clear()
        self._decl_start_recs = 0
        self.check_gen = 1
        self._is_clean = True
        self.recheck_on_error = False
        self._warm_max_index = -1
        self._warm_levels = None
        self._warm_safe_cohort = False
        self._can_perm = False
        self._saw_nonperm = False
        self._forget()

    def free(self):
        self.store.free()
        self._rule_memo.free()
        self._proj_field_cache.free()
        self._fvars.free()
        self._top_fvars.free()
        self._neq.free()
        self._failed.free()
        self._open_memo.free()

    def _decl(self, const):
        return find_decl(self.tc.declarations, const.name)

    def _leaf_decl(self, head, const):
        j = leaf_index(head)
        decl = self.store.leaf_decl[j]
        if decl is not None:
            return decl
        decl = find_decl(self.tc.declarations, const.name)
        if decl is not None:
            self.store.leaf_decl[j] = decl
        return decl

    def _leaf_flags(self, h):
        if not is_leaf(h):
            return _LF_CLASSIFIED
        j = leaf_index(h)
        f = _s32(self.store.leaf_head_kind[j])
        if f != 0:
            return f
        return self._classify_const_leaf(h, j)

    def _prop_mask_for(self, head):
        """Bitmask of argument positions (0..61) of ``head`` whose domain
        lives in ``Prop`` (and can therefore be skipped by proof irrelevance
        during same-head application comparison once all earlier arguments
        agree). Only active while checking a declaration (when both sides of
        every `def_eq` are guaranteed well-typed) and when trace writing is
        off."""
        if not is_leaf(head) or self.tc.decl is None:
            return 0
        tracer = self.tc.tracer
        if tracer.recording and tracer.writes:
            return 0
        j = leaf_index(head)
        m = self.store.leaf_prop_mask[j]
        if m != 0:
            return m
        return self._compute_prop_mask(head, j)

    @dont_inline
    def _compute_prop_mask(self, head, j):
        store = self.store
        # Store the done sentinel before walking `ty` so any re-entrant call
        # for the same head sees mask 0 and terminates soundly.
        store.leaf_prop_mask[j] = _PROP_MASK_DONE
        e = store.leaves[j]
        decl = None
        if isinstance(e, W_Const):
            decl = self._leaf_decl(head, e)
            if decl is None or len(e.levels) != len(decl.levels):
                return _PROP_MASK_DONE
            dm = decl._prop_mask
            if dm == 0:
                dm = decl.init_prop_mask(self.tc.declarations)
            if dm > 0:
                store.leaf_prop_mask[j] = dm
                return dm
            if dm <= -2:
                res = _PROP_MASK_PLANS[(-dm) - 2].eval(decl.levels, e.levels)
                store.leaf_prop_mask[j] = res
                return res
        elif isinstance(e, W_FVar):
            if _s32(store.leaf_infer[j]) == 0:
                return _PROP_MASK_DONE
        else:
            return _PROP_MASK_DONE
        ty = self.infer(head, False)
        mask = 0
        fvars = []
        k = 0
        while k < 62:
            if store.kind(ty) != KIND_FORALL:
                nf = len(fvars)
                if nf > 0:
                    if store.loose_bvar_range(ty) > 0:
                        ty = store.instantiate_multi_rev(ty, fvars, nf, 0)
                    fvars = []
                ty = self.whnf(ty)
                if store.kind(ty) != KIND_FORALL:
                    break
            dom = store.field_a(ty)
            nf = len(fvars)
            if nf > 0 and store.loose_bvar_range(dom) > 0:
                dom = store.instantiate_multi_rev(dom, fvars, nf, 0)
            if store.sort_leaf(dom) is None:
                s = self.infer(dom, False)
                if s != self.h_prop and store.sort_leaf(s) is None:
                    s = self.whnf(s)
                if s == self.h_prop:
                    mask |= (1 << k)
            body = store.field_b(ty)
            if store.loose_bvar_range(body) == 0:
                fvars = []
            else:
                fvars.append(self.fvar_for_domain(ty, dom))
            ty = body
            k += 1
        res = _PROP_MASK_DONE | mask
        store.leaf_prop_mask[j] = res
        if decl is not None and len(decl.levels) == 0:
            decl._prop_mask = res
        return res

    @dont_inline
    def _classify_const_leaf(self, h, j):
        const = self.store.leaves[j]
        assert isinstance(const, W_Const)
        name = const.name
        flags = 0
        if name.syntactic_eq(W_App._QUOT_LIFT):
            flags |= _LF_QUOT_LIFT
        elif name.syntactic_eq(_NAT_SUCC_NAME):
            flags |= _LF_NAT_SUCC
        elif name.syntactic_eq(NAT_ZERO.name):
            flags |= _LF_NAT_ZERO
        elif is_nat_binop(name):
            flags |= _LF_NAT_BINOP
        elif name.syntactic_eq(_ITE_NAME) or name.syntactic_eq(_DITE_NAME):
            flags |= (_LF_ITE | _LF_BOOL_ARG0)
        elif (name.syntactic_eq(_BOOL_AND_NAME)
              or name.syntactic_eq(_BOOL_OR_NAME)
              or name.syntactic_eq(_AND_NAME)
              or name.syntactic_eq(_OR_NAME)):
            flags |= (_LF_SHORT_BOOL | _LF_BOOL_ARG0)
        elif name.syntactic_eq(_BOOL_NOT_NAME) or name.syntactic_eq(_COND_NAME):
            flags |= _LF_BOOL_ARG0
        decl = self._leaf_decl(h, const)
        if decl is not None:
            flags |= _LF_CLASSIFIED
            dk = decl.w_kind
            if isinstance(dk, W_Recursor):
                flags |= _LF_RECURSOR
            elif isinstance(dk, W_Constructor):
                flags |= _LF_CTOR
            elif isinstance(dk, W_Definition):
                if dk.get_delta_reduce_target() is not None:
                    flags |= _LF_DELTA
                    henc = dk.hint + 2
                    if henc < 0 or henc >= _LF_HINT_OVF:
                        henc = _LF_HINT_OVF
                    flags |= (henc << _LF_HINT_SHIFT)
            self.store.leaf_head_kind[j] = _u32(flags)
        return flags

    @dont_inline
    def _delta_hint_slow(self, head):
        decl = self.store.leaf_decl[leaf_index(head)]
        assert decl is not None
        dk = decl.w_kind
        assert isinstance(dk, W_Definition)
        return dk.hint

    def export(self, h):
        return self.store.export_term(h)

    # ---- whnf ------------------------------------------------------------

    @dont_inline
    def _trace_whnf_leaf(self, h):
        tc = self.tc
        if tc.tracer.writes:
            tc.tracer.whnf_step(self.export(h), tc.declarations)
        return h

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
        if is_leaf(h):
            if traced and self._def_eq_hooked:
                return self._trace_whnf_leaf(h)
            return h
        store = self.store
        slot = M_WHNF_CORE_CHEAP if cheap_proj else M_WHNF_CORE
        memos = store.memos
        mbase = rec_index(h) * MEMO_SLOTS
        cached = _s32(memos[mbase + slot])
        if cached != 0:
            if (cached & _UNFOLD_TAG) != 0:
                return h
            return cached
        # A term already known to be in full WHNF is whnf_core-normal
        # either way, and a full whnf_core result is a cheap one too.
        if _s32(memos[mbase + M_WHNF]) == h:
            return h
        if cheap_proj:
            if _s32(memos[mbase + M_WHNF_CORE]) == h:
                return h
        elif (_s32(memos[mbase + M_WHNF_CORE_CHEAP]) & _UNFOLD_TAG) != 0:
            return h
        return self._whnf_core_miss(h, cheap_proj, traced, slot)

    @dont_inline
    def _whnf_core_miss(self, h, cheap_proj, traced, slot):
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("whnf_core")
        store = self.store
        tc = self.tc
        tracer = tc.tracer
        writes = traced and tracer.recording and tracer.writes
        start = h
        while True:
            if tc.has_limits:
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
                    if (cached & _UNFOLD_TAG) != 0:
                        break
                    h = cached
                    break
        store.set_memo(start, slot, h)
        return h

    def _beta_spine_buf(self, head, mark, n):
        """Multi-arg beta-reduce a leading `KIND_LAMBDA` telescope ``head``
        applied to `_spine_buf[mark .. mark + n)` (outermost-first) in a single
        substitution pass without allocating argument lists."""
        store = self.store
        k = 0
        body = head
        while k < n and store.kind(body) == KIND_LAMBDA:
            body = store.field_b(body)
            k += 1
        if k == 0:
            return store.apply_buf_rev(body, mark, n - 1)
        if self.tc.tracer.recording:
            j = 0
            while j < k:
                self.tc.tracer.beta()
                j += 1
        if store.loose_bvar_range(body) == 0:
            res = body
        elif is_leaf(body):
            bid = (_s32(store.leaf_meta[leaf_index(body)]) >> 1) - 1
            if bid < k:
                res = store.spine_arg(mark + n - k + bid)
            else:
                res = store.bvar(bid - k)
        elif k == 1:
            res = store.instantiate(body, store.spine_arg(mark + n - 1), 0)
        else:
            res = store.instantiate_multi_buf(body, mark + n - k, k, 0)
        return store.apply_buf_rev(res, mark, n - 1 - k)

    def _whnf_core_step(self, h, cheap_proj):
        """One whnf_core step of ``h``, or 0 when there is none."""
        if is_leaf(h):
            return 0
        store = self.store
        recs = store.recs
        base = rec_index(h) << 2
        kind = _s32(recs[base]) & _KIND_MASK
        if kind == KIND_APP:
            fn = _s32(recs[base + F_A])
            if (fn & 1) == 0:
                fbase = rec_index(fn) << 2
                fk = _s32(recs[fbase]) & _KIND_MASK
                if fk == KIND_LAMBDA:
                    if self.tc.tracer.recording:
                        self.tc.tracer.beta()
                    return store.instantiate(
                        _s32(recs[fbase + F_B]), _s32(recs[base + F_B]), 0,
                    )
                if fk == KIND_APP:
                    head = _s32(recs[fbase + F_A])
                    while (head & 1) == 0:
                        hbase = rec_index(head) << 2
                        if (_s32(recs[hbase]) & _KIND_MASK) != KIND_APP:
                            break
                        head = _s32(recs[hbase + F_A])
                else:
                    head = fn
            else:
                head = fn
            if (head & 1) != 0:
                flags = self._leaf_flags(head)
                if (flags & (_LF_RECURSOR | _LF_QUOT_LIFT)) == 0:
                    return 0
                if (flags & _LF_RECURSOR) != 0:
                    j = leaf_index(head)
                    const = store.leaves[j]
                    assert isinstance(const, W_Const)
                    decl = store.leaf_decl[j]
                    assert decl is not None
                    dkind = decl.w_kind
                    assert isinstance(dkind, W_Recursor)
                    mark = store._spine_top
                    store.unapp_push(h)
                    try:
                        return self._try_iota_spine(
                            h, head, const, decl, dkind, mark, store._spine_top - mark,
                        )
                    finally:
                        store.unapp_pop(mark)
                mark = store._spine_top
                store.unapp_push(h)
                try:
                    return self._try_quot_lift_spine(mark, store._spine_top - mark)
                finally:
                    store.unapp_pop(mark)
            hk = _s32(recs[rec_index(head) << 2]) & _KIND_MASK
            if hk == KIND_LAMBDA:
                mark = store._spine_top
                store.unapp_push(h)
                try:
                    return self._beta_spine_buf(head, mark, store._spine_top - mark)
                finally:
                    store.unapp_pop(mark)
            if hk == KIND_PROJ or hk == KIND_LET:
                head_w = self.whnf_core(head, cheap_proj, False)
                if head_w == head:
                    return 0
                mark = store._spine_top
                store.unapp_push(h)
                try:
                    n = store._spine_top - mark
                    if (store.kind(head_w) == KIND_LAMBDA
                            and not (self.tc.tracer.recording
                                     and self.tc.tracer.writes)):
                        return self._beta_spine_buf(head_w, mark, n)
                    return store.apply_buf_rev(head_w, mark, n - 1)
                finally:
                    store.unapp_pop(mark)
            return 0
        if kind == KIND_LET:
            pair = _s32(recs[base + F_B])
            return store.instantiate(store.field_b(pair), store.field_a(pair), 0)
        if kind == KIND_PROJ:
            return self.try_proj(h, cheap_proj)
        return 0

    def whnf(self, h):
        """Weak head normal form, unfolding definitions as needed."""
        store = self.store
        if is_leaf(h):
            cached = _s32(store.leaf_whnf[leaf_index(h)])
        else:
            cached = store.memo(h, M_WHNF)
        if cached != 0:
            return cached
        return self._whnf_miss(h)

    @dont_inline
    def _whnf_miss(self, h):
        store = self.store
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
            store.leaf_whnf[leaf_index(start)] = _u32(h)
        else:
            store.set_memo(start, M_WHNF, h)
        return h

    def _apply_stripped_body(self, body, k, mark, n):
        """Substitute ``k`` already-stripped leading lambdas (plus any further
        leading `KIND_LAMBDA`s on ``body`` up to ``n``) with `_spine_buf[mark .. mark + n)`
        (outermost-first) and apply any leftover arguments."""
        store = self.store
        while k < n and store.kind(body) == KIND_LAMBDA:
            body = store.field_b(body)
            k += 1
        if k == 0:
            return store.apply_buf_rev(body, mark, n - 1)
        if self.tc.tracer.recording:
            j = 0
            while j < k:
                self.tc.tracer.beta()
                j += 1
        if store.loose_bvar_range(body) == 0:
            res = body
        elif is_leaf(body):
            bid = (_s32(store.leaf_meta[leaf_index(body)]) >> 1) - 1
            if bid < k:
                res = store.spine_arg(mark + n - k + bid)
            else:
                res = store.bvar(bid - k)
        elif k == 1:
            res = store.instantiate(body, store.spine_arg(mark + n - 1), 0)
        else:
            res = store.instantiate_multi_buf(body, mark + n - k, k, 0)
        return store.apply_buf_rev(res, mark, n - 1 - k)

    def try_unfold_head(self, h):
        """``h`` with its head constant unfolded one definition layer and
        the spine re-applied (beta-reducing leading lambdas when not writing
        traces), or 0 when the head isn't unfoldable."""
        store = self.store
        if not is_leaf(h):
            ri = rec_index(h)
            if (_s32(store.recs[ri << 2]) & _KIND_MASK) != KIND_APP:
                return 0
            if not self.tc.tracer.recording:
                cached = _s32(store.memos[ri * MEMO_SLOTS + M_WHNF_CORE_CHEAP])
                if (cached & _UNFOLD_TAG) != 0:
                    return cached & _UNFOLD_MASK
            res = self._try_unfold_app_miss(h)
            if res != 0 and not self.tc.tracer.recording:
                store.memos[ri * MEMO_SLOTS + M_WHNF_CORE_CHEAP] = _u32(
                    res | _UNFOLD_TAG,
                )
            return res
        if (self._leaf_flags(h) & _LF_DELTA) == 0:
            return 0
        const = store.leaves[leaf_index(h)]
        assert isinstance(const, W_Const)
        return self._delta_value(h, const)

    @dont_inline
    def _try_unfold_app_miss(self, h):
        store = self.store
        head = store.head(h)
        if (self._leaf_flags(head) & _LF_DELTA) == 0:
            return 0
        j = leaf_index(head)
        const = store.leaves[j]
        assert isinstance(const, W_Const)
        if self.tc.tracer.recording and self.tc.tracer.writes:
            val = self._delta_value(head, const)
            if val == 0:
                return 0
            if store.field_a(h) == head:
                return store.cons_app(val, store.field_b(h))
            mark = store._spine_top
            store.unapp_push(h)
            try:
                return store.apply_buf_rev(val, mark, store._spine_top - mark - 1)
            finally:
                store.unapp_pop(mark)
        packed = store.leaf_delta_body[j]
        if packed == 0:
            packed = self._delta_body(head, const, j)
        if packed < 0:
            return 0
        tag = packed >> _DB_TAG_SHIFT
        if tag != 0:
            return self._unfold_fast(h, head, const, packed, tag)
        m = packed >> 32
        body_h = packed & 0xFFFFFFFF
        if store.field_a(h) == head:
            if m == 0:
                return store.cons_app(body_h, store.field_b(h))
            if m == 1:
                if self.tc.tracer.recording:
                    self.tc.tracer.beta()
                return store.instantiate(body_h, store.field_b(h), 0)
            val = self._delta_value(head, const)
            if val == 0:
                return 0
            if self.tc.tracer.recording:
                self.tc.tracer.beta()
            return store.instantiate(store.field_b(val), store.field_b(h), 0)
        mark = store._spine_top
        store.unapp_push(h)
        try:
            n = store._spine_top - mark
            if n >= m:
                return self._apply_stripped_body(body_h, m, mark, n)
            val = self._delta_value(head, const)
            if val == 0:
                return 0
            return self._beta_spine_buf(val, mark, n)
        finally:
            store.unapp_pop(mark)

    def _unfold_fast(self, h, head, const, packed, tag):
        """Direct delta unfold for argument-picker (`λ... => BVar(b)`) and
        structure-projection (`λ... => Proj(S, idx, BVar(b))`) definitions,
        bypassing `import_const_term` and `instantiate`."""
        store = self.store
        if tag == 1:
            m = (packed >> 32) & 0xFFFFFFF
            b = packed & 0xFFFFFFFF
            fn = store.field_a(h)
            if m == 2 and store.kind(fn) == KIND_APP and store.field_a(fn) == head:
                if self.tc.tracer.recording:
                    self.tc.tracer.beta()
                    self.tc.tracer.beta()
                return store.field_b(h) if b == 0 else store.field_b(fn)
            if m == 1 and fn == head:
                if self.tc.tracer.recording:
                    self.tc.tracer.beta()
                return store.field_b(h)
            mark = store._spine_top
            store.unapp_push(h)
            try:
                n = store._spine_top - mark
                if n >= m:
                    if self.tc.tracer.recording:
                        k = 0
                        while k < m:
                            self.tc.tracer.beta()
                            k += 1
                    res = store.spine_arg(mark + n - m + b)
                    if n > m and store.kind(res) == KIND_LAMBDA:
                        return self._beta_spine_buf(res, mark, n - m)
                    return store.apply_buf_rev(res, mark, n - 1 - m)
                val = self._delta_value(head, const)
                if val == 0:
                    return 0
                return self._beta_spine_buf(val, mark, n)
            finally:
                store.unapp_pop(mark)
        # tag == 2: structure/typeclass projection `λ... => Proj(S, idx, BVar(b))`
        m = (packed >> 52) & 0xFF
        b = (packed >> 44) & 0xFF
        name_id = (packed >> 24) & 0xFFFFF
        proj_packed = packed & 0xFFFFFF
        fn = store.field_a(h)
        if m == 2 and store.kind(fn) == KIND_APP and store.field_a(fn) == head:
            if self.tc.tracer.recording:
                self.tc.tracer.beta()
                self.tc.tracer.beta()
            arg = store.field_b(h) if b == 0 else store.field_b(fn)
            return store._cons_general(KIND_PROJ, arg, proj_packed, name_id)
        if m == 1 and fn == head:
            if self.tc.tracer.recording:
                self.tc.tracer.beta()
            return store._cons_general(KIND_PROJ, store.field_b(h), proj_packed, name_id)
        mark = store._spine_top
        store.unapp_push(h)
        try:
            n = store._spine_top - mark
            if n >= m:
                if self.tc.tracer.recording:
                    k = 0
                    while k < m:
                        self.tc.tracer.beta()
                        k += 1
                arg = store.spine_arg(mark + n - m + b)
                res = store._cons_general(KIND_PROJ, arg, proj_packed, name_id)
                return store.apply_buf_rev(res, mark, n - 1 - m)
            val = self._delta_value(head, const)
            if val == 0:
                return 0
            return self._beta_spine_buf(val, mark, n)
        finally:
            store.unapp_pop(mark)

    @dont_inline
    def _delta_body(self, head, const, j):
        """Peel leading `W_Lambda` binders from a definition's value before
        importing so fully-applied delta unfolds never import discarded binder
        domain types, and encode argument-picker / projection wrappers directly."""
        store = self.store
        cached_val = _si32(store.leaf_delta[j])
        if cached_val > 0:
            m = 0
            cur_h = cached_val
            while store.kind(cur_h) == KIND_LAMBDA:
                cur_h = store.field_b(cur_h)
                m += 1
            packed = (m << 32) | cur_h
            store.leaf_delta_body[j] = packed
            return packed
        decl = self._leaf_decl(head, const)
        if decl is None or not isinstance(decl.w_kind, W_Definition):
            store.leaf_delta_body[j] = -1
            return -1
        target = decl.w_kind.get_delta_reduce_target()
        if target is None:
            store.leaf_delta_body[j] = -1
            return -1
        if self.tc.tracer.recording:
            self.tc.tracer.delta(const.name)
        m = 0
        cur = target
        while isinstance(cur, W_Lambda):
            cur = cur.body
            m += 1
        if m > 0:
            if isinstance(cur, W_BVar):
                bid = cur.id
                if 0 <= bid < m and m < (1 << 28):
                    packed = _DB_BVAR_TAG | (m << 32) | bid
                    store.leaf_delta_body[j] = packed
                    return packed
            elif isinstance(cur, W_Proj) and m < 256:
                inner = cur.struct_expr
                if isinstance(inner, W_BVar):
                    bid = inner.id
                    if 0 <= bid < m:
                        name_id = store._name_index(cur.struct_name)
                        proj_packed = store._proj_pack(name_id, cur.field_index)
                        if name_id < (1 << 20) and proj_packed < (1 << 24):
                            packed = (
                                _DB_PROJ_TAG
                                | (m << 52)
                                | (bid << 44)
                                | (name_id << 24)
                                | proj_packed
                            )
                            store.leaf_delta_body[j] = packed
                            return packed
        body_h = store.import_const_term(const, decl, cur)
        if m == 0:
            store.leaf_delta[j] = _i32(body_h)
        packed = (m << 32) | body_h
        store.leaf_delta_body[j] = packed
        return packed

    def _delta_kind(self, head):
        """The `W_Definition` a delta-reducible head names, or None."""
        if (self._leaf_flags(head) & _LF_DELTA) == 0:
            return None
        decl = self.store.leaf_decl[leaf_index(head)]
        assert decl is not None
        kind = decl.w_kind
        assert isinstance(kind, W_Definition)
        return kind

    def _delta_value(self, head, const):
        store = self.store
        j = leaf_index(head)
        cached = _si32(store.leaf_delta[j])
        if cached != 0:
            return cached if cached > 0 else 0
        decl = self._leaf_decl(head, const)
        val = 0
        if decl is not None and isinstance(decl.w_kind, W_Definition):
            target = decl.w_kind.get_delta_reduce_target()
            if target is not None:
                if self.tc.tracer.recording and store.leaf_delta_body[j] == 0:
                    self.tc.tracer.delta(const.name)
                val = store.import_const_term(const, decl, target)
        store.leaf_delta[j] = _i32(val if val > 0 else -1)
        return val

    def _whnf_nat_arg(self, arg):
        """Evaluate an argument of a native Nat binary op to WHNF, using the
        meta-traced evaluator for closed non-literal terms."""
        store = self.store
        if store.litnat_leaf(arg) is not None or arg == self.h_nat_zero:
            return arg
        if not self.tc.tracer.recording:
            if is_leaf(arg):
                cached = _s32(store.leaf_whnf[leaf_index(arg)])
                if cached != 0:
                    return cached
                if (self._leaf_flags(arg) & _LF_DELTA) != 0:
                    ev = eval_closed_scalar(self, arg)
                    if ev != 0:
                        store.leaf_whnf[leaf_index(arg)] = _u32(ev)
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
        if (self._leaf_flags(head) & _LF_NAT_BINOP) == 0:
            return 0
        const = store.leaves[leaf_index(head)]
        assert isinstance(const, W_Const)
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
            if is_leaf(h):
                if (self._leaf_flags(h) & _LF_NAT_ZERO) != 0:
                    return rbigint.fromint(succs)
                lit = store.litnat_leaf(h)
                if lit is not None:
                    return lit.val.add(rbigint.fromint(succs))
                return None
            if store.kind(h) == KIND_APP:
                if (self._leaf_flags(store.field_a(h)) & _LF_NAT_SUCC) != 0:
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
        if (self._leaf_flags(head) & _LF_NAT_BINOP) == 0:
            return 0
        const = store.leaves[leaf_index(head)]
        assert isinstance(const, W_Const)
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
            if is_leaf(h):
                if (self._leaf_flags(h) & _LF_NAT_ZERO) != 0:
                    return rbigint.fromint(succs)
                lit = store.litnat_leaf(h)
                if lit is not None:
                    return lit.val.add(rbigint.fromint(succs))
                return None
            if store.kind(h) == KIND_APP:
                if (self._leaf_flags(store.field_a(h)) & _LF_NAT_SUCC) != 0:
                    succs += 1
                    h = self.whnf(store.field_b(h))
                    continue
            return None

    def _is_nat_zero(self, h):
        if not is_leaf(h):
            return False
        if (self._leaf_flags(h) & _LF_NAT_ZERO) != 0:
            return True
        lit = self.store.litnat_leaf(h)
        if lit is not None:
            return lit.val.eq(rbigint.fromint(0))
        return False

    def _nat_succ_pred(self, h):
        """The predecessor of a syntactic `Nat.succ pred` / non-zero
        literal, or 0."""
        store = self.store
        if is_leaf(h):
            lit = store.litnat_leaf(h)
            if lit is not None:
                if lit.val.eq(rbigint.fromint(0)):
                    return 0
                return store.leaf_for(_mk_w_litnat(lit.val.sub(rbigint.fromint(1))))
            return 0
        if store.kind(h) == KIND_APP:
            if (self._leaf_flags(store.field_a(h)) & _LF_NAT_SUCC) != 0:
                return store.field_b(h)
        return 0

    def _peel_nested_ctor_field(self, raw_field, fidxs, pbase, ptop):
        """Follow pending outer projection indices `fidxs[pbase .. ptop - 1)`
        directly through inline nested `W_Constructor` applications (and
        `W_Definition` constructor-bodied applications whose projected field
        selects an argument `W_BVar`) on the AST, setting `self._proj_popped`
        to the total number of projection layers consumed (at least 1)."""
        popped = 1
        rem = ptop - 1
        decls = self.tc.declarations
        while rem > pbase and isinstance(raw_field, W_App):
            node = raw_field
            n_app = 0
            while isinstance(node, W_App):
                node = node.fn
                n_app += 1
            if not isinstance(node, W_Const):
                break
            c2_decl = find_decl(decls, node.name)
            if c2_decl is None:
                break
            c2_kind = c2_decl.w_kind
            if isinstance(c2_kind, W_Constructor):
                idx2 = c2_kind.num_params + fidxs[rem - 1]
                if idx2 >= n_app:
                    break
                steps = n_app - 1 - idx2
                cur_app = raw_field
                while steps > 0:
                    assert isinstance(cur_app, W_App)
                    cur_app = cur_app.fn
                    steps -= 1
                assert isinstance(cur_app, W_App)
                raw_field = cur_app.arg
                rem -= 1
                popped += 1
                continue
            if isinstance(c2_kind, W_Definition):
                if len(node.levels) != len(c2_decl.levels):
                    break
                cb2 = c2_kind._ctor_body
                if cb2 is None:
                    cb2 = c2_kind.init_ctor_body(decls)
                m2 = cb2.m
                if m2 < 0 or cb2.let_vals is not None or cb2.delegate_const is not None or n_app < m2:
                    break
                idx2 = cb2.num_params + fidxs[rem - 1]
                nargs2 = len(cb2.args)
                if idx2 >= nargs2 + (n_app - m2):
                    break
                if idx2 >= nargs2:
                    arg_idx = m2 + (idx2 - nargs2)
                    steps = n_app - 1 - arg_idx
                    cur_app = raw_field
                    while steps > 0:
                        assert isinstance(cur_app, W_App)
                        cur_app = cur_app.fn
                        steps -= 1
                    assert isinstance(cur_app, W_App)
                    raw_field = cur_app.arg
                    rem -= 1
                    popped += 1
                    continue
                f2 = cb2.args[idx2]
                r2 = rem - 1
                step2 = 1
                while r2 > pbase and isinstance(f2, W_App):
                    n2 = f2
                    na2 = 0
                    while isinstance(n2, W_App):
                        n2 = n2.fn
                        na2 += 1
                    if not isinstance(n2, W_Const):
                        break
                    d3 = find_decl(decls, n2.name)
                    if d3 is None:
                        break
                    k3 = d3.w_kind
                    if not isinstance(k3, W_Constructor):
                        break
                    ix3 = k3.num_params + fidxs[r2 - 1]
                    if ix3 >= na2:
                        break
                    st3 = na2 - 1 - ix3
                    ca3 = f2
                    while st3 > 0:
                        assert isinstance(ca3, W_App)
                        ca3 = ca3.fn
                        st3 -= 1
                    assert isinstance(ca3, W_App)
                    f2 = ca3.arg
                    r2 -= 1
                    step2 += 1
                if isinstance(f2, W_BVar):
                    bid2 = f2.id
                    if 0 <= bid2 < m2:
                        steps = n_app - m2 + bid2
                        cur_app = raw_field
                        while steps > 0:
                            assert isinstance(cur_app, W_App)
                            cur_app = cur_app.fn
                            steps -= 1
                        assert isinstance(cur_app, W_App)
                        raw_field = cur_app.arg
                        rem = r2
                        popped += step2
                        continue
            break
        self._proj_popped = popped
        return raw_field

    def _import_proj_field(self, j, popped, fidxs, ptop, const, decl, raw_field):
        """Import ``raw_field`` instantiated at ``const.levels``, memoized per
        `(const_leaf_index, projection_chain)` for the current store epoch."""
        key = 0
        if popped == 1:
            f0 = fidxs[ptop - 1]
            if 0 <= f0 < 1024:
                key = ((j + 1) << 22) | (1 << 20) | f0
        elif popped == 2:
            f0 = fidxs[ptop - 1]
            f1 = fidxs[ptop - 2]
            if 0 <= f0 < 1024 and 0 <= f1 < 1024:
                key = ((j + 1) << 22) | (2 << 20) | (f0 << 10) | f1
        elif popped == 3:
            f0 = fidxs[ptop - 1]
            f1 = fidxs[ptop - 2]
            f2 = fidxs[ptop - 3]
            if 0 <= f0 < 64 and 0 <= f1 < 64 and 0 <= f2 < 64:
                key = ((j + 1) << 22) | (3 << 20) | (f0 << 12) | (f1 << 6) | f2
        if key != 0:
            fh = self._proj_field_cache.get(key, 0)
            if fh != 0:
                return fh
        fh = self.store.import_const_term(const, decl, raw_field)
        if key != 0:
            self._proj_field_cache.set(key, fh)
        return fh

    def _extract_ctor_field(self, struct, head, fidx):
        """Extract field ``fidx`` from an already-materialized constructor
        application ``struct`` with head ``head``, or return 0."""
        store = self.store
        decl = store.leaf_decl[leaf_index(head)]
        assert decl is not None
        kind = decl.w_kind
        assert isinstance(kind, W_Constructor)
        mark = store._spine_top
        store.unapp_push(struct)
        try:
            n = store._spine_top - mark
            idx = kind.num_params + fidx
            if idx < n:
                return store.spine_arg(mark + n - 1 - idx)
            return 0
        finally:
            store.unapp_pop(mark)

    def _eval_raw_field(self, j, const, decl, cb, raw_idx, raw_field,
                        popped, arg_base, m, ptop):
        """Import and instantiate ``raw_field`` (originally ``cb.args[raw_idx]``,
        after ``popped`` projection peels) in ``cb``'s environment with ``m``
        lambda arguments at `_spine_buf[arg_base:arg_base+m]`."""
        store = self.store
        fidxs = self._proj_fidxs
        let_vals = cb.let_vals
        if let_vals is None:
            if isinstance(raw_field, W_BVar):
                bid = raw_field.id
                if 0 <= bid < m:
                    return store.spine_arg(arg_base + bid)
            fh = self._import_proj_field(
                j, popped, fidxs, ptop, const, decl, raw_field,
            )
            if m == 0 or store.loose_bvar_range(fh) == 0:
                return fh
            if m == 1:
                return store.instantiate(fh, store.spine_arg(arg_base), 0)
            return store.instantiate_multi_buf(fh, arg_base, m, 0)
        nlets = len(let_vals)
        if isinstance(raw_field, W_BVar):
            bid = raw_field.id
            if nlets <= bid < nlets + m:
                return store.spine_arg(arg_base + (bid - nlets))
        smark = store._spine_top
        total = nlets + m
        store.ensure_spine_room(total)
        buf = store._spine_buf
        k = 0
        while k < m:
            buf[smark + nlets + k] = buf[arg_base + k]
            k += 1
        uses = cb.uses_lets
        assert uses is not None
        uses_let = uses[raw_idx]
        if uses_let and popped > 1:
            uses_let = _expr_has_bvar_lt(raw_field, nlets, 0)
        store._spine_top = smark + total
        try:
            if not uses_let:
                li = 0
                while li < nlets:
                    store._spine_buf[smark + li] = _u32(self.h_prop)
                    li += 1
            else:
                li = 0
                while li < nlets:
                    vh = store.import_const_term(const, decl, let_vals[li])
                    cnt = li + m
                    if cnt > 0 and store.loose_bvar_range(vh) > 0:
                        if cnt == 1:
                            vh = store.instantiate(
                                vh, store.spine_arg(smark + nlets - li), 0,
                            )
                        else:
                            vh = store.instantiate_multi_buf(
                                vh, smark + nlets - li, cnt, 0,
                            )
                    store._spine_buf[smark + nlets - 1 - li] = _u32(vh)
                    li += 1
            fh = self._import_proj_field(
                j, popped, fidxs, ptop, const, decl, raw_field,
            )
            if total == 0 or store.loose_bvar_range(fh) == 0:
                return fh
            if is_leaf(fh):
                bid = (_s32(store.leaf_meta[leaf_index(fh)]) >> 1) - 1
                return (
                    store.spine_arg(smark + bid)
                    if bid < total
                    else store.bvar(bid - total)
                )
            if total == 1:
                return store.instantiate(fh, store.spine_arg(smark), 0)
            return store.instantiate_multi_buf(fh, smark, total, 0)
        finally:
            store.unapp_pop(smark)

    def _eval_direct_ctor_proj(self, j, const, decl, cb, arg_base, m, pbase, ptop):
        """Evaluate a direct `_CtorBody` (``cb.delegate_const is None``) with
        its ``m`` lambda arguments sitting at `_spine_buf[arg_base:arg_base+m]`."""
        fidxs = self._proj_fidxs
        fidx = fidxs[ptop - 1]
        idx = cb.num_params + fidx
        if idx >= len(cb.args):
            return 0
        raw_field = self._peel_nested_ctor_field(
            cb.args[idx], fidxs, pbase, ptop,
        )
        return self._eval_raw_field(
            j, const, decl, cb, idx, raw_field,
            self._proj_popped, arg_base, m, ptop,
        )

    def _eval_delegate_ctor_proj(self, j, const, decl, cb, arg_base, m, pbase, ptop):
        """Evaluate a delegating `_CtorBody` (`Outer := Inner a_0 ... a_{k-1}`):
        if ``Inner``'s field ``fidx`` selects a single BVar, jump directly to
        that AST argument and peel any pending outer projections through it;
        otherwise materialize ONLY the proper subset of ``Inner``'s arguments
        actually referenced by field ``fidx`` (returning 0 when all arguments
        are needed so normal DAG-shared unfolding wins)."""
        store = self.store
        fidxs = self._proj_fidxs
        fidx = fidxs[ptop - 1]
        inner_decl = cb.delegate_decl
        assert inner_decl is not None
        inner_kind = inner_decl.w_kind
        assert isinstance(inner_kind, W_Definition)
        inner_cb = inner_kind._ctor_body
        assert inner_cb is not None
        inner_m = inner_cb.m
        # Fast path: Inner selects a single lambda argument `BVar(ibid)` for
        # field `fidx` — peel pending outer projections directly on the AST
        # argument `cb.args[inner_m - 1 - ibid]` without materializing Inner!
        ibid = inner_cb.bvar_field(fidx)
        if ibid >= 0:
            arg_idx = inner_m - 1 - ibid
            raw_field = self._peel_nested_ctor_field(
                cb.args[arg_idx], fidxs, pbase, ptop,
            )
            return self._eval_raw_field(
                j, const, decl, cb, arg_idx, raw_field,
                self._proj_popped, arg_base, m, ptop,
            )
        inner_mask = inner_cb.field_mask(fidx)
        if inner_mask < 0:
            return 0
        # If every argument of Inner is needed (0 skipped), fall back so normal
        # unfolding does a single DAG-shared instantiation and caches `M_WHNF`.
        if inner_m <= 62 and inner_mask == ((1 << inner_m) - 1):
            return 0
        dkey = ((j + 1) << 22) | 1023
        inner_head = self._proj_field_cache.get(dkey, 0)
        if inner_head == 0:
            del_const = cb.delegate_const
            assert del_const is not None
            inner_head = store.import_const_term(const, decl, del_const)
            self._proj_field_cache.set(dkey, inner_head)
        inner_j = leaf_index(inner_head)
        inner_const = store.leaves[inner_j]
        assert isinstance(inner_const, W_Const)
        save_top = store._spine_top
        try:
            let_vals = cb.let_vals
            if let_vals is None:
                env_base = arg_base
                env_total = m
            else:
                nlets = len(let_vals)
                env_total = nlets + m
                uses = cb.uses_lets
                assert uses is not None
                need_lets = False
                bid = 0
                while bid < inner_m:
                    if inner_mask < 0 or (inner_mask & (1 << bid)) != 0:
                        if uses[inner_m - 1 - bid]:
                            need_lets = True
                            break
                    bid += 1
                env_base = store._spine_top
                store.ensure_spine_room(env_total)
                buf = store._spine_buf
                k = 0
                while k < m:
                    buf[env_base + nlets + k] = buf[arg_base + k]
                    k += 1
                store._spine_top = env_base + env_total
                if not need_lets:
                    li = 0
                    while li < nlets:
                        store._spine_buf[env_base + li] = _u32(self.h_prop)
                        li += 1
                else:
                    li = 0
                    while li < nlets:
                        vh = store.import_const_term(const, decl, let_vals[li])
                        cnt = li + m
                        if cnt > 0 and store.loose_bvar_range(vh) > 0:
                            if cnt == 1:
                                vh = store.instantiate(
                                    vh, store.spine_arg(env_base + nlets - li), 0,
                                )
                            else:
                                vh = store.instantiate_multi_buf(
                                    vh, env_base + nlets - li, cnt, 0,
                                )
                        store._spine_buf[env_base + nlets - 1 - li] = _u32(vh)
                        li += 1
            imark = store._spine_top
            store.ensure_spine_room(inner_m)
            buf = store._spine_buf
            k = 0
            while k < inner_m:
                buf[imark + k] = _u32(self.h_prop)
                k += 1
            store._spine_top = imark + inner_m
            args = cb.args
            bid = 0
            while bid < inner_m:
                if inner_mask >= 0 and (inner_mask & (1 << bid)) == 0:
                    bid += 1
                    continue
                arg_ast = args[inner_m - 1 - bid]
                if isinstance(arg_ast, W_BVar):
                    obid = arg_ast.id
                    if 0 <= obid < env_total:
                        ah = store.spine_arg(env_base + obid)
                    else:
                        ah = store.bvar(obid - env_total)
                else:
                    if bid < 1023:
                        akey = ((j + 1) << 22) | bid
                        ah = self._proj_field_cache.get(akey, 0)
                        if ah == 0:
                            ah = store.import_const_term(const, decl, arg_ast)
                            self._proj_field_cache.set(akey, ah)
                    else:
                        ah = store.import_const_term(const, decl, arg_ast)
                    if env_total > 0 and store.loose_bvar_range(ah) > 0:
                        if env_total == 1:
                            ah = store.instantiate(
                                ah, store.spine_arg(env_base), 0,
                            )
                        else:
                            ah = store.instantiate_multi_buf(
                                ah, env_base, env_total, 0,
                            )
                store._spine_buf[imark + bid] = _u32(ah)
                bid += 1
            if inner_cb.delegate_const is not None:
                return self._eval_delegate_ctor_proj(
                    inner_j, inner_const, inner_decl, inner_cb,
                    imark, inner_m, pbase, ptop,
                )
            return self._eval_direct_ctor_proj(
                inner_j, inner_const, inner_decl, inner_cb,
                imark, inner_m, pbase, ptop,
            )
        finally:
            store.unapp_pop(save_top)

    def _try_lazy_ctor_proj(self, cur, head, pbase, ptop):
        """When ``cur`` is an application (or nullary leaf) of a `_LF_DELTA`
        `W_Definition` ``head`` whose stripped body is a constructor application
        (directly or via delegating `_CtorBody` wrappers), peel pending
        projection layers on the AST and import/instantiate only the final
        projected field and the arguments it actually depends on."""
        store = self.store
        fidxs = self._proj_fidxs
        fidx = fidxs[ptop - 1]
        j = leaf_index(head)
        const = store.leaves[j]
        assert isinstance(const, W_Const)
        decl = self._leaf_decl(head, const)
        if decl is None or len(const.levels) != len(decl.levels):
            return 0
        w_kind = decl.w_kind
        if not isinstance(w_kind, W_Definition):
            return 0
        cb = w_kind._ctor_body
        if cb is None:
            cb = w_kind.init_ctor_body(self.tc.declarations)
        m = cb.m
        if m < 0:
            return 0
        if is_leaf(cur):
            if m != 0:
                return 0
            if cb.delegate_const is not None:
                return self._eval_delegate_ctor_proj(
                    j, const, decl, cb, 0, 0, pbase, ptop,
                )
            return self._eval_direct_ctor_proj(
                j, const, decl, cb, 0, 0, pbase, ptop,
            )
        mark = store._spine_top
        store.unapp_push(cur)
        try:
            n = store._spine_top - mark
            if n < m:
                return 0
            if cb.delegate_const is not None:
                if n != m:
                    return 0
                return self._eval_delegate_ctor_proj(
                    j, const, decl, cb, mark, m, pbase, ptop,
                )
            idx = cb.num_params + fidx
            nargs = len(cb.args)
            if idx >= nargs + (n - m):
                return 0
            if idx >= nargs:
                self._proj_popped = 1
                return store.spine_arg(mark + (nargs + n - m - 1 - idx))
            return self._eval_direct_ctor_proj(
                j, const, decl, cb, mark + n - m, m, pbase, ptop,
            )
        finally:
            store.unapp_pop(mark)

    def try_proj(self, h, cheap_proj=False):
        """Projection of a constructor application, or 0."""
        store = self.store
        raw = store.field_a(h)
        if cheap_proj or self.tc.tracer.recording:
            if cheap_proj:
                struct = self.whnf_core(raw, True)
            else:
                struct = self.whnf(raw)
        else:
            if is_leaf(raw):
                struct = _s32(store.leaf_whnf[leaf_index(raw)])
            else:
                struct = store.memo(raw, M_WHNF)
            if struct == 0:
                return self._try_proj_fused(raw, store.proj_index(h))
        lit = None
        if is_leaf(struct):
            e = store.leaf(struct)
            if isinstance(e, W_LitStr):
                lit = e
        if lit is not None:
            struct = self.whnf(store.import_term(lit.build_str_expr()))
        if store.kind(struct) != KIND_APP:
            return 0
        head = store.head(struct)
        if (self._leaf_flags(head) & _LF_CTOR) == 0:
            return 0
        return self._extract_ctor_field(struct, head, store.proj_index(h))

    def _try_proj_fused(self, raw, fidx0):
        """Evaluate a projection (or chain of nested projections / projection
        wrappers) lazily, deferring intermediate `KIND_PROJ` materialization so
        `_try_lazy_ctor_proj` can peel nested constructor bodies on the AST."""
        store = self.store
        pbase = self._proj_fidx_top
        ptop = pbase
        fidxs = self._proj_fidxs
        if ptop == len(fidxs):
            fidxs = fidxs + ([0] * len(fidxs))
            self._proj_fidxs = fidxs
        fidxs[ptop] = fidx0
        ptop += 1
        self._proj_fidx_top = ptop
        cur = raw
        try:
            while True:
                if self.tc.has_limits:
                    self.tc.tick_wall_time()
                # Peel uncached nested `KIND_PROJ` records onto `fidxs` instead
                # of calling `whnf_core` on them and forcing intermediate ctors.
                while store.kind(cur) == KIND_PROJ:
                    c_whnf = store.memo(cur, M_WHNF)
                    if c_whnf != 0:
                        cur = c_whnf
                        break
                    c_core = store.memo(cur, M_WHNF_CORE)
                    if c_core != 0:
                        if c_core == cur:
                            return 0
                        cur = c_core
                        continue
                    fidxs = self._proj_fidxs
                    if ptop == len(fidxs):
                        fidxs = fidxs + ([0] * len(fidxs))
                        self._proj_fidxs = fidxs
                    fidxs[ptop] = store.proj_index(cur)
                    ptop += 1
                    self._proj_fidx_top = ptop
                    cur = store.field_a(cur)
                if store.kind(cur) != KIND_PROJ:
                    cur = self.whnf_core(cur)
                    if store.kind(cur) == KIND_PROJ:
                        continue
                cached = 0
                if cur != raw:
                    cached = (
                        _s32(store.leaf_whnf[leaf_index(cur)])
                        if is_leaf(cur)
                        else store.memo(cur, M_WHNF)
                    )
                    if cached != 0:
                        cur = cached
                k = store.kind(cur)
                if k == KIND_APP:
                    if cached == 0:
                        reduced = self.try_reduce_nat(cur)
                        if reduced != 0:
                            cur = reduced
                            continue
                    ch = store.head(cur)
                    flags = self._leaf_flags(ch)
                    if (flags & _LF_CTOR) != 0:
                        if ptop == pbase + 1 and cur != raw:
                            if is_leaf(raw):
                                store.leaf_whnf[leaf_index(raw)] = _u32(cur)
                            else:
                                store.set_memo(raw, M_WHNF, cur)
                        fld = self._extract_ctor_field(
                            cur, ch, self._proj_fidxs[ptop - 1],
                        )
                        if fld == 0:
                            return 0
                        ptop -= 1
                        self._proj_fidx_top = ptop
                        if ptop == pbase:
                            return fld
                        cur = fld
                        continue
                    if cached == 0 and (flags & _LF_DELTA) != 0:
                        fld = self._try_lazy_ctor_proj(cur, ch, pbase, ptop)
                        if fld != 0:
                            ptop -= self._proj_popped
                            self._proj_fidx_top = ptop
                            if ptop == pbase:
                                return fld
                            cur = fld
                            continue
                        unfolded = self.try_unfold_head(cur)
                        if unfolded != 0:
                            cur = unfolded
                            continue
                elif k == 0:
                    if cached == 0 and (self._leaf_flags(cur) & _LF_DELTA) != 0:
                        fld = self._try_lazy_ctor_proj(cur, cur, pbase, ptop)
                        if fld != 0:
                            ptop -= self._proj_popped
                            self._proj_fidx_top = ptop
                            if ptop == pbase:
                                return fld
                            cur = fld
                            continue
                        unfolded = self.try_unfold_head(cur)
                        if unfolded != 0:
                            cur = unfolded
                            continue
                    e = store.leaf(cur)
                    if isinstance(e, W_LitStr):
                        cur = self.whnf(store.import_term(e.build_str_expr()))
                        continue
                if ptop == pbase + 1:
                    if is_leaf(raw):
                        store.leaf_whnf[leaf_index(raw)] = _u32(cur)
                    else:
                        store.set_memo(raw, M_WHNF, cur)
                return 0
        finally:
            self._proj_fidx_top = pbase

    def _try_quot_lift_spine(self, mark, n):
        """``Quot.lift α r β f h (Quot.mk r a) extra... ⇒ f a extra...``, or 0."""
        store = self.store
        if n < 6:
            return 0
        mk = self.whnf(store.spine_arg(mark + n - 6))
        mk_mark = store._spine_top
        mk_head = store.unapp_push(mk)
        try:
            mk_const = store.const_leaf(mk_head)
            if mk_const is None or (store._spine_top - mk_mark) != 3:
                return 0
            if not mk_const.name.syntactic_eq(W_App._QUOT_MK):
                return 0
            a = store.spine_arg(mk_mark)
        finally:
            store.unapp_pop(mk_mark)
        res = store.cons_app(store.spine_arg(mark + n - 4), a)
        return store.apply_buf_rev(res, mark, n - 7)

    def _try_iota_spine(self, h, target, const, decl, rec, mark, n_args):
        """One recursor iota step on ``target`` applied to
        `_spine_buf[mark .. mark + n_args)` (outermost-first), or 0."""
        store = self.store
        tc = self.tc
        skip = rec.num_params + rec.num_indices + rec.num_minors + rec.num_motives
        major_idx = n_args - 1 - skip
        if major_idx < 0:
            return 0

        # `Nat.rec motive zero succ (literal N)` in one step.
        if const.name.syntactic_eq(_NAT_REC_NAME):
            lit = store.litnat_leaf(store.spine_arg(mark + major_idx))
            if lit is not None:
                if tc.tracer.recording:
                    tc.tracer.iota(const.name)
                succ_case = store.spine_arg(mark + major_idx + 1)
                zero_case = store.spine_arg(mark + major_idx + 2)
                if lit.val.eq(rbigint.fromint(0)):
                    if major_idx == 0:
                        return zero_case
                    if (store.kind(zero_case) == KIND_LAMBDA
                            and not (tc.tracer.recording and tc.tracer.writes)):
                        return self._beta_spine_buf(zero_case, mark, major_idx)
                    return store.apply_buf_rev(zero_case, mark, major_idx - 1)
                pred = store.leaf_for(
                    _mk_w_litnat(lit.val.sub(rbigint.fromint(1))),
                )
                rec_prefix = store.field_a(h)
                step = major_idx
                while step > 0:
                    rec_prefix = store.field_a(rec_prefix)
                    step -= 1
                rec_at_pred = store.cons_app(rec_prefix, pred)
                if (store.kind(succ_case) == KIND_LAMBDA
                        and not (tc.tracer.recording and tc.tracer.writes)):
                    rmark = store._spine_top
                    try:
                        i = 0
                        while i < major_idx:
                            store.spine_push(store.spine_arg(mark + i))
                            i += 1
                        store.spine_push(rec_at_pred)
                        store.spine_push(pred)
                        return self._beta_spine_buf(
                            succ_case, rmark, store._spine_top - rmark,
                        )
                    finally:
                        store.unapp_pop(rmark)
                res = store.cons_app(
                    store.cons_app(succ_case, pred), rec_at_pred,
                )
                return store.apply_buf_rev(res, mark, major_idx - 1)

        major = self.whnf(store.spine_arg(mark + major_idx))

        if rec.k == 1:
            major = self._to_cnstr_when_k(rec, mark, n_args, major)
            if major == 0:
                return 0

        lit = store.litnat_leaf(major)
        if lit is not None:
            major = store.import_term(lit.one_step_constructor())
        else:
            expanded = self._to_cnstr_when_structure(decl, rec, major)
            if expanded != 0:
                major = expanded

        cmark = store._spine_top
        ctor_head = store.unapp_push(major)
        try:
            n_ctor = store._spine_top - cmark
            if (self._leaf_flags(ctor_head) & _LF_CTOR) == 0:
                return 0
            cj = leaf_index(ctor_head)
            ctor = store.leaves[cj]
            assert isinstance(ctor, W_Const)
            rule = rec.rule_for_ctor(ctor.name)
            if rule is None:
                return 0
            ctor_decl = store.leaf_decl[cj]
            assert ctor_decl is not None
            ctor_kind = ctor_decl.w_kind
            assert isinstance(ctor_kind, W_Constructor)

            total = rec.num_params + rec.num_motives + rec.num_minors
            assert total >= 0
            nf = rule.num_fields
            lo = n_ctor - (ctor_kind.num_params + nf)
            hi = n_ctor - 1 - ctor_kind.num_params
            sminor = rule.simple_minor(
                decl, rec.num_params, rec.num_motives, rec.num_minors, rec.num_indices,
            )
            if sminor >= 0 and lo >= 0:
                if tc.tracer.recording:
                    tc.tracer.iota(const.name)
                    expected = total + nf
                    j = 0
                    while j < expected:
                        tc.tracer.beta()
                        j += 1
                minor = store.spine_arg(
                    mark + n_args - 1 - (rec.num_params + rec.num_motives + sminor),
                )
                rec_fields = rule._rec_fields
                if rec_fields is None:
                    if nf == 0:
                        if major_idx == 0:
                            return minor
                        if (store.kind(minor) == KIND_LAMBDA
                                and not (tc.tracer.recording and tc.tracer.writes)):
                            return self._beta_spine_buf(minor, mark, major_idx)
                        return store.apply_buf_rev(minor, mark, major_idx - 1)
                    if (store.kind(minor) == KIND_LAMBDA
                            and not (tc.tracer.recording and tc.tracer.writes)):
                        if nf == 1 and major_idx == 0:
                            if tc.tracer.recording:
                                tc.tracer.beta()
                            return store.instantiate(
                                store.field_b(minor), store.spine_arg(cmark + hi), 0,
                            )
                        rmark = store._spine_top
                        i = 0
                        while i < major_idx:
                            store.spine_push(store.spine_arg(mark + i))
                            i += 1
                        i = lo
                        while i <= hi:
                            store.spine_push(store.spine_arg(cmark + i))
                            i += 1
                        return self._beta_spine_buf(
                            minor, rmark, store._spine_top - rmark,
                        )
                    res = minor
                    i = hi
                    while i >= lo:
                        res = store.cons_app(res, store.spine_arg(cmark + i))
                        i -= 1
                    return store.apply_buf_rev(res, mark, major_idx - 1)
                # Standard non-indexed recursive rule (e.g. List.cons, Nat.succ,
                # Poly.add, Expr.add): reuse `rec_prefix` directly from `h`!
                rec_prefix = store.field_a(h)
                step = major_idx
                while step > 0:
                    rec_prefix = store.field_a(rec_prefix)
                    step -= 1
                nr = len(rec_fields)
                if (store.kind(minor) == KIND_LAMBDA
                        and not (tc.tracer.recording and tc.tracer.writes)):
                    rmark = store._spine_top
                    i = 0
                    while i < major_idx:
                        store.spine_push(store.spine_arg(mark + i))
                        i += 1
                    j = nr - 1
                    while j >= 0:
                        ih = store.cons_app(
                            rec_prefix, store.spine_arg(cmark + hi - rec_fields[j]),
                        )
                        store.spine_push(ih)
                        j -= 1
                    i = lo
                    while i <= hi:
                        store.spine_push(store.spine_arg(cmark + i))
                        i += 1
                    return self._beta_spine_buf(
                        minor, rmark, store._spine_top - rmark,
                    )
                res = minor
                i = hi
                while i >= lo:
                    res = store.cons_app(res, store.spine_arg(cmark + i))
                    i -= 1
                j = 0
                while j < nr:
                    ih = store.cons_app(
                        rec_prefix, store.spine_arg(cmark + hi - rec_fields[j]),
                    )
                    res = store.cons_app(res, ih)
                    j += 1
                return store.apply_buf_rev(res, mark, major_idx - 1)

            packed = self._rule_rhs_stripped(
                target, const, ctor_head, rule, total + nf,
            )
            if tc.tracer.recording:
                tc.tracer.iota(const.name)

            # Push rhs args onto `_spine_buf` outermost-first (extra args,
            # ctor fields, then params/motives/minors) so `_apply_stripped_body`
            # substitutes the stripped lambdas in one zero-allocation pass.
            rmark = store._spine_top
            i = 0
            while i < major_idx:
                store.spine_push(store.spine_arg(mark + i))
                i += 1
            if lo < 0:
                lo = 0
            i = lo
            while i <= hi:
                store.spine_push(store.spine_arg(cmark + i))
                i += 1
            i = n_args - total
            while i < n_args:
                store.spine_push(store.spine_arg(mark + i))
                i += 1
            m = store._spine_top - rmark
            k = packed >> 32
            body_h = packed & 0xFFFFFFFF
            if m >= k:
                return self._apply_stripped_body(body_h, k, rmark, m)
            decl = self._leaf_decl(target, const)
            if decl is None:
                decl = get_decl(tc.declarations, const.name)
            rhs = store.import_const_term(const, decl, rule.rhs)
            return self._beta_spine_buf(rhs, rmark, m)
        finally:
            store.unapp_pop(cmark)

    def _rule_rhs_stripped(self, target, const, ctor_head, rule, max_strip):
        key = ((leaf_index(target) + 1) << 30) | leaf_index(ctor_head)
        packed = self._rule_memo.get(key, 0)
        if packed != 0:
            return packed
        decl = self._leaf_decl(target, const)
        if decl is None:
            decl = get_decl(self.tc.declarations, const.name)
        k = 0
        cur = rule.rhs
        while k < max_strip and isinstance(cur, W_Lambda):
            cur = cur.body
            k += 1
        body_h = self.store.import_const_term(const, decl, cur)
        packed = (k << 32) | body_h
        self._rule_memo.set(key, packed)
        return packed

    def _to_cnstr_when_k(self, rec, mark, n, major):
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
        ctor_decl = get_decl(tc.declarations, ind_kind.ctor_names[0])
        ctor_kind = ctor_decl.w_kind
        assert isinstance(ctor_kind, W_Constructor)
        ctor = store.leaf_for(ctor_decl.name.const(old_const.levels))
        i = n - 1
        stop = n - 1 - ctor_kind.num_params
        while i > stop and i >= 0:
            ctor = store.cons_app(ctor, store.spine_arg(mark + i))
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
                self.store.leaf_checked[leaf_index(fv)] = _u32(self.check_gen)
                self._fvar_reused = True
                return fv
        self._fvar_reused = False
        store = self.store
        binder = store.binder_of(h)
        own = binder.fvar()
        if store.has_fvar_leaf(own):
            fv = store._new_fvar_leaf(W_FVar(binder))
        else:
            # The binder's own variable serves its first opening, so an
            # error in it is marked where whoever opens the binder
            # outside the machine (the printer, say) puts the variable.
            fv = store._new_fvar_leaf(own)
        j = leaf_index(fv)
        store.leaf_infer[j] = _u32(domain)
        store.leaf_checked[j] = _u32(self.check_gen)
        if key != 0:
            self._fvars.set(key, fv)
        return fv

    def _fresh_fvar(self, h, domain):
        """Allocate a guaranteed-fresh free variable for binder ``h`` with
        domain ``domain`` without touching the reuse cache."""
        store = self.store
        fv = store._new_fvar_leaf(W_FVar(store.binder_of(h)))
        j = leaf_index(fv)
        store.leaf_infer[j] = _u32(domain)
        store.leaf_checked[j] = _u32(self.check_gen)
        return fv

    def _top_fvar(self, idx, binder, domain):
        """Canonical free variable for top-level telescope position ``idx``
        with domain handle ``domain``. Reused across declarations in the same
        warm epoch so shared file-level `variable` prefixes share their
        checked domain, WHNF, infer, and def_eq memos."""
        key = self._pair_key(idx + 1, domain)
        if key != 0:
            fv = self._top_fvars.get(key, 0)
            if fv != 0:
                self.store.leaf_checked[leaf_index(fv)] = _u32(self.check_gen)
                return fv
        store = self.store
        own = binder.fvar()
        if store.has_fvar_leaf(own):
            fv = store._new_fvar_leaf(W_FVar(binder))
        else:
            fv = store._new_fvar_leaf(own)
        j = leaf_index(fv)
        store.leaf_infer[j] = _u32(domain)
        store.leaf_checked[j] = _u32(self.check_gen)
        if key != 0:
            self._top_fvars.set(key, fv)
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
            t = _s32(store.leaf_infer[j])
            if 0 < t < _LEAF_INFER_SEEN:
                if check:
                    cg = _s32(store.leaf_checked[j])
                    if cg < self.check_gen:
                        return self._check_leaf(h, t)
                    if cg != _CHECKED_PERM:
                        self._saw_nonperm = True
                return t
            return self._infer_leaf(h, check)
        ri = rec_index(h)
        mbase = ri * MEMO_SLOTS
        memos = store.memos
        if check:
            cg = _s32(memos[mbase + M_CHECKED_GEN])
            if cg >= self.check_gen:
                if cg != _CHECKED_PERM:
                    self._saw_nonperm = True
                t = _s32(memos[mbase + M_INFER])
                if t != 0:
                    return t
                return self._infer_miss(h, ri, mbase, False)
        else:
            t = _s32(memos[mbase + M_INFER])
            if t != 0:
                return t
        return self._infer_miss(h, ri, mbase, check)

    def infer_expected(self, h, expected):
        """Like `infer(h, True)`, hinting that the result is expected to equal
        the closed handle ``expected`` so `_infer_app` can verify the return
        type structurally via `inst_eq_buf` without allocating records."""
        store = self.store
        if is_leaf(h):
            j = leaf_index(h)
            t = _s32(store.leaf_infer[j])
            if 0 < t < _LEAF_INFER_SEEN:
                cg = _s32(store.leaf_checked[j])
                if cg < self.check_gen:
                    return self._check_leaf(h, t)
                if cg != _CHECKED_PERM:
                    self._saw_nonperm = True
                return t
            return self._infer_leaf(h, True)
        ri = rec_index(h)
        mbase = ri * MEMO_SLOTS
        memos = store.memos
        cg = _s32(memos[mbase + M_CHECKED_GEN])
        if cg >= self.check_gen:
            if cg != _CHECKED_PERM:
                self._saw_nonperm = True
            t = _s32(memos[mbase + M_INFER])
            if t != 0:
                return t
            return self._infer_miss(h, ri, mbase, False)
        if expected != 0 and not is_leaf(expected) and not self._def_eq_hooked:
            hk = _s32(store.recs[ri << 2]) & _KIND_MASK
            if hk == KIND_APP:
                return self._infer_app_miss_expected(h, ri, mbase, expected)
            if hk == KIND_LET:
                if not (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                        and store.is_heavy(h)):
                    return self._infer_let_miss_expected(h, ri, mbase, expected)
            elif hk == KIND_LAMBDA:
                if (store.kind(expected) == KIND_FORALL
                        and store.field_a(h) == store.field_a(expected)
                        and store.loose_bvar_range(expected) == 0
                        and not (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                                 and store.is_heavy(h))):
                    return self._infer_lambda_miss_expected(h, ri, mbase, expected)
        return self._infer_miss(h, ri, mbase, True)

    @dont_inline
    def _infer_let_miss_expected(self, h, ri, mbase, expected):
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        store = self.store
        prev_np = self._saw_nonperm
        self._saw_nonperm = False
        type_h = store.field_a(h)
        pair = store.field_b(h)
        value = store.field_a(pair)
        body = store.field_b(pair)
        self._ensure_sort(type_h, True)
        value_type = self.infer_expected(value, type_h)
        if not self.def_eq(value_type, type_h):
            raise W_TypeError(
                self.tc, self.export(value), self.export(type_h),
                inferred_type=self.export(value_type),
            )
        if store.loose_bvar_range(body) > 0:
            body = store.instantiate(body, value, 0)
        t = self.infer_expected(body, expected)
        child_np = self._saw_nonperm
        self._saw_nonperm = prev_np or child_np
        memos = store.memos
        if t != expected or not store.has_fvar(expected):
            memos[mbase + M_INFER] = _u32(t)
        if (not child_np
                and self._can_perm
                and (_s32(store.recs[ri << 2]) >> 3) == 0):
            memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
        else:
            memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
        return t

    @dont_inline
    def _infer_lambda_miss_expected(self, h, ri, mbase, expected):
        """Check `KIND_LAMBDA` ``h`` against matching `KIND_FORALL`
        ``expected`` jointly, skipping `bind_fvars` and Pi re-wrapping when
        the body's inferred type matches the opened codomain."""
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        store = self.store
        prev_np = self._saw_nonperm
        self._saw_nonperm = False
        has_fv = store.has_fvar(h) or store.has_fvar(expected)
        vbody = store.field_b(h)
        tbody = store.field_b(expected)
        if (store.kind(vbody) != KIND_LAMBDA
                or store.kind(tbody) != KIND_FORALL
                or store.field_a(vbody) != store.field_a(tbody)):
            domain = store.field_a(h)
            self._ensure_sort(domain, True)
            vb_open = store.loose_bvar_range(vbody) > 0
            tb_open = store.loose_bvar_range(tbody) > 0
            fvar = 0
            if vb_open or tb_open:
                fvar = self.fvar_for_domain(h, domain)
                if self._fvar_reused and has_fv:
                    fvar = self._fresh_fvar(h, domain)
                if vb_open:
                    vbody = store.instantiate(vbody, fvar, 0)
                if tb_open:
                    tbody = store.instantiate(tbody, fvar, 0)
            r = self._cheap_beta(self.infer_expected(vbody, tbody))
            if r == tbody or self.def_eq(tbody, r):
                t = expected
            else:
                if fvar != 0:
                    r = store.bind_fvar(r, fvar, 0)
                t = store.cons(KIND_FORALL, domain, r, store.info(h))
        else:
            records = []
            fvars = []
            vcur = h
            tcur = expected
            while (store.kind(vcur) == KIND_LAMBDA
                   and store.kind(tcur) == KIND_FORALL
                   and store.field_a(vcur) == store.field_a(tcur)):
                orig_d = store.field_a(vcur)
                idx = len(fvars)
                if idx > 0 and store.loose_bvar_range(orig_d) > 0:
                    if is_leaf(orig_d):
                        bid = (_s32(store.leaf_meta[leaf_index(orig_d)]) >> 1) - 1
                        domain = fvars[idx - 1 - bid] if bid < idx else store.bvar(bid - idx)
                    else:
                        domain = store.instantiate_multi_rev(orig_d, fvars, idx, 0)
                else:
                    domain = orig_d
                self._ensure_sort(domain, True)
                fvar = self.fvar_for_domain(vcur, domain)
                if self._fvar_reused and has_fv:
                    fvar = self._fresh_fvar(vcur, domain)
                records.append(vcur)
                fvars.append(fvar)
                vcur = store.field_b(vcur)
                tcur = store.field_b(tcur)
            n = len(fvars)
            if store.loose_bvar_range(vcur) > 0:
                vcur = store.instantiate_multi_rev(vcur, fvars, n, 0)
            if store.loose_bvar_range(tcur) > 0:
                tcur = store.instantiate_multi_rev(tcur, fvars, n, 0)
            r = self._cheap_beta(self.infer_expected(vcur, tcur))
            if r == tcur or self.def_eq(tcur, r):
                t = expected
            else:
                r = store.bind_fvars(r, fvars, 0, n)
                i = n - 1
                while i >= 0:
                    rec = records[i]
                    r = store.cons(KIND_FORALL, store.field_a(rec), r, store.info(rec))
                    i -= 1
                t = r
        child_np = self._saw_nonperm
        self._saw_nonperm = prev_np or child_np
        memos = store.memos
        if t != expected or not store.has_fvar(expected):
            memos[mbase + M_INFER] = _u32(t)
        if (not child_np
                and self._can_perm
                and (_s32(store.recs[ri << 2]) >> 3) == 0):
            memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
        else:
            memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
        return t

    @dont_inline
    def _infer_app_miss_expected(self, h, ri, mbase, expected):
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        prev_np = self._saw_nonperm
        self._saw_nonperm = False
        t = self._infer_app(h, True, expected)
        child_np = self._saw_nonperm
        self._saw_nonperm = prev_np or child_np
        store = self.store
        memos = store.memos
        memos[mbase + M_INFER] = _u32(t)
        if (not child_np
                and self._can_perm
                and (_s32(store.recs[ri << 2]) >> 3) == 0):
            memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
        else:
            memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
        return t

    @dont_inline
    def _infer_app_expected_pat(self, h, exp_pat, exp_start, exp_n):
        """Check `KIND_APP` record ``h`` expecting its return type to equal
        ``instantiate_multi_buf(exp_pat, exp_start, exp_n, 0)``.

        Returns 0 when ``h`` is verified well-typed and its return type matched
        structurally without materializing either side (marking `M_CHECKED_GEN`
        so a later shared visit computes `M_INFER` without re-checking args);
        otherwise returns the materialized type handle."""
        store = self.store
        ri = rec_index(h)
        mbase = ri * MEMO_SLOTS
        memos = store.memos
        cg = _s32(memos[mbase + M_CHECKED_GEN])
        if cg >= self.check_gen:
            if cg != _CHECKED_PERM:
                self._saw_nonperm = True
            t = _s32(memos[mbase + M_INFER])
            if t != 0:
                return t
            return self._infer_miss(h, ri, mbase, False)
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        prev_np = self._saw_nonperm
        self._saw_nonperm = False
        t = self._infer_app(h, True, exp_pat, exp_start, exp_n)
        child_np = self._saw_nonperm
        self._saw_nonperm = prev_np or child_np
        memos = store.memos
        if t != 0:
            memos[mbase + M_INFER] = _u32(t)
        if (not child_np
                and self._can_perm
                and (_s32(store.recs[ri << 2]) >> 3) == 0):
            memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
        else:
            memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
        return t

    @dont_inline
    def _infer_let_expected_pat(self, h, exp_pat, exp_start, exp_n):
        """Check `KIND_LET` record ``h`` expecting its type to match
        ``instantiate_multi_buf(exp_pat, exp_start, exp_n, 0)``.
        Returns 0 on verified match without materializing the expected type,
        else returns the materialized type handle."""
        store = self.store
        ri = rec_index(h)
        mbase = ri * MEMO_SLOTS
        memos = store.memos
        cg = _s32(memos[mbase + M_CHECKED_GEN])
        if cg >= self.check_gen:
            if cg != _CHECKED_PERM:
                self._saw_nonperm = True
            t = _s32(memos[mbase + M_INFER])
            if t != 0:
                return t
            return self._infer_miss(h, ri, mbase, False)
        if (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                and store.is_heavy(h)):
            return self._infer_miss(h, ri, mbase, True)
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        prev_np = self._saw_nonperm
        self._saw_nonperm = False
        type_h = store.field_a(h)
        pair = store.field_b(h)
        value = store.field_a(pair)
        body = store.field_b(pair)
        self._ensure_sort(type_h, True)
        value_type = self.infer_expected(value, type_h)
        if not self.def_eq(value_type, type_h):
            raise W_TypeError(
                self.tc, self.export(value), self.export(type_h),
                inferred_type=self.export(value_type),
            )
        if store.loose_bvar_range(body) > 0:
            body = store.instantiate(body, value, 0)
        if not is_leaf(body):
            bk = _s32(store.recs[rec_index(body) << 2]) & _KIND_MASK
            if bk == KIND_APP:
                t = self._infer_app_expected_pat(body, exp_pat, exp_start, exp_n)
            elif bk == KIND_LAMBDA and store.kind(exp_pat) == KIND_FORALL:
                t = self._infer_lambda_expected_pat(body, exp_pat, exp_start, exp_n)
            elif bk == KIND_LET:
                t = self._infer_let_expected_pat(body, exp_pat, exp_start, exp_n)
            else:
                t = self.infer(body, True)
        else:
            t = self.infer(body, True)
        child_np = self._saw_nonperm
        self._saw_nonperm = prev_np or child_np
        memos = store.memos
        if t != 0:
            memos[mbase + M_INFER] = _u32(t)
        if (not child_np
                and self._can_perm
                and (_s32(store.recs[ri << 2]) >> 3) == 0):
            memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
        else:
            memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
        return t

    @dont_inline
    def _infer_lambda_expected_pat(self, h, exp_pat, exp_start, exp_n):
        """Check `KIND_LAMBDA` record ``h`` expecting its type to equal
        ``instantiate_multi_buf(exp_pat, exp_start, exp_n, 0)`` where
        ``exp_pat`` is a `KIND_FORALL`, matching leading domains structurally
        against `_spine_buf` and forwarding the open expected codomain to the
        body without instantiating `exp_pat` or running `bind_fvars`.

        Returns 0 on verified match (leaving `M_INFER == 0` and marking
        `M_CHECKED_GEN`), else returns the materialized type handle."""
        store = self.store
        ri = rec_index(h)
        mbase = ri * MEMO_SLOTS
        memos = store.memos
        cg = _s32(memos[mbase + M_CHECKED_GEN])
        if cg >= self.check_gen:
            if cg != _CHECKED_PERM:
                self._saw_nonperm = True
            t = _s32(memos[mbase + M_INFER])
            if t != 0:
                return t
            return self._infer_miss(h, ri, mbase, False)
        if (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                and store.is_heavy(h)):
            return self._infer_miss(h, ri, mbase, True)
        # Quick reject before touching _spine_buf if the outermost domain
        # doesn't match the open domain pattern structurally.
        if not store.inst_eq_buf(
                store.field_a(exp_pat), exp_start, exp_n, store.field_a(h)):
            return self._infer_miss(h, ri, mbase, True)
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        prev_np = self._saw_nonperm
        self._saw_nonperm = False
        vc = store.field_b(h)
        tc = store.field_b(exp_pat)
        # Fast path for single-binder lambda (no records/fvars lists, and zero
        # _spine_buf copy when the expected codomain is closed or a BVar leaf).
        if store.kind(vc) != KIND_LAMBDA or store.kind(tc) != KIND_FORALL:
            domain = store.field_a(h)
            self._ensure_sort(domain, True)
            if store.loose_bvar_range(tc) == 0 or is_leaf(tc):
                vb_open = store.loose_bvar_range(vc) > 0
                if store.loose_bvar_range(tc) == 0:
                    exp_body = tc
                    tb_needs_fv = False
                else:
                    bid = (_s32(store.leaf_meta[leaf_index(tc)]) >> 1) - 1
                    if bid == 0:
                        exp_body = 0
                        tb_needs_fv = True
                    else:
                        exp_body = (
                            store.spine_arg(exp_start + bid - 1)
                            if bid - 1 < exp_n
                            else store.bvar(bid - 1 - exp_n)
                        )
                        tb_needs_fv = False
                fvar = 0
                if vb_open or tb_needs_fv:
                    fvar = self.fvar_for_domain(h, domain)
                    if self._fvar_reused and (
                            store.has_fvar(h)
                            or (exp_body != 0 and store.has_fvar(exp_body))):
                        fvar = self._fresh_fvar(h, domain)
                    if vb_open:
                        vc = store.instantiate(vc, fvar, 0)
                    if tb_needs_fv:
                        exp_body = fvar
                r = self._cheap_beta(self.infer_expected(vc, exp_body))
                matched = (r == exp_body or self.def_eq(exp_body, r))
                child_np = self._saw_nonperm
                self._saw_nonperm = prev_np or child_np
                memos = store.memos
                if matched:
                    if (not child_np
                            and self._can_perm
                            and (_s32(store.recs[ri << 2]) >> 3) == 0):
                        memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
                    else:
                        memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
                    return 0
                if fvar != 0:
                    r = store.bind_fvar(r, fvar, 0)
                r = store.cons(KIND_FORALL, domain, r, store.info(h))
                memos = store.memos
                memos[mbase + M_INFER] = _u32(r)
                if (not child_np
                        and self._can_perm
                        and (_s32(store.recs[ri << 2]) >> 3) == 0):
                    memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
                else:
                    memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
                return r
            # Single-binder lambda with compound open expected codomain.
            smark = store._spine_top
            total = 1 + exp_n
            store.ensure_spine_room(total)
            buf = store._spine_buf
            has_fv = store.has_fvar(h) or store.has_fvar(exp_pat)
            j = 0
            while j < exp_n:
                a = _s32(buf[exp_start + j])
                if not has_fv and store.has_fvar(a):
                    has_fv = True
                buf[smark + 1 + j] = _u32(a)
                j += 1
            fvar = self.fvar_for_domain(h, domain)
            if self._fvar_reused and has_fv:
                fvar = self._fresh_fvar(h, domain)
            buf[smark] = _u32(fvar)
            store._spine_top = smark + total
            matched = False
            r = 0
            try:
                if store.loose_bvar_range(vc) > 0:
                    vc = store.instantiate(vc, fvar, 0)
                if not is_leaf(vc):
                    vk = _s32(store.recs[rec_index(vc) << 2]) & _KIND_MASK
                    if vk == KIND_APP:
                        r = self._infer_app_expected_pat(vc, tc, smark, total)
                    elif vk == KIND_LET:
                        r = self._infer_let_expected_pat(vc, tc, smark, total)
                    else:
                        r = self.infer(vc, True)
                else:
                    r = self.infer(vc, True)
                if r == 0:
                    matched = True
                else:
                    r = self._cheap_beta(r)
                    if store.inst_eq_buf(tc, smark, total, r):
                        matched = True
                    else:
                        exp_body = store.instantiate_multi_buf(tc, smark, total, 0)
                        matched = self.def_eq(exp_body, r)
            finally:
                store.unapp_pop(smark)
            child_np = self._saw_nonperm
            self._saw_nonperm = prev_np or child_np
            memos = store.memos
            if matched:
                if (not child_np
                        and self._can_perm
                        and (_s32(store.recs[ri << 2]) >> 3) == 0):
                    memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
                else:
                    memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
                return 0
            r = store.bind_fvar(r, fvar, 0)
            r = store.cons(KIND_FORALL, domain, r, store.info(h))
            memos = store.memos
            memos[mbase + M_INFER] = _u32(r)
            if (not child_np
                    and self._can_perm
                    and (_s32(store.recs[ri << 2]) >> 3) == 0):
                memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
            else:
                memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
            return r
        # Multi-binder telescope: reserve `[fvars_rev..., outer_args...]` on
        # `_spine_buf` so each inner domain and the codomain check directly
        # against the open pattern.
        k = 2
        vc = store.field_b(vc)
        tc = store.field_b(tc)
        while store.kind(vc) == KIND_LAMBDA and store.kind(tc) == KIND_FORALL:
            k += 1
            vc = store.field_b(vc)
            tc = store.field_b(tc)
        smark = store._spine_top
        total = k + exp_n
        store.ensure_spine_room(total)
        buf = store._spine_buf
        has_fv = store.has_fvar(h) or store.has_fvar(exp_pat)
        j = 0
        while j < exp_n:
            a = _s32(buf[exp_start + j])
            if not has_fv and store.has_fvar(a):
                has_fv = True
            buf[smark + k + j] = _u32(a)
            j += 1
        store._spine_top = smark + total
        records = []
        fvars = []
        m = 0
        matched = False
        r = 0
        try:
            vcur = h
            tcur = exp_pat
            while m < k:
                orig_d = store.field_a(vcur)
                if m > 0 and store.loose_bvar_range(orig_d) > 0:
                    if is_leaf(orig_d):
                        bid = (_s32(store.leaf_meta[leaf_index(orig_d)]) >> 1) - 1
                        domain = fvars[m - 1 - bid] if bid < m else store.bvar(bid - m)
                    else:
                        domain = store.instantiate_multi_rev(orig_d, fvars, m, 0)
                else:
                    domain = orig_d
                if m > 0:
                    if not store.inst_eq_buf(
                            store.field_a(tcur), smark + k - m, m + exp_n, domain):
                        break
                self._ensure_sort(domain, True)
                fvar = self.fvar_for_domain(vcur, domain)
                if self._fvar_reused and has_fv:
                    fvar = self._fresh_fvar(vcur, domain)
                records.append(vcur)
                fvars.append(fvar)
                m += 1
                store._spine_buf[smark + k - m] = _u32(fvar)
                vcur = store.field_b(vcur)
                tcur = store.field_b(tcur)
            if store.loose_bvar_range(vcur) > 0:
                if m == 1:
                    vcur = store.instantiate(vcur, fvars[0], 0)
                else:
                    vcur = store.instantiate_multi_rev(vcur, fvars, m, 0)
            cur_start = smark + k - m
            cur_n = m + exp_n
            if store.loose_bvar_range(tcur) == 0:
                r = self._cheap_beta(self.infer_expected(vcur, tcur))
                matched = (r == tcur or self.def_eq(tcur, r))
            elif is_leaf(tcur):
                bid = (_s32(store.leaf_meta[leaf_index(tcur)]) >> 1) - 1
                exp_body = (
                    store.spine_arg(cur_start + bid)
                    if bid < cur_n
                    else store.bvar(bid - cur_n)
                )
                r = self._cheap_beta(self.infer_expected(vcur, exp_body))
                matched = (r == exp_body or self.def_eq(exp_body, r))
            else:
                if not is_leaf(vcur):
                    vk = _s32(store.recs[rec_index(vcur) << 2]) & _KIND_MASK
                    if vk == KIND_APP:
                        r = self._infer_app_expected_pat(vcur, tcur, cur_start, cur_n)
                    elif vk == KIND_LET:
                        r = self._infer_let_expected_pat(vcur, tcur, cur_start, cur_n)
                    else:
                        r = self.infer(vcur, True)
                else:
                    r = self.infer(vcur, True)
                if r == 0:
                    matched = True
                else:
                    r = self._cheap_beta(r)
                    if store.inst_eq_buf(tcur, cur_start, cur_n, r):
                        matched = True
                    else:
                        exp_body = store.instantiate_multi_buf(tcur, cur_start, cur_n, 0)
                        matched = self.def_eq(exp_body, r)
        finally:
            store.unapp_pop(smark)
        child_np = self._saw_nonperm
        self._saw_nonperm = prev_np or child_np
        memos = store.memos
        if matched:
            if (not child_np
                    and self._can_perm
                    and (_s32(store.recs[ri << 2]) >> 3) == 0):
                memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
            else:
                memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
            return 0
        r = store.bind_fvars(r, fvars, 0, m)
        i = m - 1
        while i >= 0:
            rec = records[i]
            r = store.cons(KIND_FORALL, store.field_a(rec), r, store.info(rec))
            i -= 1
        memos = store.memos
        memos[mbase + M_INFER] = _u32(r)
        if (not child_np
                and self._can_perm
                and (_s32(store.recs[ri << 2]) >> 3) == 0):
            memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
        else:
            memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
        return r

    @dont_inline
    def _infer_miss(self, h, ri, mbase, check):
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
        store = self.store
        kind = _s32(store.recs[ri << 2]) & _KIND_MASK
        prev_np = self._saw_nonperm
        if check:
            self._saw_nonperm = False
        if kind == KIND_APP:
            t = self._infer_app(h, check)
        elif kind == KIND_LAMBDA:
            if (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                    and store.is_heavy(h)):
                if check:
                    self._saw_nonperm = True
                t = self._infer_open_lambda(h, [], 0, check)
            else:
                t = self._infer_lambda(h, check)
        elif kind == KIND_FORALL:
            if (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                    and store.is_heavy(h)):
                if check:
                    self._saw_nonperm = True
                t = self._infer_open_forall(h, [], 0, check)
            else:
                t = self._infer_forall(h, check)
        elif kind == KIND_LET:
            if (store.nrecs - self._decl_start_recs >= _OPEN_RECORDS
                    and store.is_heavy(h)):
                if check:
                    self._saw_nonperm = True
                t = self._infer_open_let(h, [], 0, check)
            else:
                t = self._infer_let(h, check)
        elif kind == KIND_PROJ:
            t = self._infer_proj(h, [], 0, check)
        else:
            raise RuntimeError("infer: internal pair record")
        memos = store.memos
        memos[mbase + M_INFER] = _u32(t)
        if check:
            child_np = self._saw_nonperm
            self._saw_nonperm = prev_np or child_np
            if (not child_np
                    and self._can_perm
                    and (_s32(store.recs[ri << 2]) >> 3) == 0):
                memos[mbase + M_CHECKED_GEN] = _u32(_CHECKED_PERM)
            else:
                memos[mbase + M_CHECKED_GEN] = _u32(self.check_gen)
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
        return store.instantiate_multi_ctx(h, ctx, chain)

    def _infer_open(self, h, ctx, chain, check):
        """The type of ``h`` with the context standing for its loose
        bound variables."""
        store = self.store
        if store.loose_bvar_range(h) == 0:
            return self.infer(h, check)
        if is_leaf(h):
            return self.infer(
                ctx[(_s32(store.leaf_meta[leaf_index(h)]) >> 1) - 1], check,
            )
        if not store.is_heavy(h):
            return self.infer(self._materialize(h, ctx, chain), check)
        memo = self._open_memo
        t = memo.get(h, (chain << 1) | 1, 0)
        if t != 0:
            return t
        if not check:
            t = memo.get(h, chain << 1, 0)
            if t != 0:
                return t
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("infer")
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
        mark = store._spine_top
        head = store.unapp_push(h)
        try:
            n = store._spine_top - mark
            fn_type = self._infer_open(head, ctx, chain, check)
            i = n - 1
            while i >= 0:
                arg = store.spine_arg(mark + i)
                if store.kind(fn_type) != KIND_FORALL:
                    fn_type_whnf = self.whnf(fn_type)
                    if store.kind(fn_type_whnf) != KIND_FORALL:
                        closed = [
                            self._materialize(store.spine_arg(mark + j), ctx, chain)
                            for j in range(n)
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
        finally:
            store.unapp_pop(mark)

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
        r = store.bind_fvars(r, fvars, 0, n)
        i = n - 1
        while i >= 0:
            domain = store.bind_fvars(domains[i], fvars, 0, i)
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

    @dont_inline
    def _check_leaf(self, h, t):
        store = self.store
        tc = self.tc
        j = leaf_index(h)
        e = store.leaf(h)
        if isinstance(e, W_Const):
            decl = self._leaf_decl(h, e)
            if decl is None:
                decl = get_decl(tc.declarations, e.name)
            tc.check_reference(e, decl)
            if e.has_level_param():
                for lvl in e.levels:
                    if lvl.has_param:
                        tc.check_level(lvl)
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
            elif (self._can_perm
                    and decl.safety == SAFETY_SAFE
                    and decl.index >= 0
                    and decl.index < tc.decl.index):
                store.leaf_checked[j] = _u32(_CHECKED_PERM)
            else:
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
        elif isinstance(e, W_Sort):
            if e.level.has_param:
                tc.check_level(e.level)
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
            else:
                store.leaf_checked[j] = _u32(_CHECKED_PERM)
        elif isinstance(e, W_LitNat) or isinstance(e, W_LitStr):
            store.leaf_checked[j] = _u32(_CHECKED_PERM)
        else:
            store.leaf_checked[j] = _u32(self.check_gen)
            self._saw_nonperm = True
        return t

    @dont_inline
    def _infer_leaf(self, h, check):
        store = self.store
        tc = self.tc
        j = leaf_index(h)
        e = store.leaf(h)
        if isinstance(e, W_Const):
            decl = self._leaf_decl(h, e)
            if decl is None:
                decl = get_decl(tc.declarations, e.name)
            if check:
                tc.check_reference(e, decl)
                if e.has_level_param():
                    for lvl in e.levels:
                        if lvl.has_param:
                            tc.check_level(lvl)
                    store.leaf_checked[j] = _u32(self.check_gen)
                    self._saw_nonperm = True
                elif (self._can_perm
                        and decl.safety == SAFETY_SAFE
                        and decl.index >= 0
                        and decl.index < tc.decl.index):
                    store.leaf_checked[j] = _u32(_CHECKED_PERM)
                else:
                    store.leaf_checked[j] = _u32(self.check_gen)
                    self._saw_nonperm = True
            t = store.import_const_term(e, decl, decl.type)
        elif isinstance(e, W_Sort):
            if check:
                if e.level.has_param:
                    tc.check_level(e.level)
                    store.leaf_checked[j] = _u32(self.check_gen)
                    self._saw_nonperm = True
                else:
                    store.leaf_checked[j] = _u32(_CHECKED_PERM)
            t = store.leaf_for(e.level.succ().sort())
        elif isinstance(e, W_LitNat):
            t = self.h_nat
            store.leaf_checked[j] = _u32(_CHECKED_PERM)
        elif isinstance(e, W_LitStr):
            t = self.h_string
            store.leaf_checked[j] = _u32(_CHECKED_PERM)
        elif isinstance(e, W_FVar):
            t = store.import_term(e.binder.type)
            store.leaf_checked[j] = _u32(self.check_gen)
            if check:
                self._saw_nonperm = True
        else:
            raise LooseBoundVariable((_s32(store.leaf_meta[j]) >> 1) - 1)
        store.leaf_infer[j] = _u32(t)
        return t

    def _ensure_sort(self, h, check):
        """The level of the sort ``h`` has as its type."""
        t = self.infer(h, check)
        t_whnf = self.whnf(t)
        sort = self.store.sort_leaf(t_whnf)
        if sort is None:
            raise W_NotASort(self.tc, self.export(h), inferred_type=self.export(t))
        return sort.level

    def _infer_app(self, h, check, expected=0, exp_start=0, exp_n=0):
        store = self.store
        tc = self.tc
        fn = store.field_a(h)
        if store.kind(fn) != KIND_APP:
            arg = store.field_b(h)
            if is_leaf(fn):
                j = leaf_index(fn)
                fn_type = _s32(store.leaf_infer[j])
                if fn_type == 0 or fn_type == _LEAF_INFER_SEEN:
                    if not check:
                        return self._infer_app1_only_leaf(fn, j, arg)
                    if fn_type == 0 and not self._def_eq_hooked:
                        e = store.leaves[j]
                        if isinstance(e, W_Const):
                            store.leaf_infer[j] = _u32(_LEAF_INFER_SEEN)
                            return self._infer_app1_const_ast(
                                fn, j, e, arg, expected, exp_start, exp_n,
                            )
                    fn_type = self._infer_leaf(fn, True)
                elif check:
                    cg = _s32(store.leaf_checked[j])
                    if cg < self.check_gen:
                        fn_type = self._check_leaf(fn, fn_type)
                    elif cg != _CHECKED_PERM:
                        self._saw_nonperm = True
            else:
                fn_type = self.infer(fn, check)
            if store.kind(fn_type) != KIND_FORALL:
                fn_type = self.whnf(fn_type)
                if store.kind(fn_type) != KIND_FORALL:
                    raise W_NotAFunction(
                        tc, self.export(fn), inferred_type=self.export(fn_type),
                    )
            if check:
                domain = store.field_a(fn_type)
                arg_type = self.infer_expected(arg, domain)
                tracing = tc.tracer.recording
                if tracing:
                    tc.tracer.begin_argcheck()
                ok = self.def_eq(domain, arg_type)
                if tracing:
                    tc.tracer.end_argcheck(self._head_label(fn), 0)
                if not ok:
                    raise W_TypeError(
                        tc, self.export(arg), self.export(domain),
                        inferred_type=self.export(arg_type),
                    )
            body = store.field_b(fn_type)
            if store.loose_bvar_range(body) == 0:
                return body
            if is_leaf(body):
                bid = (_s32(store.leaf_meta[leaf_index(body)]) >> 1) - 1
                return arg if bid == 0 else store.bvar(bid - 1)
            if expected != 0 and not self._def_eq_hooked:
                if exp_n == 0:
                    if not is_leaf(expected):
                        sm = store._spine_top
                        store.spine_push(arg)
                        ok_exp = store.inst_eq_buf(body, sm, 1, expected)
                        store.unapp_pop(sm)
                        if ok_exp:
                            return expected
                else:
                    sm = store._spine_top
                    store.spine_push(arg)
                    ok_exp = store.inst_eq_inst_buf(
                        body, sm, 1, expected, exp_start, exp_n,
                    )
                    store.unapp_pop(sm)
                    if ok_exp:
                        return 0
            return store.instantiate(body, arg, 0)
        mark = store._spine_top
        head = store.unapp_push(h)
        try:
            n = store._spine_top - mark
            if not check:
                if is_leaf(head):
                    j = leaf_index(head)
                    fn_type = _s32(store.leaf_infer[j])
                    if fn_type == 0 or fn_type == _LEAF_INFER_SEEN:
                        return self._infer_app_only_leaf_buf(head, j, mark, n)
                    return self._infer_app_only_buf(head, mark, n, fn_type, n)
                fn_type = self.infer(head, False)
                return self._infer_app_only_buf(head, mark, n, fn_type, n)
            if is_leaf(head):
                j = leaf_index(head)
                fn_type = _s32(store.leaf_infer[j])
                if fn_type == 0 or fn_type == _LEAF_INFER_SEEN:
                    if fn_type == 0 and not self._def_eq_hooked:
                        e = store.leaves[j]
                        if isinstance(e, W_Const):
                            store.leaf_infer[j] = _u32(_LEAF_INFER_SEEN)
                            return self._infer_app_const_ast_buf(
                                head, j, e, mark, n, expected, exp_start, exp_n,
                            )
                    fn_type = self._infer_leaf(head, True)
                else:
                    cg = _s32(store.leaf_checked[j])
                    if cg < self.check_gen:
                        fn_type = self._check_leaf(head, fn_type)
                    elif cg != _CHECKED_PERM:
                        self._saw_nonperm = True
            else:
                fn_type = self.infer(head, True)
            return self._infer_app_rem_buf(
                head, mark, n, n - 1, 0, fn_type, expected, exp_start, exp_n,
            )
        finally:
            store.unapp_pop(mark)

    def _infer_app_rem_buf(self, head, mark, n, start_i, plen, fn_type,
                           expected, exp_start, exp_n):
        """Check arguments ``start_i .. 0`` of ``head`` (sitting at
        `_spine_buf[mark:mark+n]`) against the imported type handle ``fn_type``
        with ``plen`` pending substitutions."""
        store = self.store
        tc = self.tc
        i = start_i
        while i >= 0:
            arg = store.spine_arg(mark + i)
            if store.kind(fn_type) != KIND_FORALL:
                if plen > 0:
                    if plen == 1:
                        fn_type = store.instantiate(
                            fn_type, store.spine_arg(mark + i + 1), 0,
                        )
                    else:
                        fn_type = store.instantiate_multi_buf(
                            fn_type, mark + i + 1, plen, 0,
                        )
                    plen = 0
                fn_type = self.whnf(fn_type)
                if store.kind(fn_type) != KIND_FORALL:
                    self._not_a_function_buf(head, mark, n, i, fn_type)
            domain = store.field_a(fn_type)
            if plen == 0 or store.loose_bvar_range(domain) == 0:
                arg_type = self.infer_expected(arg, domain)
            elif is_leaf(domain):
                bid = (_s32(store.leaf_meta[leaf_index(domain)]) >> 1) - 1
                if bid < plen:
                    domain = store.spine_arg(mark + i + 1 + bid)
                else:
                    domain = store.bvar(bid - plen)
                arg_type = self.infer_expected(arg, domain)
            else:
                if not self._def_eq_hooked and not is_leaf(arg):
                    ak = _s32(store.recs[rec_index(arg) << 2]) & _KIND_MASK
                    if ak == KIND_APP:
                        arg_type = self._infer_app_expected_pat(
                            arg, domain, mark + i + 1, plen,
                        )
                    elif ak == KIND_LAMBDA and store.kind(domain) == KIND_FORALL:
                        arg_type = self._infer_lambda_expected_pat(
                            arg, domain, mark + i + 1, plen,
                        )
                    elif ak == KIND_LET:
                        arg_type = self._infer_let_expected_pat(
                            arg, domain, mark + i + 1, plen,
                        )
                    else:
                        arg_type = self.infer(arg, True)
                    if arg_type == 0:
                        fn_type = store.field_b(fn_type)
                        if store.loose_bvar_range(fn_type) == 0:
                            plen = 0
                        else:
                            plen += 1
                        i -= 1
                        continue
                else:
                    arg_type = self.infer(arg, True)
                if (not is_leaf(arg_type)
                        and not self._def_eq_hooked
                        and store.inst_eq_buf(domain, mark + i + 1, plen, arg_type)):
                    fn_type = store.field_b(fn_type)
                    if store.loose_bvar_range(fn_type) == 0:
                        plen = 0
                    else:
                        plen += 1
                    i -= 1
                    continue
                if plen == 1:
                    domain = store.instantiate(
                        domain, store.spine_arg(mark + i + 1), 0,
                    )
                else:
                    domain = store.instantiate_multi_buf(
                        domain, mark + i + 1, plen, 0,
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
                plen = 0
            else:
                plen += 1
            i -= 1
        if plen > 0:
            if is_leaf(fn_type):
                bid = (_s32(store.leaf_meta[leaf_index(fn_type)]) >> 1) - 1
                return store.spine_arg(mark + bid) if bid < plen else store.bvar(bid - plen)
            if expected != 0 and not self._def_eq_hooked:
                if exp_n == 0:
                    if (not is_leaf(expected)
                            and store.inst_eq_buf(fn_type, mark, plen, expected)):
                        return expected
                elif store.inst_eq_inst_buf(
                        fn_type, mark, plen, expected, exp_start, exp_n):
                    return 0
            if plen == 1:
                fn_type = store.instantiate(fn_type, store.spine_arg(mark), 0)
            else:
                fn_type = store.instantiate_multi_buf(fn_type, mark, plen, 0)
        return fn_type

    @dont_inline
    def _infer_app1_const_ast(self, fn, j, e, arg, expected, exp_start, exp_n):
        """Check 1-arg application ``fn arg`` directly on ``decl.type`` AST
        when ``fn`` is an unimported `W_Const` leaf (``leaf_infer[j] == 0``),
        avoiding importing unused binder domains and `KIND_FORALL` records."""
        store = self.store
        tc = self.tc
        decl = self._leaf_decl(fn, e)
        if decl is None:
            decl = get_decl(tc.declarations, e.name)
        cg = _s32(store.leaf_checked[j])
        if cg < self.check_gen:
            tc.check_reference(e, decl)
            if e.has_level_param():
                for lvl in e.levels:
                    if lvl.has_param:
                        tc.check_level(lvl)
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
            elif (self._can_perm
                    and decl.safety == SAFETY_SAFE
                    and decl.index >= 0
                    and decl.index < tc.decl.index):
                store.leaf_checked[j] = _u32(_CHECKED_PERM)
            else:
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
        elif cg != _CHECKED_PERM:
            self._saw_nonperm = True
        dt = decl.type
        if not isinstance(dt, W_ForAll):
            fn_type = store.import_const_term(e, decl, dt)
            store.leaf_infer[j] = _u32(fn_type)
            fn_type = self.whnf(fn_type)
            if store.kind(fn_type) != KIND_FORALL:
                raise W_NotAFunction(
                    tc, self.export(fn), inferred_type=self.export(fn_type),
                )
            domain = store.field_a(fn_type)
            arg_type = self.infer_expected(arg, domain)
            tracing = tc.tracer.recording
            if tracing:
                tc.tracer.begin_argcheck()
            ok = self.def_eq(domain, arg_type)
            if tracing:
                tc.tracer.end_argcheck(self._head_label(fn), 0)
            if not ok:
                raise W_TypeError(
                    tc, self.export(arg), self.export(domain),
                    inferred_type=self.export(arg_type),
                )
            body = store.field_b(fn_type)
            if store.loose_bvar_range(body) == 0:
                return body
            if is_leaf(body):
                bid = (_s32(store.leaf_meta[leaf_index(body)]) >> 1) - 1
                return arg if bid == 0 else store.bvar(bid - 1)
            return store.instantiate(body, arg, 0)
        params = decl.levels
        clevels = e.levels
        dom_ast = dt.binder.type
        matched = False
        if (not is_leaf(arg)
                and (_s32(store.recs[rec_index(arg) << 2]) & _KIND_MASK) == KIND_LAMBDA
                and isinstance(dom_ast, W_ForAll)):
            domain = store.import_const_term(e, decl, dom_ast)
            arg_type = self.infer_expected(arg, domain)
        else:
            arg_type = self.infer(arg, True)
            if store.ast_inst_eq_buf(dom_ast, params, clevels, 0, 0, arg_type):
                matched = True
            else:
                domain = store.import_const_term(e, decl, dom_ast)
        if not matched:
            tracing = tc.tracer.recording
            if tracing:
                tc.tracer.begin_argcheck()
            ok = self.def_eq(domain, arg_type)
            if tracing:
                tc.tracer.end_argcheck(self._head_label(fn), 0)
            if not ok:
                raise W_TypeError(
                    tc, self.export(arg), self.export(domain),
                    inferred_type=self.export(arg_type),
                )
        body_ast = dt.body
        if body_ast.loose_bvar_range() == 0:
            if expected != 0 and exp_n == 0:
                if store.ast_inst_eq_buf(body_ast, params, clevels, 0, 0, expected):
                    return expected
            return store.import_const_term(e, decl, body_ast)
        if body_ast.__class__ is W_BVar:
            assert isinstance(body_ast, W_BVar)
            return arg if body_ast.id == 0 else store.bvar(body_ast.id - 1)
        if expected != 0 and exp_n == 0:
            sm = store._spine_top
            store.spine_push(arg)
            ok_exp = store.ast_inst_eq_buf(body_ast, params, clevels, sm, 1, expected)
            store.unapp_pop(sm)
            if ok_exp:
                return expected
        body = store.import_const_term(e, decl, body_ast)
        if expected != 0 and exp_n > 0:
            sm = store._spine_top
            store.spine_push(arg)
            ok_exp = store.inst_eq_inst_buf(
                body, sm, 1, expected, exp_start, exp_n,
            )
            store.unapp_pop(sm)
            if ok_exp:
                return 0
        return store.instantiate(body, arg, 0)

    @dont_inline
    def _infer_app_const_ast_buf(self, head, j, e, mark, n,
                                 expected, exp_start, exp_n):
        """Check multi-arg application ``head args`` (at `_spine_buf[mark:mark+n]`)
        directly on ``decl.type`` AST when ``head`` is an unimported `W_Const`
        leaf (``leaf_infer[j] == 0``), verifying binder domains structurally via
        `ast_inst_eq_buf` so matched domains and `KIND_FORALL` records are never
        imported into `TermStore`."""
        store = self.store
        tc = self.tc
        decl = self._leaf_decl(head, e)
        if decl is None:
            decl = get_decl(tc.declarations, e.name)
        cg = _s32(store.leaf_checked[j])
        if cg < self.check_gen:
            tc.check_reference(e, decl)
            if e.has_level_param():
                for lvl in e.levels:
                    if lvl.has_param:
                        tc.check_level(lvl)
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
            elif (self._can_perm
                    and decl.safety == SAFETY_SAFE
                    and decl.index >= 0
                    and decl.index < tc.decl.index):
                store.leaf_checked[j] = _u32(_CHECKED_PERM)
            else:
                store.leaf_checked[j] = _u32(self.check_gen)
                self._saw_nonperm = True
        elif cg != _CHECKED_PERM:
            self._saw_nonperm = True
        cur = decl.type
        if not isinstance(cur, W_ForAll):
            fn_type = store.import_const_term(e, decl, cur)
            store.leaf_infer[j] = _u32(fn_type)
            return self._infer_app_rem_buf(
                head, mark, n, n - 1, 0, fn_type, expected, exp_start, exp_n,
            )
        params = decl.levels
        clevels = e.levels
        plen = 0
        i = n - 1
        while i >= 0:
            if not isinstance(cur, W_ForAll):
                fn_type = store.import_const_term(e, decl, cur)
                return self._infer_app_rem_buf(
                    head, mark, n, i, plen, fn_type, expected, exp_start, exp_n,
                )
            arg = store.spine_arg(mark + i)
            dom_ast = cur.binder.type
            if plen > 0 and dom_ast.__class__ is W_BVar:
                assert isinstance(dom_ast, W_BVar)
                bid = dom_ast.id
                if bid < plen:
                    domain = store.spine_arg(mark + i + 1 + bid)
                else:
                    domain = store.bvar(bid - plen)
                arg_type = self.infer_expected(arg, domain)
            elif (not is_leaf(arg)
                    and (_s32(store.recs[rec_index(arg) << 2]) & _KIND_MASK) == KIND_LAMBDA
                    and isinstance(dom_ast, W_ForAll)):
                dom_h = store.import_const_term(e, decl, dom_ast)
                if plen == 0 or store.loose_bvar_range(dom_h) == 0:
                    domain = dom_h
                    arg_type = self.infer_expected(arg, domain)
                else:
                    arg_type = self._infer_lambda_expected_pat(
                        arg, dom_h, mark + i + 1, plen,
                    )
                    if arg_type == 0:
                        cur = cur.body
                        if cur.loose_bvar_range() == 0:
                            plen = 0
                        else:
                            plen += 1
                        i -= 1
                        continue
                    if (not is_leaf(arg_type)
                            and store.inst_eq_buf(dom_h, mark + i + 1, plen, arg_type)):
                        cur = cur.body
                        if cur.loose_bvar_range() == 0:
                            plen = 0
                        else:
                            plen += 1
                        i -= 1
                        continue
                    if plen == 1:
                        domain = store.instantiate(
                            dom_h, store.spine_arg(mark + i + 1), 0,
                        )
                    else:
                        domain = store.instantiate_multi_buf(
                            dom_h, mark + i + 1, plen, 0,
                        )
            elif plen == 0 or dom_ast.loose_bvar_range() == 0:
                arg_type = self.infer(arg, True)
                if store.ast_inst_eq_buf(dom_ast, params, clevels, mark + i + 1, 0, arg_type):
                    cur = cur.body
                    if cur.loose_bvar_range() == 0:
                        plen = 0
                    else:
                        plen += 1
                    i -= 1
                    continue
                domain = store.import_const_term(e, decl, dom_ast)
            else:
                arg_type = self.infer(arg, True)
                if store.ast_inst_eq_buf(dom_ast, params, clevels, mark + i + 1, plen, arg_type):
                    cur = cur.body
                    if cur.loose_bvar_range() == 0:
                        plen = 0
                    else:
                        plen += 1
                    i -= 1
                    continue
                dom_h = store.import_const_term(e, decl, dom_ast)
                if plen == 1:
                    domain = store.instantiate(
                        dom_h, store.spine_arg(mark + i + 1), 0,
                    )
                else:
                    domain = store.instantiate_multi_buf(
                        dom_h, mark + i + 1, plen, 0,
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
            cur = cur.body
            if cur.loose_bvar_range() == 0:
                plen = 0
            else:
                plen += 1
            i -= 1
        if plen > 0 and cur.__class__ is W_BVar:
            assert isinstance(cur, W_BVar)
            bid = cur.id
            return store.spine_arg(mark + bid) if bid < plen else store.bvar(bid - plen)
        if expected != 0 and exp_n == 0:
            if store.ast_inst_eq_buf(cur, params, clevels, mark, plen, expected):
                return expected
        fn_type = store.import_const_term(e, decl, cur)
        if plen > 0:
            if expected != 0 and exp_n > 0:
                if store.inst_eq_inst_buf(
                        fn_type, mark, plen, expected, exp_start, exp_n):
                    return 0
            if plen == 1:
                fn_type = store.instantiate(fn_type, store.spine_arg(mark), 0)
            else:
                fn_type = store.instantiate_multi_buf(fn_type, mark, plen, 0)
        return fn_type

    @dont_inline
    def _infer_app1_only_leaf(self, fn, j, arg):
        """Infer the type of ``fn arg`` in ``check=False`` mode when ``fn`` is
        a leaf with ``leaf_infer[j] == 0``. Peels a leading ``W_ForAll`` on
        ``decl.type`` before importing so its unused domain is never imported."""
        store = self.store
        e = store.leaves[j]
        if isinstance(e, W_Const):
            decl = self._leaf_decl(fn, e)
            if decl is None:
                decl = get_decl(self.tc.declarations, e.name)
            dt = decl.type
            if isinstance(dt, W_ForAll):
                cur = dt.body
                if isinstance(cur, W_BVar):
                    bid = cur.id
                    return arg if bid == 0 else store.bvar(bid - 1)
                body = store.import_const_term(e, decl, cur)
                if store.loose_bvar_range(body) == 0:
                    return body
                return store.instantiate(body, arg, 0)
        fn_type = self._infer_leaf(fn, False)
        if store.kind(fn_type) != KIND_FORALL:
            fn_type = self.whnf(fn_type)
            if store.kind(fn_type) != KIND_FORALL:
                raise W_NotAFunction(
                    self.tc, self.export(fn), inferred_type=self.export(fn_type),
                )
        body = store.field_b(fn_type)
        if store.loose_bvar_range(body) == 0:
            return body
        if is_leaf(body):
            bid = (_s32(store.leaf_meta[leaf_index(body)]) >> 1) - 1
            return arg if bid == 0 else store.bvar(bid - 1)
        return store.instantiate(body, arg, 0)

    @dont_inline
    def _infer_app_only_leaf_buf(self, head, j, mark, n):
        """Infer the type of ``head args`` (with ``args`` at
        `_spine_buf[mark:mark+n]`) in ``check=False`` mode when ``head`` is a
        leaf with ``leaf_infer[j] == 0``. Strips up to ``n`` leading
        ``W_ForAll`` binders on ``decl.type`` before importing so unused binder
        domains are never imported into the store."""
        store = self.store
        e = store.leaves[j]
        if isinstance(e, W_Const):
            decl = self._leaf_decl(head, e)
            if decl is None:
                decl = get_decl(self.tc.declarations, e.name)
            cur = decl.type
            k = 0
            while k < n and isinstance(cur, W_ForAll):
                cur = cur.body
                k += 1
            if k > 0:
                if k == n:
                    if isinstance(cur, W_BVar):
                        bid = cur.id
                        return (
                            store.spine_arg(mark + bid)
                            if bid < n
                            else store.bvar(bid - n)
                        )
                    fn_type = store.import_const_term(e, decl, cur)
                    if store.loose_bvar_range(fn_type) == 0:
                        return fn_type
                    if n == 1:
                        return store.instantiate(
                            fn_type, store.spine_arg(mark), 0,
                        )
                    return store.instantiate_multi_buf(fn_type, mark, n, 0)
                rem = n - k
                if isinstance(cur, W_BVar):
                    bid = cur.id
                    fn_type = (
                        store.spine_arg(mark + rem + bid)
                        if bid < k
                        else store.bvar(bid - k)
                    )
                else:
                    fn_type = store.import_const_term(e, decl, cur)
                    if store.loose_bvar_range(fn_type) > 0:
                        if k == 1:
                            fn_type = store.instantiate(
                                fn_type, store.spine_arg(mark + rem), 0,
                            )
                        else:
                            fn_type = store.instantiate_multi_buf(
                                fn_type, mark + rem, k, 0,
                            )
                return self._infer_app_only_buf(head, mark, n, fn_type, rem)
        fn_type = self._infer_leaf(head, False)
        return self._infer_app_only_buf(head, mark, n, fn_type, n)

    def _infer_app_only_buf(self, head, mark, n, fn_type, rem):
        """
        The type of ``head args`` (with ``args`` at `_spine_buf[mark:mark+n]`)
        given ``head``'s type after stripping the first ``n - rem`` arguments,
        trusting the arguments.
        """
        store = self.store
        plen = 0
        i = rem - 1
        while i >= 0:
            if store.kind(fn_type) != KIND_FORALL:
                if plen > 0:
                    if plen == 1:
                        fn_type = store.instantiate(
                            fn_type, store.spine_arg(mark + i + 1), 0,
                        )
                    else:
                        fn_type = store.instantiate_multi_buf(
                            fn_type, mark + i + 1, plen, 0,
                        )
                    plen = 0
                fn_type = self.whnf(fn_type)
                if store.kind(fn_type) != KIND_FORALL:
                    self._not_a_function_buf(head, mark, n, i, fn_type)
            fn_type = store.field_b(fn_type)
            if store.loose_bvar_range(fn_type) == 0:
                plen = 0
            else:
                plen += 1
            i -= 1
        if plen > 0:
            if is_leaf(fn_type):
                bid = (_s32(store.leaf_meta[leaf_index(fn_type)]) >> 1) - 1
                return store.spine_arg(mark + bid) if bid < plen else store.bvar(bid - plen)
            if plen == 1:
                fn_type = store.instantiate(fn_type, store.spine_arg(mark), 0)
            else:
                fn_type = store.instantiate_multi_buf(fn_type, mark, plen, 0)
        return fn_type

    def _not_a_function_buf(self, head, mark, n, i, fn_type):
        store = self.store
        spine = head
        j = n - 1
        while j > i:
            spine = store.cons_app(spine, store.spine_arg(mark + j))
            j -= 1
        raise W_NotAFunction(
            self.tc, self.export(spine), inferred_type=self.export(fn_type),
        )

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

    def _infer_lambda(self, h, check):
        store = self.store
        body = store.field_b(h)
        if store.kind(body) != KIND_LAMBDA:
            domain = store.field_a(h)
            if check:
                self._ensure_sort(domain, True)
            fvar = self.fvar_for_domain(h, domain)
            if store.loose_bvar_range(body) > 0:
                body = store.instantiate(body, fvar, 0)
            r = self._cheap_beta(self.infer(body, check))
            r = store.bind_fvar(r, fvar, 0)
            return store.cons(KIND_FORALL, domain, r, store.info(h))
        records = []
        fvars = []
        reused_at = -1
        reused_domains = None
        e = h
        while store.kind(e) == KIND_LAMBDA:
            orig_d = store.field_a(e)
            idx = len(fvars)
            if idx > 0 and store.loose_bvar_range(orig_d) > 0:
                if is_leaf(orig_d):
                    bid = (_s32(store.leaf_meta[leaf_index(orig_d)]) >> 1) - 1
                    domain = fvars[idx - 1 - bid] if bid < idx else store.bvar(bid - idx)
                else:
                    domain = store.instantiate_multi_rev(orig_d, fvars, idx, 0)
            else:
                domain = orig_d
            if check:
                self._ensure_sort(domain, True)
            if reused_at >= 0:
                assert reused_domains is not None
                reused_domains.append(domain)
            fvar = self.fvar_for_domain(e, domain)
            if self._fvar_reused and reused_at < 0:
                reused_at = idx
                reused_domains = []
            records.append(e)
            fvars.append(fvar)
            e = store.field_b(e)
        n = len(fvars)
        body = store.instantiate_multi_rev(e, fvars, n, 0)
        r = self._cheap_beta(self.infer(body, check))
        # Close the telescope back up as a Pi: the body type over all
        # the variables; each binder's original domain is already closed over
        # earlier binders whenever earlier fvars were fresh (or domain has no fvars).
        r = store.bind_fvars(r, fvars, 0, n)
        i = n - 1
        while i >= 0:
            rec = records[i]
            orig_d = store.field_a(rec)
            if reused_at >= 0 and i > reused_at and store.has_fvar(orig_d):
                assert reused_domains is not None
                domain = store.bind_fvars(
                    reused_domains[i - reused_at - 1], fvars, 0, i,
                )
            else:
                domain = orig_d
            r = store.cons(KIND_FORALL, domain, r, store.info(rec))
            i -= 1
        return r

    def _infer_forall(self, h, check):
        store = self.store
        body = store.field_b(h)
        if store.kind(body) != KIND_FORALL:
            domain = store.field_a(h)
            l1 = self._ensure_sort(domain, check)
            if store.loose_bvar_range(body) > 0:
                fvar = self.fvar_for_domain(h, domain)
                body = store.instantiate(body, fvar, 0)
            l2 = self._ensure_sort(body, check)
            return store.leaf_for(l1.imax(l2).sort())
        levels = []
        fvars = []
        e = h
        while store.kind(e) == KIND_FORALL:
            orig_d = store.field_a(e)
            nf = len(fvars)
            if nf > 0 and store.loose_bvar_range(orig_d) > 0:
                if is_leaf(orig_d):
                    bid = (_s32(store.leaf_meta[leaf_index(orig_d)]) >> 1) - 1
                    domain = fvars[nf - 1 - bid] if bid < nf else store.bvar(bid - nf)
                else:
                    domain = store.instantiate_multi_rev(orig_d, fvars, nf, 0)
            else:
                domain = orig_d
            levels.append(self._ensure_sort(domain, check))
            nxt = store.field_b(e)
            if store.loose_bvar_range(nxt) == 0:
                if nf > 0:
                    fvars = []
            else:
                fvars.append(self.fvar_for_domain(e, domain))
            e = nxt
        nf = len(fvars)
        if nf > 0 and store.loose_bvar_range(e) > 0:
            e = store.instantiate_multi_rev(e, fvars, nf, 0)
        level = self._ensure_sort(e, check)
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
        head = store.head(h)
        if store.kind(head) != KIND_LAMBDA:
            return h
        mark = store._spine_top
        store.unapp_push(h)
        try:
            n = store._spine_top - mark
            i = 0
            fn = head
            while store.kind(fn) == KIND_LAMBDA and i < n:
                i += 1
                fn = store.field_b(fn)
            if store.loose_bvar_range(fn) == 0:
                return store.apply_buf_rev(fn, mark, n - 1 - i)
            idx = store.bvar_id(fn)
            if idx >= 0 and idx < i:
                return store.apply_buf_rev(
                    store.spine_arg(mark + n - 1 - (i - 1 - idx)),
                    mark, n - 1 - i,
                )
            return h
        finally:
            store.unapp_pop(mark)

    def _infer_let(self, h, check):
        store = self.store
        type_h = store.field_a(h)
        pair = store.field_b(h)
        value = store.field_a(pair)
        body = store.field_b(pair)
        if check:
            self._ensure_sort(type_h, True)
            value_type = self.infer_expected(value, type_h)
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
        tmark = store._spine_top
        type_head = store.unapp_push(struct_type)
        try:
            nt = store._spine_top - tmark
            head_const = store.const_leaf(type_head)
            if head_const is not None and head_const.is_named(struct_name):
                struct_decl = self._leaf_decl(type_head, head_const)
            else:
                struct_decl = find_decl(tc.declarations, struct_name)
            if struct_decl is None:
                raise InvalidProjection.unknown_structure(
                    struct_name, field_index,
                    self.export(self._materialize(struct, ctx, chain)),
                )
            if head_const is None:
                raise InvalidProjection.not_a_structure_type(
                    struct_name, field_index,
                    self.export(self._materialize(struct, ctx, chain)),
                )
            if not head_const.is_named(struct_name):
                raise InvalidProjection.mismatched_structure(
                    struct_name, field_index, head_const.name,
                    self.export(self._materialize(struct, ctx, chain)),
                )
            struct_kind = struct_decl.w_kind
            if not isinstance(struct_kind, W_Inductive):
                raise InvalidProjection.not_an_inductive(
                    struct_name, field_index,
                    self.export(self._materialize(struct, ctx, chain)),
                )
            if len(struct_kind.ctor_names) != 1:
                raise InvalidProjection.not_a_structure(
                    struct_name, field_index, len(struct_kind.ctor_names),
                    self.export(self._materialize(struct, ctx, chain)),
                )
            stype = struct_decl.type
            if isinstance(stype, W_ForAll):
                is_prop_type = False
            elif isinstance(stype, W_Sort):
                if not stype.has_level_param():
                    is_prop_type = stype.level.eq(W_LEVEL_ZERO)
                elif len(head_const.levels) == len(struct_decl.levels):
                    lvl = _subst_level_fast(
                        stype.level, struct_decl.levels, head_const.levels,
                    )
                    is_prop_type = lvl.eq(W_LEVEL_ZERO)
                else:
                    ind_type = self.whnf(
                        store.import_const_term(head_const, struct_decl, stype),
                    )
                    ind_sort = store.sort_leaf(ind_type)
                    is_prop_type = (
                        ind_sort is not None and ind_sort.level.eq(W_LEVEL_ZERO)
                    )
            else:
                ind_type = self.whnf(
                    store.import_const_term(head_const, struct_decl, stype),
                )
                ind_sort = store.sort_leaf(ind_type)
                is_prop_type = (
                    ind_sort is not None and ind_sort.level.eq(W_LEVEL_ZERO)
                )

            ctor_decl = struct_kind._proj_ctor
            if ctor_decl is None:
                ctor_decl = get_decl(tc.declarations, struct_kind.ctor_names[0])
                struct_kind.init_proj_cache(ctor_decl)
            fields = struct_kind._proj_fields
            if (not is_prop_type
                    and fields is not None
                    and nt == struct_kind.num_params
                    and 0 <= field_index < len(fields)
                    and len(head_const.levels) == len(ctor_decl.levels)):
                raw_ft = fields[field_index]
                if isinstance(raw_ft, W_BVar):
                    bid = raw_ft.id
                    if bid >= field_index and bid - field_index < nt:
                        return store.spine_arg(tmark + (bid - field_index))
                if raw_ft.loose_bvar_range() == 0:
                    return store.import_const_term(head_const, ctor_decl, raw_ft)
                ft_h = store.import_const_term(head_const, ctor_decl, raw_ft)
                if field_index == 0:
                    if nt == 0:
                        return ft_h
                    if nt == 1:
                        return store.instantiate(ft_h, store.spine_arg(tmark), 0)
                    return store.instantiate_multi_buf(ft_h, tmark, nt, 0)
                uses = struct_kind._proj_field_uses_earlier
                assert uses is not None
                mat_struct = 0
                if uses[field_index]:
                    mat_struct = self._materialize(struct, ctx, chain)
                base = store._spine_top
                j = field_index - 1
                while j >= 0:
                    if mat_struct != 0:
                        store.spine_push(store.proj(struct_name, j, mat_struct))
                    else:
                        store.spine_push(self.h_prop)
                    j -= 1
                j = 0
                while j < nt:
                    store.spine_push(store.spine_arg(tmark + j))
                    j += 1
                return store.instantiate_multi_buf(ft_h, base, field_index + nt, 0)

            ctor_type = store.import_const_term(
                head_const, ctor_decl, ctor_decl.type,
            )
            # Batch-instantiate leading type arguments left to right using `_spine_buf`.
            plen = 0
            i = nt - 1
            while i >= 0:
                if store.kind(ctor_type) != KIND_FORALL:
                    if plen > 0:
                        if plen == 1:
                            ctor_type = store.instantiate(
                                ctor_type, store.spine_arg(tmark + i + 1), 0,
                            )
                        else:
                            ctor_type = store.instantiate_multi_buf(
                                ctor_type, tmark + i + 1, plen, 0,
                            )
                        plen = 0
                    ctor_type = self.whnf(ctor_type)
                    if store.kind(ctor_type) != KIND_FORALL:
                        raise InvalidProjection.out_of_bounds(
                            struct_name, field_index, 0,
                            self.export(self._materialize(struct, ctx, chain)),
                        )
                ctor_type = store.field_b(ctor_type)
                if store.loose_bvar_range(ctor_type) == 0:
                    plen = 0
                else:
                    plen += 1
                i -= 1
            if plen > 0:
                if plen == 1:
                    ctor_type = store.instantiate(ctor_type, store.spine_arg(tmark), 0)
                else:
                    ctor_type = store.instantiate_multi_buf(ctor_type, tmark, plen, 0)
        finally:
            store.unapp_pop(tmark)
        mat_struct = 0
        i = -1
        for i in range(field_index):
            if store.kind(ctor_type) != KIND_FORALL:
                ctor_type = self.whnf(ctor_type)
                if store.kind(ctor_type) != KIND_FORALL:
                    raise InvalidProjection.out_of_bounds(
                        struct_name, field_index, i + 1,
                        self.export(self._materialize(struct, ctx, chain)),
                    )
            body = store.field_b(ctor_type)
            if store.loose_bvar_range(body) > 0:
                if is_prop_type:
                    if not self._is_prop(store.field_a(ctor_type), check):
                        raise InvalidProjection.non_prop_field(
                            struct_name, field_index,
                            self.export(self._materialize(struct, ctx, chain)),
                        )
                if mat_struct == 0:
                    mat_struct = self._materialize(struct, ctx, chain)
                ctor_type = store.instantiate(
                    body, store.proj(struct_name, i, mat_struct), 0,
                )
            else:
                ctor_type = body
        if store.kind(ctor_type) != KIND_FORALL:
            ctor_type = self.whnf(ctor_type)
            if store.kind(ctor_type) != KIND_FORALL:
                raise InvalidProjection.out_of_bounds(
                    struct_name, field_index, i + 1,
                    self.export(self._materialize(struct, ctx, chain)),
                )
        field_type = store.field_a(ctor_type)
        if is_prop_type:
            if not self._is_prop(field_type, check):
                raise InvalidProjection.non_prop_field(
                    struct_name, field_index,
                    self.export(self._materialize(struct, ctx, chain)),
                )
        return field_type

    def _is_prop(self, h, check):
        """Whether the type ``h`` lives in `Prop`."""
        sort = self.store.sort_leaf(self.whnf(self.infer(h, check)))
        return sort is not None and sort.level.eq(W_LEVEL_ZERO)

    # ---- definitional equality --------------------------------------------

    def _find(self, h):
        if self._eqv_count == 0:
            return h
        store = self.store
        parent = store.eqv_get(h)
        if parent == 0:
            return h
        root = parent
        while True:
            p = store.eqv_get(root)
            if p == 0:
                break
            root = p
        if parent != root:
            cur = h
            while cur != root:
                nxt = store.eqv_get(cur)
                store.eqv_set(cur, root)
                cur = nxt
        return root

    def _union(self, h1, h2):
        r1 = self._find(h1)
        r2 = self._find(h2)
        if r1 != r2:
            self.store.eqv_set(r1, r2)
            self._eqv_count += 1

    @staticmethod
    @always_inline
    def _pair_key(h1, h2):
        if (h1 | h2) >= (1 << 31):
            return 0
        return (h1 << 31) | h2

    @staticmethod
    @always_inline
    def _sym_pair_key(h1, h2):
        if (h1 | h2) >= (1 << 31):
            return 0
        return ((h1 << 31) | h2) if h1 < h2 else ((h2 << 31) | h1)

    def def_eq(self, h1, h2):
        """Whether ``h1`` and ``h2`` are definitionally equal."""
        if h1 == h2 and not self._def_eq_hooked:
            return True
        return self._def_eq_slow(h1, h2)

    @dont_inline
    def _def_eq_slow(self, h1, h2):
        if self._def_eq_hooked:
            return self._def_eq_hooked_slow(h1, h2)
        if self._eqv_count > 0 and self._find(h1) == self._find(h2):
            return True
        key = self._sym_pair_key(h1, h2)
        if self._neq.size > 0 and key != 0 and self._neq.contains(key):
            return False
        store = self.store
        if (self._eqv_count > 0
                and store.kind(h1) == KIND_APP
                and store.kind(h2) == KIND_APP):
            if self._spine_cheap_eq(h1, h2):
                self._union(h1, h2)
                return True
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("def_eq")
        result = self._def_eq_uncached(h1, h2)
        if result:
            self._union(h1, h2)
        elif key != 0:
            self._neq.add(key)
        return result

    @dont_inline
    def _def_eq_hooked_slow(self, h1, h2):
        tc = self.tc
        if tc.has_limits:
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
        if self._eqv_count > 0 and self._find(h1) == self._find(h2):
            if tracing:
                tracer.eqv_hit()
                return self._traced_result(True)
            return True
        key = self._sym_pair_key(h1, h2)
        if self._neq.size > 0 and key != 0 and self._neq.contains(key):
            if tracing:
                return self._traced_result(False)
            return False
        store = self.store
        if (self._eqv_count > 0
                and store.kind(h1) == KIND_APP
                and store.kind(h2) == KIND_APP):
            if self._spine_cheap_eq(h1, h2):
                self._union(h1, h2)
                if tracing:
                    tracer.eqv_hit()
                    return self._traced_result(True)
                return True
        tick = (self._stack_tick + 1) & 31
        self._stack_tick = tick
        if tick == 0:
            self._check_stack_slow("def_eq")
        result = self._def_eq_uncached(h1, h2)
        if result:
            self._union(h1, h2)
        elif key != 0:
            self._neq.add(key)
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

        status = self._try_lazy_delta(h1, h2)
        if status == _LD_TRUE:
            return True
        h1 = self._ld_h1
        h2 = self._ld_h2
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

    def _is_ctor_body_leaf(self, head):
        """Whether ``head`` (already known `_LF_DELTA`) is a `W_Definition`
        with a `_CtorBody` (so unfolding it in full inside `_proj_lazy_eq`
        would materialize unused sibling/proof fields instead of letting
        `try_proj` extract only the projected field lazily)."""
        j = leaf_index(head)
        e = self.store.leaves[j]
        if not isinstance(e, W_Const):
            return False
        decl = self._leaf_decl(head, e)
        if decl is None:
            return False
        wk = decl.w_kind
        if not isinstance(wk, W_Definition):
            return False
        cb = wk._ctor_body
        if cb is None:
            cb = wk.init_ctor_body(self.tc.declarations)
        return cb.m >= 0

    def _proj_lazy_eq(self, h1, h2, depth):
        """Bounded cheap definitional equality check for two projected
        structures (no full projection reduction, no unbounded recursion).
        Uses the shared step budget ``self._proj_rem`` across all recursive
        calls so wide Mathlib typeclass diamonds never branch exponentially."""
        store = self.store
        while True:
            if h1 == h2 or (self._eqv_count > 0 and self._find(h1) == self._find(h2)):
                return True
            h1 = self.whnf_core(h1, True)
            h2 = self.whnf_core(h2, True)
            if h1 == h2 or (self._eqv_count > 0 and self._find(h1) == self._find(h2)):
                return True
            head1 = store.head(h1)
            head2 = store.head(h2)
            if depth > 0 and self._same_const(head1, head2):
                m1 = store._spine_top
                store.unapp_push(h1)
                try:
                    n1 = store._spine_top - m1
                    m2 = store._spine_top
                    store.unapp_push(h2)
                    n2 = store._spine_top - m2
                    if n1 == n2:
                        all_eq = True
                        pmask = -1
                        j = n1 - 1
                        k = 0
                        while j >= 0:
                            a1 = store.spine_arg(m1 + j)
                            a2 = store.spine_arg(m2 + j)
                            if a1 != a2:
                                if pmask == -1:
                                    pmask = self._prop_mask_for(head1)
                                if k < 62 and (pmask & (1 << k)) != 0:
                                    j -= 1
                                    k += 1
                                    continue
                                if not self._proj_lazy_eq(a1, a2, depth - 1):
                                    all_eq = False
                                    break
                            j -= 1
                            k += 1
                        if all_eq:
                            self._union(h1, h2)
                            return True
                finally:
                    store.unapp_pop(m1)
            if self._proj_rem <= 0:
                return False
            f1 = self._leaf_flags(head1)
            f2 = self._leaf_flags(head2)
            d1 = (f1 & _LF_DELTA) != 0
            d2 = (f2 & _LF_DELTA) != 0
            if d1 and self._is_ctor_body_leaf(head1):
                d1 = False
            if d2 and self._is_ctor_body_leaf(head2):
                d2 = False
            if not d1 and not d2:
                return False
            self._proj_rem -= 1
            if not d1:
                new2 = self.try_unfold_head(h2)
                if new2 == 0:
                    return False
                h2 = new2
            elif not d2:
                new1 = self.try_unfold_head(h1)
                if new1 == 0:
                    return False
                h1 = new1
            else:
                e1 = f1 >> _LF_HINT_SHIFT
                e2 = f2 >> _LF_HINT_SHIFT
                hint1 = (e1 - 2) if e1 < _LF_HINT_OVF else self._delta_hint_slow(head1)
                hint2 = (e2 - 2) if e2 < _LF_HINT_OVF else self._delta_hint_slow(head2)
                if (hint1 == HINT_ABBREV and hint2 != HINT_ABBREV) or hint1 > hint2:
                    new1 = self.try_unfold_head(h1)
                    if new1 == 0:
                        return False
                    h1 = new1
                elif (hint2 == HINT_ABBREV and hint1 != HINT_ABBREV) or hint2 > hint1:
                    new2 = self.try_unfold_head(h2)
                    if new2 == 0:
                        return False
                    h2 = new2
                else:
                    new1 = self.try_unfold_head(h1)
                    new2 = self.try_unfold_head(h2)
                    if new1 == 0 and new2 == 0:
                        return False
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
                saved_rem = self._proj_rem
                self._proj_rem = 8
                ok = self._proj_lazy_eq(
                    store.field_a(h1), store.field_a(h2), 3,
                )
                self._proj_rem = saved_rem
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
                m1 = store._spine_top
                store.unapp_push(h1)
                saved_rem = self._proj_rem
                try:
                    n1 = store._spine_top - m1
                    m2 = store._spine_top
                    store.unapp_push(h2)
                    n2 = store._spine_top - m2
                    if n1 != n2:
                        return False
                    self._proj_rem = 8
                    if not self._proj_lazy_eq(
                        store.field_a(head1), store.field_a(head2), 3,
                    ):
                        self._cache_failure(head1, head2)
                        return False
                    self._union(head1, head2)
                    j = n1 - 1
                    while j >= 0:
                        a1 = store.spine_arg(m1 + j)
                        a2 = store.spine_arg(m2 + j)
                        if a1 != a2:
                            if not self._proj_lazy_eq(a1, a2, 2):
                                self._cache_failure(h1, h2)
                                return False
                        j -= 1
                    return True
                finally:
                    self._proj_rem = saved_rem
                    store.unapp_pop(m1)
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
            if self.tc.has_limits:
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

    def _is_closed_ite(self, h, flags):
        """Whether ``h`` is a fully-applied `ite`/`dite` whose `Decidable`
        instance argument is closed (no free variables), so unfolding it
        can take a branch without reducing an open condition."""
        if (flags & _LF_ITE) == 0:
            return False
        store = self.store
        if store.kind(h) != KIND_APP:
            return False
        mark = store._spine_top
        store.unapp_push(h)
        try:
            n = store._spine_top - mark
            if n < 5:
                return False
            inst_idx = n - 3
            assert inst_idx >= 0
            return not store.has_fvar(store.spine_arg(mark + inst_idx))
        finally:
            store.unapp_pop(mark)

    def _bool_arg0_reducible(self, fn):
        """Whether the first argument of a 2-arg boolean op ``(op a) b``
        is a concrete Bool constructor or a reducible boolean combinator."""
        store = self.store
        arg0 = store.field_b(fn)
        if arg0 == self.h_true or arg0 == self.h_false:
            return True
        return (self._leaf_flags(store.head(arg0)) & _LF_BOOL_ARG0) != 0

    def _try_lazy_delta(self, h1, h2):
        store = self.store
        for _ in range(self._LAZY_DELTA_MAX_ITER):
            if h1 == h2:
                return _LD_TRUE
            peeled = False
            while True:
                lit1 = store.litnat_leaf(h1)
                lit2 = store.litnat_leaf(h2)
                if lit1 is not None and lit2 is not None:
                    if lit1.val.eq(lit2.val):
                        return _LD_TRUE
                    break
                pred1 = self._nat_succ_pred(h1)
                if pred1 == 0:
                    break
                pred2 = self._nat_succ_pred(h2)
                if pred2 == 0:
                    break
                if self.tc.has_limits:
                    self.tc.tick_wall_time()
                h1 = pred1
                h2 = pred2
                peeled = True
            if peeled:
                h1 = self.whnf_core(h1, True)
                h2 = self.whnf_core(h2, True)
                if h1 == h2:
                    return _LD_TRUE

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
            f1 = self._leaf_flags(head1)
            f2 = self._leaf_flags(head2)
            d1 = (f1 & _LF_DELTA) != 0
            d2 = (f2 & _LF_DELTA) != 0
            if not d1 and not d2:
                self._ld_h1 = h1
                self._ld_h2 = h2
                return _LD_UNDEF

            if not d1:
                new2 = self._unfold_or_nat(h2)
                if new2 == 0:
                    self._ld_h1 = h1
                    self._ld_h2 = h2
                    return _LD_UNDEF
                if store.kind(head1) == KIND_PROJ:
                    c2 = self.whnf_core(new2, True)
                    if self._def_eq_proj_lazy(h1, c2):
                        return _LD_TRUE
                    h2 = self.whnf_core(c2)
                else:
                    h2 = self.whnf_core(new2)
                continue
            if not d2:
                new1 = self._unfold_or_nat(h1)
                if new1 == 0:
                    self._ld_h1 = h1
                    self._ld_h2 = h2
                    return _LD_UNDEF
                if store.kind(head2) == KIND_PROJ:
                    c1 = self.whnf_core(new1, True)
                    if self._def_eq_proj_lazy(c1, h2):
                        return _LD_TRUE
                    h1 = self.whnf_core(c1)
                else:
                    h1 = self.whnf_core(new1)
                continue

            e1 = f1 >> _LF_HINT_SHIFT
            e2 = f2 >> _LF_HINT_SHIFT
            hint1 = (e1 - 2) if e1 < _LF_HINT_OVF else self._delta_hint_slow(head1)
            hint2 = (e2 - 2) if e2 < _LF_HINT_OVF else self._delta_hint_slow(head2)
            if hint1 == HINT_ABBREV and hint2 != HINT_ABBREV:
                new1 = self._unfold_or_nat(h1)
                if new1 == 0:
                    self._ld_h1 = h1
                    self._ld_h2 = h2
                    return _LD_UNDEF
                h1 = self.whnf_core(new1)
                continue
            if hint2 == HINT_ABBREV and hint1 != HINT_ABBREV:
                new2 = self._unfold_or_nat(h2)
                if new2 == 0:
                    self._ld_h1 = h1
                    self._ld_h2 = h2
                    return _LD_UNDEF
                h2 = self.whnf_core(new2)
                continue

            # Unfold a closed-condition `ite`/`dite` before an unrelated
            # regular definition so taking a branch (e.g.
            # `if true = true then big else other = big`) resolves without
            # evaluating the taken branch.
            ite1 = self._is_closed_ite(h1, f1)
            ite2 = self._is_closed_ite(h2, f2)
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
                if ((f1 & _LF_SHORT_BOOL) != 0
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
                    m1 = store._spine_top
                    store.unapp_push(h1)
                    try:
                        n1 = store._spine_top - m1
                        m2 = store._spine_top
                        store.unapp_push(h2)
                        n2 = store._spine_top - m2
                        if n1 == n2:
                            if not self._failed_before(h1, h2):
                                all_eq = True
                                pmask = -1
                                j = n1 - 1
                                k = 0
                                while j >= 0:
                                    a1 = store.spine_arg(m1 + j)
                                    a2 = store.spine_arg(m2 + j)
                                    if a1 != a2:
                                        if pmask == -1:
                                            pmask = self._prop_mask_for(head1)
                                        if k < 62 and (pmask & (1 << k)) != 0:
                                            j -= 1
                                            k += 1
                                            continue
                                        if not self.def_eq(a1, a2):
                                            all_eq = False
                                            break
                                    elif self._def_eq_hooked:
                                        if not self.def_eq(a1, a2):
                                            all_eq = False
                                            break
                                    j -= 1
                                    k += 1
                                if all_eq:
                                    return _LD_TRUE
                                self._cache_failure(h1, h2)
                    finally:
                        store.unapp_pop(m1)

            # Unfold a regular non-Nat-binop definition before forcing native
            # Nat reduction on the other side's potentially expensive args
            # (e.g. `[slowA, 1].sum = slowA + (1 + 0)`).
            nat1 = (f1 & _LF_NAT_BINOP) != 0
            nat2 = (f2 & _LF_NAT_BINOP) != 0
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
                    self._ld_h1 = h1
                    self._ld_h2 = h2
                    return _LD_UNDEF
                h1 = self.whnf_core(new1)
                continue
            if hint1 < hint2:
                new2 = self._unfold_or_nat(h2)
                if new2 == 0:
                    self._ld_h1 = h1
                    self._ld_h2 = h2
                    return _LD_UNDEF
                h2 = self.whnf_core(new2)
                continue

            new1 = self._unfold_or_nat(h1)
            new2 = self._unfold_or_nat(h2)
            if new1 == 0 and new2 == 0:
                self._ld_h1 = h1
                self._ld_h2 = h2
                return _LD_UNDEF
            if new1 != 0 and new2 != 0:
                c1 = self.whnf_core(new1, True)
                c2 = self.whnf_core(new2, True)
                if c1 == c2 or self._def_eq_proj_lazy(c1, c2):
                    return _LD_TRUE
                h1 = self.whnf_core(c1)
                h2 = self.whnf_core(c2)
            elif new1 != 0:
                h1 = self.whnf_core(new1)
            elif new2 != 0:
                h2 = self.whnf_core(new2)
        self._ld_h1 = h1
        self._ld_h2 = h2
        return _LD_UNDEF

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
        key = self._sym_pair_key(h1, h2)
        return key != 0 and self._failed.contains(key)

    def _cache_failure(self, h1, h2):
        key = self._sym_pair_key(h1, h2)
        if key != 0:
            self._failed.add(key)

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
        if store.kind(fn1) != KIND_APP or store.kind(fn2) != KIND_APP:
            if not self.def_eq(fn1, fn2):
                return False
            a1 = store.field_b(h1)
            a2 = store.field_b(h2)
            if a1 != a2:
                pmask = self._prop_mask_for(fn1)
                if pmask == 0 and is_leaf(fn2):
                    pmask = self._prop_mask_for(fn2)
                if (pmask & 1) != 0:
                    return True
                return self.def_eq(a1, a2)
            if self._def_eq_hooked:
                return self.def_eq(a1, a2)
            return True
        mark = store._spine_top
        top = mark
        buf = store._spine_buf
        cap = store._spine_cap
        try:
            while store.kind(h1) == KIND_APP and store.kind(h2) == KIND_APP:
                if top + 2 > cap:
                    new_cap = cap * 2
                    buf = _grow_u32(buf, top, new_cap)
                    store._spine_buf = buf
                    store._spine_cap = new_cap
                    cap = new_cap
                buf[top] = _u32(store.field_b(h1))
                buf[top + 1] = _u32(store.field_b(h2))
                top += 2
                h1 = store.field_a(h1)
                h2 = store.field_a(h2)
            store._spine_top = top
            if not self.def_eq(h1, h2):
                return False
            pmask = -1
            i = top - 2
            k = 0
            while i >= mark:
                a1 = store.spine_arg(i)
                a2 = store.spine_arg(i + 1)
                if a1 != a2:
                    if pmask == -1:
                        pmask = self._prop_mask_for(h1)
                        if pmask == 0 and is_leaf(h2):
                            pmask = self._prop_mask_for(h2)
                    if k < 62 and (pmask & (1 << k)) != 0:
                        i -= 2
                        k += 1
                        continue
                    if not self.def_eq(a1, a2):
                        return False
                elif self._def_eq_hooked:
                    if not self.def_eq(a1, a2):
                        return False
                i -= 2
                k += 1
            return True
        finally:
            store.unapp_pop(mark)

    def _def_eq_binders(self, h1, h2):
        store = self.store
        kind = store.kind(h1)
        b1 = store.field_b(h1)
        b2 = store.field_b(h2)
        if store.kind(b1) != kind or store.kind(b2) != kind:
            if not self.def_eq(store.field_a(h1), store.field_a(h2)):
                return False
            if b1 == b2 and not self._def_eq_hooked:
                return True
            if store.loose_bvar_range(b1) == 0 and store.loose_bvar_range(b2) == 0:
                return self.def_eq(b1, b2)
            fvar = self.fvar_for(h1)
            return self.def_eq(
                store.instantiate(b1, fvar, 0),
                store.instantiate(b2, fvar, 0),
            )
        fvars = []
        while store.kind(h1) == kind and store.kind(h2) == kind:
            if h1 == h2 and not self._def_eq_hooked:
                return True
            d1 = store.field_a(h1)
            d2 = store.field_a(h2)
            same_d = (d1 == d2)
            nf = len(fvars)
            if nf > 0:
                if store.loose_bvar_range(d1) > 0:
                    if is_leaf(d1):
                        bid = (_s32(store.leaf_meta[leaf_index(d1)]) >> 1) - 1
                        d1 = fvars[nf - 1 - bid] if bid < nf else store.bvar(bid - nf)
                    else:
                        d1 = store.instantiate_multi_rev(d1, fvars, nf, 0)
                if same_d:
                    d2 = d1
                elif store.loose_bvar_range(d2) > 0:
                    if is_leaf(d2):
                        bid = (_s32(store.leaf_meta[leaf_index(d2)]) >> 1) - 1
                        d2 = fvars[nf - 1 - bid] if bid < nf else store.bvar(bid - nf)
                    else:
                        d2 = store.instantiate_multi_rev(d2, fvars, nf, 0)
            if not same_d or self._def_eq_hooked:
                if not self.def_eq(d1, d2):
                    return False
            nxt1 = store.field_b(h1)
            nxt2 = store.field_b(h2)
            if nxt1 == nxt2 and not self._def_eq_hooked:
                return True
            if (store.loose_bvar_range(nxt1) == 0
                    and store.loose_bvar_range(nxt2) == 0):
                if nf > 0:
                    fvars = []
            else:
                fvars.append(self.fvar_for_domain(h1, d1))
            h1 = nxt1
            h2 = nxt2
        if h1 == h2 and not self._def_eq_hooked:
            return True
        nf = len(fvars)
        if nf > 0:
            if store.loose_bvar_range(h1) > 0:
                h1 = store.instantiate_multi_rev(h1, fvars, nf, 0)
            if store.loose_bvar_range(h2) > 0:
                h2 = store.instantiate_multi_rev(h2, fvars, nf, 0)
        return self.def_eq(h1, h2)

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
        head = store.head(ctor_side)
        if (self._leaf_flags(head) & _LF_CTOR) == 0:
            return False
        ctor_decl = store.leaf_decl[leaf_index(head)]
        assert ctor_decl is not None
        ctor_kind = ctor_decl.w_kind
        assert isinstance(ctor_kind, W_Constructor)
        num_params = ctor_kind.num_params
        num_fields = ctor_kind.num_fields
        mark = store._spine_top
        store.unapp_push(ctor_side)
        try:
            n = store._spine_top - mark
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
                if not self.def_eq(proj, store.spine_arg(mark + n - 1 - (num_params + i))):
                    return False
                i += 1
            return True
        finally:
            store.unapp_pop(mark)

    def def_eq_unit(self, h1, h2):
        store = self.store
        tc = self.tc
        t1 = self.whnf(self.infer(h1, False))
        t1_head = store.head(t1)
        const = store.const_leaf(t1_head)
        if const is None:
            return False
        decl = self._leaf_decl(t1_head, const)
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

    def _check_value_joint_ast(self, type, value, prop):
        """Jointly check a leading `W_ForAll` / `W_Lambda` telescope directly
        on the raw AST: imports binder domains, codomain, and proof body with
        canonical `_top_fvar` handles substituted inline (eliminating both
        throwaway `BVar`-bearing records and `instantiate_multi_rev`).

        Returns True when accepted, False to fall back to the general path for
        diagnostics (top-level NotASort / NotAProp / TypeError)."""
        store = self.store
        levels = []
        fvars = []
        tcur = type
        vcur = value
        try:
            while isinstance(tcur, W_ForAll) and isinstance(vcur, W_Lambda):
                t_dom_ast = tcur.binder.type
                v_dom_ast = vcur.binder.type
                nf = len(fvars)
                if t_dom_ast is v_dom_ast:
                    if nf == 0 or t_dom_ast.loose_bvar_range() == 0:
                        dom = store.import_term(t_dom_ast)
                    elif t_dom_ast.__class__ is W_BVar:
                        assert isinstance(t_dom_ast, W_BVar)
                        bid = t_dom_ast.id
                        dom = (
                            fvars[nf - 1 - bid]
                            if bid < nf
                            else store.bvar(bid - nf)
                        )
                    else:
                        dom = store.import_term_fvars(
                            t_dom_ast, fvars, nf, _next_cache_gen(),
                        )
                        if store._fvar_base_gen != 0:
                            store.clear_fvar_gens()
                else:
                    if nf == 0:
                        dom = store.import_term(t_dom_ast)
                        vdom = store.import_term(v_dom_ast)
                    else:
                        fg = _next_cache_gen()
                        dom = store.import_term_fvars(t_dom_ast, fvars, nf, fg)
                        vdom = store.import_term_fvars(v_dom_ast, fvars, nf, fg)
                        if store._fvar_base_gen != 0:
                            store.clear_fvar_gens()
                    if vdom != dom:
                        break
                levels.append(self._ensure_sort(dom, True))
                tnxt = tcur.body
                vnxt = vcur.body
                if (tnxt.loose_bvar_range() == 0
                        and vnxt.loose_bvar_range() == 0):
                    if nf > 0:
                        fvars = []
                else:
                    fvars.append(self._top_fvar(nf, vcur.binder, dom))
                tcur = tnxt
                vcur = vnxt
            if len(levels) == 0:
                return False
            nf = len(fvars)
            fgen = 0
            if nf > 0 and (
                    tcur.loose_bvar_range() > 0 or vcur.loose_bvar_range() > 0):
                fgen = _next_cache_gen()
            if nf > 0 and tcur.loose_bvar_range() > 0:
                tcur_h = store.import_term_fvars(tcur, fvars, nf, fgen)
            else:
                tcur_h = store.import_term(tcur)
            t_ty = self.infer(tcur_h, True)
            t_sort = store.sort_leaf(self.whnf(t_ty))
            if t_sort is None:
                return False
            level = t_sort.level
            i = len(levels) - 1
            while i >= 0:
                level = levels[i].imax(level)
                i -= 1
            if prop and not level.eq(W_LEVEL_ZERO):
                return False
            if nf > 0 and vcur.loose_bvar_range() > 0:
                vcur_h = store.import_term_fvars(vcur, fvars, nf, fgen)
            else:
                vcur_h = store.import_term(vcur)
        finally:
            if store._fvar_base_gen != 0 or store._fvar_gens_len > 0:
                store.clear_fvar_gens()
        val_ty = self.infer_expected(vcur_h, tcur_h)
        return self.def_eq(tcur_h, val_ty)

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
        if (not self._def_eq_hooked
                and isinstance(type, W_ForAll)
                and isinstance(value, W_Lambda)
                and type.loose_bvar_range() == 0
                and not type.has_fvar()
                and not value.has_fvar()
                and store.nrecs - self._decl_start_recs < _OPEN_RECORDS):
            if self._check_value_joint_ast(type, value, prop):
                return None
        ty = store.import_term(type)
        val = store.import_term(value)
        ty_ty = self.infer(ty, True)
        ty_ty_whnf = self.whnf(ty_ty)
        sort = store.sort_leaf(ty_ty_whnf)
        if sort is None:
            return W_NotASort(tc, type, inferred_type=self.export(ty_ty), name=None)
        if prop and not sort.level.eq(W_LEVEL_ZERO):
            return W_NotAProp(tc, type, inferred_sort=sort, name=None)
        val_ty = self.infer_expected(val, ty)
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


def _levels_subset(prev, cur):
    """Whether every universe parameter Name in ``prev`` is present in ``cur``."""
    if prev is cur:
        return True
    if prev is None:
        return False
    n = len(prev)
    if n == 0:
        return True
    if cur is None:
        return False
    m = len(cur)
    if n > m:
        return False
    if n == 1:
        p0 = prev[0]
        if m == 1:
            return cur[0] is p0
        i = 0
        while i < m:
            if cur[i] is p0:
                return True
            i += 1
        return False
    i = 0
    while i < n:
        p = prev[i]
        found = False
        j = 0
        while j < m:
            if cur[j] is p:
                found = True
                break
            j += 1
        if not found:
            return False
        i += 1
    return True


def _init_warm_cohort(machine, tc, allow_warm):
    decl = tc.decl
    if (allow_warm
            and decl is not None
            and decl.index >= 0
            and decl.group < 0
            and decl.safety == SAFETY_SAFE
            and not tc.def_eq_hooked):
        machine._warm_max_index = decl.index
        machine._warm_levels = decl.levels
        machine._warm_safe_cohort = True
        machine._can_perm = True
    else:
        machine._warm_max_index = (
            decl.index if (decl is not None and decl.index >= 0) else -1
        )
        machine._warm_levels = None
        machine._warm_safe_cohort = False
        machine._can_perm = False
    machine._saw_nonperm = False


def acquire(tc, allow_warm=False):
    """A machine for ``tc``'s declaration: the spare one, if there is one.

    When ``allow_warm`` is true and the spare machine belongs to the same
    `Environment`, is below its warm-cache caps, and declarations arrive in
    monotonic index order with ``group < 0``, it is reused without resetting.
    Safe consecutive declarations with compatible `decl.levels` share
    `check_gen` so verified subterms skip redundant re-checking; incompatible
    cohorts bump `check_gen` while preserving `_CHECKED_PERM` entries for
    closed, zero-level-param, safe subterms.
    """
    machine = _SPARE.machine
    if machine is None:
        machine = Machine(tc)
        machine._last_env = tc.env
        machine._is_clean = False
        machine.store.record_nodes = (not allow_warm) or tc.tracer.writes
        machine.recheck_on_error = not machine.store.record_nodes
        _init_warm_cohort(machine, tc, allow_warm)
        return machine
    _SPARE.machine = None
    machine.tc = tc
    machine.store.tc = tc
    machine._def_eq_hooked = tc.def_eq_hooked
    decl = tc.decl
    if (allow_warm
            and decl is not None
            and decl.index >= machine._warm_max_index
            and decl.group < 0
            and machine._last_env is tc.env
            and not machine._is_clean
            and (machine.store.record_nodes or not tc.tracer.writes)
            and machine.is_warm_ready()):
        safe_cur = (decl.safety == SAFETY_SAFE and not tc.def_eq_hooked)
        if (safe_cur
                and machine._warm_safe_cohort
                and _levels_subset(machine._warm_levels, decl.levels)):
            machine._warm_levels = decl.levels
        else:
            machine.check_gen += 1
            machine._warm_safe_cohort = safe_cur
            machine._warm_levels = decl.levels if safe_cur else None
        machine._warm_max_index = decl.index
        machine._can_perm = safe_cur
        machine._saw_nonperm = False
        machine._open_memo.clear()
        machine._decl_start_recs = machine.store.nrecs
        machine.store.record_nodes = tc.tracer.writes
        machine.recheck_on_error = True
        return machine
    if not machine._is_clean or machine._last_env is not tc.env:
        machine.reset()
    machine._decl_start_recs = 0
    machine._last_env = tc.env
    machine._is_clean = False
    machine.store.record_nodes = (not allow_warm) or tc.tracer.writes
    machine.recheck_on_error = not machine.store.record_nodes
    _init_warm_cohort(machine, tc, allow_warm)
    return machine


def release(machine, failed=False, keep_warm=False):
    """Hand back a machine whose declaration has been checked."""
    machine._census()
    if _SPARE.machine is None:
        if failed or not keep_warm or not machine.is_warm_ready():
            machine.reset()
            machine._last_env = None
        _SPARE.machine = machine
    else:
        machine.free()
