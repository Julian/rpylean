"""
Terms as flat records in raw memory, addressed by integer handles.

The boxed `W_Expr` tree is the parsed representation: it is what the
garbage collector traces, so every reduction product that lives in it
is re-traced on every major collection for as long as it is retained.
Here a term is instead a *record*: a fixed run of machine words in a
raw (untraced) array, named by an integer *handle*. Records are
hash-consed, so structurally equal terms have equal handles and
syntactic equality is an integer comparison. Leaves that carry no
sub-terms (constants, sorts, variables, literals) stay boxed and are
referenced from a side table; they are canonicalised by content on the
way in, which is what makes handle equality meaningful.

A store is per declaration: the working set of one check, freed
wholesale when the check ends.
"""

from rpython.rlib.objectmodel import always_inline
from rpython.rlib.rarithmetic import intmask, r_uint
from rpython.rlib.rstack import stack_almost_full
from rpython.rtyper.lltypesystem import lltype, rffi

from rpython.rlib.rbigint import rbigint

from rpylean.exceptions import HeartbeatExceeded, InvalidProjection
from rpylean.objects import (
    HINT_ABBREV,
    NAT,
    NAT_ZERO,
    PROP,
    STRING,
    W_App,
    W_BVar,
    W_Closure,
    W_Const,
    W_Constructor,
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
    _BOOL_TRUE,
    _NAT_REC_NAME,
    _NAT_SUCC_NAME,
    _mk_app_in,
    _mk_w_forall_in,
    _mk_w_lambda_in,
    _mk_w_litnat,
    apply_const_level_params,
    find_decl,
    get_decl,
    is_nat_binop,
    name_dict,
    nat_binop_value,
    syntactic_eq,
)


class RawBail(Exception):
    """
    The machine cannot (or will not) decide this; the caller falls
    back to the boxed kernel.
    """

    def __init__(self, reason):
        self.reason = reason


# ---- Handles --------------------------------------------------------------
#
# A handle is a tagged machine int. Bit 0 set: a leaf, index `h >> 1`
# into the boxed leaf table. Bit 0 clear and non-zero: a record, index
# `(h >> 1) - 1`. Zero never names anything, so it doubles as the empty
# marker of every raw table.

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
# which packs `loose_bvar_range << 1 | has_fvar` exactly as the boxed
# node's `_packed` upper half does.

KIND_APP = 1      # a = fn, b = arg
KIND_LAMBDA = 2   # a = binder type, b = body; info = the boxed Binder
KIND_FORALL = 3   # a = binder type, b = body; info = the boxed Binder
KIND_PROJ = 4     # a = struct, b = field index, c = struct Name id; info = the Name
KIND_LET = 5      # a = type, b = PAIR(value, body); info = the let Name
KIND_PAIR = 6     # a = value, b = body (auxiliary to KIND_LET)

REC_WORDS = 5
F_KIND = 0
F_A = 1
F_B = 2
F_C = 3
F_META = 4

# Per-record memo slots (parallel to the records, 0 = not yet known).
MEMO_SLOTS = 4
M_WHNF_CORE = 0
M_WHNF = 1
M_INFER = 2
M_INFER_CHECKED = 3

_SIGNED_ARRAY = rffi.CArray(lltype.Signed)
_NO_INFO = -1


def _raw_alloc(n):
    return lltype.malloc(_SIGNED_ARRAY, n, flavor='raw', zero=True)


def _raw_free(arr):
    lltype.free(arr, flavor='raw')


@always_inline
def _mix(h, x):
    return (h * 1000003) ^ x


@always_inline
def _spread(k):
    # Packed keys carry their most distinguishing bits high up (a
    # record handle shifted by 38) and their least (a depth) low, so
    # the table index has to depend on every bit: a full 64-bit
    # finalizer (murmur3's fmix64) rather than a multiply.
    x = r_uint(k)
    x ^= x >> 33
    x *= r_uint(0xff51afd7ed558ccd)
    x ^= x >> 33
    x *= r_uint(0xc4ceb9fe1a85ec53)
    x ^= x >> 33
    return intmask(x)


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


class RawIntMap(object):
    """
    An open-addressed int -> int map in raw memory. Keys must be
    non-zero (zero marks an empty slot).
    """

    _attrs_ = ['keys', 'vals', 'mask', 'size']

    def __init__(self, capacity=1 << 10):
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.keys = _raw_alloc(cap)
        self.vals = _raw_alloc(cap)
        self.mask = cap - 1
        self.size = 0

    def get(self, key, default):
        assert key != 0
        mask = self.mask
        keys = self.keys
        i = _spread(key) & mask
        while True:
            k = keys[i]
            if k == key:
                return self.vals[i]
            if k == 0:
                return default
            i = (i + 1) & mask

    def set(self, key, val):
        assert key != 0
        if (self.size + 1) * 2 > self.mask + 1:
            self._grow()
        mask = self.mask
        keys = self.keys
        i = _spread(key) & mask
        while True:
            k = keys[i]
            if k == key:
                self.vals[i] = val
                return
            if k == 0:
                keys[i] = key
                self.vals[i] = val
                self.size += 1
                return
            i = (i + 1) & mask

    def _grow(self):
        old_keys = self.keys
        old_vals = self.vals
        old_cap = self.mask + 1
        cap = old_cap * 2
        keys = _raw_alloc(cap)
        vals = _raw_alloc(cap)
        mask = cap - 1
        i = 0
        while i < old_cap:
            k = old_keys[i]
            if k != 0:
                j = _spread(k) & mask
                while keys[j] != 0:
                    j = (j + 1) & mask
                keys[j] = k
                vals[j] = old_vals[i]
            i += 1
        self.keys = keys
        self.vals = vals
        self.mask = mask
        _raw_free(old_keys)
        _raw_free(old_vals)

    def free(self):
        if self.mask >= 0:
            _raw_free(self.keys)
            _raw_free(self.vals)
            self.mask = -1
            self.size = 0


class RawTermStore(object):
    """
    The record arena for one declaration's check: records, the consing
    table over them, the boxed leaf table, and the memoised boundary
    in both directions.

    ``tc`` is the `TypeChecker` whose arenas boxed products built at the
    boundary go to (``None`` in tests routes them to the persistent
    intern tables).
    """

    _attrs_ = [
        'tc',
        'recs', 'rec_info', 'memos', 'nrecs', 'cap',
        'table', 'tmask',
        'leaves', 'leaf_meta', 'leaf_bvar', 'leaf_whnf', 'leaf_infer',
        'leaf_checked', 'nleaves', 'leaf_cap',
        'infos', 'names', '_name_ids',
        '_bvar_leaves', '_fvar_leaves', '_content_leaves',
        '_import_memo', '_export_memo',
        '_inst_memo', '_shift_memo', '_bind_memo',
        '_freed',
    ]

    def __init__(self, tc, capacity=1 << 14):
        self.tc = tc
        cap = 1
        while cap < capacity:
            cap <<= 1
        self.cap = cap
        self.recs = _raw_alloc(cap * REC_WORDS)
        self.rec_info = _raw_alloc(cap)
        self.memos = _raw_alloc(cap * MEMO_SLOTS)
        self.nrecs = 0
        self.table = _raw_alloc(cap * 2)
        self.tmask = cap * 2 - 1
        #: Boxed leaves by index; `leaf_meta` / `leaf_bvar` mirror the
        #: two facts the machine reads on hot paths so it need not touch
        #: the boxed object: the packed meta word, and the de Bruijn
        #: index for a bound variable (-1 otherwise).
        self.leaves = []
        self.leaf_cap = 1 << 10
        self.leaf_meta = _raw_alloc(self.leaf_cap)
        self.leaf_bvar = _raw_alloc(self.leaf_cap)
        self.leaf_whnf = _raw_alloc(self.leaf_cap)
        #: A leaf's inferred type (0 = not yet), and whether that type
        #: was produced in check mode (a constant's reference check has
        #: run).
        self.leaf_infer = _raw_alloc(self.leaf_cap)
        self.leaf_checked = _raw_alloc(self.leaf_cap)
        self.nleaves = 0
        #: Binder infos (boxed `Binder`s, for the name and style) and
        #: `Name`s (for projections and lets), by `rec_info` index.
        self.infos = []
        self.names = []
        self._name_ids = name_dict()
        self._bvar_leaves = {}
        self._fvar_leaves = {}
        self._content_leaves = {}
        self._import_memo = {}
        self._export_memo = {}
        self._inst_memo = RawIntMap(1 << 12)
        self._shift_memo = RawIntMap(1 << 10)
        self._bind_memo = RawIntMap(1 << 10)
        self._freed = False

    # ---- lifecycle -------------------------------------------------------

    def free(self):
        if self._freed:
            return
        self._freed = True
        _raw_free(self.recs)
        _raw_free(self.rec_info)
        _raw_free(self.memos)
        _raw_free(self.table)
        _raw_free(self.leaf_meta)
        _raw_free(self.leaf_bvar)
        _raw_free(self.leaf_whnf)
        _raw_free(self.leaf_infer)
        _raw_free(self.leaf_checked)
        self._inst_memo.free()
        self._shift_memo.free()
        self._bind_memo.free()

    # ---- record access ---------------------------------------------------

    @always_inline
    def kind(self, h):
        if is_leaf(h):
            return 0
        return self.recs[rec_index(h) * REC_WORDS + F_KIND]

    @always_inline
    def field_a(self, h):
        return self.recs[rec_index(h) * REC_WORDS + F_A]

    @always_inline
    def field_b(self, h):
        return self.recs[rec_index(h) * REC_WORDS + F_B]

    @always_inline
    def field_c(self, h):
        return self.recs[rec_index(h) * REC_WORDS + F_C]

    @always_inline
    def meta(self, h):
        if is_leaf(h):
            return self.leaf_meta[leaf_index(h)]
        return self.recs[rec_index(h) * REC_WORDS + F_META]

    @always_inline
    def loose_bvar_range(self, h):
        return self.meta(h) >> 1

    @always_inline
    def has_fvar(self, h):
        return (self.meta(h) & 1) != 0

    def info(self, h):
        return self.rec_info[rec_index(h)]

    @always_inline
    def memo(self, h, slot):
        return self.memos[rec_index(h) * MEMO_SLOTS + slot]

    @always_inline
    def set_memo(self, h, slot, value):
        self.memos[rec_index(h) * MEMO_SLOTS + slot] = value

    def binder_of(self, h):
        """The boxed `Binder` recorded for a lambda or forall record."""
        return self.infos[self.info(h)]

    def name_of(self, h):
        """The `Name` recorded for a projection or let record."""
        return self.names[self.info(h)]

    def leaf(self, h):
        """The boxed leaf a leaf handle names."""
        return self.leaves[leaf_index(h)]

    def bvar_id(self, h):
        """The de Bruijn index of a bound-variable leaf, else -1."""
        if not is_leaf(h):
            return -1
        return self.leaf_bvar[leaf_index(h)]

    # ---- consing ---------------------------------------------------------

    def _meta_for(self, kind, a, b):
        if kind == KIND_APP or kind == KIND_PAIR:
            la = self.loose_bvar_range(a)
            lb = self.loose_bvar_range(b)
            loose = la if la > lb else lb
            fvar = self.has_fvar(a) or self.has_fvar(b)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            la = self.loose_bvar_range(a)
            lb = self.loose_bvar_range(b) - 1
            if lb < 0:
                lb = 0
            loose = la if la > lb else lb
            fvar = self.has_fvar(a) or self.has_fvar(b)
        elif kind == KIND_PROJ:
            loose = self.loose_bvar_range(a)
            fvar = self.has_fvar(a)
        else:
            assert kind == KIND_LET
            # b is the (value, body) pair: its range is max of the two,
            # but the body sits under the let's binder.
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

    def cons(self, kind, a, b, c, info=_NO_INFO):
        """
        The record ``(kind, a, b, c)``, creating it if new. ``info`` is
        not part of the identity: the first recorded binder or name
        stands for every later alpha-equal request.
        """
        recs = self.recs
        table = self.table
        tmask = self.tmask
        h = _mix(_mix(_mix(kind, a), b), c)
        i = _spread(h) & tmask
        while True:
            slot = table[i]
            if slot == 0:
                break
            base = (slot - 1) * REC_WORDS
            if (recs[base + F_KIND] == kind and recs[base + F_A] == a
                    and recs[base + F_B] == b and recs[base + F_C] == c):
                return rec_handle(slot - 1)
            i = (i + 1) & tmask
        idx = self.nrecs
        if idx == self.cap:
            self._grow_records()
            recs = self.recs
        base = idx * REC_WORDS
        recs[base + F_KIND] = kind
        recs[base + F_A] = a
        recs[base + F_B] = b
        recs[base + F_C] = c
        recs[base + F_META] = self._meta_for(kind, a, b)
        self.rec_info[idx] = info
        self.nrecs = idx + 1
        if (idx + 1) * 2 > self.tmask + 1:
            self._rehash()
        else:
            self.table[i] = idx + 1
        return rec_handle(idx)

    def _grow_records(self):
        old = self.recs
        old_info = self.rec_info
        old_memos = self.memos
        cap = self.cap * 2
        recs = _raw_alloc(cap * REC_WORDS)
        info = _raw_alloc(cap)
        memos = _raw_alloc(cap * MEMO_SLOTS)
        n = self.nrecs * REC_WORDS
        i = 0
        while i < n:
            recs[i] = old[i]
            i += 1
        i = 0
        while i < self.nrecs:
            info[i] = old_info[i]
            i += 1
        n = self.nrecs * MEMO_SLOTS
        i = 0
        while i < n:
            memos[i] = old_memos[i]
            i += 1
        self.recs = recs
        self.rec_info = info
        self.memos = memos
        self.cap = cap
        _raw_free(old)
        _raw_free(old_info)
        _raw_free(old_memos)

    def _rehash(self):
        _raw_free(self.table)
        cap = (self.tmask + 1) * 2
        table = _raw_alloc(cap)
        tmask = cap - 1
        recs = self.recs
        idx = 0
        while idx < self.nrecs:
            base = idx * REC_WORDS
            h = _mix(_mix(_mix(recs[base + F_KIND], recs[base + F_A]),
                          recs[base + F_B]), recs[base + F_C])
            i = _spread(h) & tmask
            while table[i] != 0:
                i = (i + 1) & tmask
            table[i] = idx + 1
            idx += 1
        self.table = table
        self.tmask = tmask

    def app(self, fn, arg):
        return self.cons(KIND_APP, fn, arg, 0)

    def lam(self, binder, type, body):
        return self.cons(KIND_LAMBDA, type, body, 0, self._info_index(binder))

    def forall(self, binder, type, body):
        return self.cons(KIND_FORALL, type, body, 0, self._info_index(binder))

    def proj(self, struct_name, field_index, struct):
        # The structure's name is part of a projection's identity: it
        # decides the field's type and which constructor it reads.
        name_id = self._name_index(struct_name)
        return self.cons(KIND_PROJ, struct, field_index, name_id, name_id)

    def let(self, name, type, value, body):
        pair = self.cons(KIND_PAIR, value, body, 0)
        return self.cons(KIND_LET, type, pair, 0, self._name_index(name))

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
            meta = _raw_alloc(cap)
            bv = _raw_alloc(cap)
            wh = _raw_alloc(cap)
            inf = _raw_alloc(cap)
            chk = _raw_alloc(cap)
            i = 0
            while i < j:
                meta[i] = self.leaf_meta[i]
                bv[i] = self.leaf_bvar[i]
                wh[i] = self.leaf_whnf[i]
                inf[i] = self.leaf_infer[i]
                chk[i] = self.leaf_checked[i]
                i += 1
            _raw_free(self.leaf_meta)
            _raw_free(self.leaf_bvar)
            _raw_free(self.leaf_whnf)
            _raw_free(self.leaf_infer)
            _raw_free(self.leaf_checked)
            self.leaf_meta = meta
            self.leaf_bvar = bv
            self.leaf_whnf = wh
            self.leaf_infer = inf
            self.leaf_checked = chk
            self.leaf_cap = cap
        self.leaves.append(e)
        self.leaf_meta[j] = e._packed >> 32
        self.leaf_bvar[j] = bvar
        self.nleaves = j + 1
        return leaf_handle(j)

    def bvar(self, id):
        h = self._bvar_leaves.get(id, 0)
        if h != 0:
            return h
        h = self._new_leaf(W_BVar(id), id)
        self._bvar_leaves[id] = h
        return h

    def leaf_for(self, e):
        """
        The canonical leaf handle for the boxed leaf ``e``: bound
        variables by index, free variables by identity, everything else
        by content.
        """
        cls = e.__class__
        if cls is W_BVar:
            assert isinstance(e, W_BVar)
            h = self._bvar_leaves.get(e.id, 0)
            if h != 0:
                return h
            h = self._new_leaf(e, e.id)
            self._bvar_leaves[e.id] = h
            return h
        if cls is W_FVar:
            h = self._fvar_leaves.get(e._uid, 0)
            if h != 0:
                return h
            h = self._new_leaf(e, -1)
            self._fvar_leaves[e._uid] = h
            return h
        key = e.hash()
        bucket = self._content_leaves.get(key, None)
        if bucket is None:
            bucket = []
            self._content_leaves[key] = bucket
        else:
            for h in bucket:
                if syntactic_eq(self.leaves[leaf_index(h)], e):
                    return h
        h = self._new_leaf(e, -1)
        bucket.append(h)
        return h

    # ---- spines ----------------------------------------------------------

    def head(self, h):
        """The head of the application spine ``h``."""
        while self.kind(h) == KIND_APP:
            h = self.field_a(h)
        return h

    def unapp(self, h):
        """
        ``(head, args)`` for the spine ``h``, args outermost-first (the
        last argument first), as the boxed `unapp` returns them.
        """
        args = []
        while self.kind(h) == KIND_APP:
            args.append(self.field_b(h))
            h = self.field_a(h)
        return h, args

    def apply(self, fn, args, start, stop):
        """``fn`` applied to ``args[start:stop]``, left to right."""
        i = start
        while i < stop:
            fn = self.cons(KIND_APP, fn, args[i], 0)
            i += 1
        return fn

    def apply_rev(self, fn, args, hi):
        """``fn`` applied to ``args[hi]``, ``args[hi-1]``, … ``args[0]``:
        re-applies an outermost-first arg list up to index ``hi``."""
        i = hi
        while i >= 0:
            fn = self.cons(KIND_APP, fn, args[i], 0)
            i -= 1
        return fn

    def const_leaf(self, h):
        """The boxed `W_Const` a leaf handle names, or ``None``."""
        if not is_leaf(h):
            return None
        e = self.leaves[leaf_index(h)]
        if isinstance(e, W_Const):
            return e
        return None

    def litnat_leaf(self, h):
        """The boxed `W_LitNat` a leaf handle names, or ``None``."""
        if not is_leaf(h):
            return None
        e = self.leaves[leaf_index(h)]
        if isinstance(e, W_LitNat):
            return e
        return None

    # ---- substitution ----------------------------------------------------

    def instantiate(self, h, sub, depth=0):
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
                return self.shift(sub, depth, 0)
            return self.bvar(id - 1)
        key = _pack_key(h, sub, depth)
        if key != 0:
            r = self._inst_memo.get(key, 0)
            if r != 0:
                return r
        if stack_almost_full():
            raise RawBail("instantiate: stack")
        recs = self.recs
        base = rec_index(h) * REC_WORDS
        kind = recs[base + F_KIND]
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = self.rec_info[rec_index(h)]
        if kind == KIND_APP:
            na = self.instantiate(a, sub, depth)
            nb = self.instantiate(b, sub, depth)
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(KIND_APP, na, nb, 0)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = self.instantiate(a, sub, depth)
            nb = self.instantiate(b, sub, depth + 1)
            if na == a and nb == b:
                r = h
            else:
                r = self.cons(kind, na, nb, 0, info)
        elif kind == KIND_PROJ:
            na = self.instantiate(a, sub, depth)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, recs[base + F_C], info)
        else:
            assert kind == KIND_LET
            value = self.field_a(b)
            body = self.field_b(b)
            na = self.instantiate(a, sub, depth)
            nv = self.instantiate(value, sub, depth)
            nbody = self.instantiate(body, sub, depth + 1)
            if na == a and nv == value and nbody == body:
                r = h
            else:
                pair = self.cons(KIND_PAIR, nv, nbody, 0)
                r = self.cons(KIND_LET, na, pair, 0, info)
        if key != 0:
            self._inst_memo.set(key, r)
        return r

    def shift(self, h, count, depth=0):
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
            if r != 0:
                return r
        if stack_almost_full():
            raise RawBail("shift: stack")
        recs = self.recs
        base = rec_index(h) * REC_WORDS
        kind = recs[base + F_KIND]
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = self.rec_info[rec_index(h)]
        if kind == KIND_APP:
            r = self.cons(
                KIND_APP, self.shift(a, count, depth),
                self.shift(b, count, depth), 0,
            )
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            r = self.cons(
                kind, self.shift(a, count, depth),
                self.shift(b, count, depth + 1), 0, info,
            )
        elif kind == KIND_PROJ:
            r = self.cons(
                KIND_PROJ, self.shift(a, count, depth), b,
                recs[base + F_C], info,
            )
        else:
            assert kind == KIND_LET
            pair = self.cons(
                KIND_PAIR, self.shift(self.field_a(b), count, depth),
                self.shift(self.field_b(b), count, depth + 1), 0,
            )
            r = self.cons(KIND_LET, self.shift(a, count, depth), pair, 0, info)
        if key != 0:
            self._shift_memo.set(key, r)
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
            if r != 0:
                return r
        if stack_almost_full():
            raise RawBail("bind_fvar: stack")
        recs = self.recs
        base = rec_index(h) * REC_WORDS
        kind = recs[base + F_KIND]
        a = recs[base + F_A]
        b = recs[base + F_B]
        info = self.rec_info[rec_index(h)]
        if kind == KIND_APP:
            na = self.bind_fvar(a, fvar, depth)
            nb = self.bind_fvar(b, fvar, depth)
            r = h if (na == a and nb == b) else self.cons(KIND_APP, na, nb, 0)
        elif kind == KIND_LAMBDA or kind == KIND_FORALL:
            na = self.bind_fvar(a, fvar, depth)
            nb = self.bind_fvar(b, fvar, depth + 1)
            r = h if (na == a and nb == b) else self.cons(kind, na, nb, 0, info)
        elif kind == KIND_PROJ:
            na = self.bind_fvar(a, fvar, depth)
            if na == a:
                r = h
            else:
                r = self.cons(KIND_PROJ, na, b, recs[base + F_C], info)
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
                pair = self.cons(KIND_PAIR, nv, nbody, 0)
                r = self.cons(KIND_LET, na, pair, 0, info)
        if key != 0:
            self._bind_memo.set(key, r)
        return r

    def sort_leaf(self, h):
        """The boxed `W_Sort` a leaf handle names, or ``None``."""
        if not is_leaf(h):
            return None
        e = self.leaves[leaf_index(h)]
        if isinstance(e, W_Sort):
            return e
        return None

    # ---- boundary --------------------------------------------------------

    def import_term(self, e):
        """The handle for the boxed term ``e``, memoised per boxed node."""
        memo = self._import_memo
        h = memo.get(e._uid, 0)
        if h != 0:
            return h
        if stack_almost_full():
            raise RawBail("import: stack")
        cls = e.__class__
        if cls is W_App:
            # Walk the spine down to the first already-imported node
            # (or the head), then fold applications back up, memoising
            # every spine node on the way.
            spine = []
            cur = e
            head = 0
            while True:
                if not isinstance(cur, W_App):
                    head = self.import_term(cur)
                    break
                hh = memo.get(cur._uid, 0)
                if hh != 0:
                    head = hh
                    break
                spine.append(cur)
                cur = cur.fn
            i = len(spine) - 1
            while i >= 0:
                app = spine[i]
                head = self.app(head, self.import_term(app.arg))
                memo[app._uid] = head
                i -= 1
            return head
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(e, W_Lambda) or isinstance(e, W_ForAll)
            binder = e.binder
            type = self.import_term(binder.type)
            body = self.import_term(e.body)
            if cls is W_Lambda:
                h = self.lam(binder, type, body)
            else:
                h = self.forall(binder, type, body)
        elif cls is W_Proj:
            assert isinstance(e, W_Proj)
            h = self.proj(
                e.struct_name, e.field_index, self.import_term(e.struct_expr),
            )
        elif cls is W_Let:
            assert isinstance(e, W_Let)
            h = self.let(
                e.name,
                self.import_term(e.type),
                self.import_term(e.value),
                self.import_term(e.body),
            )
        elif cls is W_Closure:
            assert isinstance(e, W_Closure)
            h = self.import_term(e.force(self.tc))
        else:
            h = self.leaf_for(e)
        memo[e._uid] = h
        return h

    def export_term(self, h):
        """The boxed term for ``h``, memoised per record."""
        if is_leaf(h):
            return self.leaves[leaf_index(h)]
        memo = self._export_memo
        cached = memo.get(h, None)
        if cached is not None:
            return cached
        if stack_almost_full():
            raise RawBail("export: stack")
        tc = self.tc
        kind = self.kind(h)
        if kind == KIND_APP:
            args = []
            cur = h
            head = None
            while True:
                if self.kind(cur) != KIND_APP:
                    head = self.export_term(cur)
                    break
                cached = memo.get(cur, None)
                if cached is not None:
                    head = cached
                    break
                args.append(cur)
                cur = self.field_a(cur)
            assert head is not None
            i = len(args) - 1
            while i >= 0:
                app = args[i]
                head = _mk_app_in(tc, head, self.export_term(self.field_b(app)))
                memo[app] = head
                i -= 1
            return head
        if kind == KIND_LAMBDA or kind == KIND_FORALL:
            binder = self.binder_of(h).with_type(
                self.export_term(self.field_a(h)),
            )
            body = self.export_term(self.field_b(h))
            if kind == KIND_LAMBDA:
                e = _mk_w_lambda_in(tc, binder, body)
            else:
                e = _mk_w_forall_in(tc, binder, body)
        elif kind == KIND_PROJ:
            e = self.name_of(h).proj_in(
                tc, self.field_b(h), self.export_term(self.field_a(h)),
            )
        else:
            assert kind == KIND_LET
            pair = self.field_b(h)
            e = self.name_of(h).let(
                type=self.export_term(self.field_a(h)),
                value=self.export_term(self.field_a(pair)),
                body=self.export_term(self.field_b(pair)),
            )
        memo[h] = e
        return e


class RawMachine(object):
    """
    A declaration checker over handles. Anything it cannot decide
    raises `RawBail`, and the caller runs the boxed kernel instead.

    Every step mirrors the boxed kernel: `whnf_core` is beta / zeta /
    projection / iota / quot only, `whnf` adds native Nat arithmetic
    and one delta layer per iteration, `def_eq` runs the same sequence
    of checks in the same order, and `infer` opens each binder with one
    canonical free variable per binder record.
    """

    _attrs_ = [
        'tc', 'store', '_delta_memo', '_rule_memo', '_fvars',
        '_eqv', '_neq', '_failed',
        'h_prop', 'h_true', 'h_nat', 'h_string',
    ]

    _LAZY_DELTA_MAX_ITER = 100000

    def __init__(self, tc):
        self.tc = tc
        store = RawTermStore(tc)
        self.store = store
        #: const leaf index -> handle of its unfolded value (0 = none)
        self._delta_memo = {}
        #: (rec const leaf index, ctor leaf index) -> rule rhs handle
        self._rule_memo = {}
        #: binder record -> its canonical free-variable leaf
        self._fvars = {}
        #: proven-def-eq forest over handles (handle -> parent)
        self._eqv = RawIntMap(1 << 10)
        #: pairs proven NOT def-eq
        self._neq = RawIntMap(1 << 10)
        #: pairs whose same-head argument comparison failed (symmetric)
        self._failed = RawIntMap(1 << 8)
        self.h_prop = store.leaf_for(PROP)
        self.h_true = store.leaf_for(_BOOL_TRUE)
        self.h_nat = store.leaf_for(NAT)
        self.h_string = store.leaf_for(STRING)

    def free(self):
        self.store.free()
        self._eqv.free()
        self._neq.free()
        self._failed.free()

    def _decl(self, const):
        return find_decl(self.tc.declarations, const.name)

    def export(self, h):
        return self.store.export_term(h)

    # ---- whnf ------------------------------------------------------------

    def whnf_core(self, h):
        """
        Weak head normal form without unfolding definitions: beta, zeta,
        projection of a constructor, iota and quot only.
        """
        store = self.store
        if is_leaf(h):
            return h
        cached = store.memo(h, M_WHNF_CORE)
        if cached != 0:
            return cached
        # A term already known to be in full WHNF is whnf_core-normal.
        cached = store.memo(h, M_WHNF)
        if cached == h:
            return h
        if stack_almost_full():
            raise RawBail("whnf_core: stack")
        start = h
        tc = self.tc
        while True:
            tc.tick_wall_time()
            next = self._whnf_core_step(h)
            if next == 0:
                break
            h = next
        store.set_memo(start, M_WHNF_CORE, h)
        return h

    def _whnf_core_step(self, h):
        """One whnf_core step of ``h``, or 0 when there is none."""
        store = self.store
        kind = store.kind(h)
        if kind == KIND_APP:
            fn = store.field_a(h)
            arg = store.field_b(h)
            fn_whnf = self.whnf_core(fn)
            if fn_whnf != fn:
                return store.cons(KIND_APP, fn_whnf, arg, 0)
            if store.kind(fn) == KIND_LAMBDA:
                if self.tc.tracer.recording:
                    self.tc.tracer.beta()
                return store.instantiate(store.field_b(fn), arg, 0)
            reduced = self.try_iota(h)
            if reduced != 0:
                return reduced
            return self.try_quot_lift(h)
        if kind == KIND_LET:
            pair = store.field_b(h)
            return store.instantiate(store.field_b(pair), store.field_a(pair), 0)
        if kind == KIND_PROJ:
            return self.try_proj(h)
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
        the spine re-applied, or 0 when the head isn't unfoldable."""
        store = self.store
        head, args = store.unapp(h)
        const = store.const_leaf(head)
        if const is None:
            return 0
        val = self._delta_value(head, const)
        if val == 0:
            return 0
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
        j = leaf_index(head)
        val = self._delta_memo.get(j, -1)
        if val >= 0:
            return val
        decl = self._decl(const)
        val = 0
        if decl is not None and isinstance(decl.w_kind, W_Definition):
            target = decl.w_kind.get_delta_reduce_target()
            if target is not None:
                if self.tc.tracer.recording:
                    self.tc.tracer.delta(const.name)
                val = self.store.import_term(
                    apply_const_level_params(const, target, self.tc),
                )
        self._delta_memo[j] = val
        return val

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
        v1 = self._nat_value(self.whnf(store.field_b(fn)))
        if v1 is None:
            return 0
        v2 = self._nat_value(self.whnf(store.field_b(h)))
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

    def try_proj(self, h):
        """Projection of a constructor application, or 0."""
        store = self.store
        struct = self.whnf(store.field_a(h))
        lit = None
        if is_leaf(struct):
            e = store.leaf(struct)
            if isinstance(e, W_LitStr):
                lit = e
        if lit is not None:
            struct = self.whnf(store.import_term(lit.build_str_expr(self.tc)))
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
        idx = kind.num_params + store.field_b(h)
        n = len(args)
        if idx < n:
            # args are outermost-first: field i of a left-to-right list
            # sits at n - 1 - i.
            return args[n - 1 - idx]
        return 0

    def try_quot_lift(self, h):
        """``Quot.lift f h (Quot.mk r a) ⇒ f a``, or 0."""
        store = self.store
        head, args = store.unapp(h)
        const = store.const_leaf(head)
        if const is None or len(args) != 6:
            return 0
        if not const.name.syntactic_eq(W_App._QUOT_LIFT):
            return 0
        mk = self.whnf(args[0])
        mk_head, mk_args = store.unapp(mk)
        mk_const = store.const_leaf(mk_head)
        if mk_const is None or len(mk_args) != 3:
            return 0
        if not mk_const.name.syntactic_eq(W_App._QUOT_MK):
            return 0
        return store.cons(KIND_APP, args[2], mk_args[0], 0)

    def try_iota(self, h):
        """One recursor iota step of the spine ``h``, or 0."""
        store = self.store
        tc = self.tc
        target, args = store.unapp(h)
        const = store.const_leaf(target)
        if const is None:
            return 0
        decl = self._decl(const)
        if decl is None:
            return 0
        rec = decl.w_kind
        if not isinstance(rec, W_Recursor):
            return 0
        skip = rec.num_params + rec.num_indices + rec.num_minors + rec.num_motives
        major_idx = len(args) - 1 - skip
        if major_idx < 0:
            return 0

        # `Nat.rec motive zero succ (literal N)` in one step.
        if major_idx == 0 and const.name.syntactic_eq(_NAT_REC_NAME):
            lit = store.litnat_leaf(args[0])
            if lit is not None:
                if tc.tracer.recording:
                    tc.tracer.iota(const.name)
                succ_case = args[1]
                zero_case = args[2]
                motive = args[3]
                if lit.val.eq(rbigint.fromint(0)):
                    return zero_case
                pred = store.leaf_for(_mk_w_litnat(lit.val.sub(rbigint.fromint(1))))
                rec_at_pred = store.cons(KIND_APP, store.cons(KIND_APP, store.cons(
                    KIND_APP, store.cons(KIND_APP, target, motive, 0),
                    zero_case, 0), succ_case, 0), pred, 0)
                return store.cons(
                    KIND_APP, store.cons(KIND_APP, succ_case, pred, 0),
                    rec_at_pred, 0,
                )

        major = self.whnf(args[major_idx])

        if rec.k == 1:
            major = self._to_cnstr_when_k(rec, args, major)
            if major == 0:
                return 0

        lit = store.litnat_leaf(major)
        if lit is not None:
            major = store.import_term(lit.one_step_constructor(tc))
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
        n_args = len(args)
        # args are outermost-first; the first `total` declared arguments
        # (params, motives, minors) are the last `total` entries.
        total = rec.num_params + rec.num_motives + rec.num_minors
        assert total >= 0
        result = rhs
        i = n_args - 1
        stop = n_args - total
        while i >= stop:
            result = store.cons(KIND_APP, result, args[i], 0)
            i -= 1
        # The constructor's fields, left to right.
        n_ctor = len(ctor_args)
        i = n_ctor - 1 - ctor_kind.num_params
        stop = n_ctor - 1 - (ctor_kind.num_params + rule.num_fields)
        while i > stop:
            if i < 0:
                break
            result = store.cons(KIND_APP, result, ctor_args[i], 0)
            i -= 1
        # Then whatever followed the major premise.
        result = store.apply_rev(result, args, major_idx - 1)
        if tc.tracer.recording:
            tc.tracer.iota(const.name)
        return result

    def _rule_rhs(self, target, const, ctor_head, rule):
        key = (leaf_index(target) << 30) | leaf_index(ctor_head)
        rhs = self._rule_memo.get(key, 0)
        if rhs != 0:
            return rhs
        rhs = self.store.import_term(
            apply_const_level_params(const, rule.rhs, self.tc),
        )
        self._rule_memo[key] = rhs
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
            ctor = store.cons(KIND_APP, ctor, args[i], 0)
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
            result = store.cons(KIND_APP, result, type_args[i], 0)
            i -= 1
        for i in range(ctor_kind.num_fields):
            result = store.cons(
                KIND_APP, result, store.proj(induct_name, i, major), 0,
            )
        return result

    # ---- inference -------------------------------------------------------

    def fvar_for(self, h):
        """The canonical free variable opening the binder record ``h``."""
        fv = self._fvars.get(h, 0)
        if fv != 0:
            return fv
        store = self.store
        fv = store.leaf_for(W_FVar(store.binder_of(h)))
        j = leaf_index(fv)
        store.leaf_infer[j] = store.field_a(h)
        store.leaf_checked[j] = 1
        self._fvars[h] = fv
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
            raise RawBail("infer: stack")
        kind = store.kind(h)
        if kind == KIND_APP:
            t = self._infer_app(h, check)
        elif kind == KIND_LAMBDA:
            t = self._infer_lambda(h, check)
        elif kind == KIND_FORALL:
            t = self._infer_forall(h, check)
        elif kind == KIND_LET:
            t = self._infer_let(h, check)
        elif kind == KIND_PROJ:
            t = self._infer_proj(h, check)
        else:
            raise RawBail("infer: pair")
        if check:
            store.set_memo(h, M_INFER_CHECKED, t)
        store.set_memo(h, M_INFER, t)
        return t

    def _check_leaf(self, h):
        store = self.store
        e = store.leaf(h)
        if isinstance(e, W_Const):
            self.tc.check_reference(e, get_decl(self.tc.declarations, e.name))
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
                store.leaf_checked[j] = 1
            if not decl.levels:
                t = store.import_term(decl.type)
            else:
                t = store.import_term(
                    apply_const_level_params(e, decl.type, tc),
                )
        elif isinstance(e, W_Sort):
            t = store.leaf_for(e.level.succ().sort())
            store.leaf_checked[j] = 1
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
            raise RawBail("infer: loose bvar")
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
        i = n - 1
        while i >= 0:
            arg = args[i]
            fn_type_whnf = self.whnf(fn_type)
            if store.kind(fn_type_whnf) != KIND_FORALL:
                spine = head
                j = n - 1
                while j > i:
                    spine = store.cons(KIND_APP, spine, args[j], 0)
                    j -= 1
                raise W_NotAFunction(
                    tc, self.export(spine), inferred_type=self.export(fn_type),
                )
            if check:
                arg_type = self.infer(arg, True)
                domain = store.field_a(fn_type_whnf)
                if not self.def_eq(domain, arg_type):
                    raise W_TypeError(
                        tc, self.export(arg), self.export(domain),
                        inferred_type=self.export(arg_type),
                    )
            fn_type = store.instantiate(store.field_b(fn_type_whnf), arg, 0)
            i -= 1
        return fn_type

    def _infer_lambda(self, h, check):
        store = self.store
        type_h = store.field_a(h)
        if check:
            self._ensure_sort(type_h, True)
        fvar = self.fvar_for(h)
        body_type = self.infer(store.instantiate(store.field_b(h), fvar, 0), check)
        return store.cons(
            KIND_FORALL, type_h, store.bind_fvar(body_type, fvar, 0), 0,
            store.info(h),
        )

    def _infer_forall(self, h, check):
        store = self.store
        type_h = store.field_a(h)
        binder_level = self._ensure_sort(type_h, check)
        fvar = self.fvar_for(h)
        body = store.instantiate(store.field_b(h), fvar, 0)
        body_level = self._ensure_sort(body, check)
        return store.leaf_for(binder_level.imax(body_level).sort())

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

    def _infer_proj(self, h, check):
        store = self.store
        tc = self.tc
        struct = store.field_a(h)
        field_index = store.field_b(h)
        struct_name = store.name_of(h)
        struct_type = self.whnf(self.infer(struct, check))
        type_head, type_args = store.unapp(struct_type)

        struct_decl = find_decl(tc.declarations, struct_name)
        if struct_decl is None:
            raise InvalidProjection.unknown_structure(
                struct_name, field_index, self.export(struct),
            )
        head_const = store.const_leaf(type_head)
        if head_const is None:
            raise InvalidProjection.not_a_structure_type(
                struct_name, field_index, self.export(struct),
            )
        if not head_const.is_named(struct_name):
            raise InvalidProjection.mismatched_structure(
                struct_name, field_index, head_const.name, self.export(struct),
            )
        struct_kind = struct_decl.w_kind
        if not isinstance(struct_kind, W_Inductive):
            raise InvalidProjection.not_an_inductive(
                struct_name, field_index, self.export(struct),
            )
        if len(struct_kind.ctor_names) != 1:
            raise InvalidProjection.not_a_structure(
                struct_name, field_index, len(struct_kind.ctor_names),
                self.export(struct),
            )
        ind_type = self.whnf(store.import_term(
            apply_const_level_params(head_const, struct_decl.type, tc),
        ))
        ind_sort = store.sort_leaf(ind_type)
        is_prop_type = ind_sort is not None and ind_sort.level.eq(W_LEVEL_ZERO)

        ctor_decl = struct_kind.constructor_decls(tc.declarations)[0]
        ctor_type = store.import_term(
            apply_const_level_params(head_const, ctor_decl.type, tc),
        )
        # Type arguments left to right.
        i = len(type_args) - 1
        while i >= 0:
            ctor_type = self.whnf(ctor_type)
            if store.kind(ctor_type) != KIND_FORALL:
                raise InvalidProjection.out_of_bounds(
                    struct_name, field_index, 0, self.export(struct),
                )
            ctor_type = store.instantiate(store.field_b(ctor_type), type_args[i], 0)
            i -= 1
        i = -1
        for i in range(field_index):
            ctor_type = self.whnf(ctor_type)
            if store.kind(ctor_type) != KIND_FORALL:
                raise InvalidProjection.out_of_bounds(
                    struct_name, field_index, i + 1, self.export(struct),
                )
            body = store.field_b(ctor_type)
            if store.loose_bvar_range(body) > 0:
                if is_prop_type:
                    if not self._is_prop(store.field_a(ctor_type), check):
                        raise InvalidProjection.non_prop_field(
                            struct_name, field_index, self.export(struct),
                        )
                ctor_type = store.instantiate(
                    body, store.proj(struct_name, i, struct), 0,
                )
            else:
                ctor_type = body
        ctor_type = self.whnf(ctor_type)
        if store.kind(ctor_type) != KIND_FORALL:
            raise InvalidProjection.out_of_bounds(
                struct_name, field_index, i + 1, self.export(struct),
            )
        field_type = store.field_a(ctor_type)
        if is_prop_type:
            if not self._is_prop(field_type, check):
                raise InvalidProjection.non_prop_field(
                    struct_name, field_index, self.export(struct),
                )
        return field_type

    def _is_prop(self, h, check):
        """Whether the type ``h`` lives in `Prop`."""
        sort = self.store.sort_leaf(self.whnf(self.infer(h, check)))
        return sort is not None and sort.level.eq(W_LEVEL_ZERO)

    # ---- definitional equality --------------------------------------------

    def _find(self, h):
        eqv = self._eqv
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
        if self._find(h1) == self._find(h2):
            if tracing:
                tracer.eqv_hit()
                return self._traced_result(True)
            return True
        key = self._pair_key(h1, h2)
        if key != 0 and self._neq.get(key, 0) != 0:
            if tracing:
                return self._traced_result(False)
            return False
        store = self.store
        if store.kind(h1) == KIND_APP and store.kind(h2) == KIND_APP:
            if self._spine_cheap_eq(h1, h2):
                self._union(h1, h2)
                if tracing:
                    tracer.eqv_hit()
                    return self._traced_result(True)
                return True
        if stack_almost_full():
            raise RawBail("def_eq: stack")
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

    def _def_eq_uncached(self, h1, h2):
        store = self.store
        tracer = self.tc.tracer
        h1 = self.whnf_core(h1)
        h2 = self.whnf_core(h2)
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
        return self._def_eq_core(h1, h2)

    def _def_eq_offset(self, h1, h2):
        store = self.store
        while True:
            lit1 = store.litnat_leaf(h1)
            lit2 = store.litnat_leaf(h2)
            if lit1 is not None and lit2 is not None:
                if lit1.val.eq(lit2.val):
                    return _OFFSET_TRUE
                return _OFFSET_FALSE
            if self._is_nat_zero(h1) and self._is_nat_zero(h2):
                return _OFFSET_TRUE
            pred1 = self._nat_succ_pred(h1)
            if pred1 == 0:
                return _OFFSET_UNDEF
            pred2 = self._nat_succ_pred(h2)
            if pred2 == 0:
                return _OFFSET_UNDEF
            self.tc.tick_wall_time()
            h1 = pred1
            h2 = pred2

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
                h1 = self.whnf_core(h1)
                h2 = self.whnf_core(h2)
                if h1 == h2:
                    return _LD_TRUE, h1, h2

            if not store.has_fvar(h1) and not store.has_fvar(h2):
                if store.kind(h1) == KIND_APP:
                    reduced = self.try_reduce_nat(h1)
                    if reduced != 0:
                        h1 = reduced
                        continue
                if store.kind(h2) == KIND_APP:
                    reduced = self.try_reduce_nat(h2)
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
                if store.kind(head1) == KIND_PROJ:
                    new1 = self.whnf_core(h1)
                    if new1 != h1:
                        h1 = new1
                        continue
                new2 = self.try_unfold_head(h2)
                if new2 == 0:
                    return _LD_UNDEF, h1, h2
                h2 = self.whnf_core(new2)
                continue
            if kind2 is None:
                if store.kind(head2) == KIND_PROJ:
                    new2 = self.whnf_core(h2)
                    if new2 != h2:
                        h2 = new2
                        continue
                new1 = self.try_unfold_head(h1)
                if new1 == 0:
                    return _LD_UNDEF, h1, h2
                h1 = self.whnf_core(new1)
                continue

            hint1 = kind1.hint
            hint2 = kind2.hint
            if hint1 == HINT_ABBREV and hint2 != HINT_ABBREV:
                new1 = self.try_unfold_head(h1)
                if new1 == 0:
                    return _LD_UNDEF, h1, h2
                h1 = self.whnf_core(new1)
                continue
            if hint2 == HINT_ABBREV and hint1 != HINT_ABBREV:
                new2 = self.try_unfold_head(h2)
                if new2 == 0:
                    return _LD_UNDEF, h1, h2
                h2 = self.whnf_core(new2)
                continue

            if hint1 >= 0 and head1 == head2:
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

            if hint1 > hint2:
                new1 = self.try_unfold_head(h1)
                if new1 == 0:
                    return _LD_UNDEF, h1, h2
                h1 = self.whnf_core(new1)
                continue
            if hint1 < hint2:
                new2 = self.try_unfold_head(h2)
                if new2 == 0:
                    return _LD_UNDEF, h1, h2
                h2 = self.whnf_core(new2)
                continue

            new1 = self.try_unfold_head(h1)
            new2 = self.try_unfold_head(h2)
            if new1 == 0 and new2 == 0:
                return _LD_UNDEF, h1, h2
            if new1 != 0:
                h1 = self.whnf_core(new1)
            if new2 != 0:
                h2 = self.whnf_core(new2)
        return _LD_UNDEF, h1, h2

    def _failed_before(self, h1, h2):
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
                    if e1.name.syntactic_eq(e2.name) and e1.def_eq(e2, self.tc):
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
                        and store.name_of(h1).syntactic_eq(store.name_of(h2))
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
                store.import_term(lit1.one_step_constructor(self.tc)), h2,
            )
        lit2 = store.litnat_leaf(h2)
        if lit2 is not None:
            return self.def_eq(
                h1, store.import_term(lit2.one_step_constructor(self.tc)),
            )
        if is_leaf(h1):
            s1 = store.leaf(h1)
            if isinstance(s1, W_LitStr):
                return self.def_eq(
                    store.import_term(s1.build_str_expr(self.tc)), h2,
                )
        if is_leaf(h2):
            s2 = store.leaf(h2)
            if isinstance(s2, W_LitStr):
                return self.def_eq(
                    h1, store.import_term(s2.build_str_expr(self.tc)),
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
        body = store.cons(KIND_APP, store.shift(h2, 1, 0), store.bvar(0), 0)
        return store.cons(KIND_LAMBDA, store.field_a(t2), body, 0, store.info(t2))

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
        if not self.def_eq(ty, val_ty):
            return W_TypeError(tc, value, type, inferred_type=self.export(val_ty))
        return None


_OFFSET_UNDEF = 0
_OFFSET_TRUE = 1
_OFFSET_FALSE = 2
_LD_TRUE = 1
_LD_UNDEF = 0
