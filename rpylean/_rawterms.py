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
from rpython.rlib.rstack import stack_almost_full
from rpython.rtyper.lltypesystem import lltype, rffi

from rpython.rlib.rbigint import rbigint

from rpylean.objects import (
    NAT_SUCC,
    NAT_ZERO,
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
    W_Proj,
    W_Recursor,
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
KIND_PROJ = 4     # a = struct, b = field index; info = the struct Name
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
    # Handles and packed keys are small and sequential; smear the low
    # bits before masking so neighbouring keys don't march in lockstep.
    return (k * 1000003) ^ (k >> 17)


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
        'leaves', 'leaf_meta', 'leaf_bvar', 'leaf_whnf', 'nleaves',
        'leaf_cap',
        'infos', 'names',
        '_bvar_leaves', '_fvar_leaves', '_content_leaves',
        '_import_memo', '_export_memo',
        '_inst_memo', '_shift_memo',
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
        self.nleaves = 0
        #: Binder infos (boxed `Binder`s, for the name and style) and
        #: `Name`s (for projections and lets), by `rec_info` index.
        self.infos = []
        self.names = []
        self._bvar_leaves = {}
        self._fvar_leaves = {}
        self._content_leaves = {}
        self._import_memo = {}
        self._export_memo = {}
        self._inst_memo = RawIntMap(1 << 12)
        self._shift_memo = RawIntMap(1 << 10)
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
        self._inst_memo.free()
        self._shift_memo.free()

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
        return self.cons(
            KIND_PROJ, struct, field_index, 0, self._name_index(struct_name),
        )

    def let(self, name, type, value, body):
        pair = self.cons(KIND_PAIR, value, body, 0)
        return self.cons(KIND_LET, type, pair, 0, self._name_index(name))

    def _info_index(self, binder):
        i = len(self.infos)
        self.infos.append(binder)
        return i

    def _name_index(self, name):
        i = len(self.names)
        self.names.append(name)
        return i

    # ---- leaves ----------------------------------------------------------

    def _new_leaf(self, e, bvar):
        j = self.nleaves
        if j == self.leaf_cap:
            cap = self.leaf_cap * 2
            meta = _raw_alloc(cap)
            bv = _raw_alloc(cap)
            wh = _raw_alloc(cap)
            i = 0
            while i < j:
                meta[i] = self.leaf_meta[i]
                bv[i] = self.leaf_bvar[i]
                wh[i] = self.leaf_whnf[i]
                i += 1
            _raw_free(self.leaf_meta)
            _raw_free(self.leaf_bvar)
            _raw_free(self.leaf_whnf)
            self.leaf_meta = meta
            self.leaf_bvar = bv
            self.leaf_whnf = wh
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
                r = self.cons(KIND_PROJ, na, b, 0, info)
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
            r = self.cons(KIND_PROJ, self.shift(a, count, depth), b, 0, info)
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

    Reduction mirrors the boxed kernel step for step: `whnf_core` is
    beta / zeta / projection / iota / quot only, `whnf` adds native Nat
    arithmetic and one delta layer per iteration, and iota evaluates
    the major premise with `whnf`.
    """

    _attrs_ = ['tc', 'store', '_delta_memo', '_rule_memo']

    def __init__(self, tc):
        self.tc = tc
        self.store = RawTermStore(tc)
        #: const leaf index -> handle of its unfolded value (0 = none)
        self._delta_memo = {}
        #: (rec const leaf index, ctor leaf index) -> rule rhs handle
        self._rule_memo = {}

    def free(self):
        self.store.free()

    def _decl(self, const):
        return find_decl(self.tc.declarations, const.name)

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
        tc = self.tc
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
            raise RawBail("iota: k-like")

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
        head = store.head(major)
        head_const = store.const_leaf(head)
        if head_const is not None:
            head_decl = find_decl(tc.declarations, head_const.name)
            if head_decl is not None and head_decl.w_kind.is_constructor():
                return 0
        raise RawBail("iota: struct-eta major")

    # ---- checking --------------------------------------------------------

    def check_value(self, type, value, prop):
        """
        Check a definition-like declaration: ``type`` must be a sort (a
        proposition when ``prop``, for a theorem) and ``value`` must
        have that type. Returns ``None`` when accepted, a `W_CheckError`
        when rejected.
        """
        store = self.store
        ty = store.import_term(type)
        store.import_term(value)
        self.whnf(ty)
        raise RawBail("check: unported")
