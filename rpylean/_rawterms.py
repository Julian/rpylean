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

from rpylean.objects import (
    Binder,
    W_App,
    W_BVar,
    W_Closure,
    W_Expr,
    W_ForAll,
    W_FVar,
    W_Lambda,
    W_Let,
    W_Proj,
    _mk_app_in,
    _mk_w_forall_in,
    _mk_w_lambda_in,
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
        'recs', 'rec_info', 'nrecs', 'cap',
        'table', 'tmask',
        'leaves', 'leaf_meta', 'leaf_bvar', 'nleaves', 'leaf_cap',
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
        _raw_free(self.table)
        _raw_free(self.leaf_meta)
        _raw_free(self.leaf_bvar)
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
        cap = self.cap * 2
        recs = _raw_alloc(cap * REC_WORDS)
        info = _raw_alloc(cap)
        n = self.nrecs * REC_WORDS
        i = 0
        while i < n:
            recs[i] = old[i]
            i += 1
        i = 0
        while i < self.nrecs:
            info[i] = old_info[i]
            i += 1
        self.recs = recs
        self.rec_info = info
        self.cap = cap
        _raw_free(old)
        _raw_free(old_info)

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
            i = 0
            while i < j:
                meta[i] = self.leaf_meta[i]
                bv[i] = self.leaf_bvar[i]
                i += 1
            _raw_free(self.leaf_meta)
            _raw_free(self.leaf_bvar)
            self.leaf_meta = meta
            self.leaf_bvar = bv
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
    """

    _attrs_ = ['tc', 'store']

    def __init__(self, tc):
        self.tc = tc
        self.store = RawTermStore(tc)

    def free(self):
        self.store.free()

    def check_value(self, type, value, prop):
        """
        Check a definition-like declaration: ``type`` must be a sort (a
        proposition when ``prop``, for a theorem) and ``value`` must
        have that type. Returns ``None`` when accepted, a `W_CheckError`
        when rejected.
        """
        store = self.store
        store.import_term(type)
        store.import_term(value)
        raise RawBail("check: unported")
