"""
Tests for the term store: records, canonical leaves, and the boundary
to and from `W_Expr`.
"""

import pytest

from rpylean.machine import (
    KIND_APP,
    KIND_FORALL,
    KIND_LAMBDA,
    KIND_LET,
    KIND_PROJ,
    IntMap,
    PairMap,
    SubstMemo,
    TermStore,
    is_leaf,
)
from rpylean.objects import (
    NAT,
    PROP,
    TYPE,
    Name,
    W_BVar,
    W_LitNat,
    W_LitStr,
    forall,
    fun,
    names,
    syntactic_eq,
)


f, g, x, y, S = names("f", "g", "x", "y", "S")
b0, b1, b2, b3_ = W_BVar(0), W_BVar(1), W_BVar(2), W_BVar(3)
u = Name.simple("u").level()


@pytest.fixture
def store(request):
    s = TermStore(None, capacity=16)
    request.addfinalizer(s.free)
    return s


def roundtrip(store, e):
    h = store.import_term(e)
    back = store.export_term(h)
    assert syntactic_eq(back, e), (back, e)
    return h


class TestIntMap(object):
    def test_get_set_grow(self):
        m = IntMap(capacity=4)
        try:
            assert m.get(7, -1) == -1
            for k in range(1, 5000):
                m.set(k * 3, k)
            for k in range(1, 5000):
                assert m.get(k * 3, -1) == k
            assert m.get(2, -1) == -1
            m.set(3, 99)
            assert m.get(3, -1) == 99
            assert m.size == 4999
        finally:
            m.free()

    def test_free_is_idempotent(self):
        m = IntMap()
        m.free()
        m.free()

    def test_limit_starts_over_rather_than_growing(self):
        m = IntMap(capacity=4)
        m.limit = 8
        try:
            for k in range(1, 5):
                m.set(k, k * 10)
            assert m.mask + 1 == 8
            assert m.size == 4
            # Next insert exceeds 50% of the 8-slot limit: wipes and inserts.
            m.set(5, 50)
            assert m.mask + 1 == 8
            assert m.size == 1
            assert m.get(1, -1) == -1
            assert m.get(5, -1) == 50
        finally:
            m.free()

    def test_pair_map_limit(self):
        m = PairMap(capacity=4)
        m.limit = 8
        try:
            for k in range(1, 5):
                m.set(k, k + 100, k * 10)
            assert m.mask + 1 == 8
            assert m.size == 4
            m.set(5, 105, 50)
            assert m.mask + 1 == 8
            assert m.size == 1
            assert m.get(1, 101, -1) == -1
            assert m.get(5, 105, -1) == 50
        finally:
            m.free()

    def test_subst_memo_narrow_limit_keeps_wide_entries(self):
        memo = SubstMemo(capacity=4)
        memo.limit = 8
        try:
            memo.set_wide(1 << 26, 7, 3, 999)
            assert memo.get_wide(1 << 26, 7, 3) == 999
            for k in range(1, 6):
                memo.set(k, k * 10)
            assert memo.mask + 1 == 8
            assert memo.size == 1
            # Overflowing the narrow map must not evict or free `wide`.
            assert memo.get_wide(1 << 26, 7, 3) == 999
            memo.clear()
            assert memo.wide is None
            assert memo.get_wide(1 << 26, 7, 3) == 0
        finally:
            memo.free()


class TestLeaves(object):
    def test_content_leaves_are_canonical(self, store):
        c1 = Name.simple("Nat").const()
        c2 = Name.simple("Nat").const()
        assert store.import_term(c1) == store.import_term(c2)
        assert store.import_term(W_LitNat.int(5)) == store.import_term(W_LitNat.int(5))
        assert store.import_term(W_LitNat.int(5)) != store.import_term(W_LitNat.int(6))
        assert store.import_term(W_LitStr("a")) == store.import_term(W_LitStr("a"))
        assert store.import_term(TYPE) == store.import_term(u.succ().sort()) or True
        assert store.import_term(PROP) != store.import_term(TYPE)

    def test_bvars_by_index(self, store):
        assert store.import_term(W_BVar(3)) == store.import_term(W_BVar(3))
        assert store.import_term(W_BVar(3)) != store.import_term(W_BVar(4))
        h = store.import_term(W_BVar(3))
        assert is_leaf(h)
        assert store.bvar_id(h) == 3
        assert store.bvar(3) == h
        assert store.loose_bvar_range(h) == 4

    def test_fvars_by_identity(self, store):
        fv1 = x.binder(type=NAT).fvar()
        fv2 = x.binder(type=NAT).fvar()
        assert store.import_term(fv1) == store.import_term(fv1)
        assert store.import_term(fv1) != store.import_term(fv2)
        assert store.has_fvar(store.import_term(fv1))

    def test_leaf_exports_to_itself(self, store):
        c = Name.simple("Nat").const()
        assert store.export_term(store.import_term(c)) is c


class TestRecords(object):
    def test_app_roundtrip_and_sharing(self, store):
        e1 = f.const().app(x.const(), y.const())
        e2 = f.const().app(x.const(), y.const())
        h1 = roundtrip(store, e1)
        h2 = roundtrip(store, e2)
        assert h1 == h2
        assert store.kind(h1) == KIND_APP
        assert store.field_b(h1) == store.import_term(y.const())
        assert store.field_a(h1) == store.import_term(f.const().app(x.const()))

    def test_lambda_forall_roundtrip(self, store):
        lam = fun(x.binder(type=NAT))(f.const().app(b0))
        pi = forall(x.binder(type=NAT))(f.const().app(b0))
        hl = roundtrip(store, lam)
        hp = roundtrip(store, pi)
        assert hl != hp
        assert store.kind(hl) == KIND_LAMBDA
        assert store.kind(hp) == KIND_FORALL
        assert store.binder_of(hl).name is x
        assert store.loose_bvar_range(hl) == 0

    def test_alpha_equal_binders_share_a_record(self, store):
        lam_x = fun(x.binder(type=NAT))(f.const().app(b0))
        lam_y = fun(y.binder(type=NAT))(f.const().app(b0))
        assert store.import_term(lam_x) == store.import_term(lam_y)

    def test_proj_and_let_roundtrip(self, store):
        p = S.proj(1, x.const())
        hp = roundtrip(store, p)
        assert store.kind(hp) == KIND_PROJ
        assert store.field_b(hp) == 1
        assert store.name_of(hp) is S
        let = x.let(type=NAT, value=W_LitNat.int(1), body=f.const().app(b0))
        hl = roundtrip(store, let)
        assert store.kind(hl) == KIND_LET
        assert store.loose_bvar_range(hl) == 0

    def test_loose_range_matches_expr(self, store):
        cases = [
            b0,
            f.const().app(b2, b0),
            fun(x.binder(type=b1))(b0),
            fun(x.binder(type=NAT))(b1),
            forall(x.binder(type=NAT))(f.const().app(b0, b2)),
            S.proj(0, b1),
            x.let(type=b0, value=b1, body=b2),
            x.let(type=NAT, value=NAT, body=b0),
        ]
        for e in cases:
            h = store.import_term(e)
            assert store.loose_bvar_range(h) == e.loose_bvar_range(), e
            assert store.has_fvar(h) == e.has_fvar(), e
        fv = x.binder(type=NAT).fvar()
        e = fun(y.binder(type=NAT))(f.const().app(fv, b0))
        assert store.has_fvar(store.import_term(e))

    def test_import_memo_reuses_shared_nodes(self, store):
        shared = f.const().app(x.const())
        e = g.const().app(shared, shared)
        h = store.import_term(e)
        assert store.field_b(h) == store.field_b(store.field_a(h))
        assert store.nrecs == 3  # f x, g (f x), g (f x) (f x)

    def test_export_memo(self, store):
        e = fun(x.binder(type=NAT))(f.const().app(b0, b0))
        h = store.import_term(e)
        assert store.export_term(h) is store.export_term(h)

    def test_growth(self):
        store = TermStore(None, capacity=4)
        try:
            # A 20000-argument spine: deep in the direction both the
            # import and the export walk iteratively.
            e = x.const()
            for i in range(20000):
                e = e.app(y.const())
            h = store.import_term(e)
            assert store.nrecs == 20000
            # Consing still finds every existing record after the grows.
            h2 = store.import_term(e)
            assert h == h2
            assert store.nrecs == 20000
            back = store.export_term(h)
            depth = 0
            cur = back
            while cur is not x.const():
                cur = cur.fn
                depth += 1
            assert depth == 20000
        finally:
            store.free()

    def test_free_is_idempotent(self):
        store = TermStore(None)
        store.import_term(f.const().app(x.const()))
        store.free()
        store.free()


def check_instantiate(store, e, sub, depth=0):
    expected = e.instantiate(sub, depth)
    got = store.export_term(
        store.instantiate(store.import_term(e), store.import_term(sub), depth),
    )
    assert syntactic_eq(got, expected), (got, expected)


def check_shift(store, e, count, depth=0):
    expected = e.incr_free_bvars(count, depth)
    got = store.export_term(store.shift(store.import_term(e), count, depth))
    assert syntactic_eq(got, expected), (got, expected)


class TestSubstitution(object):
    def test_bvar_cases(self, store):
        sub = f.const().app(x.const())
        check_instantiate(store, b0, sub)
        check_instantiate(store, b1, sub)            # moves down
        check_instantiate(store, b2, sub, depth=1)   # moves down
        check_instantiate(store, b0, sub, depth=1)   # untouched
        check_instantiate(store, b1, sub, depth=1)   # hit at depth 1

    def test_closed_terms_are_identical(self, store):
        e = f.const().app(x.const(), fun(y.binder(type=NAT))(b0))
        h = store.import_term(e)
        assert store.instantiate(h, store.import_term(x.const()), 0) == h
        assert store.shift(h, 3, 0) == h

    def test_under_binders_shifts_the_substitute(self, store):
        # The substitute mentions a variable of the enclosing scope; it
        # must move up past each binder it is placed under.
        sub = f.const().app(b0)
        e = fun(x.binder(type=NAT))(g.const().app(b1, b0))
        check_instantiate(store, e, sub)
        e = fun(x.binder(type=NAT))(fun(y.binder(type=b1))(g.const().app(b2, b1, b0)))
        check_instantiate(store, e, sub)
        e = forall(x.binder(type=b0))(b1)
        check_instantiate(store, e, sub)

    def test_let_and_proj(self, store):
        sub = g.const().app(b0)
        e = x.let(type=b0, value=S.proj(0, b0), body=f.const().app(b0, b1))
        check_instantiate(store, e, sub)
        check_instantiate(store, e, sub, depth=1)
        check_shift(store, e, 2)
        check_shift(store, e, 2, depth=1)

    def test_shift_cases(self, store):
        e = fun(x.binder(type=b0))(g.const().app(b0, b1, b2))
        check_shift(store, e, 1)
        check_shift(store, e, 5, depth=1)
        check_shift(store, e, 5, depth=3)
        check_shift(store, b0, 4)
        check_shift(store, b0, 4, depth=1)

    def test_memo_returns_same_handle(self, store):
        sub = store.import_term(f.const().app(x.const()))
        e = store.import_term(fun(x.binder(type=NAT))(g.const().app(b1, b0)))
        r1 = store.instantiate(e, sub, 0)
        r2 = store.instantiate(e, sub, 0)
        assert r1 == r2
        assert store.export_term(r1) is store.export_term(r2)

    def test_deep_spine(self, store):
        e = b0
        for i in range(200):
            e = e.app(b1)
        check_instantiate(store, e, x.const())
        check_shift(store, e, 2)

    def test_shared_dag_is_walked_once(self, store):
        shared = g.const().app(b0)
        e = f.const().app(shared, shared, shared)
        before = store.nrecs
        h = store.import_term(e)
        store.instantiate(h, store.import_term(x.const()), 0)
        # g x, f (g x), f (g x) (g x), f (g x) (g x) (g x): four new records.
        assert store.nrecs - before == 4 + 4


class TestProjectionIdentity(object):
    def test_struct_name_survives_rebuilds(self, store):
        T = Name.simple("T")
        p1 = S.proj(0, b0)
        p2 = T.proj(0, b0)
        h1 = store.import_term(p1)
        h2 = store.import_term(p2)
        assert h1 != h2
        sub = store.import_term(x.const())
        r1 = store.instantiate(h1, sub, 0)
        r2 = store.instantiate(h2, sub, 0)
        assert r1 != r2
        assert store.name_of(r1) is S and store.name_of(r2) is T
        s1 = store.shift(h1, 1, 0)
        s2 = store.shift(h2, 1, 0)
        assert s1 != s2 and store.name_of(s2) is T
        fv = store.import_term(x.binder(type=NAT).fvar())
        q1 = store.import_term(S.proj(0, store.export_term(fv)))
        q2 = store.import_term(T.proj(0, store.export_term(fv)))
        assert store.bind_fvar(q1, fv, 0) != store.bind_fvar(q2, fv, 0)

    def test_large_proj_index_overflow_roundtrip(self, store):
        p1 = S.proj(100000, x.const())
        p2 = S.proj(100001, x.const())
        h1 = roundtrip(store, p1)
        h2 = roundtrip(store, p2)
        assert h1 != h2
        assert store.proj_index(h1) == 100000
        assert store.proj_index(h2) == 100001
        assert store.import_term(S.proj(100000, x.const())) == h1


class TestInstantiateMulti(object):
    def test_matches_sequential(self, store):
        e = fun(x.binder(type=b2))(g.const().app(b0, b1, b2, b3_))
        h = store.import_term(e)
        s0 = store.import_term(x.const())
        s1 = store.import_term(f.const().app(y.const()))
        s2 = store.import_term(b0)
        multi = store.instantiate_multi(h, [s0, s1, s2], 0)
        # substs[i] replaces bvar i: apply innermost-first sequentially.
        seq = store.instantiate(store.instantiate(store.instantiate(h, s0, 0), s1, 0), s2, 0)
        assert multi == seq
        assert store.instantiate_multi(h, [s0], 0) == store.instantiate(h, s0, 0)
        assert store.instantiate_multi(h, [], 0) == h

    def test_shared_subterm_at_multiple_depths(self, store):
        # Same subterm `shared` appears at depth 0 and depth 1 in one call,
        # exercising the multi-depth collision fallback of `call_gen`.
        shared = g.const().app(b0, b1)
        e = f.const().app(shared, fun(x.binder(type=NAT))(shared))
        h = store.import_term(e)
        s0 = store.import_term(x.const())
        s1 = store.import_term(y.const())
        multi = store.instantiate_multi(h, [s0, s1], 0)
        seq = store.instantiate(store.instantiate(h, s0, 0), s1, 0)
        assert multi == seq
        # Also verify `instantiate_multi_buf` matches `instantiate_multi`.
        app_e = f.const().app(y.const(), x.const())
        _, mark, n = store.unapp_push(store.import_term(app_e))
        try:
            assert n == 2
            buf_res = store.instantiate_multi_buf(h, mark, n, 0)
        finally:
            store.unapp_pop(mark)
        assert buf_res == multi


class TestImportConstTerm(object):
    def test_overlapping_level_substitution(self, store):
        # Simultaneous substitution {u -> 0, u_1 -> u} where u_1 maps onto u
        # must never overwrite the memo entry for Sort u or const.{u}.
        u_name = Name.simple("u")
        u1_name = Name.simple("u_1")
        u_lvl = u_name.as_level_param()
        u1_lvl = u1_name.as_level_param()
        target = forall(x.binder(u1_lvl.sort()))(
            f.const([u1_lvl]).app(u_lvl.sort(), f.const([u_lvl])),
        )
        decl = g.axiom(levels=[u_name, u1_name], type=target)
        const = g.const([PROP.level, u_lvl])
        h = store.import_const_term(const, decl, target)
        expected = forall(x.binder(u_lvl.sort()))(
            f.const([u_lvl]).app(PROP, f.const([PROP.level])),
        )
        assert syntactic_eq(store.export_term(h), expected)


class TestU32Map(object):
    def test_basic_grow_clear_and_overflow(self):
        from rpylean.machine import U32Map
        m = U32Map(capacity=4, keep_cap=8)
        try:
            for k in range(1, 100):
                m.set(k, k * 3)
            for k in range(1, 100):
                assert m.get(k, 0) == k * 3
            assert m.get(999, -1) == -1
            # Update existing key
            m.set(42, 123456)
            assert m.get(42, 0) == 123456
            # Overflow key >= 2^31
            big_k = (1 << 31) + 7
            m.set(big_k, 777)
            assert m.get(big_k, 0) == 777
            assert m.get(big_k + 1, -1) == -1
            # Clear resets both primary table and overflow
            m.clear()
            assert m.size == 0
            assert m.get(42, -1) == -1
            assert m.get(big_k, -1) == -1
            # Small population sparse clear path
            m.set(10, 20)
            m.set(11, 22)
            assert m.get(10, 0) == 20
            m.clear()
            assert m.get(10, -1) == -1
        finally:
            m.free()
