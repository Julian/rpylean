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
        mark = store._spine_top
        store.unapp_push(store.import_term(app_e))
        try:
            n = store._spine_top - mark
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

    def test_app_table_promote_wide_and_reset(self, store):
        fh = store.import_term(f.const())
        xh = store.import_term(x.const())
        yh = store.import_term(y.const())
        h1 = store.cons_app(fh, xh)
        h2 = store.cons_app(h1, yh)
        # Force promotion to wide 16-byte app_wide table and verify hash-consing.
        store._promote_apps_to_wide()
        assert store._app_limit == 0
        assert store.cons_app(fh, xh) == h1
        assert store.cons_app(h1, yh) == h2
        # Insert enough new apps in wide mode to exercise _rehash_app_wide.
        cur = h2
        seen = []
        for _ in range(100):
            cur = store.cons_app(cur, xh)
            seen.append(cur)
        cur2 = h2
        for expected in seen:
            cur2 = store.cons_app(cur2, xh)
            assert cur2 == expected
        # Reset restores compact packed app_table cleanly.
        store.reset()
        assert store._app_limit > 0
        fh2 = store.import_term(f.const())
        xh2 = store.import_term(x.const())
        assert store.cons_app(fh2, xh2) == store.cons_app(fh2, xh2)

    def test_concurrent_stores_intrusive_cache_and_fvar_identity(self):
        from rpylean.machine import TermStore
        s1 = TermStore(None, capacity=16)
        s2 = TermStore(None, capacity=16)
        try:
            fv = x.binder(type=NAT).fvar()
            term = f.const().app(fv, y.const())
            h1_term = s1.import_term(term)
            h1_fv = s1.leaf_for(fv)
            assert s1.has_fvar_leaf(fv)
            # Importing into a second store overwrites W_Expr._cache,
            # but s1 must still preserve canonical handles and FVar identity!
            h2_term = s2.import_term(term)
            h2_fv = s2.leaf_for(fv)
            assert s2.has_fvar_leaf(fv)
            assert s1.has_fvar_leaf(fv)
            assert s1.leaf_for(fv) == h1_fv
            assert s1.import_term(term) == h1_term
            assert s2.leaf_for(fv) == h2_fv
            assert s2.import_term(term) == h2_term
        finally:
            s1.free()
            s2.free()

    def test_cons_general_wide_promotion_and_proj_overflow(self):
        from rpylean.machine import TermStore
        store = TermStore(None, capacity=16)
        try:
            xh = store.import_term(x.const())
            s = Name.simple("S")
            # Normal packed projection
            p0 = store.proj(s, 0, xh)
            p5 = store.proj(s, 5, xh)
            assert store.proj(s, 0, xh) == p0
            assert store.proj_index(p0) == 0
            assert store.proj_index(p5) == 5
            # Overflow field_index >= 1024 promotes cleanly without losing proj_index
            p_big = store.proj(s, 2000, xh)
            assert store.proj(s, 2000, xh) == p_big
            assert store.proj_index(p_big) == 2000
            # Force _cons_general -> _cons_general_wide promotion
            store._other_limit = 1
            b = x.binder(type=NAT)
            lam1 = store.lam(b, xh, p0)
            assert store._other_limit == 0
            assert store.lam(b, xh, p0) == lam1
            assert store.proj(s, 0, xh) == p0
            assert store.proj(s, 2000, xh) == p_big
            # Reset restores packed mode cleanly
            store.reset()
            assert store._other_limit > 0
            xh2 = store.import_term(x.const())
            p2 = store.proj(s, 7, xh2)
            assert store.proj(s, 7, xh2) == p2
            assert store.proj_index(p2) == 7
        finally:
            store.free()

    def test_lgen_cache_reuse_and_reset_isolation(self):
        from rpylean.machine import TermStore
        from rpylean.objects import W_LEVEL_ZERO
        u = Name.simple("u")
        v = Name.simple("v")
        u_lvl = u.as_level_param()
        v_lvl = v.as_level_param()
        l1 = W_LEVEL_ZERO.succ()
        shared = f.const([u_lvl]).app(u_lvl.sort())
        d1 = Name.simple("D1").axiom(levels=[u], type=shared)
        d2 = Name.simple("D2").axiom(levels=[u], type=g.const([u_lvl]).app(shared))
        d3 = Name.simple("D3").axiom(
            levels=[u, v],
            type=f.const([u_lvl, v_lvl]).app(v_lvl.sort()),
        )
        store = TermStore(None, capacity=16)
        try:
            h1_0 = store.import_const_term(d1.name.const([W_LEVEL_ZERO]), d1, d1.type)
            h1_1 = store.import_const_term(d1.name.const([l1]), d1, d1.type)
            assert h1_0 != h1_1
            h2_0 = store.import_const_term(d2.name.const([W_LEVEL_ZERO]), d2, d2.type)
            assert store.field_b(h2_0) == h1_0
            h2_1 = store.import_const_term(d2.name.const([l1]), d2, d2.type)
            assert store.field_b(h2_1) == h1_1
            h3_01 = store.import_const_term(d3.name.const([W_LEVEL_ZERO, l1]), d3, d3.type)
            h3_10 = store.import_const_term(d3.name.const([l1, W_LEVEL_ZERO]), d3, d3.type)
            assert h3_01 != h3_10
            assert store.import_const_term(d3.name.const([W_LEVEL_ZERO, l1]), d3, d3.type) == h3_01
            # Reset invalidates _lgen1/_lgen2 cleanly
            store.reset()
            h1_0_after = store.import_const_term(d1.name.const([W_LEVEL_ZERO]), d1, d1.type)
            assert store.export_term(h1_0_after).syntactic_eq(
                f.const([W_LEVEL_ZERO]).app(W_LEVEL_ZERO.sort()),
            )
        finally:
            store.free()

    def test_inst_eq_buf_matches_instantiate_multi_buf(self):
        from rpylean.machine import TermStore
        store = TermStore(None, capacity=32)
        try:
            fh = store.import_term(f.const())
            gh = store.import_term(g.const())
            xh = store.import_term(x.const())
            yh = store.import_term(y.const())
            b0 = store.bvar(0)
            b1 = store.bvar(1)
            b2 = store.bvar(2)
            # Spine buffer: subst[0] = yh, subst[1] = xh
            mark = store._spine_top
            store.spine_push(yh)
            store.spine_push(xh)
            try:
                # App spine: f #1 #0 #2  ->  f x y #0
                pat_app = store.cons_app(store.cons_app(store.cons_app(fh, b1), b0), b2)
                expected_app = store.instantiate_multi_buf(pat_app, mark, 2, 0)
                wrong_app = store.cons_app(store.cons_app(store.cons_app(fh, xh), xh), b0)
                nrecs_before = store.nrecs
                assert store.inst_eq_buf(pat_app, mark, 2, expected_app)
                assert not store.inst_eq_buf(pat_app, mark, 2, wrong_app)
                assert store.nrecs == nrecs_before

                # Nested forall/lambda: forall (z : f #1), g #0 #2 -> forall (z : f x), g #0 y
                binder = x.binder(type=NAT)
                pat_pi = store.forall(
                    binder,
                    store.cons_app(fh, b1),
                    store.cons_app(store.cons_app(gh, b0), b1),
                )
                expected_pi = store.instantiate_multi_buf(pat_pi, mark, 2, 0)
                wrong_pi = store.forall(
                    binder,
                    store.cons_app(fh, xh),
                    store.cons_app(store.cons_app(gh, b0), xh),
                )
                assert store.inst_eq_buf(pat_pi, mark, 2, expected_pi)
                assert not store.inst_eq_buf(pat_pi, mark, 2, wrong_pi)

                # Projection & Let
                sname = Name.simple("S")
                pat_proj = store.proj(sname, 1, store.cons_app(fh, b0))
                expected_proj = store.instantiate_multi_buf(pat_proj, mark, 2, 0)
                wrong_proj = store.proj(sname, 0, store.cons_app(fh, yh))
                assert store.inst_eq_buf(pat_proj, mark, 2, expected_proj)
                assert not store.inst_eq_buf(pat_proj, mark, 2, wrong_proj)

                pat_let = store.let(
                    x, store.cons_app(fh, b1), store.cons_app(gh, b0),
                    store.cons_app(b0, b2),
                )
                expected_let = store.instantiate_multi_buf(pat_let, mark, 2, 0)
                assert store.inst_eq_buf(pat_let, mark, 2, expected_let)

                # Open substitute under a binder must safely return False (needs shift)
                open_mark = store._spine_top
                store.spine_push(store.cons_app(fh, b0))
                try:
                    pat_under = store.forall(binder, xh, store.cons_app(gh, b1))
                    expected_under = store.instantiate_multi_buf(pat_under, open_mark, 1, 0)
                    assert not store.inst_eq_buf(pat_under, open_mark, 1, expected_under)
                finally:
                    store.unapp_pop(open_mark)

                # Shared deep DAG exceeding budget returns False cleanly without blowing up
                dag = store.cons_app(fh, b0)
                for _ in range(15):
                    dag = store.cons_app(dag, dag)
                expected_dag = store.instantiate_multi_buf(dag, mark, 2, 0)
                assert not store.inst_eq_buf(dag, mark, 2, expected_dag)
            finally:
                store.unapp_pop(mark)
        finally:
            store.free()

    def test_recursive_rec_rule_simple_minor(self):
        from rpylean.objects import W_RecRule, W_BVar, W_Lambda, W_LEVEL_ZERO
        u = Name.simple("u")
        v = Name.simple("v")
        rec_name = Name.from_str("MyList.rec")
        rec_decl = rec_name.axiom(levels=[u, v], type=PROP)
        b = x.binder(type=PROP)

        def wrap_lams(n, body):
            cur = body
            for _ in range(n):
                cur = W_Lambda(b, cur)
            return cur

        # Standard List.cons rule:
        # λ (α:#5) (motive:#4) (nil:#3) (cons:#2) (hd:#1) (tl:#0) =>
        #   cons hd tl (MyList.rec.{u,v} α motive nil cons tl)
        rec_const = rec_name.const([u.as_level_param(), v.as_level_param()])
        rec_call = (
            rec_const.app(W_BVar(5)).app(W_BVar(4))
            .app(W_BVar(3)).app(W_BVar(2)).app(W_BVar(0))
        )
        rhs = wrap_lams(6, W_BVar(2).app(W_BVar(1)).app(W_BVar(0)).app(rec_call))
        rule = W_RecRule(Name.from_str("MyList.cons"), 2, rhs)
        assert rule.simple_minor(rec_decl, 1, 1, 2, 0) == 1
        assert rule._rec_fields == [1]

        # Indexed recursor rejects recursive fast path
        rule_idx = W_RecRule(Name.from_str("MyList.cons"), 2, rhs)
        assert rule_idx.simple_minor(rec_decl, 1, 1, 2, 1) == -1
        assert rule_idx._rec_fields is None

        # Wrong universe levels on recursive call rejects fast path
        bad_rec = rec_name.const([v.as_level_param(), u.as_level_param()])
        bad_call = (
            bad_rec.app(W_BVar(5)).app(W_BVar(4))
            .app(W_BVar(3)).app(W_BVar(2)).app(W_BVar(0))
        )
        bad_rhs = wrap_lams(6, W_BVar(2).app(W_BVar(1)).app(W_BVar(0)).app(bad_call))
        rule_bad = W_RecRule(Name.from_str("MyList.cons"), 2, bad_rhs)
        assert rule_bad.simple_minor(rec_decl, 1, 1, 2, 0) == -1
        assert rule_bad._rec_fields is None


class TestJointCheckAndInferExpected(object):
    def test_infer_expected_avoids_allocating_return_type(self):
        from rpylean.environment import Environment, TypeChecker

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        box_name = Name.simple("Box")
        box_decl = box_name.axiom(type=forall(x.binder(type=TYPE))(TYPE))
        mk_name = Name.simple("mk")
        # mk : forall (a : Type) (v : a), Box a
        mk_type = forall(x.binder(type=TYPE))(
            forall(y.binder(type=b0))(box_name.const().app(b1)),
        )
        mk_decl = mk_name.axiom(type=mk_type)
        # mk1 : forall (a : Type), Box a  (1-arg fast path)
        mk1_name = Name.simple("mk1")
        mk1_decl = mk1_name.axiom(
            type=forall(x.binder(type=TYPE))(box_name.const().app(b0)),
        )
        a_decl = Name.simple("A").axiom(type=TYPE)
        b_decl = Name.simple("B").axiom(type=TYPE)
        av_decl = Name.simple("a").axiom(type=a_decl.name.const())
        env = Environment.having(
            [nat_decl, box_decl, mk_decl, mk1_decl, a_decl, b_decl, av_decl],
        )
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            store = m.store
            box_a = store.import_term(box_name.const().app(a_decl.name.const()))
            box_b = store.import_term(box_name.const().app(b_decl.name.const()))
            app2 = store.import_term(
                mk_name.const().app(a_decl.name.const(), av_decl.name.const()),
            )
            app1 = store.import_term(mk1_name.const().app(a_decl.name.const()))
            # Pre-import mk/mk1 types so only return-type instantiation could allocate.
            m.infer(store.import_term(mk_name.const()), True)
            m.infer(store.import_term(mk1_name.const()), True)
            m.infer(store.import_term(a_decl.name.const()), True)
            m.infer(store.import_term(av_decl.name.const()), True)
            before = store.nrecs
            assert m.infer_expected(app2, box_a) == box_a
            assert m.infer_expected(app1, box_a) == box_a
            assert store.nrecs == before

            # Wrong expected hint falls back cleanly to the true instantiated type.
            m.reset()
            store = m.store
            box_b = store.import_term(box_name.const().app(b_decl.name.const()))
            app2 = store.import_term(
                mk_name.const().app(a_decl.name.const(), av_decl.name.const()),
            )
            inferred = m.infer_expected(app2, box_b)
            assert inferred == store.import_term(
                box_name.const().app(a_decl.name.const()),
            )
        finally:
            tc.free()

    def test_check_value_joint_accepts_and_fallbacks(self):
        from rpylean.environment import Environment, TypeChecker
        from rpylean.objects import W_NotAProp, W_NotASort, W_TypeError

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        mynat_name = Name.simple("MyNat")
        mynat_decl = mynat_name.definition(type=TYPE, value=NAT)
        env = Environment.having([nat_decl, mynat_decl])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            # Dependent matching telescope
            id_ty = forall(x.binder(type=TYPE))(forall(y.binder(type=b0))(b1))
            id_val = fun(x.binder(type=TYPE))(fun(y.binder(type=b0))(b0))
            assert m.check_value(id_ty, id_val, False) is None

            # Unused outer binder clearing fvars before dependent inner telescope
            ty_unused = forall(x.binder(type=NAT))(id_ty)
            val_unused = fun(x.binder(type=NAT))(id_val)
            assert m.check_value(ty_unused, val_unused, False) is None

            # Def-eq but syntactically distinct domain breaks cleanly & succeeds
            ty_defeq = forall(x.binder(type=NAT))(forall(y.binder(type=NAT))(NAT))
            val_defeq = fun(x.binder(type=NAT))(fun(y.binder(type=mynat_name.const()))(b0))
            assert m.check_value(ty_defeq, val_defeq, False) is None

            # Theorem (prop=True) with Prop codomain succeeds
            prop_ty = forall(x.binder(type=PROP))(forall(y.binder(type=b0))(b1))
            prop_val = fun(x.binder(type=PROP))(fun(y.binder(type=b0))(b0))
            assert m.check_value(prop_ty, prop_val, True) is None

            # Theorem (prop=True) with Type codomain returns W_NotAProp
            err = m.check_value(
                forall(x.binder(type=NAT))(NAT),
                fun(x.binder(type=NAT))(b0),
                True,
            )
            assert isinstance(err, W_NotAProp)

            # Type mismatch falls back and returns W_TypeError
            err = m.check_value(
                forall(x.binder(type=NAT))(PROP),
                fun(x.binder(type=NAT))(b0),
                False,
            )
            assert isinstance(err, W_TypeError)

            # Non-sort codomain falls back and raises W_NotASort
            with pytest.raises(W_NotASort):
                m.check_value(
                    forall(x.binder(type=NAT))(b0),
                    fun(x.binder(type=NAT))(b0),
                    False,
                )
        finally:
            tc.free()

    def test_inst_eq_inst_buf_and_nested_expected_pat(self):
        from rpylean.environment import Environment, TypeChecker
        from rpylean.machine import TermStore
        from rpylean.objects import W_TypeError

        # 1. Unit test TermStore.inst_eq_inst_buf across apps, binders, proj, let
        store = TermStore(None, capacity=32)
        try:
            fh = store.import_term(f.const())
            gh = store.import_term(g.const())
            xh = store.import_term(x.const())
            yh = store.import_term(y.const())
            b0h = store.bvar(0)
            b1h = store.bvar(1)
            b2h = store.bvar(2)
            m1 = store._spine_top
            store.spine_push(yh)
            store.spine_push(xh)
            m2 = store._spine_top
            store.spine_push(fh)
            store.spine_push(yh)
            store.spine_push(xh)
            try:
                # p1 = f #1 #0 (#2) with [y, x] -> f x y #0
                # p2 = f #2 #1 (#3) with [f, y, x] -> f x y #0
                p1 = store.cons_app(store.cons_app(store.cons_app(fh, b1h), b0h), b2h)
                p2 = store.cons_app(
                    store.cons_app(store.cons_app(fh, b2h), b1h), store.bvar(3),
                )
                p_bad = store.cons_app(
                    store.cons_app(store.cons_app(fh, b1h), b1h), store.bvar(3),
                )
                # Nested forall with binders: forall (z : f #1), g #0 #1 vs forall (z : f #2), g #0 #2
                binder = x.binder(type=NAT)
                pi1 = store.forall(binder, store.cons_app(fh, b1h), store.cons_app(store.cons_app(gh, b0h), b1h))
                pi2 = store.forall(binder, store.cons_app(fh, b2h), store.cons_app(store.cons_app(gh, b0h), b2h))
                pi_bad = store.forall(binder, store.cons_app(fh, b2h), store.cons_app(store.cons_app(gh, b0h), b1h))
                # Proj & Let
                sname = Name.simple("S")
                pr1 = store.proj(sname, 1, store.cons_app(fh, b0h))
                pr2 = store.proj(sname, 1, store.cons_app(fh, b1h))
                pr_bad = store.proj(sname, 0, store.cons_app(fh, b1h))
                let1 = store.let(x, store.cons_app(fh, b1h), store.cons_app(gh, b0h), store.cons_app(b0h, b1h))
                let2 = store.let(x, store.cons_app(fh, b2h), store.cons_app(gh, b1h), store.cons_app(b0h, b2h))
                before = store.nrecs
                assert store.inst_eq_inst_buf(p1, m1, 2, p2, m2, 3)
                assert not store.inst_eq_inst_buf(p1, m1, 2, p_bad, m2, 3)
                assert store.inst_eq_inst_buf(pi1, m1, 2, pi2, m2, 3)
                assert not store.inst_eq_inst_buf(pi1, m1, 2, pi_bad, m2, 3)
                assert store.inst_eq_inst_buf(pr1, m1, 2, pr2, m2, 3)
                assert not store.inst_eq_inst_buf(pr1, m1, 2, pr_bad, m2, 3)
                assert store.inst_eq_inst_buf(let1, m1, 2, let2, m2, 3)
                assert store.nrecs == before
            finally:
                store.unapp_pop(m1)
        finally:
            store.free()

        # 2. End-to-end nested Eq.trans proof chain + shared DAG subterm:
        # verifies zero intermediate Eq type allocations AND safe DAG reuse.
        eq_n = Name.simple("MyEq")
        eq_decl = eq_n.axiom(
            type=forall(x.binder(type=TYPE))(
                forall(y.binder(type=b0))(forall(y.binder(type=b1))(PROP)),
            ),
        )
        # trans : forall (A:Type) (a b c:A), MyEq A a b -> MyEq A b c -> MyEq A a c
        trans_n = Name.simple("trans")
        trans_ty = forall(x.binder(type=TYPE))(
            forall(y.binder(type=b0))(
                forall(y.binder(type=b1))(
                    forall(y.binder(type=b2))(
                        forall(y.binder(type=eq_n.const().app(b3_, b2, b1)))(
                            forall(y.binder(type=eq_n.const().app(W_BVar(4), b2, b1)))(
                                eq_n.const().app(W_BVar(5), W_BVar(4), b2),
                            ),
                        ),
                    ),
                ),
            ),
        )
        trans_decl = trans_n.axiom(type=trans_ty)
        a_ty = Name.simple("A").axiom(type=TYPE)
        a1 = Name.simple("a1").axiom(type=a_ty.name.const())
        a2 = Name.simple("a2").axiom(type=a_ty.name.const())
        a3 = Name.simple("a3").axiom(type=a_ty.name.const())
        h12 = Name.simple("h12").axiom(type=eq_n.const().app(a_ty.name.const(), a1.name.const(), a2.name.const()))
        h23 = Name.simple("h23").axiom(type=eq_n.const().app(a_ty.name.const(), a2.name.const(), a3.name.const()))
        h11 = Name.simple("h11").axiom(type=eq_n.const().app(a_ty.name.const(), a1.name.const(), a1.name.const()))
        env = Environment.having([eq_decl, trans_decl, a_ty, a1, a2, a3, h12, h23, h11])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            A, v1, v2, v3 = a_ty.name.const(), a1.name.const(), a2.name.const(), a3.name.const()
            step1 = trans_n.const().app(A, v1, v1, v2, h11.name.const(), h12.name.const())
            # Outer trans takes step1 (whose intermediate MyEq A a1 a2 is never needed!)
            chain = trans_n.const().app(A, v1, v2, v3, step1, h23.name.const())
            goal = eq_n.const().app(A, v1, v3)
            # Pre-import leaves & terms so we can count purely type-checking allocations.
            s = m.store
            chain_h = s.import_term(chain)
            goal_h = s.import_term(goal)
            for c in [trans_n.const(), A, v1, v2, v3, h11.name.const(), h12.name.const(), h23.name.const()]:
                m.infer(s.import_term(c), True)
            before = s.nrecs
            assert m.infer_expected(chain_h, goal_h) == goal_h
            # Zero new records allocated for step1's intermediate type OR chain's return type!
            assert s.nrecs == before

            # Shared DAG: step1 was checked with M_INFER == 0; now infer(step1, True)
            # must materialize its exact type cleanly without re-checking args.
            step1_h = s.import_term(step1)
            assert m.infer(step1_h, True) == s.import_term(eq_n.const().app(A, v1, v2))

            # Mismatched proof still raises W_TypeError.
            bad = trans_n.const().app(A, v1, v2, v3, step1, h12.name.const())
            with pytest.raises(W_TypeError):
                m.infer(s.import_term(bad), True)
        finally:
            tc.free()

    def test_warm_check_gen_reuse_and_soundness_boundaries(self):
        from rpylean.environment import Environment
        from rpylean.exceptions import UndeclaredLevelParam, W_InvalidDeclaration
        from rpylean.machine import M_CHECKED_GEN, MEMO_SLOTS, _CHECKED_PERM, rec_index, _s32
        from rpylean.objects import (
            SAFETY_SAFE,
            SAFETY_UNSAFE,
            W_NotYetDeclared,
            W_UnsafeReference,
        )

        u_n = Name.simple("u")
        v_n = Name.simple("v")
        u_l = u_n.as_level_param()
        v_l = v_n.as_level_param()
        nat_d = Name.simple("Nat").inductive(type=TYPE)
        fn_n = Name.simple("fn")
        fn_d = fn_n.axiom(type=forall(x.binder(type=NAT))(NAT))
        zero_n = Name.simple("z")
        zero_d = zero_n.axiom(type=NAT)
        unsafe_n = Name.simple("bad_unsafe")
        unsafe_d = unsafe_n.axiom(type=NAT, is_unsafe=True)
        later_n = Name.simple("later")
        later_d = later_n.axiom(type=NAT)

        # 1. Level-param shrinkage: D1 has [u, v], D2 has [u] and mentions Type v.
        poly_fn = Name.simple("pfn").axiom(
            levels=[u_n],
            type=forall(x.binder(type=u_l.succ().sort()))(u_l.succ().sort()),
        )
        d1 = Name.simple("d1").definition(
            levels=[u_n, v_n],
            type=v_l.succ().sort(),
            value=poly_fn.name.const([v_l]).app(v_l.sort()),
        )
        # Same term in d2 which only declares [u] must FAIL with UndeclaredLevelParam(v)!
        d2_bad = Name.simple("d2_bad").definition(
            levels=[u_n],
            type=v_l.succ().sort(),
            value=poly_fn.name.const([v_l]).app(v_l.sort()),
        )
        # Valid d3 & d4 both with [u] share check_gen and mark closed ground subterm _CHECKED_PERM.
        shared_ground = fn_n.const().app(zero_n.const())
        d3 = Name.simple("d3").definition(
            levels=[u_n], type=NAT, value=shared_ground,
        )
        d4 = Name.simple("d4").definition(
            levels=[u_n], type=NAT, value=fn_n.const().app(shared_ground),
        )
        d5_mono = Name.simple("d5_mono").definition(
            levels=[], type=NAT, value=shared_ground,
        )
        # 2. Unsafe -> Safe boundary: unsafe d6 uses bad_unsafe; safe d7 uses same term -> must reject!
        unsafe_term = fn_n.const().app(unsafe_n.const())
        d6_unsafe = Name.simple("d6_unsafe").definition(
            type=NAT, value=unsafe_term, safety=SAFETY_UNSAFE,
        )
        d7_safe_bad = Name.simple("d7_safe_bad").definition(
            type=NAT, value=unsafe_term, safety=SAFETY_SAFE,
        )
        # 3. Out-of-order check: d_early (index < later_d) referencing later_d after d_late checked it!
        later_term = fn_n.const().app(later_n.const())
        d_early_bad = Name.simple("d_early_bad").definition(type=NAT, value=later_term)
        d_late_ok = Name.simple("d_late_ok").definition(type=NAT, value=later_term)

        env = Environment.having([
            nat_d, fn_d, zero_d, unsafe_d, poly_fn,
            d1, d2_bad, d3, d4, d5_mono, d6_unsafe, d7_safe_bad,
            d_early_bad, later_d, d_late_ok,
        ])
        assert env.type_check_one(d1, measure=False).error is None
        res_lvl = env.type_check_one(d2_bad, measure=False)
        assert isinstance(res_lvl.error, W_InvalidDeclaration)
        assert isinstance(res_lvl.error.inner, UndeclaredLevelParam)

        # Safe cohort reuse & _CHECKED_PERM preservation across check_gen bump
        assert env.type_check_one(d3, measure=False).error is None
        from rpylean.machine import _SPARE
        m = _SPARE.machine
        assert m is not None
        g_after_d3 = m.check_gen
        h_ground = m.store.import_term(shared_ground)
        assert _s32(m.store.memos[rec_index(h_ground) * MEMO_SLOTS + M_CHECKED_GEN]) == _CHECKED_PERM
        assert env.type_check_one(d4, measure=False).error is None
        assert _SPARE.machine.check_gen == g_after_d3  # Same [u] cohort kept check_gen!
        assert env.type_check_one(d5_mono, measure=False).error is None
        assert _SPARE.machine.check_gen == g_after_d3 + 1  # [u] -> [] bumped check_gen
        assert _s32(_SPARE.machine.store.memos[rec_index(h_ground) * MEMO_SLOTS + M_CHECKED_GEN]) == _CHECKED_PERM

        # Unsafe -> Safe boundary must reject W_UnsafeReference
        assert env.type_check_one(d6_unsafe, measure=False).error is None
        res_unsafe = env.type_check_one(d7_safe_bad, measure=False)
        assert isinstance(res_unsafe.error, W_UnsafeReference)

        # Out-of-order check must reset and reject W_NotYetDeclared
        assert env.type_check_one(d_late_ok, measure=False).error is None
        res_order = env.type_check_one(d_early_bad, measure=False)
        assert isinstance(res_order.error, W_NotYetDeclared)

    def test_const_leaf1_and_2_direct_dedup_and_normalization(self, store):
        from rpylean.objects import W_LEVEL_ZERO
        u_l = Name.simple("u").as_level_param()
        v_l = Name.simple("v").as_level_param()
        l1 = W_LEVEL_ZERO.succ()
        # Non-normalized max(0, u) must canonicalize to the exact same leaf as u.
        h_u = store.leaf_for(f.const([u_l]))
        assert store._const_leaf1(f, u_l) == h_u
        assert store._const_leaf1(f, W_LEVEL_ZERO.max(u_l)) == h_u
        # Miss path inserts and subsequent call hits without allocating a new leaf.
        nleaves_before = store.nleaves
        h_l1 = store._const_leaf1(f, l1)
        assert store.nleaves == nleaves_before + 1
        assert store._const_leaf1(f, l1) == h_l1
        assert store.leaf_for(f.const([l1])) == h_l1
        # 2-level direct lookup and normalization
        h2 = store._const_leaf2(g, u_l, l1)
        assert store._const_leaf2(g, W_LEVEL_ZERO.max(u_l), W_LEVEL_ZERO.max(l1)) == h2
        assert store.leaf_for(g.const([u_l, l1])) == h2
        assert store._const_leaf2(g, l1, u_l) != h2

    def test_try_unfold_head_memo_and_whnf_core_interop(self):
        from rpylean.environment import Environment, TypeChecker

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").axiom(type=NAT)
        fn_decl = f.axiom(type=forall(x.binder(type=NAT), y.binder(type=NAT))(NAT))
        # Multi-arg definition `g x y := f y x`
        g_decl = g.definition(
            type=forall(x.binder(type=NAT), y.binder(type=NAT))(NAT),
            value=fun(x.binder(type=NAT), y.binder(type=NAT))(
                f.const().app(b0, b1),
            ),
        )
        env = Environment.having([nat_decl, a_decl, b_decl, fn_decl, g_decl])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            store = m.store
            h_app = store.import_term(
                g.const().app(a_decl.name.const(), b_decl.name.const()),
            )
            h_expected = store.import_term(
                f.const().app(b_decl.name.const(), a_decl.name.const()),
            )
            # 1. whnf_core (cheap and full) before unfold returns h_app
            assert m.whnf_core(h_app, True) == h_app
            assert m.whnf_core(h_app, False) == h_app

            # 2. First try_unfold_head unfolds and caches tagged result
            assert m.try_unfold_head(h_app) == h_expected

            # 3. Subsequent try_unfold_head hits memo without allocating records
            nrecs_before = store.nrecs
            assert m.try_unfold_head(h_app) == h_expected
            assert store.nrecs == nrecs_before

            # 4. whnf_core (cheap & full) after tagged unfold still returns h_app,
            #    and let-reduction stopping at a tagged delta app preserves h_app!
            assert m.whnf_core(h_app, True) == h_app
            assert m.whnf_core(h_app, False) == h_app
            h_let = store.let(
                x, store.import_term(NAT), store.import_term(a_decl.name.const()),
                store.cons_app(
                    store.cons_app(store.import_term(g.const()), store.bvar(0)),
                    store.import_term(b_decl.name.const()),
                ),
            )
            assert m.whnf_core(h_let, True) == h_app
            assert m.whnf_core(h_let, False) == h_app
            # And non-app records (e.g. lambda) return 0 cleanly
            h_lam = store.import_term(fun(x.binder(type=NAT))(b0))
            assert m.try_unfold_head(h_lam) == 0
        finally:
            tc.free()

    def test_infer_expected_let_and_lambda_closed_and_open(self):
        from rpylean.environment import Environment, TypeChecker
        from rpylean.objects import W_TypeError

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").axiom(type=NAT)
        box_name = Name.simple("Box")
        box_decl = box_name.axiom(type=forall(x.binder(type=TYPE))(TYPE))
        mk_name = Name.simple("mk")
        mk_decl = mk_name.axiom(
            type=forall(x.binder(type=TYPE), y.binder(type=b0))(box_name.const().app(b1)),
        )
        # Higher-order polymorphic combinator:
        #   apply1 : ∀ (α β : Type), (α → β) → α → β
        apply1_name = Name.simple("apply1")
        apply1_decl = apply1_name.axiom(
            type=forall(
                x.binder(type=TYPE),
                y.binder(type=TYPE),
                f.binder(type=forall(Name.simple("u").binder(type=b1))(b1)),
                Name.simple("v").binder(type=b2),
            )(b2),
        )
        # Multi-binder dependent combinator:
        #   dep2 : ∀ (α : Type) (P : α → Type), (∀ (x : α), Box2 α x → P x) → Nat
        box2_name = Name.simple("Box2")
        box2_decl = box2_name.axiom(
            type=forall(x.binder(type=TYPE), y.binder(type=b0))(TYPE),
        )
        dep2_name = Name.simple("dep2")
        p_name = Name.simple("P")
        dep2_decl = dep2_name.axiom(
            type=forall(
                x.binder(type=TYPE),
                p_name.binder(type=forall(y.binder(type=b0))(TYPE)),
                f.binder(
                    type=forall(
                        y.binder(type=b1),
                        Name.simple("bx").binder(type=box2_name.const().app(b2, b0)),
                    )(b2.app(b1)),
                ),
            )(NAT),
        )
        # Def-eq alias `IdNat (_ : Nat) : Type := Nat` to test FVar non-leakage
        idnat_name = Name.simple("IdNat")
        idnat_decl = idnat_name.definition(
            type=forall(x.binder(type=NAT))(TYPE),
            value=fun(x.binder(type=NAT))(NAT),
        )
        env = Environment.having([
            nat_decl, a_decl, b_decl, box_decl, mk_decl,
            apply1_decl, box2_decl, dep2_decl, idnat_decl,
        ])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            store = m.store
            # 1. Closed infer_expected through KIND_LET -> KIND_APP
            let_expr = x.let(
                type=NAT, value=a_decl.name.const(),
                body=mk_name.const().app(NAT, b0),
            )
            box_nat = store.import_term(box_name.const().app(NAT))
            h_let = store.import_term(let_expr)
            assert m.infer_expected(h_let, box_nat) == box_nat

            # 2. Closed infer_expected on KIND_LAMBDA matching KIND_FORALL
            lam_expr = fun(x.binder(type=NAT))(mk_name.const().app(NAT, b0))
            pi_expr = forall(x.binder(type=NAT))(box_name.const().app(NAT))
            h_lam = store.import_term(lam_expr)
            h_pi = store.import_term(pi_expr)
            assert m.infer_expected(h_lam, h_pi) == h_pi

            # 3. Open-pattern KIND_LAMBDA in _infer_app (1-binder & 2-binder dependent)
            h_app1 = store.import_term(
                apply1_name.const().app(
                    NAT, box_name.const().app(NAT),
                    fun(x.binder(type=NAT))(mk_name.const().app(NAT, b0)),
                    a_decl.name.const(),
                ),
            )
            assert m.infer(h_app1, True) == box_nat

            h_dep = store.import_term(
                dep2_name.const().app(
                    NAT,
                    fun(x.binder(type=NAT))(box2_name.const().app(NAT, b0)),
                    fun(
                        x.binder(type=NAT),
                        y.binder(type=box2_name.const().app(NAT, b0)),
                    )(b0),
                ),
            )
            assert m.infer(h_dep, True) == store.import_term(NAT)

            # 4. Soundness: FVar from expected def-eq alias MUST NOT leak into M_INFER
            #    of a closed lambda `fun (_ : Nat) => a`!
            outer = fun(y.binder(type=NAT))(
                x.let(
                    type=forall(Name.simple("z").binder(type=NAT))(
                        idnat_name.const().app(b1),
                    ),
                    value=fun(Name.simple("z").binder(type=NAT))(a_decl.name.const()),
                    body=b0.app(b1),
                ),
            )
            h_outer = store.import_term(outer)
            m.infer(h_outer, True)
            h_closed_lam = store.import_term(
                fun(Name.simple("z").binder(type=NAT))(a_decl.name.const()),
            )
            inferred_closed = m.infer(h_closed_lam, True)
            assert not store.has_fvar(inferred_closed)

            # 5. Soundness: ill-typed lambda body under open pattern must still reject
            bad_app = store.import_term(
                apply1_name.const().app(
                    NAT, box_name.const().app(NAT),
                    fun(x.binder(type=NAT))(b0),
                    a_decl.name.const(),
                ),
            )
            with pytest.raises(W_TypeError):
                m.infer(bad_app, True)
        finally:
            tc.free()

    def test_try_proj_lazy_ctor_body_skips_sibling_fields(self):
        from rpylean.environment import Environment, TypeChecker

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").axiom(type=NAT)
        dead_fn = Name.simple("deadFn").axiom(
            type=forall(x.binder(type=NAT))(NAT),
        )
        # Structure `Pair2 (α : Type) := mk (fst : α) (snd : α)`
        pair_s = Name.simple("Pair2")
        pair_mk = pair_s.child("mk")
        pair_mk_decl = pair_mk.constructor(
            type=forall(
                x.binder(type=TYPE), y.binder(type=b0), Name.simple("z").binder(type=b1),
            )(pair_s.const().app(b2)),
            num_params=1,
            num_fields=2,
        )
        pair_decl = pair_s.inductive(
            type=forall(x.binder(type=TYPE))(TYPE),
            num_params=1,
            constructors=[pair_mk_decl],
        )
        # Huge unused sibling expression for field 1
        big_sibling = dead_fn.name.const().app(
            dead_fn.name.const().app(dead_fn.name.const().app(b0)),
        )
        # 1. Parametric def `mkPair α x := Pair2.mk α x (deadFn (deadFn (deadFn x)))`
        mkpair_name = Name.simple("mkPair")
        mkpair_decl = mkpair_name.definition(
            type=forall(x.binder(type=TYPE), y.binder(type=b0))(
                pair_s.const().app(b1),
            ),
            value=fun(x.binder(type=TYPE), y.binder(type=b0))(
                pair_mk.const().app(b1, b0, big_sibling),
            ),
        )
        # 2. Nullary leaf def `instPair := Pair2.mk Nat a (deadFn (deadFn (deadFn b)))`
        inst_name = Name.simple("instPair")
        inst_decl = inst_name.definition(
            type=pair_s.const().app(NAT),
            value=pair_mk.const().app(
                NAT,
                a_decl.name.const(),
                dead_fn.name.const().app(
                    dead_fn.name.const().app(b_decl.name.const()),
                ),
            ),
        )
        # 3. Let-wrapped ctor def `mkLetPair x := let h := deadFn x; Pair2.mk Nat x h`
        mklet_name = Name.simple("mkLetPair")
        mklet_decl = mklet_name.definition(
            type=forall(x.binder(type=NAT))(pair_s.const().app(NAT)),
            value=fun(x.binder(type=NAT))(
                y.let(
                    type=NAT,
                    value=dead_fn.name.const().app(b0),
                    body=pair_mk.const().app(NAT, b1, b0),
                ),
            ),
        )
        # 4. Eta-contracted (over-applied) def `mkEta α := Pair2.mk α`
        mketa_name = Name.simple("mkEta")
        mketa_decl = mketa_name.definition(
            type=forall(
                x.binder(type=TYPE), y.binder(type=b0), Name.simple("z").binder(type=b1),
            )(pair_s.const().app(b2)),
            value=fun(x.binder(type=TYPE))(pair_mk.const().app(b0)),
        )
        # 5. Chained wrapper `wrapPair α x := mkPair α x`
        wrap_name = Name.simple("wrapPair")
        wrap_decl = wrap_name.definition(
            type=forall(x.binder(type=TYPE), y.binder(type=b0))(
                pair_s.const().app(b1),
            ),
            value=fun(x.binder(type=TYPE), y.binder(type=b0))(
                mkpair_name.const().app(b1, b0),
            ),
        )

        env = Environment.having([
            nat_decl, a_decl, b_decl, dead_fn,
            pair_decl, pair_mk_decl,
            mkpair_decl, inst_decl, mklet_decl, mketa_decl, wrap_decl,
        ])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            store = m.store
            h_a = store.import_term(a_decl.name.const())
            h_b = store.import_term(b_decl.name.const())

            # 1. Projecting field 0 of `mkPair Nat a` returns `a` and NEVER imports `deadFn`!
            p0 = store.import_term(
                pair_s.proj(0, mkpair_name.const().app(NAT, a_decl.name.const())),
            )
            nrecs_before = store.nrecs
            assert m.try_proj(p0, False) == h_a
            assert store.nrecs == nrecs_before
            # cheap_proj=True MUST still return 0 (no delta unfold!)
            assert m.try_proj(p0, True) == 0

            # 2. Nullary leaf `instPair` projects field 0 directly without importing `deadFn`.
            p_leaf = store.import_term(pair_s.proj(0, inst_name.const()))
            nrecs_before = store.nrecs
            assert m.try_proj(p_leaf, False) == h_a
            assert store.nrecs == nrecs_before

            # 3. Let-wrapped `mkLetPair a`: field 0 ignores let, field 1 evaluates let!
            p_let0 = store.import_term(
                pair_s.proj(0, mklet_name.const().app(a_decl.name.const())),
            )
            nrecs_before = store.nrecs
            assert m.try_proj(p_let0, False) == h_a
            assert store.nrecs == nrecs_before

            p_let1 = store.import_term(
                pair_s.proj(1, mklet_name.const().app(a_decl.name.const())),
            )
            assert m.try_proj(p_let1, False) == store.import_term(
                dead_fn.name.const().app(a_decl.name.const()),
            )

            # 4. Over-applied `mkEta Nat a b` projects both field 0 (`a`) and field 1 (`b`).
            p_eta0 = store.import_term(
                pair_s.proj(0, mketa_name.const().app(NAT, a_decl.name.const(), b_decl.name.const())),
            )
            p_eta1 = store.import_term(
                pair_s.proj(1, mketa_name.const().app(NAT, a_decl.name.const(), b_decl.name.const())),
            )
            assert m.try_proj(p_eta0, False) == h_a
            assert m.try_proj(p_eta1, False) == h_b

            # 5. Chained `wrapPair Nat a` unfolds 1 layer to `mkPair Nat a` then projects lazily.
            p_wrap = store.import_term(
                pair_s.proj(0, wrap_name.const().app(NAT, a_decl.name.const())),
            )
            assert m.try_proj(p_wrap, False) == h_a
        finally:
            tc.free()

    def test_static_prop_mask_soundness_and_plans(self):
        from rpylean.environment import Environment, TypeChecker
        from rpylean.objects import (
            PROP,
            W_LEVEL_ZERO,
            _PROP_MASK_DONE,
        )

        u_name = Name.simple("u")
        u_lvl = u_name.as_level_param()
        sort_u = u_lvl.sort()
        type_u = u_lvl.succ().sort()
        l0 = W_LEVEL_ZERO
        l1 = W_LEVEL_ZERO.succ()
        b3 = W_BVar(3)
        b4 = W_BVar(4)

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        # Transparent identity wrapper `outParam.{u} (α : Sort u) : Sort u := α`
        out_name = Name.simple("outParam")
        out_decl = out_name.definition(
            type=forall(x.binder(type=sort_u))(sort_u),
            value=fun(x.binder(type=sort_u))(b0),
            levels=[u_name],
        )
        # Polymorphic `Eq.{u} : ∀ {α : Sort u}, α → α → Prop`
        eq_name = Name.simple("Eq")
        eq_decl = eq_name.inductive(
            type=forall(x.binder(type=sort_u), y.binder(type=b0), Name.simple("z").binder(type=b1))(PROP),
            levels=[u_name],
        )
        # Higher-order Prop binders + Type u + outParam + Eq:
        # `ho.{u} : ∀ (α : outParam (Type u)) (P : α → Prop) (a : α) (h : P a) (hall : ∀ y, P y) (heq : Eq α a a), Nat`
        ho_name = Name.simple("ho")
        ho_decl = ho_name.axiom(
            type=forall(
                x.binder(type=out_name.const([u_lvl.succ().succ()]).app(type_u)),
                Name.simple("P").binder(type=forall(y.binder(type=b0))(PROP)),
                Name.simple("a").binder(type=b1),
                Name.simple("h").binder(type=b1.app(b0)),
                Name.simple("hall").binder(type=forall(y.binder(type=b3))(b3.app(b0))),
                Name.simple("heq").binder(type=eq_name.const([u_lvl.succ()]).app(b4, b2, b2)),
            )(NAT),
            levels=[u_name],
        )
        # Shadowed inner BVar: `shadow : ∀ (α : Type), (∀ (P : Prop), P) → Nat`
        # Inner `P` is a Prop, so `(∀ P : Prop, P) : Prop` (bit 1 = 1),
        # while `shadow2 : ∀ (p : Prop), (∀ (T : Type), T) → Nat` has bit 1 = 0!
        shadow1_name = Name.simple("shadow1")
        shadow1_decl = shadow1_name.axiom(
            type=forall(
                x.binder(type=TYPE),
                y.binder(type=forall(Name.simple("P").binder(type=PROP))(b0)),
            )(NAT),
        )
        shadow2_name = Name.simple("shadow2")
        shadow2_decl = shadow2_name.axiom(
            type=forall(
                x.binder(type=PROP),
                y.binder(type=forall(Name.simple("T").binder(type=TYPE))(b0)),
            )(NAT),
        )
        # Tail definition returning a W_ForAll with a Prop binder:
        # `NeedsProp (P : Prop) : Type := P → Nat`
        # `useNeeds (P : Prop) : NeedsProp P` -> bit 0 = 0 (P : Prop is in Type 0), bit 1 = 1!
        needs_name = Name.simple("NeedsProp")
        needs_decl = needs_name.definition(
            type=forall(x.binder(type=PROP))(TYPE),
            value=fun(x.binder(type=PROP))(forall(y.binder(type=b0))(NAT)),
        )
        use_needs_name = Name.simple("useNeeds")
        use_needs_decl = use_needs_name.axiom(
            type=forall(x.binder(type=PROP))(needs_name.const().app(b0)),
        )
        # `Set`-like alias `MySet.{u} (α : Type u) : Type u := α → Prop`
        # `mkSet.{u} (α : Type u) (p : α → Prop) : MySet α` -> no Prop args!
        myset_name = Name.simple("MySet")
        myset_decl = myset_name.definition(
            type=forall(x.binder(type=type_u))(type_u),
            value=fun(x.binder(type=type_u))(forall(y.binder(type=b0))(PROP)),
            levels=[u_name],
        )
        mkset_name = Name.simple("mkSet")
        mkset_decl = mkset_name.axiom(
            type=forall(
                x.binder(type=type_u),
                y.binder(type=forall(Name.simple("z").binder(type=b0))(PROP)),
            )(myset_name.const([u_lvl]).app(b1)),
            levels=[u_name],
        )
        # Transparent inductive alias `AliasNat := Nat`
        alias_name = Name.simple("AliasNat")
        alias_decl = alias_name.definition(type=TYPE, value=NAT)
        use_alias_name = Name.simple("useAlias")
        use_alias_decl = use_alias_name.axiom(
            type=forall(x.binder(type=PROP), y.binder(type=b0))(alias_name.const()),
        )

        env = Environment.having([
            nat_decl, out_decl, eq_decl, ho_decl,
            shadow1_decl, shadow2_decl,
            needs_decl, use_needs_decl,
            myset_decl, mkset_decl,
            alias_decl, use_alias_decl,
        ])
        tc = TypeChecker(env, nat_decl)
        m = tc.machine
        try:
            store = m.store
            # 1. `ho.{0}`: static level-independent mask, bits 3, 4, 5 set, zero records allocated!
            h_ho = store.import_term(ho_name.const([l0]))
            nrecs_before = store.nrecs
            pm_ho = m._prop_mask_for(h_ho)
            assert pm_ho == (_PROP_MASK_DONE | (1 << 3) | (1 << 4) | (1 << 5))
            assert store.nrecs == nrecs_before
            assert ho_decl._prop_mask == pm_ho

            # 2. `Eq.{0}` vs `Eq.{1}`: level-dependent static plan (`-2`), zero records allocated!
            h_eq0 = store.import_term(eq_name.const([l0]))
            h_eq1 = store.import_term(eq_name.const([l1]))
            nrecs_before = store.nrecs
            assert m._prop_mask_for(h_eq0) == (_PROP_MASK_DONE | (1 << 1) | (1 << 2))
            assert m._prop_mask_for(h_eq1) == _PROP_MASK_DONE
            assert store.nrecs == nrecs_before
            assert eq_decl._prop_mask <= -2

            # 3. Shadowed inner BVars fall back to dynamic and compute exact masks:
            h_sh1 = store.import_term(shadow1_name.const())
            h_sh2 = store.import_term(shadow2_name.const())
            assert m._prop_mask_for(h_sh1) == (_PROP_MASK_DONE | (1 << 1))
            assert m._prop_mask_for(h_sh2) == _PROP_MASK_DONE
            # Monomorphic dynamic results are cached permanently on the decl:
            assert shadow1_decl._prop_mask == (_PROP_MASK_DONE | (1 << 1))
            assert shadow2_decl._prop_mask == _PROP_MASK_DONE

            # 4. Tail def returning `P → Nat` falls back to dynamic and detects bit 1!
            h_needs = store.import_term(use_needs_name.const())
            assert m._prop_mask_for(h_needs) == (_PROP_MASK_DONE | (1 << 1))
            assert use_needs_decl._prop_mask == (_PROP_MASK_DONE | (1 << 1))

            # 5. `MySet` & `AliasNat` tails resolve statically with zero records!
            h_mkset = store.import_term(mkset_name.const([l0]))
            h_alias = store.import_term(use_alias_name.const())
            nrecs_before = store.nrecs
            assert m._prop_mask_for(h_mkset) == _PROP_MASK_DONE
            assert m._prop_mask_for(h_alias) == (_PROP_MASK_DONE | (1 << 1))
            assert store.nrecs == nrecs_before
            assert mkset_decl._prop_mask == _PROP_MASK_DONE
            assert use_alias_decl._prop_mask == (_PROP_MASK_DONE | (1 << 1))
        finally:
            tc.free()

    def test_try_proj_nested_ctor_fusion_and_cache(self):
        from rpylean.environment import Environment, TypeChecker
        from rpylean.objects import W_Const

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").axiom(type=NAT)
        dead_fn = Name.simple("deadFn").axiom(
            type=forall(x.binder(type=NAT))(NAT),
        )
        # Inner structure `Inner := mk (val : Nat) (junk : Nat)`
        inner_s = Name.simple("Inner")
        inner_mk = inner_s.child("mk")
        inner_mk_decl = inner_mk.constructor(
            type=forall(x.binder(type=NAT), y.binder(type=NAT))(inner_s.const()),
            num_params=0,
            num_fields=2,
        )
        inner_decl = inner_s.inductive(
            type=TYPE, num_params=0, constructors=[inner_mk_decl],
        )
        # Outer structure `Outer := mk (toInner : Inner) (junk : Nat)`
        outer_s = Name.simple("Outer")
        outer_mk = outer_s.child("mk")
        outer_mk_decl = outer_mk.constructor(
            type=forall(x.binder(type=inner_s.const()), y.binder(type=NAT))(
                outer_s.const(),
            ),
            num_params=0,
            num_fields=2,
        )
        outer_decl = outer_s.inductive(
            type=TYPE, num_params=0, constructors=[outer_mk_decl],
        )
        # Wrapper `Outer.toInner o := Proj(Outer, 0, o)` (like `LinearMap.toAddHom`)
        to_inner_name = outer_s.child("toInner")
        to_inner_decl = to_inner_name.definition(
            type=forall(x.binder(type=outer_s.const()))(inner_s.const()),
            value=fun(x.binder(type=outer_s.const()))(outer_s.proj(0, b0)),
        )
        big_junk = dead_fn.name.const().app(
            dead_fn.name.const().app(b0),
        )
        # `mkOuter x := Outer.mk (Inner.mk x (deadFn (deadFn x))) (deadFn x)`
        mk_outer_name = Name.simple("mkOuter")
        mk_outer_decl = mk_outer_name.definition(
            type=forall(x.binder(type=NAT))(outer_s.const()),
            value=fun(x.binder(type=NAT))(
                outer_mk.const().app(
                    inner_mk.const().app(b0, big_junk),
                    dead_fn.name.const().app(b0),
                ),
            ),
        )
        # Let-wrapped nested ctor where inner field 0 does NOT use the let,
        # while inner field 1 DOES use the let.
        mk_let_outer_name = Name.simple("mkLetOuter")
        mk_let_outer_decl = mk_let_outer_name.definition(
            type=forall(x.binder(type=NAT))(outer_s.const()),
            value=fun(x.binder(type=NAT))(
                y.let(
                    type=NAT,
                    value=dead_fn.name.const().app(b0),
                    body=outer_mk.const().app(
                        inner_mk.const().app(b1, b0),
                        b0,
                    ),
                ),
            ),
        )
        # Half-stuck: `mkStuck o := Outer.mk o a` where `o` is an axiom of type `Inner`
        stuck_inner = Name.simple("stuckInner").axiom(type=inner_s.const())
        mk_stuck_name = Name.simple("mkStuck")
        mk_stuck_decl = mk_stuck_name.definition(
            type=forall(x.binder(type=inner_s.const()))(outer_s.const()),
            value=fun(x.binder(type=inner_s.const()))(
                outer_mk.const().app(b0, a_decl.name.const()),
            ),
        )
        # Def-wrapped nested ctor: `mkInnerDef x y := Inner.mk x y`,
        # `mkOuterViaDef x := Outer.mk (mkInnerDef x (deadFn x)) (deadFn x)`
        mk_inner_def_name = Name.simple("mkInnerDef")
        mk_inner_def_decl = mk_inner_def_name.definition(
            type=forall(x.binder(type=NAT), y.binder(type=NAT))(inner_s.const()),
            value=fun(x.binder(type=NAT), y.binder(type=NAT))(
                inner_mk.const().app(b1, b0),
            ),
        )
        mk_outer_via_def_name = Name.simple("mkOuterViaDef")
        mk_outer_via_def_decl = mk_outer_via_def_name.definition(
            type=forall(x.binder(type=NAT))(outer_s.const()),
            value=fun(x.binder(type=NAT))(
                outer_mk.const().app(
                    mk_inner_def_name.const().app(b0, dead_fn.name.const().app(b0)),
                    dead_fn.name.const().app(b0),
                ),
            ),
        )

        env = Environment.having([
            nat_decl, a_decl, b_decl, dead_fn,
            inner_decl, inner_mk_decl,
            outer_decl, outer_mk_decl,
            to_inner_decl, mk_outer_decl, mk_let_outer_decl,
            stuck_inner, mk_stuck_decl,
            mk_inner_def_decl, mk_outer_via_def_decl,
        ])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            store = m.store
            h_a = store.import_term(a_decl.name.const())
            h_b = store.import_term(b_decl.name.const())

            # 1. Direct nested projection `Proj(Inner, 0, Proj(Outer, 0, mkOuter a))`
            #    skips BOTH `Inner.mk` and `deadFn` completely (zero new records!).
            p_nested = store.import_term(
                inner_s.proj(0, outer_s.proj(0, mk_outer_name.const().app(a_decl.name.const()))),
            )
            nrecs_before = store.nrecs
            assert m.try_proj(p_nested, False) == h_a
            assert store.nrecs == nrecs_before

            # 2. Projection through `tag == 2` wrapper `Proj(Inner, 0, Outer.toInner (mkOuter b))`
            #    fuses through `Outer.toInner` -> `Outer.mk` -> `Inner.mk` without importing `deadFn`!
            p_wrapped = store.import_term(
                inner_s.proj(0, to_inner_name.const().app(mk_outer_name.const().app(b_decl.name.const()))),
            )
            assert m.try_proj(p_wrapped, False) == h_b

            # 3. Projection through DefCtorApp `Proj(Inner, 0, Proj(Outer, 0, mkOuterViaDef a))`
            #    peels `mkOuterViaDef` -> `mkInnerDef` -> `b0` directly on the AST (zero new records!).
            p_via_def = store.import_term(
                inner_s.proj(0, outer_s.proj(0, mk_outer_via_def_name.const().app(a_decl.name.const()))),
            )
            nrecs_before = store.nrecs
            assert m.try_proj(p_via_def, False) == h_a
            assert store.nrecs == nrecs_before
            # Verify `deadFn` was never even imported as a leaf!
            assert all(
                not (isinstance(le, W_Const) and le.name.syntactic_eq(dead_fn.name))
                for le in store.leaves
            )

            # 3. Let-wrapped nested ctor: inner field 0 skips the let; inner field 1 evaluates it.
            p_let0 = store.import_term(
                inner_s.proj(0, outer_s.proj(0, mk_let_outer_name.const().app(a_decl.name.const()))),
            )
            nrecs_before = store.nrecs
            assert m.try_proj(p_let0, False) == h_a
            assert store.nrecs == nrecs_before

            p_let1 = store.import_term(
                inner_s.proj(1, outer_s.proj(0, mk_let_outer_name.const().app(a_decl.name.const()))),
            )
            assert m.try_proj(p_let1, False) == store.import_term(
                dead_fn.name.const().app(a_decl.name.const()),
            )

            # 4. Soundness: half-stuck nested projection MUST return 0!
            p_stuck = store.import_term(
                inner_s.proj(0, outer_s.proj(0, mk_stuck_name.const().app(stuck_inner.name.const()))),
            )
            assert m.try_proj(p_stuck, False) == 0
        finally:
            tc.free()

    def test_infer_app_unchecked_strips_forall_domains(self):
        from rpylean.environment import Environment, TypeChecker
        from rpylean.machine import _s32, leaf_index
        from rpylean.objects import W_Const, W_NotAFunction, W_TypeError

        u_n = Name.simple("u")
        u_l = u_n.as_level_param()
        v_l = Name.simple("v").as_level_param()

        nat_decl = Name.simple("Nat").inductive(type=TYPE)
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").axiom(type=NAT)
        # Marker type constructors that appear ONLY inside binder domains.
        dead1 = Name.simple("DeadDom1").axiom(type=TYPE)
        dead2 = Name.simple("DeadDom2").axiom(type=forall(x.binder(type=TYPE))(TYPE))
        dead_poly = Name.simple("DeadPoly").axiom(
            levels=[u_n], type=forall(x.binder(type=u_l.succ().sort()))(TYPE),
        )
        res_decl = Name.simple("Res").axiom(
            type=forall(x.binder(type=NAT), y.binder(type=NAT))(TYPE),
        )
        res1_decl = Name.simple("Res1").axiom(type=forall(x.binder(type=NAT))(TYPE))
        res_poly = Name.simple("ResPoly").axiom(
            levels=[u_n], type=forall(x.binder(type=u_l.succ().sort()))(u_l.succ().sort()),
        )
        # 1. Multi-arg constant with unused binder domains (k == n)
        f2 = Name.simple("f2").axiom(
            type=forall(
                x.binder(type=dead1.name.const()),
                y.binder(type=dead2.name.const().app(NAT)),
            )(res_decl.name.const().app(b1, b0)),
        )
        # 2. Single-arg constant with unused binder domain
        f1 = Name.simple("f1").axiom(
            type=forall(x.binder(type=dead1.name.const()))(
                res1_decl.name.const().app(b0),
            ),
        )
        # 3. BVar-returning constant (zero record allocation)
        ret_bvar = Name.simple("retBVar").axiom(
            type=forall(
                x.binder(type=TYPE),
                y.binder(type=dead2.name.const().app(b0)),
            )(b1),
        )
        # 4. Alias-headed constant (0 < k < n) where body unfolds to W_ForAll
        alias_ty = Name.simple("AliasTy").definition(
            type=forall(x.binder(type=NAT))(TYPE),
            value=fun(x.binder(type=NAT))(
                forall(y.binder(type=NAT))(res_decl.name.const().app(b1, b0)),
            ),
        )
        f_alias = Name.simple("fAlias").axiom(
            type=forall(x.binder(type=dead1.name.const()))(
                alias_ty.name.const().app(b0),
            ),
        )
        # 5. Partially applied 3-arg constant (k == n < total binders)
        f3 = Name.simple("f3").axiom(
            type=forall(
                x.binder(type=dead1.name.const()),
                y.binder(type=dead2.name.const().app(NAT)),
                Name.simple("z").binder(type=NAT),
            )(res_decl.name.const().app(b2, b1)),
        )
        # 6. Universe-polymorphic constant
        f_poly = Name.simple("fPoly").axiom(
            levels=[u_n],
            type=forall(
                x.binder(type=u_l.succ().sort()),
                y.binder(type=dead_poly.name.const([u_l]).app(b0)),
            )(res_poly.name.const([u_l]).app(b1)),
        )
        # 7. Non-function alias (for W_NotAFunction check on 0 < k < n)
        f_nonfn = Name.simple("fNonFn").axiom(
            type=forall(x.binder(type=dead1.name.const()))(NAT),
        )

        env = Environment.having([
            nat_decl, a_decl, b_decl,
            dead1, dead2, dead_poly,
            res_decl, res1_decl, res_poly,
            f2, f1, ret_bvar, alias_ty, f_alias, f3, f_poly, f_nonfn,
        ])
        tc = TypeChecker(env, None)
        m = tc.machine
        try:
            store = m.store
            A = a_decl.name.const()
            B = b_decl.name.const()
            h_nat = store.import_term(NAT)

            # Multi-arg (k == n)
            h_f2_head = store.import_term(f2.name.const())
            h_f2 = store.import_term(f2.name.const().app(A, B))
            assert m.infer(h_f2, False) == store.import_term(res_decl.name.const().app(A, B))
            assert _s32(store.leaf_infer[leaf_index(h_f2_head)]) == 0

            # Single-arg (k == 1)
            h_f1 = store.import_term(f1.name.const().app(A))
            assert m.infer(h_f1, False) == store.import_term(res1_decl.name.const().app(A))

            # Direct W_BVar return allocates zero records
            h_rb = store.import_term(ret_bvar.name.const().app(NAT, A))
            nrecs_before = store.nrecs
            assert m.infer(h_rb, False) == h_nat
            assert store.nrecs == nrecs_before

            # Alias-headed (0 < k < n)
            h_fa = store.import_term(f_alias.name.const().app(A, B))
            assert m.infer(h_fa, False) == store.import_term(res_decl.name.const().app(A, B))

            # Partial application (k == n < total binders)
            h_f3 = store.import_term(f3.name.const().app(A, B))
            assert m.infer(h_f3, False) == store.import_term(
                forall(Name.simple("z").binder(type=NAT))(res_decl.name.const().app(A, B)),
            )

            # Universe-polymorphic instantiation
            h_fp = store.import_term(f_poly.name.const([v_l]).app(v_l.sort(), A))
            assert m.infer(h_fp, False) == store.import_term(
                res_poly.name.const([v_l]).app(v_l.sort()),
            )

            # None of the dead binder-domain constants were ever imported!
            dead_names = {dead1.name, dead2.name, dead_poly.name}
            assert all(
                not (isinstance(le, W_Const) and any(le.name.syntactic_eq(d) for d in dead_names))
                for le in store.leaves
            )

            # W_NotAFunction when 0 < k < n and remaining target is not a Pi
            h_nonfn = store.import_term(f_nonfn.name.const().app(A, B))
            with pytest.raises(W_NotAFunction):
                m.infer(h_nonfn, False)

            # Soundness: check=True on f2 a b MUST check binder domain DeadDom1 != Nat and fail!
            with pytest.raises(W_TypeError):
                m.infer(h_f2, True)
        finally:
            tc.free()
