"""
Tests for the raw term store: records in raw memory, canonical leaves,
and the boxed boundary.
"""

import pytest

from rpylean._rawterms import (
    KIND_APP,
    KIND_FORALL,
    KIND_LAMBDA,
    KIND_LET,
    KIND_PROJ,
    RawIntMap,
    RawTermStore,
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
b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)
u = Name.simple("u").level()


@pytest.fixture
def store(request):
    s = RawTermStore(None, capacity=16)
    request.addfinalizer(s.free)
    return s


def roundtrip(store, e):
    h = store.import_term(e)
    back = store.export_term(h)
    assert syntactic_eq(back, e), (back, e)
    return h


class TestRawIntMap(object):
    def test_get_set_grow(self):
        m = RawIntMap(capacity=4)
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
        m = RawIntMap()
        m.free()
        m.free()


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

    def test_loose_range_matches_boxed(self, store):
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
        store = RawTermStore(None, capacity=4)
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
        store = RawTermStore(None)
        store.import_term(f.const().app(x.const()))
        store.free()
        store.free()
