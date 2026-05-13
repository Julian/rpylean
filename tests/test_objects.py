from rpython.rlib.rbigint import rbigint
import pytest

from rpylean.objects import (
    NAT,
    NAT_ZERO,
    PROP,
    TYPE,
    W_LEVEL_ZERO,
    Binder,
    Name,
    W_App,
    W_Axiom,
    W_BVar,
    W_Closure,
    W_Const,
    W_Constructor,
    W_Declaration,
    W_Definition,
    W_ForAll,
    W_Inductive,
    W_Lambda,
    W_Let,
    W_LevelIMax,
    W_LevelMax,
    W_LevelParam,
    W_LevelSucc,
    W_LitNat,
    W_LitStr,
    W_Opaque,
    W_Proj,
    W_Recursor,
    W_Sort,
    W_Theorem,
    forall,
    fun,
    names,
)


Empty, x, y = names("Empty", "x", "y")
u, v = Name.simple("u").level(), Name.simple("v").level()


class TestName(object):
    def test_simple(self):
        assert Name.simple("foo") == Name.of(["foo"])

    def test_simple_hierarchical(self):
        assert Name.simple("foo.bar") == Name.of(["foo.bar"])

    def test_from_str(self):
        assert Name.from_str("foo") == Name.of(["foo"])

    def test_from_str_multipart(self):
        assert Name.from_str("foo.bar") == Name.of(["foo", "bar"])

    def test_child(self):
        assert Name.simple("foo").child("bar") == Name.of(["foo", "bar"])

    def test_child_anonymous(self):
        assert Name.ANONYMOUS.child("foo") == Name.simple("foo")

    def test_is_private_via_prefix(self):
        assert Name.of(["_private", "foo"]).is_private

    def test_is_private_via_nested(self):
        assert Name.from_str("foo._private.bar.0.baz").is_private

    def test_not_private(self):
        assert not Name.of(["foo"]).is_private

    def test_not_private_nested(self):
        assert not Name.of(["foo", "bar"]).is_private

    def test_eq_different_identity(self):
        """Names with equal components but different identity are equal."""
        n1 = Name.simple("Nat")
        n2 = Name.simple("Nat")
        assert n1 is not n2
        assert n1 == n2

    def test_ne_different_identity(self):
        """Names with equal components but different identity are not unequal."""
        n1 = Name.simple("Nat")
        n2 = Name.simple("Nat")
        assert n1 is not n2
        assert not (n1 != n2)

    def test_app(self):
        bar = Name.of(["foo", "bar"])
        bvar = W_BVar(0)
        assert bar.app(bvar) == W_App(bar.const(), bvar)

    def test_const_no_levels(self):
        bar = Name.of(["foo", "bar"])
        assert bar.const() == W_Const(bar, [])

    def test_const_with_levels(self):
        bar = Name.of(["foo", "bar"])
        assert bar.const([u, v]) == W_Const(bar, [u, v])

    def test_let(self):
        foo = Name.simple("foo")
        Nat = Name.simple("Nat")
        zero = Nat.child("zero")
        bvar = W_BVar(0)
        assert foo.let(
            type=Nat.const(),
            value=zero.const(),
            body=bvar,
        ) == W_Let(
            name=foo,
            type=Nat.const(),
            value=zero.const(),
            body=bvar,
        )

    def test_level(self):
        assert Name.simple("foo").level() == W_LevelParam(Name.of(["foo"]))

    def test_definition(self):
        foo = Name.simple("foo")
        Nat = Name.simple("Nat")
        zero = Nat.child("zero")
        assert foo.definition(
            type=Nat.const(),
            value=zero.const(),
        ) == W_Declaration(
            name=foo,
            type=Nat.const(),
            levels=[],
            w_kind=W_Definition(value=zero.const(), hint=1),
        )

    def test_axiom(self):
        foo = Name.simple("foo")
        assert foo.axiom(type=NAT) == W_Declaration(
            name=foo,
            type=NAT,
            levels=[],
            w_kind=W_Axiom(),
        )

    def test_theorem(self):
        foo = Name.simple("foo")
        # FIXME: this theorem is not a Prop, but that's too annoying to make
        theorem = foo.theorem(type=NAT, value=NAT_ZERO)
        assert theorem == W_Declaration(
            name=Name.simple("foo"),
            type=NAT,
            levels=[],
            w_kind=W_Theorem(value=NAT_ZERO),
        )

    def test_inductive(self):
        assert Empty.inductive(type=TYPE) == W_Declaration(
            name=Empty,
            type=TYPE,
            levels=[],
            w_kind=W_Inductive(
                names=[Empty],
                constructors=[],
                recursors=[],
                num_nested=0,
                num_params=0,
                num_indices=0,
                is_recursive=False,
                is_reflexive=False,
            ),
        )

    def test_structure(self):
        Point = Name.simple("Point")
        x_nat, y_nat = x.binder(type=NAT), y.binder(type=NAT)
        mk = Point.child("mk").constructor(
            type=forall(x_nat, y_nat)(Point.const()),
            num_params=0,
            num_fields=2,
        )
        struct = Point.structure(type=TYPE, constructor=mk)
        assert struct == Point.inductive(
            type=TYPE,
            constructors=[mk],
        )

    def test_constructor(self):
        True_ = Name.simple("True")
        intro = True_.child("intro")
        assert intro.constructor(type=True_.const()) == W_Declaration(
            name=intro,
            type=True_.const(),
            levels=[],
            w_kind=W_Constructor(num_params=0, num_fields=0),
        )

    def test_recursor(self):
        rec = Empty.child("rec")
        assert rec.recursor(type=Empty.const()) == W_Declaration(
            name=rec,
            type=Empty.const(),
            levels=[],
            w_kind=W_Recursor(
                names=[rec],
                rules=[],
                num_motives=1,
                num_params=0,
                num_indices=0,
                num_minors=0,
                k=0,
            ),
        )

    def test_opaque(self):
        o = Name.simple("o")
        Nat = Name.simple("Nat")
        zero = Nat.child("zero")
        assert o.opaque(type=Nat.const(), value=zero.const()) == W_Declaration(
            name=o,
            type=Nat.const(),
            levels=[],
            w_kind=W_Opaque(value=zero.const()),
        )

    def test_proj(self):
        Prod = Name.simple("Prod")
        mk = Prod.child("mk")
        expr = mk.app(NAT_ZERO, NAT_ZERO)
        assert Prod.proj(0, expr) == W_Proj(Prod, 0, expr)

    def test_binder(self):
        Nat = Name.simple("Nat")
        assert x.binder(type=Nat) == Binder(
            name=x,
            type=Nat,
            left="(",
            right=")",
        )

    def test_implicit_binder(self):
        Nat = Name.simple("Nat")
        assert x.implicit_binder(type=Nat) == Binder(
            name=x,
            type=Nat,
            left="{",
            right="}",
        )

    def test_instance_implicit_binder(self):
        NeZero = Name.simple("NeZero")
        assert x.instance_binder(type=NeZero) == Binder(
            name=x,
            type=NeZero,
            left="[",
            right="]",
        )

    def test_strict_implicit_binder(self):
        Nat = Name.simple("Nat")
        assert x.strict_implicit_binder(type=Nat) == Binder(
            name=x,
            type=Nat,
            left="⦃",
            right="⦄",
        )

    def test_hash_is_order_sensitive(self):
        assert Name.of(["foo", "bar"]).hash() != Name.of(["bar", "foo"]).hash()


def test_names():
    assert names("foo", "A.b") == [Name.simple("foo"), Name.of(["A", "b"])]


class TestBinder(object):
    def test_to_implicit(self):
        Nat = Name.simple("Nat")
        binder = Binder.default(name=x, type=Nat).to_implicit()
        assert binder == Binder.implicit(name=x, type=Nat)

    def test_default_is_default(self):
        assert Name.simple("x").binder(type=NAT).is_default()

    def test_not_default_is_not_default(self):
        assert not Name.simple("x").implicit_binder(type=NAT).is_default()


class TestDeclaration(object):
    def test_const(self):
        decl = Name.simple("foo").axiom(type=NAT)
        assert decl.const() == W_Const(Name.simple("foo"), [])

    def test_const_with_level_params_no_levels(self):
        decl = Name.simple("foo").axiom(type=NAT)
        assert decl.const_with_level_params() == W_Const(Name.simple("foo"), [])

    def test_const_with_level_params_polymorphic(self):
        u, v = Name.simple("u"), Name.simple("v")
        decl = Name.simple("foo").axiom(type=u.level().sort(), levels=[u, v])
        assert decl.const_with_level_params() == W_Const(
            Name.simple("foo"),
            [W_LevelParam(u), W_LevelParam(v)],
        )


class TestLevel(object):
    @pytest.mark.parametrize(
        "lhs, rhs, expected",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (
                W_LEVEL_ZERO.succ(),
                W_LEVEL_ZERO.succ().succ().succ(),
                W_LEVEL_ZERO.succ().succ().succ(),
            ),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (
                W_LEVEL_ZERO.succ().succ(),
                W_LEVEL_ZERO.succ(),
                W_LEVEL_ZERO.succ().succ(),
            ),
            (u, u, u),
            (u, v, W_LevelMax(u, v)),
            (u.succ(), v, W_LevelMax(u.succ(), v)),
            (u, v.succ(), W_LevelMax(u, v.succ())),
            (u.succ(), v.succ(), u.max(v).succ()),
            (u.succ(), u, u.succ()),
            (u, u.succ(), u.succ()),
            (u, u.max(v), u.max(v)),
            (v, u.max(v), u.max(v)),
            (u, u.imax(v), u.imax(v)),
            (v, u.imax(v), u.imax(v)),
        ],
        ids=[
            "0_0",
            "0_1",
            "1_3",
            "1_0",
            "2_1",
            "u_u",
            "u_v",
            "u+1_v",
            "u_v+1",
            "u+1_v+1",
            "u+1_u",
            "u_u+1",
            "u_maxuv",
            "v_maxuv",
            "u_imaxuv",
            "v_imaxuv",
        ],
    )
    def test_max(self, lhs, rhs, expected):
        assert lhs.max(rhs) == expected

    @pytest.mark.parametrize(
        "lhs, rhs, expected",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO, W_LEVEL_ZERO),
            # imax 1 0 = 0
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO, W_LEVEL_ZERO),
            # in fact imax u 0 = 0 for any u
            (u, W_LEVEL_ZERO, W_LEVEL_ZERO),
            # but imax 0 1 = 1
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            # in fact imax 0 u = u for any u
            (W_LEVEL_ZERO, u, u),
            # and in fact imax 1 u = u for any u as well
            (W_LEVEL_ZERO.succ(), u, u),
            (u, u, u),
            (u, v, W_LevelIMax(u, v)),
        ],
        ids=[
            "0_0",
            "1_0",
            "u_0",
            "0_1",
            "0_u",
            "1_u",
            "u_u",
            "u_v",
        ],
    )
    def test_imax(self, lhs, rhs, expected):
        assert lhs.imax(rhs) == expected

    @pytest.mark.parametrize(
        "lhs, rhs",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u.succ()),
            (u, u.succ().succ()),
            (W_LEVEL_ZERO, u),
            (W_LEVEL_ZERO, u.max(v)),
            (W_LEVEL_ZERO, u.imax(v)),
            (u.max(v), u.succ().max(v.succ())),
            (u.imax(v), u.succ().imax(v.succ())),
        ],
        ids=[
            "0_1",
            "1_2",
            "u_u+1",
            "u_u+2",
            "0_u",
            "0_max_uv",
            "0_imax_uv",
            "max_uv_u+1v+1",
            "imax_uv_u+1v+1",
        ],
    )
    def test_leq_lt(self, lhs, rhs):
        assert lhs.leq(rhs)
        assert not rhs.leq(lhs)

    @pytest.mark.parametrize(
        "lhs, rhs",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ().succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u),
            (u.succ(), u.succ()),
            (u.succ().succ(), u.succ().succ()),
            (u.max(v), u.max(v)),
            (u.max(v).succ(), u.max(v).succ()),
            (u.imax(v), u.imax(v)),
            (u.imax(v).succ(), u.imax(v).succ()),
        ],
        ids=[
            "0_0",
            "1_1",
            "2_2",
            "u_u",
            "u+1_u+1",
            "u+2_u+2",
            "max_uv",
            "max_uv+1",
            "imax_uv",
            "imax_uv+1",
        ],
    )
    def test_leq_eq(self, lhs, rhs):
        assert lhs.leq(rhs)
        assert rhs.leq(lhs)
        assert lhs.eq(rhs)
        assert rhs.eq(lhs)

    def test_leq_eq_distinct_max_succ(self):
        """(max 1 u) + 1 ≤ (max 1 u) + 1 with distinct objects."""
        u1 = Name.simple("u").level()
        u2 = Name.simple("u").level()
        lhs = W_LEVEL_ZERO.succ().max(u1).succ()
        rhs = W_LEVEL_ZERO.succ().max(u2).succ()
        assert lhs is not rhs
        assert lhs.leq(rhs)
        assert rhs.leq(lhs)
        assert lhs.eq(rhs)

    def test_leq_eq_distinct_param(self):
        """u ≤ u with distinct W_LevelParam objects."""
        u1 = Name.simple("u").level()
        u2 = Name.simple("u").level()
        assert u1 is not u2
        assert u1.leq(u2)
        assert u2.leq(u1)
        assert u1.eq(u2)

    def test_leq_eq_nested_max_dup(self):
        """max (max 1 u) (max 1 u) ≤ max 1 u."""
        u1 = Name.simple("u").level()
        u2 = Name.simple("u").level()
        u3 = Name.simple("u").level()
        inner1 = W_LEVEL_ZERO.succ().max(u1)
        inner2 = W_LEVEL_ZERO.succ().max(u2)
        lhs = W_LevelMax(inner1, inner2)
        rhs = W_LEVEL_ZERO.succ().max(u3)
        assert lhs.leq(rhs)
        assert rhs.leq(lhs)
        assert lhs.eq(rhs)

    def test_max_gt_zero(self):
        """0 ≤ max(u, v)"""
        assert u.max(v).gt(W_LEVEL_ZERO, 0)

    def test_max_gt_param(self):
        """u ≤ max(u, v)"""
        u2 = Name.simple("u").level()
        assert u.max(v).gt(u2, 0)

    def test_max_gt_param_negative_balance(self):
        """u ≤ max(u, v) - 1 is unknown"""
        assert not u.max(v).gt(u, -1)

    def test_param_gt_zero(self):
        """0 ≤ u"""
        assert u.gt(W_LEVEL_ZERO, 0)

    def test_param_gt_same(self):
        """u ≤ u with distinct objects"""
        u2 = Name.simple("u").level()
        assert u.gt(u2, 0)

    def test_param_gt_different(self):
        """v ≤ u is unknown"""
        assert not u.gt(v, 0)

    def test_param_gt_zero_negative(self):
        """0 ≤ u - 1 is unknown"""
        assert not u.gt(W_LEVEL_ZERO, -1)

    def test_succ(self):
        assert u.succ() == W_LevelSucc(W_LevelParam(Name.of(["u"])))

    def test_succ_level_zero(self):
        assert W_LEVEL_ZERO.succ() == W_LevelSucc(W_LEVEL_ZERO)

    def test_sort(self):
        assert W_LEVEL_ZERO.sort() == W_Sort(W_LEVEL_ZERO) == PROP


class TestConst(object):
    def test_child(self):
        name = Name.simple("foo")
        assert name.const().child("bar") == name.child("bar").const()

    def test_app(self):
        bvar = W_BVar(0)
        id = Name.simple("id").const()
        assert id.app(bvar) == W_App(id, bvar)

    def test_app_multiarg(self):
        b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)
        foo = Name.simple("foo").const()
        assert foo.app(b0, b1, b2) == W_App(W_App(W_App(foo, b0), b1), b2)


class TestLitNat(object):
    def test_char(self):
        assert W_LitNat.char("o") == W_LitNat.int(111)

    def test_int(self):
        assert W_LitNat.int(37) == W_LitNat(rbigint.fromint(37))


class TestLitStr(object):
    def test_subst_levels(self):
        lit = W_LitStr("hi")
        assert lit.subst_levels({Name.simple("u"): W_LEVEL_ZERO}) is lit

    def test_bind_fvar(self):
        lit = W_LitStr("hi")
        fvar = x.binder(type=NAT).fvar()
        assert lit.bind_fvar(fvar, 0) is lit

    def test_incr_free_bvars(self):
        lit = W_LitStr("hi")
        assert lit.incr_free_bvars(1, 0) is lit


class TestForAll(object):
    def test_single(self):
        nat = x.binder(type=NAT)
        assert forall(nat)(y.const()) == W_ForAll(binder=nat, body=y.const())

    def test_multiple(self):
        P = Name.simple("P").const()
        x_nat = x.binder(type=NAT)
        y_type = y.binder(type=TYPE)
        assert forall(x_nat, y_type)(P) == W_ForAll(
            binder=x_nat,
            body=W_ForAll(binder=y_type, body=P),
        )


class TestFun(object):
    def test_single(self):
        nat = x.binder(type=NAT)
        assert fun(nat)(y.const()) == W_Lambda(binder=nat, body=y.const())

    def test_multiple(self):
        P = Name.simple("P").const()
        x_nat = x.binder(type=NAT)
        y_type = y.binder(type=TYPE)
        assert fun(x_nat, y_type)(P) == W_Lambda(
            binder=x_nat,
            body=W_Lambda(binder=y_type, body=P),
        )


class TestClosure(object):
    def test_loose_bvar_range_closed_body(self):
        """Closure([fvar], BVar(0)) has no loose bvars (env entry is closed)."""
        fvar = x.binder(type=NAT).fvar()
        assert W_BVar(0).closure([fvar]).loose_bvar_range == 0

    def test_loose_bvar_range_body_leaks(self):
        """Closure([fvar], BVar(2)) leaks bvar(2-1) = bvar(1) outside."""
        fvar = x.binder(type=NAT).fvar()
        assert W_BVar(2).closure([fvar]).loose_bvar_range == 2

    def test_loose_bvar_range_env_entry_open(self):
        """An env entry's loose bvars contribute to the closure's range."""
        assert W_BVar(0).closure([W_BVar(3)]).loose_bvar_range == 4

    def test_closure_of_closed_body_is_identity(self):
        """A body with no loose bvars doesn't need wrapping."""
        const = Name.simple("c").const()
        fvar = x.binder(type=NAT).fvar()
        assert const.closure([fvar]) is const

    def test_closure_with_empty_env_is_identity(self):
        bvar = W_BVar(0)
        assert bvar.closure([]) is bvar

    def test_force_substitutes_innermost_bvar(self):
        """Closure([a], BVar(0)).force() = a."""
        a_decl = Name.simple("a").axiom(type=NAT)
        a = a_decl.const()
        closure = W_Closure([a], W_BVar(0))
        assert closure.force() == a

    def test_force_with_multi_env(self):
        """Closure([a, b], App(BVar(0), BVar(1))).force() = App(a, b)."""
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").axiom(type=NAT)
        a = a_decl.const()
        b = b_decl.const()
        body = W_App(W_BVar(0), W_BVar(1))
        closure = W_Closure([a, b], body)
        assert closure.force() == W_App(a, b)

    def test_force_preserves_env_entry_bvars(self):
        """env entries' free bvars survive force without being over-substituted."""
        # env=[BVar(0), BVar(0)], body=App(BVar(0), BVar(1))
        # Semantics: body's bvar(0) -> env[0] = BVar(0) (refers to OUTER bvar(0));
        #           body's bvar(1) -> env[1] = BVar(0) (also refers to OUTER bvar(0)).
        # Both env entries refer to the same outer bvar, so result should be
        # App(BVar(0), BVar(0)).
        body = W_App(W_BVar(0), W_BVar(1))
        closure = W_Closure([W_BVar(0), W_BVar(0)], body)
        assert closure.force() == W_App(W_BVar(0), W_BVar(0))
