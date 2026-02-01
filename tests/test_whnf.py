"""
Tests for weak head normal form (WHNF) reduction.
"""

from rpylean.environment import Environment
from rpylean.objects import (
    NAT,
    TYPE,
    PROP,
    Name,
    W_BVar,
    W_LitNat,
    W_LitStr,
    forall,
    fun,
    names,
    syntactic_eq,
)


S, a, b, f, x, y, z = names("S", "a", "b", "f", "x", "y", "z")
b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)
u = Name.simple("u").level()


class TestFVar:
    def test_already_whnf(self):
        fvar = x.binder(type=NAT).fvar()
        assert fvar.whnf(Environment.EMPTY) is fvar


class TestLitStr:
    def test_already_whnf(self):
        lit = W_LitStr("hello")
        assert lit.whnf(Environment.EMPTY) is lit


class TestLitNat:
    def test_already_whnf(self):
        lit = W_LitNat.int(42)
        assert lit.whnf(Environment.EMPTY) is lit


class TestSort:
    def test_already_whnf(self):
        assert TYPE.whnf(Environment.EMPTY) is TYPE
        assert PROP.whnf(Environment.EMPTY) is PROP

        sort_u = u.sort()
        assert sort_u.whnf(Environment.EMPTY) is sort_u


class TestLambda:
    def test_already_whnf(self):
        lam = fun(x.binder(type=NAT))(b0)
        assert lam.whnf(Environment.EMPTY) is lam

    def test_body_not_reduced(self):
        # f := fun x ↦ x
        f_decl = Name.simple("f").definition(
            type=forall(x.binder(type=NAT))(NAT),
            value=fun(x.binder(type=NAT))(b0),
        )
        env = Environment.having([f_decl])

        # fun y ↦ f y - the body contains an application that could reduce
        lam = fun(y.binder(type=NAT))(f_decl.const().app(b0))
        assert lam.whnf(env) is lam


class TestForAll:
    def test_already_whnf(self):
        fa = forall(x.binder(type=NAT))(NAT)
        assert fa.whnf(Environment.EMPTY) is fa


class TestConst:
    def test_axiom_already_whnf(self):
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])
        const = a_decl.const()
        assert const.whnf(env) is const

    def test_definition_unfolds_to_value(self):
        # a := b
        b_decl = b.axiom(type=NAT)
        a_decl = a.definition(type=NAT, value=b_decl.const())
        env = Environment.having([a_decl, b_decl])

        assert syntactic_eq(a_decl.const().whnf(env), b_decl.const())

    def test_nested_definitions_fully_reduce(self):
        # c is an axiom
        # b := c
        # a := b
        # a.whnf gives c
        c_decl = Name.simple("c").axiom(type=NAT)
        b_decl = b.definition(type=NAT, value=c_decl.const())
        a_decl = a.definition(type=NAT, value=b_decl.const())
        env = Environment.having([a_decl, b_decl, c_decl])

        assert syntactic_eq(a_decl.const().whnf(env), c_decl.const())


class TestApp:
    """W_App.whnf performs beta reduction when head is a lambda."""

    def test_app_of_axiom_is_whnf(self):
        """Application of axiom (non-lambda) is already in WHNF."""
        f_decl = f.axiom(type=forall(x.binder(type=NAT))(NAT))
        a_decl = a.axiom(type=NAT)
        env = Environment.having([f_decl, a_decl])

        app = f_decl.const().app(a_decl.const())
        # Can't reduce - f is an axiom, not a lambda
        assert syntactic_eq(app.whnf(env), app)

    def test_beta_reduction(self):
        """(fun x ↦ x) a reduces to a."""
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        identity = fun(x.binder(type=NAT))(b0)
        app = identity.app(a_decl.const())

        assert syntactic_eq(app.whnf(env), a_decl.const())

    def test_beta_reduction_via_delta(self):
        """f a reduces to a when f := fun x ↦ x."""
        a_decl = a.axiom(type=NAT)
        f_decl = f.definition(
            type=forall(x.binder(type=NAT))(NAT),
            value=fun(x.binder(type=NAT))(b0),
        )
        env = Environment.having([f_decl, a_decl])

        app = f_decl.const().app(a_decl.const())

        # f unfolds to identity, then beta reduces
        assert syntactic_eq(app.whnf(env), a_decl.const())

    def test_nested_beta_reduction(self):
        """(fun x ↦ fun y ↦ x) a b reduces to a."""
        a_decl = a.axiom(type=NAT)
        b_decl = b.axiom(type=NAT)
        env = Environment.having([a_decl, b_decl])

        # fun x ↦ fun y ↦ x (returns first argument)
        const_fn = fun(x.binder(type=NAT), y.binder(type=NAT))(b1)
        app = const_fn.app(a_decl.const(), b_decl.const())

        assert syntactic_eq(app.whnf(env), a_decl.const())

    def test_partial_application(self):
        """(fun x y ↦ x) a reduces to fun y ↦ a."""
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        const_fn = fun(x.binder(type=NAT), y.binder(type=NAT))(b1)
        partial = const_fn.app(a_decl.const())

        # fun y ↦ a
        expected = fun(y.binder(type=NAT))(a_decl.const())
        assert syntactic_eq(partial.whnf(env), expected)


class TestLet:
    def test_zeta(self):
        """
        let x := a in x reduces to a.
        """
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        let_expr = x.let(type=NAT, value=a_decl.const(), body=b0)

        assert syntactic_eq(let_expr.whnf(env), a_decl.const())

    def test_nested(self):
        """
        let x := a in let y := x in y reduces to a.
        """
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        inner_let = y.let(type=NAT, value=b0, body=b0)  # let y := x in y
        outer_let = x.let(type=NAT, value=a_decl.const(), body=inner_let)

        assert syntactic_eq(outer_let.whnf(env), a_decl.const())


class TestProj:
    def test_reduces_struct(self):
        a_decl = a.axiom(type=NAT)
        f_decl = f.definition(type=NAT, value=a_decl.const())
        env = Environment.having([a_decl, f_decl])

        # Create a projection where the struct expr can reduce
        # proj.0 (f) where f := a
        proj = S.proj(field_index=0, struct_expr=f_decl.const())

        expected = S.proj(field_index=0, struct_expr=a_decl.const())
        assert syntactic_eq(proj.whnf(env), expected)
