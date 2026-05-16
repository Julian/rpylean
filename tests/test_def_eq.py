# -*- coding: utf-8 -*-
"""
Tests for definitional equality of Lean objects.
"""

import pytest

from io import BytesIO

from rpylean.environment import Environment, StreamTracer
from rpylean.objects import (
    W_LEVEL_ZERO,
    NAT,
    STRING,
    TYPE,
    Name,
    W_BVar,
    W_FVar,
    W_LevelIMax,
    W_LitNat,
    W_LitStr,
    W_Proj,
    forall,
    fun,
    names,
    syntactic_eq,
)

env = Environment.having([
    Name.simple("Nat").axiom(type=TYPE),
    Name.simple("String").axiom(type=TYPE),
])
a, f, g, x, y = names("a", "f", "g", "x", "y")
b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)
u, v = Name.simple("u").level(), Name.simple("v").level()


class TestFVar(object):
    def test_eq(self):
        fvar = W_FVar(x.binder(type=NAT))
        assert env.def_eq(fvar, fvar)

    def test_not_eq(self):
        binder = x.binder(type=NAT)
        assert not env.def_eq(W_FVar(binder), W_FVar(binder))


class TestLitNat(object):
    def test_eq(self):
        assert env.def_eq(W_LitNat.int(37), W_LitNat.int(37))

    def test_not_eq(self):
        assert not env.def_eq(W_LitNat.int(37), W_LitNat.int(73))

    def test_large_eq(self):
        """Large nat literals (> machine word) compare equal via rbigint.eq."""
        assert env.def_eq(W_LitNat.long(4294967296), W_LitNat.long(4294967296))

    def test_large_not_eq(self):
        assert not env.def_eq(W_LitNat.long(4294967296), W_LitNat.long(4294967297))


class TestLitStr(object):
    def test_eq(self):
        assert env.def_eq(W_LitStr("foo"), W_LitStr("foo"))

    def test_not_eq(self):
        assert not env.def_eq(W_LitStr("foo"), W_LitStr("bar"))

    def test_eq_expanded(self):
        """
        "ok" = String.ofList (List.nil.cons (Char.ofNat 107) |>.cons <| Char.ofNat 111)
        """
        alpha = Name.simple("α").binder(type=u.succ().sort())
        b0, b1, b2 = [W_BVar(i) for i in range(3)]

        head, tail = names("head", "tail")

        ListFn = Name.simple("List").const(levels=[u])
        nil_ctor = Name.of(["List", "nil"]).constructor(
            type=forall(alpha.to_implicit())(ListFn.app(b0)),
            levels=[u.name],
            num_params=1,
        )
        cons_ctor = Name.of(["List", "cons"]).constructor(
            type=forall(
                alpha.to_implicit(),
                head.binder(type=b0),
                tail.binder(type=ListFn.app(b1)),
            )(ListFn.app(b2)),
            levels=[u.name],
            num_params=1,
            num_fields=2,
        )
        List = Name.simple("List").inductive(
            type=forall(alpha)(u.succ().sort()),
            constructors=[nil_ctor, cons_ctor],
            levels=[u.name],
            num_params=1,
            is_recursive=True,
        )

        Char, ofNat, String_mk = names("Char", "Char.ofNat", "String.ofList")

        # List.{0} Char = List Char
        List_Char = Name.simple("List").const([W_LEVEL_ZERO]).app(Char.const())

        String = Name.simple("String").inductive(
            type=TYPE,
            constructors=[
                String_mk.constructor(
                    type=forall(x.binder(type=List_Char))(STRING),
                ),
            ],
        )

        decls = [
            List,
            nil_ctor,
            cons_ctor,
            String,
            String.w_kind.constructors[0],
            Char.axiom(type=TYPE),
            NAT.name.axiom(type=TYPE),
            ofNat.axiom(type=forall(x.binder(type=NAT))(Char.const())),
        ]
        env = Environment.having(decls)

        o = ofNat.app(W_LitNat.char("o"))
        k = ofNat.app(W_LitNat.char("k"))
        nil = Name.of(["List", "nil"]).const([W_LEVEL_ZERO]).app(Char.const())
        cons = Name.of(["List", "cons"]).const([W_LEVEL_ZERO]).app(Char.const())
        o_k = cons.app(o, cons.app(k, nil))
        assert env.def_eq(W_LitStr("ok"), String_mk.app(o_k))


class TestSort(object):
    @pytest.mark.parametrize(
        "level1, level2",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (u, u),
            (u.succ(), u.succ()),
            (u.max(v), u.max(v)),
            (u.max(v), v.max(u)),
            (u.imax(v), u.imax(v)),
        ],
        ids=[
            "zero",
            "succ",
            "param",
            "param_succ",
            "max",
            "max_comm",
            "imax",
        ],
    )
    def test_eq(self, level1, level2):
        assert level1.eq(level2)
        assert env.def_eq(level1.sort(), level2.sort())

    @pytest.mark.parametrize(
        "level1, level2",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO, u),
            (u, v),
            (u.succ(), v.succ()),
            (u.max(v), u.max(W_LEVEL_ZERO)),
            (u.imax(v), v.imax(u)),
            (u.imax(v), u.imax(W_LEVEL_ZERO)),
        ],
        ids=[
            "zero_succ",
            "zero_param",
            "param_param",
            "param_succ_param_succ",
            "max_ne",
            "not_max_comm",
            "imax_ne",
        ],
    )
    def test_not_eq(self, level1, level2):
        assert not level1.eq(level2)
        assert not env.def_eq(level1.sort(), level2.sort())


class TestConst(object):
    @pytest.mark.parametrize(
        "const1, const2, decls",
        [
            (
                x.const(),
                x.const(),
                [x.axiom(type=TYPE)],
            ),
            (
                x.const(levels=[u]),
                x.const(levels=[u]),
                [x.axiom(type=TYPE, levels=[u.name])],
            ),
            (
                x.const(levels=[u, v]),
                x.const(levels=[u, v]),
                [x.axiom(type=TYPE, levels=[u.name, v.name])],
            ),
        ],
        ids=[
            "same",
            "with_level",
            "multiple_levels",
        ],
    )
    def test_eq(self, const1, const2, decls):
        env = Environment.having(decls)
        assert env.def_eq(const1, const2)

    @pytest.mark.parametrize(
        "const1, const2, decls",
        [
            (
                x.const(),
                y.const(),
                [x.axiom(type=TYPE), y.axiom(type=TYPE)],
            ),
            (
                x.const(levels=[u, v]),
                x.const(levels=[v, u]),
                [x.axiom(type=TYPE, levels=[u.name, v.name])],
            ),
        ],
        ids=[
            "different_name",
            "different_level_order",
        ],
    )
    def test_not_eq(self, const1, const2, decls):
        env = Environment.having(decls)
        assert not env.def_eq(const1, const2)

    def test_mismatched_level_arity(self):
        assert not x.const().def_eq(x.const(levels=[u]), env.def_eq)
        assert not x.const(levels=[u]).def_eq(x.const(), env.def_eq)

    def test_def_eq_via_delta(self):
        """
        If def foo := bar, the two are def eq.
        """
        foo, bar = Name.simple("foo"), Name.simple("bar")
        decls = [
            bar.axiom(type=TYPE),
            foo.definition(type=TYPE, value=bar.const()),
        ]
        env = Environment.having(decls)
        assert env.def_eq(foo.const(), bar.const())

    def test_eq_different_name_identity(self):
        """
        Constants with structurally equal but non-identical Name objects
        are definitionally equal.
        """
        x1 = Name.simple("x")
        x2 = Name.simple("x")
        assert x1 is not x2
        decls = [x1.axiom(type=TYPE)]
        env = Environment.having(decls)
        assert env.def_eq(x1.const(), x2.const())


class TestForAll(object):
    @pytest.mark.parametrize(
        "forall1, forall2, decls",
        [
            (
                forall(x.binder(type=NAT))(NAT),
                forall(x.binder(type=NAT))(NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                forall(x.binder(type=NAT))(NAT),
                forall(y.binder(type=NAT))(NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                forall(x.binder(type=NAT))(b0),
                forall(y.binder(type=NAT))(b0),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                forall(x.binder(type=NAT), y.binder(type=NAT))(b0),
                forall(a.binder(type=NAT), f.binder(type=NAT))(b0),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
        ],
        ids=[
            "same",
            "alpha_equivalent",
            "same_body_reference",
            "nested_same",
        ],
    )
    def test_eq(self, forall1, forall2, decls):
        env = Environment.having(decls)
        assert env.def_eq(forall1, forall2)

    @pytest.mark.parametrize(
        "forall1, forall2, decls",
        [
            (
                forall(x.binder(type=NAT))(NAT),
                forall(x.binder(type=TYPE))(NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                forall(x.binder(type=NAT))(NAT),
                forall(x.binder(type=NAT))(TYPE),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                forall(x.binder(type=NAT))(NAT),
                forall(x.binder(type=NAT), y.binder(type=NAT))(NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
        ],
        ids=[
            "different_binder_types",
            "different_bodies",
            "different_structure",
        ],
    )
    def test_not_eq(self, forall1, forall2, decls):
        env = Environment.having(decls)
        assert not env.def_eq(forall1, forall2)


class TestApp(object):
    @pytest.mark.parametrize(
        "app1, app2, decls",
        [
            (
                f.app(x.const()),
                f.app(x.const()),
                [
                    x.axiom(type=TYPE),
                    f.axiom(type=forall(x.binder(type=TYPE))(TYPE)),
                ],
            ),
            (
                f.app(x.const(), y.const()),
                f.app(x.const(), y.const()),
                [
                    x.axiom(type=TYPE),
                    y.axiom(type=TYPE),
                    f.axiom(
                        type=forall(x.binder(type=TYPE), y.binder(type=TYPE))(
                            TYPE,
                        ),
                    ),
                ],
            ),
            (
                f.const(levels=[u]).app(x.const()),
                f.const(levels=[u]).app(x.const()),
                [
                    x.axiom(type=TYPE),
                    f.axiom(
                        type=forall(x.binder(type=TYPE))(TYPE),
                        levels=[u.name],
                    ),
                ],
            ),
        ],
        ids=[
            "simple",
            "nested_app",
            "with_levels",
        ],
    )
    def test_eq(self, app1, app2, decls):
        env = Environment.having(decls)
        assert env.def_eq(app1, app2)

    @pytest.mark.parametrize(
        "app1, app2, decls",
        [
            (
                f.app(x.const()),
                g.app(x.const()),
                [
                    x.axiom(type=TYPE),
                    f.axiom(type=forall(x.binder(type=TYPE))(TYPE)),
                    g.axiom(type=forall(x.binder(type=TYPE))(TYPE)),
                ],
            ),
            (
                f.app(x.const()),
                f.app(y.const()),
                [
                    x.axiom(type=TYPE),
                    y.axiom(type=TYPE),
                    f.axiom(type=forall(x.binder(type=TYPE))(TYPE)),
                ],
            ),
            (
                f.app(x.const(), y.const()),
                f.app(y.const(), x.const()),
                [
                    x.axiom(type=TYPE),
                    y.axiom(type=TYPE),
                    f.axiom(
                        type=forall(
                            x.binder(type=TYPE),
                            y.binder(type=TYPE),
                        )(TYPE),
                    ),
                ],
            ),
        ],
        ids=[
            "different_function",
            "different_argument",
            "different_app_order",
        ],
    )
    def test_not_eq(self, app1, app2, decls):
        env = Environment.having(decls)
        assert not env.def_eq(app1, app2)


class TestProj(object):
    def test_eq(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        Nat_decl = Name.simple("Nat").axiom(type=TYPE)
        mk_decl = mk.constructor(
            type=forall(a.binder(type=NAT))(Foo.const()),
            num_fields=1,
        )
        foo_type = Foo.structure(type=TYPE, constructor=mk_decl)
        bar = Name.simple("bar")
        x_decl = x.axiom(type=Foo.const())
        bar_def = bar.definition(type=Foo.const(), value=x.const())
        env = Environment.having([foo_type, mk_decl, Nat_decl, x_decl, bar_def])
        proj1 = Foo.proj(0, x.const())
        proj2 = Foo.proj(0, bar.const())
        assert env.def_eq(proj1, proj2)

    def test_not_def_eq(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        Nat_decl = Name.simple("Nat").axiom(type=TYPE)
        mk_decl = mk.constructor(
            type=forall(a.binder(type=NAT))(Foo.const()),
            num_fields=1,
        )
        foo_type = Foo.structure(type=TYPE, constructor=mk_decl)
        x_decl = x.axiom(type=Foo.const())
        y_decl = y.axiom(type=Foo.const())
        env = Environment.having([foo_type, mk_decl, Nat_decl, x_decl, y_decl])
        proj1 = Foo.proj(0, x.const())
        proj2 = Foo.proj(0, y.const())
        assert not env.def_eq(proj1, proj2)


class TestStructEta(object):
    """Structure eta: S.mk (S.p₁ x) ... (S.pₙ x) ≡ x."""

    def test_struct_eta_single_field(self):
        """Wrap.mk (Wrap.proj 0 b) is def-eq to b for b : Wrap."""
        Wrap = Name.simple("Wrap")
        mk = Wrap.child("mk")
        mk_decl = mk.constructor(
            type=forall(x.binder(type=NAT))(Wrap.const()),
            num_params=0,
            num_fields=1,
        )
        wrap_type = Wrap.structure(type=TYPE, constructor=mk_decl)
        Nat_decl = Name.simple("Nat").axiom(type=TYPE)

        b_binder = Name.simple("b").binder(type=Wrap.const())
        b_fvar = W_FVar(b_binder)

        # Wrap.mk (Wrap.proj 0 b)
        ctor_app = mk.app(W_Proj(Wrap, 0, b_fvar))

        env = Environment.having([wrap_type, mk_decl, Nat_decl])
        assert env.def_eq(b_fvar, ctor_app)
        assert env.def_eq(ctor_app, b_fvar)

    def test_struct_eta_multiple_fields(self):
        """Pair.mk (Pair.proj 0 p) (Pair.proj 1 p) is def-eq to p."""
        Pair = Name.simple("Pair")
        Pair_mk = Pair.child("mk")
        mk_decl = Pair_mk.constructor(
            type=forall(
                x.binder(type=NAT),
                y.binder(type=NAT),
            )(Pair.const()),
            num_params=0,
            num_fields=2,
        )
        pair_type = Pair.structure(type=TYPE, constructor=mk_decl)
        Nat_decl = Name.simple("Nat").axiom(type=TYPE)

        p_binder = Name.simple("p").binder(type=Pair.const())
        p_fvar = W_FVar(p_binder)

        # Pair.mk (Pair.proj 0 p) (Pair.proj 1 p)
        ctor_app = Pair_mk.app(
            W_Proj(Pair, 0, p_fvar),
            W_Proj(Pair, 1, p_fvar),
        )

        env = Environment.having([pair_type, mk_decl, Nat_decl])
        assert env.def_eq(p_fvar, ctor_app)
        assert env.def_eq(ctor_app, p_fvar)

    def test_struct_eta_parametric(self):
        """Struct eta skips type parameters, comparing only fields."""
        alpha = Name.simple("alpha")
        Box = Name.simple("Box")
        Box_mk = Box.child("mk")
        mk_decl = Box_mk.constructor(
            type=forall(
                alpha.binder(type=TYPE).to_implicit(),  # (α : Type)
                x.binder(type=W_BVar(0)),  # (val : α)
            )(Box.const().app(W_BVar(1))),  # Box α
            num_params=1,
            num_fields=1,
        )
        box_type = Box.inductive(
            type=forall(alpha.binder(type=TYPE))(TYPE),
            constructors=[mk_decl],
            num_params=1,
        )
        Nat_decl = Name.simple("Nat").axiom(type=TYPE)

        b_binder = Name.simple("b").binder(type=Box.const().app(NAT))
        b_fvar = W_FVar(b_binder)

        # Box.mk Nat (Box.proj 0 b)
        ctor_app = Box_mk.const().app(NAT, W_Proj(Box, 0, b_fvar))

        env = Environment.having([box_type, mk_decl, Nat_decl])
        assert env.def_eq(b_fvar, ctor_app)
        assert env.def_eq(ctor_app, b_fvar)

    def test_struct_eta_rejects_recursive_type(self):
        """Struct eta does not apply to recursive inductive types."""
        MyNat = Name.simple("MyNat")
        mk = MyNat.child("mk")
        mk_decl = mk.constructor(
            type=forall(x.binder(type=MyNat.const()))(MyNat.const()),
            num_params=0,
            num_fields=1,
        )
        mynat_type = MyNat.inductive(
            type=TYPE,
            constructors=[mk_decl],
            num_indices=0,
            is_recursive=True,
        )

        b_binder = Name.simple("b").binder(type=MyNat.const())
        b_fvar = W_FVar(b_binder)

        ctor_app = mk.app(W_Proj(MyNat, 0, b_fvar))

        env = Environment.having([mynat_type, mk_decl])
        assert not env.def_eq(b_fvar, ctor_app)

    def test_struct_eta_rejects_wrong_field(self):
        """Struct eta fails when a field does not match the projection."""
        Wrap = Name.simple("Wrap")
        mk = Wrap.child("mk")
        mk_decl = mk.constructor(
            type=forall(x.binder(type=NAT))(Wrap.const()),
            num_params=0,
            num_fields=1,
        )
        wrap_type = Wrap.structure(type=TYPE, constructor=mk_decl)
        Nat_decl = Name.simple("Nat").axiom(type=TYPE)
        c = Name.simple("c")
        c_decl = c.axiom(type=NAT)

        b_binder = Name.simple("b").binder(type=Wrap.const())
        b_fvar = W_FVar(b_binder)

        # Wrap.mk c -- c is not Wrap.proj 0 b
        ctor_app = mk.app(c_decl.const())

        env = Environment.having([wrap_type, mk_decl, Nat_decl, c_decl])
        assert not env.def_eq(b_fvar, ctor_app)

    def test_unit_like_eta(self):
        """Any two values of a zero-field structure are def-eq."""
        MyUnit = Name.simple("MyUnit")
        mk = MyUnit.child("mk")
        mk_decl = mk.constructor(type=MyUnit.const(), num_fields=0)
        unit_type = MyUnit.structure(type=TYPE, constructor=mk_decl)
        env = Environment.having([unit_type, mk_decl])
        fvar1 = W_FVar(x.binder(type=MyUnit.const()))
        fvar2 = W_FVar(y.binder(type=MyUnit.const()))
        assert env.def_eq(fvar1, fvar2)


def test_beta_reduction():
    env = Environment.having(
        [
            Name.simple("Nat").axiom(type=TYPE),
            f.axiom(type=forall(x.binder(type=NAT), y.binder(type=NAT))(TYPE)),
            a.axiom(type=NAT),
            y.axiom(type=NAT),
        ],
    )

    F = fun(x.binder(type=NAT))(f.app(b0, y.const()))
    assert env.def_eq(F.app(a.const()), f.app(a.const(), y.const()))
    assert env.def_eq(f.app(a.const(), y.const()), F.app(a.const()))


def test_nested_beta_reduction():
    a_decl = a.axiom(type=NAT)
    env = Environment.having([a_decl, Name.simple("Nat").axiom(type=TYPE)])

    # (fun x => (fun y => y) x)
    inner_id = fun(y.binder(type=NAT))(b0)  # fun y => y
    outer = fun(x.binder(type=NAT))(inner_id.app(b0))  # fun x => (fun y => y) x

    # outer a reduces to a via two beta steps
    assert env.def_eq(outer.app(a_decl.const()), a_decl.const())
    assert env.def_eq(a_decl.const(), outer.app(a_decl.const()))


def test_forall_chain_eq_app_of_fun():
    """
    `∀ (z : Nat), (fun T ↦ T) Nat` ≟ `(fun T ↦ ∀ (z : Nat), T) Nat`.

    Both reduce to `∀ (z : Nat), Nat` after beta. The first puts the
    redex inside the forall body; the second has it at the top.
    """
    nat_decl = Name.simple("Nat").axiom(type=TYPE)
    e = Environment.having([nat_decl])
    nat_const = nat_decl.const()

    z_binder = Name.simple("z").binder(type=nat_const)
    inner_fun = fun(Name.simple("T").binder(type=TYPE))(b0)
    lhs = forall(z_binder)(inner_fun.app(nat_const))
    outer_fun = fun(Name.simple("T").binder(type=TYPE))(forall(z_binder)(b1))
    rhs = outer_fun.app(nat_const)

    assert e.def_eq(lhs, rhs)


def test_zeta_reduction():
    env = Environment.having(
        [
            Name.simple("Nat").axiom(type=TYPE),
            a.axiom(type=NAT),
        ],
    )

    let_expr = x.let(type=NAT, value=a.const(), body=b0)
    assert env.def_eq(let_expr, a.const())
    assert env.def_eq(a.const(), let_expr)


def test_succ_max_eq_imax_succ():
    assert (W_LEVEL_ZERO.succ().max(u)).eq(u.imax(W_LEVEL_ZERO.succ()))


def test_trace_def_eq():
    """Tracing def_eq writes each comparison to the trace stream."""
    trace = BytesIO()
    from rpylean._tokens import TokenWriter, FORMAT_PLAIN

    traced_env = Environment.having(
        [Name.simple("Nat").axiom(type=TYPE)],
    )
    traced_env.tracer = StreamTracer(TokenWriter(trace, FORMAT_PLAIN))
    traced_env.def_eq(NAT, NAT)
    assert "def_eq" in trace.getvalue()


def test_trace_def_eq_records_whnf_of_each_side():
    """A def_eq trace nests the WHNF reduction of each side under it."""
    trace = BytesIO()
    from rpylean._tokens import TokenWriter, FORMAT_PLAIN

    # Use a beta-redex on one side and a bare constant on the other:
    # they're def-equal but not syntactically equal, so def_eq has to
    # actually WHNF rather than short-circuit on either pointer- or
    # syntactic-equality. Binder type is `Type` (= `Nat`'s sort) so
    # the redex itself type-checks: `(fun x : Type => x) Nat`.
    beta = fun(Name.simple("x").binder(type=TYPE))(W_BVar(0)).app(NAT)
    traced_env = Environment.having(
        [Name.simple("Nat").axiom(type=TYPE)],
    )
    traced_env.tracer = StreamTracer(TokenWriter(trace, FORMAT_PLAIN))
    traced_env.def_eq(beta, NAT)
    output = trace.getvalue().decode("utf-8")
    assert u"whnf" in output
    assert output.rstrip().endswith(u"✓")


def test_trace_def_eq_short_circuits_on_identity():
    """When both sides are the same instance, def_eq skips WHNF."""
    trace = BytesIO()
    from rpylean._tokens import TokenWriter, FORMAT_PLAIN

    traced_env = Environment.having(
        [Name.simple("Nat").axiom(type=TYPE)],
    )
    traced_env.tracer = StreamTracer(TokenWriter(trace, FORMAT_PLAIN))
    traced_env.def_eq(NAT, NAT)
    assert trace.getvalue().decode("utf-8") == u"def_eq Nat ≟ Nat ✓\n"


def test_trace_uses_check_and_cross_marks():
    """Successful comparisons use ✓ and failures use ✗."""
    trace = BytesIO()
    from rpylean._tokens import TokenWriter, FORMAT_PLAIN

    traced_env = Environment.having(
        [Name.simple("Nat").axiom(type=TYPE),
         Name.simple("String").axiom(type=TYPE)],
    )
    traced_env.tracer = StreamTracer(TokenWriter(trace, FORMAT_PLAIN))
    traced_env.def_eq(NAT, STRING)
    assert u"✗" in trace.getvalue().decode("utf-8")


def test_trace_nested_result_on_own_line():
    """A parent def_eq shows its result on its own line below children."""
    trace = BytesIO()
    from rpylean._tokens import TokenWriter, FORMAT_PLAIN

    # A forall whose binder type is a beta-redex def-equal but not
    # syntactically equal to its reduct on the other side. Forces
    # def_eq to recurse into the binder so the parent's ✓ lands on
    # its own line below the children.
    redex_nat = fun(Name.simple("x").binder(type=TYPE))(W_BVar(0)).app(NAT)
    pi_lhs = forall(Name.simple("x").binder(type=redex_nat))(NAT)
    pi_rhs = forall(Name.simple("x").binder(type=NAT))(NAT)
    traced_env = Environment.having([
        Name.simple("Nat").axiom(type=TYPE),
    ])
    traced_env.tracer = StreamTracer(TokenWriter(trace, FORMAT_PLAIN))
    traced_env.def_eq(pi_lhs, pi_rhs)
    output = trace.getvalue().decode("utf-8")
    lines = output.strip().split(u"\n")
    assert lines[-1] == u"✓"
