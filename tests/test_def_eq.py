"""
Tests for definitional equality of Lean objects.
"""

import pytest

from rpylean.environment import Environment
from rpylean.objects import (
    W_LEVEL_ZERO,
    NAT,
    STRING,
    TYPE,
    Name,
    W_BVar,
    W_FVar,
    W_LitNat,
    W_LitStr,
    forall,
    fun,
    names,
)

env = Environment.EMPTY
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


class TestLitStr(object):
    def test_eq(self):
        assert env.def_eq(W_LitStr("foo"), W_LitStr("foo"))

    def test_not_eq(self):
        assert not env.def_eq(W_LitStr("foo"), W_LitStr("bar"))

    def test_eq_expanded(self):
        """
        "ok" = String.mk (List.nil.cons (Char.ofNat 107) |>.cons <| Char.ofNat 111)
        """
        alpha = Name.simple("α").binder(type=u.succ().sort())
        b0, b1, b2 = [W_BVar(i) for i in range(3)]

        head, tail = names("head", "tail")

        ListFn = Name.simple("List").const(levels=[u])
        nil_ctor = Name(["List", "nil"]).constructor(
            type=forall(alpha.to_implicit())(ListFn.app(b0)),
            levels=[u.name],
            num_params=1,
        )
        cons_ctor = Name(["List", "cons"]).constructor(
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

        Char, ofNat, String_mk = names("Char", "Char.ofNat", "String.mk")

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
        nil = Name(["List", "nil"]).const([W_LEVEL_ZERO])
        cons = Name(["List", "cons"]).const([W_LEVEL_ZERO])
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
                x.const(),
                x.const(levels=[u]),
                [x.axiom(type=TYPE, levels=[u.name])],
            ),
            (
                x.const(levels=[u]),
                x.const(),
                [x.axiom(type=TYPE, levels=[u.name])],
            ),
            (
                x.const(levels=[u, v]),
                x.const(levels=[v, u]),
                [x.axiom(type=TYPE, levels=[u.name, v.name])],
            ),
        ],
        ids=[
            "different_name",
            "missing_level",
            "extra_level",
            "different_level_order",
        ],
    )
    def test_not_eq(self, const1, const2, decls):
        env = Environment.having(decls)
        assert not env.def_eq(const1, const2)

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
        foo_type = Foo.inductive(type=TYPE)
        mk_decl = mk.constructor(type=Foo.const())
        bar = Name.simple("bar")
        x_decl = x.axiom(type=Foo.const())
        bar_def = bar.definition(type=Foo.const(), value=x.const())
        env = Environment.having([foo_type, mk_decl, x_decl, bar_def])
        proj1 = Foo.proj(0, x.const())
        proj2 = Foo.proj(0, bar.const())
        assert env.def_eq(proj1, proj2)

    def test_not_def_eq(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        foo_type = Foo.inductive(type=TYPE)
        mk_decl = mk.constructor(type=Foo.const())
        x_decl = x.axiom(type=Foo.const())
        y_decl = y.axiom(type=Foo.const())
        env = Environment.having([foo_type, mk_decl, x_decl, y_decl])
        proj1 = Foo.proj(0, x.const())
        proj2 = Foo.proj(0, y.const())
        assert not env.def_eq(proj1, proj2)


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
