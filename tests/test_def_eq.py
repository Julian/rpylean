"""
Tests for definitional equality of Lean objects.
"""
import pytest

from rpython.rlib.rbigint import rbigint

from rpylean.environment import Environment
from rpylean.objects import (
    W_LEVEL_ZERO,
    NAT,
    TYPE,
    Name,
    W_BVar,
    W_FVar,
    W_LitNat,
    W_LitStr,
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
        assert env.def_eq(
            W_LitNat(rbigint.fromint(37)),
            W_LitNat(rbigint.fromint(37)),
        )

    def test_not_eq(self):
        assert not env.def_eq(
            W_LitNat(rbigint.fromint(37)),
            W_LitNat(rbigint.fromint(73)),
        )


class TestLitStr(object):
    def test_eq(self):
        assert env.def_eq(W_LitStr("foo"), W_LitStr("foo"))

    def test_not_eq(self):
        assert not env.def_eq(W_LitStr("foo"), W_LitStr("bar"))


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
        ]
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
        ]
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
                [x.axiom(type=TYPE, levels=[u])],
            ),
            (
                x.const(levels=[u, v]),
                x.const(levels=[u, v]),
                [x.axiom(type=TYPE, levels=[u, v])],
            ),
        ],
        ids=[
            "same",
            "with_level",
            "multiple_levels",
        ]
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
                [x.axiom(type=TYPE, levels=[u])],
            ),
            (
                x.const(levels=[u]),
                x.const(),
                [x.axiom(type=TYPE, levels=[u])],
            ),
            (
                x.const(levels=[u, v]),
                x.const(levels=[v, u]),
                [x.axiom(type=TYPE, levels=[u, v])],
            ),
        ],
        ids=[
            "different_name",
            "missing_level",
            "extra_level",
            "different_level_order",
        ]
    )
    def test_not_eq(self, const1, const2, decls):
        env = Environment.having(decls)
        assert not env.def_eq(const1, const2)

    def test_defeq_different_names_via_unfolding(self):
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
                x.binder(type=NAT).forall(body=NAT),
                x.binder(type=NAT).forall(body=NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                x.binder(type=NAT).forall(body=NAT),
                y.binder(type=NAT).forall(body=NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                x.binder(type=NAT).forall(body=b0),
                y.binder(type=NAT).forall(body=b0),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                x.binder(type=NAT).forall(
                    body=y.binder(type=NAT).forall(body=b0)
                ),
                a.binder(type=NAT).forall(
                    body=f.binder(type=NAT).forall(body=b0)
                ),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
        ],
        ids=[
            "same",
            "alpha_equivalent",
            "same_body_reference",
            "nested_same",
        ]
    )
    def test_eq(self, forall1, forall2, decls):
        env = Environment.having(decls)
        assert env.def_eq(forall1, forall2)

    @pytest.mark.parametrize(
        "forall1, forall2, decls",
        [
            (
                x.binder(type=NAT).forall(body=NAT),
                x.binder(type=TYPE).forall(body=NAT),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                x.binder(type=NAT).forall(body=NAT),
                x.binder(type=NAT).forall(body=TYPE),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
            (
                x.binder(type=NAT).forall(body=NAT),
                x.binder(type=NAT).forall(
                    body=y.binder(type=NAT).forall(body=NAT)
                ),
                [x.axiom(type=TYPE), Name.simple("Nat").axiom(type=TYPE)],
            ),
        ],
        ids=[
            "different_binder_types",
            "different_bodies",
            "different_structure",
        ]
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
                    f.axiom(type=x.binder(type=TYPE).forall(body=TYPE)),
                ],
            ),
            (
                f.app(x.const(), y.const()),
                f.app(x.const(), y.const()),
                [
                    x.axiom(type=TYPE),
                    y.axiom(type=TYPE),
                    f.axiom(type=x.binder(type=TYPE).forall(
                        body=y.binder(type=TYPE).forall(body=TYPE)
                    )),
                ],
            ),
            (
                f.const(levels=[u]).app(x.const()),
                f.const(levels=[u]).app(x.const()),
                [
                    x.axiom(type=TYPE),
                    f.axiom(
                        type=x.binder(type=TYPE).forall(body=TYPE),
                        levels=[u],
                    ),
                ],
            ),
        ],
        ids=[
            "simple",
            "nested_app",
            "with_levels",
        ]
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
                    f.axiom(type=x.binder(type=TYPE).forall(body=TYPE)),
                    g.axiom(type=x.binder(type=TYPE).forall(body=TYPE)),
                ],
            ),
            (
                f.app(x.const()),
                f.app(y.const()),
                [
                    x.axiom(type=TYPE),
                    y.axiom(type=TYPE),
                    f.axiom(type=x.binder(type=TYPE).forall(body=TYPE)),
                ],
            ),
            (
                f.app(x.const(), y.const()),
                f.app(y.const(), x.const()),
                [
                    x.axiom(type=TYPE),
                    y.axiom(type=TYPE),
                    f.axiom(type=x.binder(type=TYPE).forall(
                        body=y.binder(type=TYPE).forall(body=TYPE)
                    )),
                ],
            ),
        ],
        ids=[
            "different_function",
            "different_argument",
            "different_app_order",
        ]
    )
    def test_not_eq(self, app1, app2, decls):
        env = Environment.having(decls)
        assert not env.def_eq(app1, app2)
