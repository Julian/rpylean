"""
Tests for definitional equality of Lean objects.
"""
import pytest

from rpython.rlib.rbigint import rbigint

from rpylean.environment import Environment
from rpylean.objects import (
    W_LEVEL_ZERO,
    NAT,
    Name,
    W_BVar,
    W_FVar,
    W_LitNat,
    names,
)

env = Environment.EMPTY
a, f, g, x, y = names("a", "f", "g", "x", "y")
b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)
u, v = Name.simple("u").level(), Name.simple("v").level()


class TestFVar:
    def test_eq(self):
        fvar = W_FVar(x.binder(type=NAT))
        assert env.def_eq(fvar, fvar)

    def test_not_eq(self):
        binder = x.binder(type=NAT)
        assert not env.def_eq(W_FVar(binder), W_FVar(binder))


class TestLitNat:
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


class TestSort:
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
        assert not env.def_eq(level1.sort(), level2.sort())
