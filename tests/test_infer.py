"""
Type inference of Lean objects.
"""

from rpython.rlib.rbigint import rbigint

from rpylean.environment import Environment
from rpylean.objects import (
    NAT,
    STRING,
    TYPE,
    W_LEVEL_ZERO,
    Name,
    W_LitNat,
    W_LitStr,
)


def test_fvar():
    Foo = Name.simple("foo").const()
    fvar = Name.simple("x").binder(type=Foo).fvar()
    assert fvar.infer(Environment.EMPTY) == Foo


class TestSort(object):
    def test_prop(self):
        Prop = W_LEVEL_ZERO.sort()
        assert Prop.infer(Environment.EMPTY) == TYPE


def test_nat():
    lit = W_LitNat(rbigint.fromint(42))
    assert lit.infer(Environment.EMPTY) is NAT


def test_str():
    lit = W_LitStr("hello")
    assert lit.infer(Environment.EMPTY) is STRING
