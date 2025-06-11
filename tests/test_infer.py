"""
Type inference of Lean objects.
"""

from rpython.rlib.rbigint import rbigint

from rpylean.environment import Environment
from rpylean.objects import NAT, STRING, W_LEVEL_ZERO, Name, W_LitNat, W_LitStr


def infer(obj):
    """
    Out of laziness (or need to improve the API), type-infer in an empty env.
    """

    return obj.infer(Environment.having([]))


def test_fvar():
    Foo = Name.simple("foo").const()
    fvar = Name.simple("x").binder(type=Foo).fvar()
    assert infer(fvar) == Foo


class TestSort(object):
    def test_prop(self):
        Prop = W_LEVEL_ZERO.sort()
        assert infer(Prop) == W_LEVEL_ZERO.succ().sort()


def test_nat():
    lit = W_LitNat(rbigint.fromint(42))
    assert infer(lit) is NAT


def test_str():
    lit = W_LitStr("hello")
    assert infer(lit) is STRING
