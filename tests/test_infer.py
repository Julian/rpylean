"""
Type inference of Lean objects.
"""

from rpylean.environment import Environment
from rpylean.objects import NAT_CONST, Name


def test_fvar():
    fvar = Name.simple("x").binder(type=NAT_CONST).fvar()
    assert fvar.infer(Environment.having([])) == NAT_CONST
