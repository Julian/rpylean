"""
Type inference of Lean objects.
"""

from rpylean.environment import Environment
from rpylean.objects import NAT, Name


def test_fvar():
    fvar = Name.simple("x").binder(type=NAT).fvar()
    assert fvar.infer(Environment.having([])) == NAT
