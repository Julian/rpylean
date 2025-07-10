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
    W_BVar,
    W_LitNat,
    W_LitStr,
    names,
)


Empty, T, true, a, f, x = names("Empty", "T", "True", "a", "f", "x")
EMPTY = Empty.inductive(type=TYPE)
u, v = Name.simple("u").level(), Name.simple("v").level()


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


class TestLambda(object):
    def test_simple(self):
        intro = true.child("intro").constructor(type=true.const())
        TRUE = true.inductive(type=TYPE, constructors=[intro])

        env = Environment.having([T.inductive(type=TYPE), TRUE, intro])
        X = x.binder(type=T.const())
        fun = X.fun(body=true.child("intro").const())
        assert fun.infer(env) == X.forall(body=true.const())

    def test_with_dependent_body(self):
        env = Environment.having([EMPTY])
        X = x.binder(type=Empty.const())
        fun = X.fun(body=W_BVar(0))
        assert fun.infer(env) == X.forall(body=Empty.const())


class TestConst(object):
    def test_level_param_substitution(self):
        decl = a.axiom(type=u.sort(), levels=[u.name])
        env = Environment.having([decl])
        assert decl.const(levels=[u]).infer(env) == u.sort()

    def test_level_max_substitution(self):
        uv = u.max(v).sort()
        decl = a.axiom(type=uv, levels=[u.name, v.name])
        env = Environment.having([decl])
        assert decl.const(levels=[u, v]).infer(env) == uv

    def test_level_imax_substitution(self):
        uv = u.imax(v).sort()
        decl = a.axiom(type=uv, levels=[u.name, v.name])
        env = Environment.having([decl])
        assert decl.const(levels=[u, v]).infer(env) == uv
