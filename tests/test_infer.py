"""
Type inference of Lean objects.
"""

from rpython.rlib.rbigint import rbigint

import pytest

from rpylean.environment import Environment
from rpylean.exceptions import InvalidProjection
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
b0 = W_BVar(0)


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


class TestLet(object):
    def test_simple(self):
        env = Environment.having([Name.simple("Nat").inductive(type=TYPE)])

        zero = W_LitNat(rbigint.fromint(0))
        let = x.let(type=NAT, value=zero, body=b0)
        assert let.infer(env) == NAT

    def test_body(self):
        env = Environment.having([Name.simple("Nat").inductive(type=TYPE)])
        zero = W_LitNat(rbigint.fromint(0))
        let = x.let(type=NAT, value=zero, body=W_LitStr("hi"))
        assert let.infer(env) == STRING


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


class TestProj(object):
    def test_returns_field_type(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        mk_decl = mk.constructor(type=a.binder(type=NAT).forall(body=Foo.const()))
        Foo_decl = Foo.inductive(type=TYPE, constructors=[mk_decl])
        x_decl = x.axiom(type=Foo.const())
        env = Environment.having([Foo_decl, mk_decl, x_decl])
        proj = Foo.proj(0, mk.app(NAT))
        inferred = proj.infer(env)
        assert inferred == NAT

    def test_out_of_bounds_1(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        ctor_type = a.binder(type=NAT).forall(body=Foo.const())
        mk_decl = mk.constructor(type=ctor_type)
        Foo_decl = Foo.inductive(type=TYPE, constructors=[mk_decl])
        env = Environment.having([Foo_decl, mk_decl])
        proj = Foo.proj(1, mk.app(NAT))
        with pytest.raises(InvalidProjection) as e:
            proj.infer(env)

        assert str(e.value) == (
            "index 1 is not valid for Foo, which has only 1 field"
        )

    def test_out_of_bounds_0(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        mk_decl = mk.constructor(type=Foo.const())
        Foo_decl = Foo.inductive(type=TYPE, constructors=[mk_decl])
        env = Environment.having([Foo_decl, mk_decl])
        proj = Foo.proj(0, mk.const())
        with pytest.raises(InvalidProjection) as e:
            proj.infer(env)

        assert str(e.value) == (
            "index 0 is not valid for Foo, which has no fields"
        )

    def test_out_of_bounds_3(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        ctor_type = a.binder(type=NAT).forall(body=Foo.const())
        mk_decl = mk.constructor(type=ctor_type)
        Foo_decl = Foo.inductive(type=TYPE, constructors=[mk_decl])
        env = Environment.having([Foo_decl, mk_decl])
        proj = Foo.proj(3, mk.app(NAT))
        with pytest.raises(InvalidProjection) as e:
            proj.infer(env)

        assert str(e.value) == (
            "index 3 is not valid for Foo, which has only 2 fields"
        )
