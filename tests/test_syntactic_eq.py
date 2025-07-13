"""
Tests for syntactic equality of Lean objects.
"""

from rpylean.objects import (
    NAT,
    Name,
    W_BVar,
    forall,
    fun,
    names,
    syntactic_eq,
)


x, y = names("x", "y")
b0, b1 = W_BVar(0), W_BVar(1)


def test_same_bvar():
    assert syntactic_eq(b0, b0)


def test_different_bvar():
    assert not syntactic_eq(b0, b1)


def test_same_const():
    const1 = Name.simple("foo").const()
    const2 = Name.simple("foo").const()
    assert syntactic_eq(const1, const2)


def test_app_equal():
    app1 = NAT.app(b0)
    app2 = NAT.app(b0)
    assert syntactic_eq(app1, app2)


def test_app_different():
    app1 = NAT.app(b0)
    app2 = NAT.app(b1)
    assert not syntactic_eq(app1, app2)


def test_forall_vs_lambda_not_equal():
    forall_expr = forall(x.binder(type=NAT))(b0)
    lambda_expr = fun(x.binder(type=NAT))(b0)
    assert not syntactic_eq(forall_expr, lambda_expr)


def test_let_equal():
    let1 = x.let(type=NAT, value=NAT, body=b0)
    let2 = x.let(type=NAT, value=NAT, body=b0)
    assert syntactic_eq(let1, let2)


def test_let_different_name():
    let1 = x.let(type=NAT, value=NAT, body=b0)
    let2 = y.let(type=NAT, value=NAT, body=b0)
    assert not syntactic_eq(let1, let2)


def test_let_different_body():
    let1 = x.let(type=NAT, value=NAT, body=b0)
    let2 = x.let(type=NAT, value=NAT, body=b1)
    assert not syntactic_eq(let1, let2)


def test_different_types():
    assert not syntactic_eq(b0, NAT)
