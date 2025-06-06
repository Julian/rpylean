"""
Tests from https://github.com/leanprover/lean4export/blob/master/Test.lean
"""

from rpython.rlib.rbigint import rbigint

from rpylean.environment import Environment
from rpylean.objects import (
    W_LEVEL_ZERO,
    Name,
    W_BVar,
    W_ForAll,
    W_Lambda,
    W_Let,
    W_LitNat,
    W_LitStr,
    W_Proj,
)


def from_source(source):
    # TODO: assert Environment.export() == source
    return Environment.from_lines(source.replace("⏎", "").splitlines())


def test_dump_name():
    assert from_source(
        #eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")
        """
        1 #NS 0 foo
        2 #NS 1 bla
        3 #NI 2 1
        4 #NS 3 boo
        """,
    ) == Environment(
        names=[
            Name.ANONYMOUS,
            Name(["foo"]),
            Name(["foo", "bla"]),
            Name(["foo", "bla", "1"]),
            Name(["foo", "bla", "1", "boo"]),
        ],
    )


def test_dump_level():
    l1 = Name.simple("l1")
    l2 = Name.simple("l2")
    assert from_source(
        #eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))
        """
        1 #US 0
        2 #US 1
        1 #NS 0 l1
        3 #UP 1
        4 #UM 2 3
        2 #NS 0 l2
        5 #UP 2
        6 #UIM 4 5
        """,
    ) == Environment(
        levels=[
            W_LEVEL_ZERO,
            W_LEVEL_ZERO.succ(),
            W_LEVEL_ZERO.succ().succ(),
            l1.level(),
            W_LEVEL_ZERO.succ().succ().max(l1.level()),
            Name.simple("l2").level(),
            W_LEVEL_ZERO.succ().succ().max(l1.level()).imax(l2.level()),
        ],
        names=[Name.ANONYMOUS, l1, l2],
    )


def test_dump_expr_lambda():
    bvar = W_BVar(0)
    fun = Name.simple("a").binder(type=bvar).fun(body=bvar)
    Type = W_LEVEL_ZERO.succ().sort()
    assert from_source(
        #eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)
        """
        1 #NS 0 A
        1 #US 0
        0 #ES 1
        2 #NS 0 a
        1 #EV 0
        2 #EL #BD 2 1 1
        3 #EL #BI 1 0 2
        """,
    ) == Environment(
        exprs=[
            W_LEVEL_ZERO.succ().sort(),
            bvar,
            fun,
            Name.simple("A").implicit_binder(type=Type).fun(body=fun),
        ],
        levels=[
            W_LEVEL_ZERO,
            W_LEVEL_ZERO.succ(),
        ],
        names=[Name.ANONYMOUS, Name.simple("A"), Name.simple("a")],
    )


def test_dump_expr_let():
    bvar = W_BVar(0)
    x = Name.simple("x")
    Nat = Name.simple("Nat")
    zero = Nat.child("zero")

    assert from_source(
        #eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)
        """
        1 #NS 0 x
        2 #NS 0 Nat
        0 #EC 2 ⏎
        3 #NS 2 zero
        1 #EC 3 ⏎
        2 #EV 0
        3 #EZ 1 0 1 2
        """,
    ) == Environment(
        exprs=[
            Nat.const(),
            zero.const(),
            bvar,
            W_Let(name=x, type=Nat.const(), value=zero.const(), body=bvar),
        ],
        names=[Name.ANONYMOUS, x, Nat, zero],
    )


def test_dump_expr_proj():
    bvar = W_BVar(0)
    Prod = Name.simple("Prod")
    assert from_source(
        #eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))
        """
        1 #NS 0 Prod
        0 #EV 0
        1 #EJ 1 1 0
        """,
    ) == Environment(
        exprs=[
            bvar,
            W_Proj(
                struct_name=Name.simple("Prod"),
                field_idx=1,
                struct_expr=bvar,
            ),
        ],
        names=[Name.ANONYMOUS, Prod],
    )


def test_dump_large_natlit():
    assert from_source(
        #eval run <| dumpExpr (.lit (.natVal 1000000000000000))
        """
        0 #ELN 1000000000000000
        """,
    ) == Environment(exprs=[W_LitNat(rbigint.fromlong(1000000000000000))])


def test_dump_litstr():
    assert from_source(
        #eval run <| dumpExpr (.lit (.strVal "hi"))
        """
        0 #ELS 68 69
        """,
    ) == Environment(exprs=[W_LitStr("hi")])
