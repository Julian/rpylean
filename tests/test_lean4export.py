"""
Tests from https://github.com/leanprover/lean4export/blob/master/Test.lean
"""
import pytest

from rpylean.exceptions import UnknownQuotient
from rpylean.environment import EnvironmentBuilder, Environment, from_ndjson
from rpylean.objects import (
    W_LEVEL_ZERO,
    TYPE,
    Name,
    W_BVar,
    W_LitNat,
    W_LitStr,
    forall,
    fun,
)


def test_dump_name():
    assert from_ndjson(
        #eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")
        """
        {"i":1,"str":{"pre":0,"str":"foo"}}
        {"i":2,"str":{"pre":1,"str":"bla"}}
        {"i":3,"num":{"i":1,"pre":2}}
        {"i":4,"str":{"pre":3,"str":"boo"}}
        """,
    ) == EnvironmentBuilder(
        names=[
            Name(["foo"]),
            Name(["foo", "bla"]),
            Name(["foo", "bla", "1"]),
            Name(["foo", "bla", "1", "boo"]),
        ],
    )


def test_dump_level():
    l1 = Name.simple("l1")
    l2 = Name.simple("l2")
    assert from_ndjson(
        # eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))
        """
        {"i":1,"succ":0}
        {"i":2,"succ":1}
        {"i":1,"str":{"pre":0,"str":"l1"}}
        {"i":3,"param":1}
        {"i":4,"max":[2,3]}
        {"i":2,"str":{"pre":0,"str":"l2"}}
        {"i":5,"param":2}
        {"i":6,"imax":[4,5]}
        """,
    ) == EnvironmentBuilder(
        levels=[
            W_LEVEL_ZERO,
            W_LEVEL_ZERO.succ(),
            W_LEVEL_ZERO.succ().succ(),
            l1.level(),
            W_LEVEL_ZERO.succ().succ().max(l1.level()),
            Name.simple("l2").level(),
            W_LEVEL_ZERO.succ().succ().max(l1.level()).imax(l2.level()),
        ],
        names=[l1, l2],
    )


def test_dump_expr_lambda():
    bvar = W_BVar(0)
    f = fun(Name.simple("a").binder(type=bvar))(bvar)
    assert from_ndjson(
        #eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)
        """
        {"i":1,"str":{"pre":0,"str":"A"}}
        {"i":1,"succ":0}
        {"i":0,"sort":{"u":1}}
        {"i":2,"str":{"pre":0,"str":"a"}}
        {"bvar":{"deBruijnIndex":0},"i":1}
        {"i":2,"lam":{"binderInfo":"default","binderName":2,"binderType":1,"body":1}}
        {"i":3,"lam":{"binderInfo":"implicit","binderName":1,"binderType":0,"body":2}}
        """,
    ) == EnvironmentBuilder(
        exprs=[
            TYPE,
            bvar,
            f,
            fun(Name.simple("A").implicit_binder(type=TYPE))(f),
        ],
        levels=[
            W_LEVEL_ZERO,
            W_LEVEL_ZERO.succ(),
        ],
        names=[Name.simple("A"), Name.simple("a")],
    )


def test_dump_expr_let():
    bvar = W_BVar(0)
    x = Name.simple("x")
    Nat = Name.simple("Nat")
    zero = Nat.child("zero")

    assert from_ndjson(
        #eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)
        """
        {"i":1,"str":{"pre":0,"str":"x"}}
        {"i":2,"str":{"pre":0,"str":"Nat"}}
        {"const":{"declName":2,"us":[]},"i":0}
        {"i":3,"str":{"pre":2,"str":"zero"}}
        {"const":{"declName":3,"us":[]},"i":1}
        {"bvar":{"deBruijnIndex":0},"i":2}
        {"i":3,"letE":{"body":2,"declName":1,"nondep":false,"type":0,"value":1}}
        """,
    ) == EnvironmentBuilder(
        exprs=[
            Nat.const(),
            zero.const(),
            bvar,
            x.let(type=Nat.const(), value=zero.const(), body=bvar),
        ],
        names=[x, Nat, zero],
    )


def test_dump_expr_proj():
    bvar = W_BVar(0)
    Prod = Name.simple("Prod")
    assert from_ndjson(
        #eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))
        """
        {"i":1,"str":{"pre":0,"str":"Prod"}}
        {"bvar":{"deBruijnIndex":0},"i":0}
        {"i":1,"proj":{"idx":1,"struct":0,"typeName":1}}
        """,
    ) == EnvironmentBuilder(
        exprs=[
            bvar,
            Name.simple("Prod").proj(field_index=1, struct_expr=bvar),
        ],
        names=[Prod],
    )


def test_dump_large_natlit():
    assert from_ndjson(
        #eval run <| dumpExpr (.lit (.natVal 1000000000000000))
        """
        {"i":0,"natVal":"1000000000000000"}
        """,
    ) == EnvironmentBuilder(exprs=[W_LitNat.long(1000000000000000)])


def test_dump_natlit():
    assert from_ndjson(
        #eval run <| dumpExpr (.lit (.natVal 123456789))
        """
        {"i":0,"natVal":"123456789"}
        """,
    ) == EnvironmentBuilder(exprs=[W_LitNat.int(123456789)])


def test_dump_litstr():
    assert from_ndjson(
        #eval run <| dumpExpr (.lit (.strVal "hi"))
        """
        {"i":0,"strVal":"hi"}
        """,
    ) == EnvironmentBuilder(exprs=[W_LitStr("hi")])


def test_dump_litstr_escapes():
    assert from_ndjson(
        #eval run <| dumpExpr (.lit (.strVal "\r\rh
#       i\t\t"))
        """
        {"i":0,"strVal":"\r\rh\ni\u0009\u0009"}
        """,
    ) == EnvironmentBuilder(exprs=[W_LitStr("\r\rh\ni\u0009\u0009")])


def test_dump_litstr_unicode():
    assert from_ndjson(
        #eval run <| dumpExpr (.lit (.strVal "اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"))
        """
        {"i":0,"strVal":"اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"}
        """,
    ) == EnvironmentBuilder(
        exprs=[
            W_LitStr("اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"),
        ],
    )


def test_dump_constant_id():
    a, alpha = Name.simple("a"), Name.simple("α")
    u = Name.simple("u").level()
    b0 = W_BVar(0)
    b1 = W_BVar(1)

    id = Name.simple("id")
    id_type = forall(
        alpha.implicit_binder(type=u.sort()),
        a.binder(type=b0),
    )(b1)
    id_value = fun(
        alpha.implicit_binder(type=u.sort()),
        a.binder(type=b0),
    )(b0)

    assert from_ndjson(
        #eval run <| dumpConstant `id
        """
        {"i":1,"str":{"pre":0,"str":"id"}}
        {"i":2,"str":{"pre":0,"str":"u"}}
        {"i":1,"param":2}
        {"i":3,"str":{"pre":0,"str":"α"}}
        {"i":0,"sort":{"u":1}}
        {"i":4,"str":{"pre":0,"str":"a"}}
        {"bvar":{"deBruijnIndex":0},"i":1}
        {"bvar":{"deBruijnIndex":1},"i":2}
        {"forallE":{"binderInfo":"default","binderName":4,"binderType":1,"body":2},"i":3}
        {"forallE":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":3},"i":4}
        {"i":5,"lam":{"binderInfo":"default","binderName":4,"binderType":1,"body":1}}
        {"i":6,"lam":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":5}}
        {"defnInfo":{"all":[1],"hints":{"regular":1},"levelParams":[2],"name":1,"safety":"safe","type":4,"value":6}}
        """,
    ).finish() == Environment.having(
        [
            id.definition(
                type=id_type,
                value=id_value,
                levels=[Name.simple("u")],
            )
        ],
    )


def test_dump_constant_list():
    u = Name.simple("u").level()
    alpha = Name.simple("α").binder(type=u.succ().sort())
    b0, b1, b2 = [W_BVar(i) for i in range(3)]

    head = Name.simple("head")
    tail = Name.simple("tail")

    ListFn = Name.simple("List").const(levels=[u])
    nil = Name(["List", "nil"]).constructor(
        type=forall(alpha.to_implicit())(ListFn.app(b0)),
        levels=[Name.simple("u")],
        num_params=1,
    )
    cons = Name(["List", "cons"]).constructor(
        type=forall(
            alpha.to_implicit(),
            head.binder(type=b0),
            tail.binder(type=ListFn.app(b1)),
        )(ListFn.app(b2)),
        levels=[Name.simple("u")],
        num_params=1,
        num_fields=2,
    )
    List = Name.simple("List").inductive(
        type=forall(alpha)(u.succ().sort()),
        constructors=[nil, cons],
        levels=[Name.simple("u")],
        num_params=1,
        is_recursive=True,
    )
    assert from_ndjson(
        #eval run <| dumpConstant `List
        """
        {"i":1,"str":{"pre":0,"str":"List"}}
        {"i":2,"str":{"pre":0,"str":"u"}}
        {"i":1,"param":2}
        {"i":3,"str":{"pre":0,"str":"α"}}
        {"i":2,"succ":1}
        {"i":0,"sort":{"u":2}}
        {"forallE":{"binderInfo":"default","binderName":3,"binderType":0,"body":0},"i":1}
        {"i":4,"str":{"pre":1,"str":"nil"}}
        {"i":5,"str":{"pre":1,"str":"cons"}}
        {"inductInfo":{"all":[1],"ctors":[4,5],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[2],"name":1,"numIndices":0,"numNested":0,"numParams":1,"type":1}}
        {"const":{"declName":1,"us":[1]},"i":2}
        {"bvar":{"deBruijnIndex":0},"i":3}
        {"app":{"arg":3,"fn":2},"i":4}
        {"forallE":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":4},"i":5}
        {"ctorInfo":{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[2],"name":4,"numFields":0,"numParams":1,"type":5}}
        {"i":6,"str":{"pre":0,"str":"head"}}
        {"i":7,"str":{"pre":0,"str":"tail"}}
        {"bvar":{"deBruijnIndex":1},"i":6}
        {"app":{"arg":6,"fn":2},"i":7}
        {"bvar":{"deBruijnIndex":2},"i":8}
        {"app":{"arg":8,"fn":2},"i":9}
        {"forallE":{"binderInfo":"default","binderName":7,"binderType":7,"body":9},"i":10}
        {"forallE":{"binderInfo":"default","binderName":6,"binderType":3,"body":10},"i":11}
        {"forallE":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":11},"i":12}
        {"ctorInfo":{"cidx":1,"induct":1,"isUnsafe":false,"levelParams":[2],"name":5,"numFields":2,"numParams":1,"type":12}}
        """,
    ).finish() == Environment.having([List, nil, cons])


# ------------------------
# |  Extra tests we add  |
# ------------------------


def test_unknown_quotient():
    with pytest.raises(UnknownQuotient) as e:
        from_ndjson(
            """
            {"i":1,"str":{"pre":0,"str":"Quot"}}
            {"i":2,"str":{"pre":1,"str":"something"}}
            {"i":1,"succ":0}
            {"i":0,"sort":{"u":1}}
            {"quotInfo":{"kind":"type","levelParams":[],"name":2,"type":1}}
            """
        ).finish()

    assert e.value.str() == "Unknown quotient declaration: Quot.something"
