"""
Pretty printing of Lean objects.
"""
from textwrap import dedent

from rpython.rlib.rbigint import rbigint
import pytest

from rpylean.objects import W_LEVEL_ZERO, Name, W_BVar, W_LitNat, W_LitStr


@pytest.mark.parametrize(
    "parts, expected",
    [
        (["foo"], "foo"),
        (["Lean", "Meta", "whnf"], "Lean.Meta.whnf"),
        (["Foo", "bar.baz"], "Foo.«bar.baz»"),
        (["_uniq", 231], "_uniq.231"),
        ([], "[anonymous]"),
    ],
    ids=[
        "simple",
        "multipart_hierarchical",
        "with_atomic_part",
        "with_number",
        "anonymous",
    ]
)
def test_name(parts, expected):
    assert Name(parts).pretty() == expected


u = Name.simple("u").level()
v = Name.simple("v").level()


@pytest.mark.parametrize(
    "level, expected",
    [
        (W_LEVEL_ZERO, "Prop"),
        (W_LEVEL_ZERO.succ(), "Type"),
        (W_LEVEL_ZERO.succ().succ(), "Type 1"),
        (u, "Sort u"),
        (u.succ(), "Type u"),
        (u.succ().succ().succ(), "Type (u + 2)"),
        (W_LEVEL_ZERO.succ().max(u), "Sort (max 1 u)"),
        (u.max(W_LEVEL_ZERO.succ()), "Sort (max u 1)"),
        (u.max(v), "Sort (max u v)"),
        (u.max(u), "Sort u"),
        (u.max(u.succ()), "Type u"),
        (u.succ().succ().max(u.succ()), "Type (u + 1)"),
        (u.succ().max(u), "Type u"),
        (u.succ().max(v.succ()), "Type (max u v)"),
        (u.succ().max(v), "Sort (max (u + 1) v)"),
        (u.imax(v), "Sort (imax u v)"),
        (u.imax(W_LEVEL_ZERO), "Prop"),
        (W_LEVEL_ZERO.succ().imax(u), "Sort u"),
    ],
    ids=[
        "prop",
        "type",
        "type1",
        "param_u",
        "param_u_succ",
        "param_u+3",
        "max_1_u",
        "max_u_1",
        "max_u_v",
        "max_u_u",
        "max_u_u+1",
        "max_u+1_u",
        "max_u+2_u+1",
        "max_u+1_v+1",
        "max_u+1_v",
        "imax",
        "imax_0",
        "imax_1_u",
    ]
)
def test_sort(level, expected):
    assert level.sort().pretty() == expected


def test_let():
    Nat = Name.simple("Nat")
    zero = Nat.child("zero")
    x = Name.simple("x")
    let = x.let(type=Nat.const(), value=zero.const(), body=W_BVar(0))
    assert let.pretty() == "let x : Nat := Nat.zero\n(BVar [0])"


def test_forall():
    x = Name.simple("x")
    forall = x.binder(type=Name.simple("Nat").const()).forall(
        Name.simple("P").const(),
    )
    assert forall.pretty() == "∀ (x : Nat), P"


class TestConst(object):
    def test_multiple_levels(self):
        foo = Name.simple("foo").const(levels=[u, v])
        assert foo.pretty() == "foo.{u, v}"

    def test_one_level(self):
        List = Name.simple("List").const(levels=[u])
        assert List.pretty() == "List.{u}"

    def test_no_levels(self):
        foo = Name.simple("foo").const()
        assert foo.pretty() == "foo"


class TestInductive(object):
    def test_multiple_constructors(self):
        name = Name.simple("Foo")
        Foo = name.inductive(
            type=W_LEVEL_ZERO.sort(),
            constructors=[
                name.child("bar").constructor(type=name.const()),
                name.child("baz").constructor(type=name.const()),
                # TODO: test constructors with params
            ],
        )
        assert Foo.pretty() == dedent(
            """
            inductive Foo : Prop
            | Foo.bar
            | Foo.baz
            """,
        ).strip("\n")

    def test_one_constructor(self):
        name = Name.simple("Foo")
        Foo = name.inductive(
            type=W_LEVEL_ZERO.sort(),
            constructors=[name.child("bar").constructor(type=name.const())],
        )
        assert Foo.pretty() == dedent(
            """
            inductive Foo : Prop
            | Foo.bar
            """,
        ).strip("\n")

    def test_no_constructors(self):
        Empty = Name.simple("Empty").inductive(type=W_LEVEL_ZERO.succ().sort())
        assert Empty.pretty() == "inductive Empty : Type"


class TestConstructor(object):
    def test_no_params(self):
        True_ = Name.simple("True")
        intro = True_.child("intro").constructor(type=True_.const())
        assert intro.pretty() == "constructor True.intro : True"


class TestRecursor(object):
    def test_no_rules(self):
        Empty = Name.simple("Empty")
        t = Name.simple("t")
        motive = Name.simple("motive")
        rec = Empty.child("rec").recursor(
            type=motive.binder(
                type=t.binder(type=Empty.const()).forall(body=u.sort()),
            ).forall(
                body=t.binder(type=Empty.const()).forall(
                    body=W_BVar(1).app(W_BVar(0))
                ),
            ),
            levels=[u],
        )

        assert rec.pretty() == (
            "recursor Empty.rec"
            # FIXME
            # .{u}
            " : "
            # "(motive : Empty → Sort u) → (t : Empty) → motive t"
            "∀ (motive : ∀ (t : Empty), Sort u), ∀ (t : Empty), "
            "{motive@1050} {t@1051}"
        )


def test_litnat():
    nat = W_LitNat(rbigint.fromlong(1000000000000000))
    assert nat.pretty() == "1000000000000000"


def test_litstr():
    hi = W_LitStr("hi")
    assert hi.pretty() == '"hi"'


def test_lambda_binder_default():
    Nat = Name.simple("Nat")
    zero = Nat.child("zero")

    fun = Name.simple("a").binder(type=Nat.const()).fun(body=zero.const())

    assert fun.pretty() == "fun (a : Nat) ↦ Nat.zero"
