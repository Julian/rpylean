"""
Pretty printing of Lean objects.
"""
from textwrap import dedent

from rpython.rlib.rbigint import rbigint
import pytest

from rpylean.environment import Environment
from rpylean.objects import (
    W_LEVEL_ZERO,
    NAT,
    NAT_ZERO,
    PROP,
    TYPE,
    Name,
    W_BVar,
    W_LitNat,
    W_LitStr,
    names,
)


u = Name.simple("u").level()
v = Name.simple("v").level()


class TestName(object):
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
    def test_no_levels(self, parts, expected):
        assert Name(parts).pretty() == expected

    def test_one_level(self):
        assert Name.simple("foo").pretty_with_levels([u]) == "foo.{u}"

    def test_multiple_levels(self):
        assert Name.simple("bar").pretty_with_levels([u, v]) == "bar.{u, v}"


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


# TODO: something like the `variable` command?
Nat = Name.simple("Nat").inductive(
    type=TYPE,
    constructors=[],  # FIXME: zero, succ obviously
)
print()
i, h, p, q, P, alpha = names("i", "h", "p", "q", "P", "α")
constants = {
    Name.simple("Nat"): Nat,
    i: Nat,
    p: PROP,
    q: PROP,
    P: P.binder(type=NAT).forall(body=PROP),
    alpha: Name.ANONYMOUS.binder(type=NAT).forall(body=TYPE),
}


@pytest.mark.parametrize(
    "forall, expected",
    [
        (
            i.binder(type=NAT).forall(body=NAT),
            "Nat → Nat",
        ),
        (
            i.implicit_binder(type=NAT).forall(body=NAT),
            "{i : Nat} → Nat",
        ),
        (
            h.binder(type=p.const()).forall(body=q.const()),
            "p → q",
        ),
        (
            i.binder(type=NAT).forall(body=p.const()),
            "∀ (i : Nat), p",
        ),
        (
            i.implicit_binder(type=NAT).forall(alpha.const().app(i.const())),
            "{i : Nat} → α i",
        ),
        (
            i.binder(type=NAT).forall(alpha.const().app(i.const())),
            "(i : Nat) → α i",
        ),
        (
            i.implicit_binder(type=NAT).forall(alpha.const().app(i.const())),
            "{i : Nat} → α i",
        ),
        (
            i.binder(type=NAT).forall(P.const().app(i.const())),
            "∀ (i : Nat), P i",
        ),
        (
            i.implicit_binder(type=NAT).forall(P.const().app(i.const())),
            "∀ {i : Nat}, P i",
        ),
        (
            i.implicit_binder(type=NAT).forall(p.const()),
            "∀ {i : Nat}, p",
        ),
    ],
    ids=[
        "(i : Nat) → Nat",
        "{i : Nat} → Nat",
        "(h : p) → q",
        "(i : Nat) → p",
        "{i : Nat} → α i",
        "(i : Nat) → α i",  # dependent type, so show the real binder
        "{i : Nat} → α i",
        "(i : Nat) → P i",
        "{i : Nat} → P i",
        "{i : Nat} → p",
    ],
)
def test_forall(forall, expected):
    if expected in {"(i : Nat) → α i", "∀ (i : Nat), P i", "∀ {i : Nat}, P i"}:
        pytest.xfail("Dependent forall pretty-printing is broken")
    assert forall.pretty(constants=constants) == expected


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
            type=PROP,
            constructors=[
                name.child("bar").constructor(type=name.const()),
                name.child("baz").constructor(type=name.const()),
                # TODO: test constructors with params
            ],
        )
        assert Foo.pretty() == dedent(
            """
            inductive Foo : Prop
            | bar
            | baz
            """,
        ).strip("\n")

    def test_one_constructor(self):
        name = Name.simple("Foo")
        Foo = name.inductive(
            type=PROP,
            constructors=[name.child("bar").constructor(type=name.const())],
        )
        assert Foo.pretty() == dedent(
            """
            inductive Foo : Prop
            | bar
            """,
        ).strip("\n")

    def test_no_constructors(self):
        Empty = Name.simple("Empty").inductive(type=TYPE)
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
            "recursor Empty.rec.{u} : "
            # FIXME "(motive : Empty → Sort u) → (t : Empty) → motive t"
            "Empty → Sort u → Empty → motive t"
        )


class TestTheorem(object):
    def test_delaborate(self):
        # FIXME: this theorem is not a Prop, but that's too annoying now
        theorem = Name.simple("foo").theorem(type=NAT, value=NAT_ZERO)
        assert theorem.pretty() == "theorem foo : Nat := Nat.zero"


class TestAxiom(object):
    def test_delaborate(self):
        axiom = Name.simple("sorryAx").axiom(type=NAT)
        assert axiom.pretty() == "axiom sorryAx : Nat"


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
