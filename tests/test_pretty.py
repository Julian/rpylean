"""
Pretty printing of Lean objects.
"""

from textwrap import dedent

import pytest

from rpylean._tokens import (
    DECL_NAME,
    FORMAT_PLAIN,
    KEYWORD,
    LEVEL,
    LITERAL,
    OPERATOR,
    PLAIN,
    PUNCT,
    SORT,
)
from rpylean.objects import (
    W_LEVEL_ZERO,
    NAT,
    NAT_ZERO,
    PROP,
    TYPE,
    Name,
    W_BVar,
    W_LevelSucc,
    W_LitNat,
    W_LitStr,
    forall,
    fun,
    name_with_levels,
    names,
)


u = Name.simple("u").level()
v = Name.simple("v").level()

a, f, x, y = names("a", "f", "x", "y")
b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)


class TestName(object):
    @pytest.mark.parametrize(
        "parts, expected",
        [
            (["foo"], "foo"),
            (["Lean", "Meta", "whnf"], "Lean.Meta.whnf"),
            (["Foo", "bar.baz"], "Foo.«bar.baz»"),
            (["_uniq", 231], "_uniq.231"),
            ([], "[anonymous]"),
            (["t'"], "t'"),
            (["foo bar"], "«foo bar»"),
            (["foo-bar"], "«foo-bar»"),
            (["foo@bar"], "«foo@bar»"),
            (["foo#bar"], "«foo#bar»"),
            (["foo bar", "baz"], "«foo bar».baz"),
        ],
        ids=[
            "simple",
            "multipart_hierarchical",
            "with_atomic_part",
            "with_number",
            "anonymous",
            "apostrophe",
            "with_space",
            "with_dash",
            "with_at",
            "with_hash",
            "multipart_with_space",
        ],
    )
    def test_str(self, parts, expected):
        name = Name(parts)
        assert FORMAT_PLAIN(name.tokens({})) == expected

    def test_tokens(self):
        assert Name.simple("foo").tokens({}) == [DECL_NAME.emit("foo")]


class TestNameWithLevels(object):
    def test_one_level(self):
        assert name_with_levels(x, [u]) == "x.{u}"

    def test_multiple_levels(self):
        assert name_with_levels(y, [u, v]) == "y.{u, v}"

    def test_no_levels(self):
        assert name_with_levels(a, []) == "a"


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
    ],
)
def test_sort(level, expected):
    assert FORMAT_PLAIN(level.sort().tokens({})) == expected


def test_sort_tokens():
    assert TYPE.tokens({}) == [SORT.emit("Type")]


class TestLet(object):
    def test_basic(self):
        let = a.let(type=NAT, value=NAT_ZERO, body=NAT_ZERO)
        assert FORMAT_PLAIN(let.tokens({})) == "let a : Nat := Nat.zero\nNat.zero"


Nat = Name.simple("Nat").axiom(type=TYPE)
i, h, p, q, P, alpha = names("i", "h", "p", "q", "P", "α")
constants = {
    Name.simple("Nat"): Nat,
    i: i.axiom(type=NAT),
    p: p.axiom(type=PROP),
    q: q.axiom(type=PROP),
    P: P.axiom(type=forall(P.binder(type=NAT))(PROP)),
    alpha: alpha.axiom(type=forall(Name.ANONYMOUS.binder(type=NAT))(TYPE)),
}


@pytest.mark.parametrize(
    "binder, body, expected",
    [
        (
            i.binder(type=NAT),
            NAT,
            "Nat → Nat",
        ),
        (
            i.implicit_binder(type=NAT),
            NAT,
            "{i : Nat} → Nat",
        ),
        (
            h.binder(type=p.const()),
            q.const(),
            "p → q",
        ),
        (
            i.binder(type=NAT),
            p.const(),
            "∀ (i : Nat), p",
        ),
        (
            i.implicit_binder(type=NAT),
            alpha.app(b0),
            "{i : Nat} → α i",
        ),
        (
            i.binder(type=NAT),
            alpha.app(b0),
            "(i : Nat) → α i",
        ),
        (
            i.implicit_binder(type=NAT),
            alpha.app(b0),
            "{i : Nat} → α i",
        ),
        (
            i.binder(type=NAT),
            P.app(b0),
            "∀ (i : Nat), P i",
        ),
        (
            i.implicit_binder(type=NAT),
            P.app(b0),
            "∀ {i : Nat}, P i",
        ),
        (
            i.implicit_binder(type=NAT),
            p.const(),
            "∀ {i : Nat}, p",
        ),
        (
            i.binder(type=forall(h.binder(type=NAT))(NAT)),
            NAT,
            "(Nat → Nat) → Nat",
        ),
        (
            Name(["x"]).binder(type=W_LEVEL_ZERO.sort()),
            W_LEVEL_ZERO.sort(),
            "Prop → Prop",
        ),
        (
            Name(["a", "_@", "_internal", "_hyg", "1"]).binder(type=PROP),
            PROP,
            "Prop → Prop",
        ),
        (
            p.binder(type=PROP),
            b0,
            "∀ (p : Prop), p",
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
        "(Nat → Nat) → Nat",
        "Prop_via_syntactic_eq",
        "hygienic",
        "∀ (p : Prop), p",
    ],
)
def test_forall(binder, body, expected):
    assert FORMAT_PLAIN(forall(binder)(body).tokens(constants=constants)) == expected


def test_forall_binder_type_reduces_to_prop():
    """
    Forall with binder type that reduces to Prop uses ∀ notation.

    When the binder type is an application like `id_prop Prop` (which reduces
    to Prop), the forall is printed with ∀ rather than →.
    """
    id_prop_name = Name.simple("id_prop")
    id_prop_decl = id_prop_name.definition(
        type=forall(p.binder(type=PROP))(PROP),
        value=fun(p.binder(type=PROP))(b0),
    )
    local_constants = {id_prop_name: id_prop_decl}
    # ∀ (p : id_prop Prop), p
    expr = forall(p.binder(type=id_prop_name.app(PROP)))(b0)
    assert FORMAT_PLAIN(expr.tokens(local_constants)) == "∀ (p : id_prop Prop), p"


def test_forall_binder_type_multi_arg_reduces_to_prop():
    """
    Forall with binder type that is a multi-arg application reducing to Prop uses ∀.

    When the binder type is `id Type Prop` (two explicit args, reduces to Prop),
    the forall is still printed with ∀ rather than →.
    """
    # id2 : (α : Type) → α → α  (simplified non-polymorphic id with two binders)
    id2_name = Name.simple("id2")
    id2_decl = id2_name.definition(
        type=forall(alpha.binder(type=TYPE), p.binder(type=b0))(b0),
        value=fun(alpha.binder(type=TYPE), p.binder(type=b0))(b0),
    )
    local_constants = {id2_name: id2_decl}
    # ∀ (p : id2 Type Prop), p  -- binder type = id2 applied to two args
    binder_type = id2_name.app(TYPE, PROP)
    expr = forall(p.binder(type=binder_type))(b0)
    assert FORMAT_PLAIN(expr.tokens(local_constants)) == "∀ (p : id2 Type Prop), p"


def test_forall_fvar_binder_type_prop():
    """
    Forall with a Prop-typed FVar binder uses → not ∀.

    `∀ (p : Prop), p → p` — the inner `p → p` must use → not ∀,
    because the binder type is `p` which is a Prop (not a type-level thing).
    """
    # ∀ (p : Prop), p → p
    # inner: forall(h : BVar(0))(BVar(1)) -- h : p, body is outer p
    expr = forall(p.binder(type=PROP))(forall(h.binder(type=b0))(b1))
    assert FORMAT_PLAIN(expr.tokens({})) == "∀ (p : Prop), p → p"


def test_forall_arrow_uses_operator_token():
    """Arrow in a function type is tagged as an operator, not punctuation."""
    # Type → Type
    expr = forall(x.binder(type=TYPE))(TYPE)
    tokens = expr.tokens({})
    arrows = [(tag, text) for tag, text in tokens if "→" in text]
    assert arrows == [OPERATOR.emit(" → ")]


def test_forall_prop_body_is_prop():
    """
    Forall whose body is itself a forall over a Prop-typed variable uses ∀.

    `∀ (p : id_prop Prop), p → p` — the outer forall must use ∀ notation
    because the body `p → p` is a Prop (a proposition).
    """
    id_prop_name = Name.simple("id_prop")
    id_prop_decl = id_prop_name.definition(
        type=forall(p.binder(type=PROP))(PROP),
        value=fun(p.binder(type=PROP))(b0),
    )
    local_constants = {id_prop_name: id_prop_decl}
    # ∀ (p : id_prop Prop), p → p
    # inner forall: (h : p) → p, i.e. forall(h : BVar(0))(BVar(1))
    inner = forall(h.binder(type=b0))(b1)
    expr = forall(p.binder(type=id_prop_name.app(PROP)))(inner)
    assert FORMAT_PLAIN(expr.tokens(local_constants)) == "∀ (p : id_prop Prop), p → p"


def test_forall_prop_body_with_universe_polymorphic_id():
    """
    Forall over a universe-polymorphic id application reducing to Prop uses ∀.

    Mirrors `forallSortWhnf` in Lean where the binder type is `id.{2} Type Prop`
    which delta-reduces to `Prop`. The outer forall must use ∀ notation, not →.
    """
    u_name = Name.simple("u")
    u_level = u_name.level()
    u_succ = W_LevelSucc(u_level)
    # id : {α : Sort u} → α → α  (with universe param u)
    id_name = Name.simple("id")
    sort_u = u_level.sort()
    id_type = forall(a.implicit_binder(type=sort_u))(forall(h.binder(type=b0))(b1))
    id_value = fun(a.implicit_binder(type=sort_u))(fun(h.binder(type=b0))(b0))
    id_decl = id_name.definition(type=id_type, value=id_value, levels=[u_name])
    local_constants = {id_name: id_decl}
    # id.{u+1} (Sort u) Prop  delta-reduces to Prop
    binder_type = id_name.const(levels=[u_succ]).app(sort_u, PROP)
    inner = forall(h.binder(type=b0))(b1)
    expr = forall(p.binder(type=binder_type))(inner)
    assert FORMAT_PLAIN(expr.tokens(local_constants)) == "∀ (p : id Prop), p → p"


class TestAppImplicitSuppression(object):
    def test_implicit_arg_suppressed(self):
        """
        Application suppresses implicit arguments.

        `id.{2} Type Prop` pretty-prints as `id Prop` because `Type` is the
        implicit `α` argument and is hidden by default.
        """
        id_name = Name.simple("id")
        u_name = Name.simple("u")
        sort_u = u_name.level().sort()
        id_type = forall(a.implicit_binder(type=sort_u))(forall(h.binder(type=b0))(b1))
        id_decl = id_name.definition(
            type=id_type,
            value=fun(a.implicit_binder(type=sort_u))(fun(h.binder(type=b0))(b0)),
            levels=[u_name],
        )
        level_2 = W_LevelSucc(W_LevelSucc(W_LEVEL_ZERO))
        expr = id_name.const(levels=[level_2]).app(TYPE, PROP)
        assert FORMAT_PLAIN(expr.tokens({id_name: id_decl})) == "id Prop"


class TestConst(object):
    def test_multiple_levels(self):
        foo = Name.simple("foo").const(levels=[u, v])
        assert FORMAT_PLAIN(foo.tokens({})) == "foo.{u, v}"

    def test_one_level(self):
        List = Name.simple("List").const(levels=[u])
        assert FORMAT_PLAIN(List.tokens({})) == "List.{u}"

    def test_no_levels(self):
        foo = Name.simple("foo").const()
        assert FORMAT_PLAIN(foo.tokens({})) == "foo"

    def test_level_zero(self):
        ofNat = Name.simple("ofNat").const(levels=[W_LEVEL_ZERO])
        assert FORMAT_PLAIN(ofNat.tokens({})) == "ofNat.{0}"

    def test_tokens(self):
        assert Name.simple("foo").const().tokens({}) == [DECL_NAME.emit("foo")]

    def test_tokens_with_levels(self):
        foo = Name.simple("foo").const(levels=[u, v])
        assert foo.tokens({}) == [
            DECL_NAME.emit("foo"),
            PUNCT.emit(".{"),
            LEVEL.emit("u"),
            PUNCT.emit(", "),
            LEVEL.emit("v"),
            PUNCT.emit("}"),
        ]

    def test_tokens_with_level_zero(self):
        ofNat = Name.simple("ofNat").const(levels=[W_LEVEL_ZERO])
        assert ofNat.tokens({}) == [
            DECL_NAME.emit("ofNat"),
            PUNCT.emit(".{"),
            LEVEL.emit("0"),
            PUNCT.emit("}"),
        ]


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
        assert FORMAT_PLAIN(Foo.tokens({})) == dedent(
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
        assert FORMAT_PLAIN(Foo.tokens({})) == dedent(
            """
            inductive Foo : Prop
            | bar
            """,
        ).strip("\n")

    def test_no_constructors(self):
        Empty = Name.simple("Empty").inductive(type=TYPE)
        assert FORMAT_PLAIN(Empty.tokens({})) == "inductive Empty : Type"


class TestConstructor(object):
    def test_no_params(self):
        True_ = Name.simple("True")
        intro = True_.child("intro").constructor(type=True_.const())
        assert FORMAT_PLAIN(intro.tokens({})) == "constructor True.intro : True"


class TestRecursor(object):
    def test_no_rules(self):
        Empty = Name.simple("Empty")
        t = Name.simple("t")
        motive = Name.simple("motive")
        rec = Empty.child("rec").recursor(
            type=forall(
                motive.binder(
                    type=forall(t.binder(type=Empty.const()))(u.sort()),
                ),
                t.binder(type=Empty.const()),
            )(b1.app(b0)),
            levels=[u.name],
        )

        assert FORMAT_PLAIN(
            rec.tokens({Name.simple("Empty"): Name.simple("Empty").axiom(type=TYPE)})
        ) == (
            "recursor Empty.rec.{u} : "
            "(motive : Empty → Sort u) → (t : Empty) → motive t"
        )


class TestTheorem(object):
    def test_delaborate(self):
        # FIXME: this theorem is not a Prop, but that's too annoying now
        theorem = Name.simple("foo").theorem(type=NAT, value=NAT_ZERO)
        assert FORMAT_PLAIN(theorem.tokens({})) == "theorem foo : Nat := Nat.zero"

    def test_assign_uses_operator_token(self):
        theorem = Name.simple("foo").theorem(type=NAT, value=NAT_ZERO)
        tokens = theorem.tokens({})
        assigns = [(tag, text) for tag, text in tokens if ":=" in text]
        assert assigns == [OPERATOR.emit(" := ")]


class TestAxiom(object):
    def test_delaborate(self):
        axiom = Name.simple("sorryAx").axiom(type=NAT)
        assert FORMAT_PLAIN(axiom.tokens({})) == "axiom sorryAx : Nat"

    def test_tokens(self):
        axiom = Name.simple("sorryAx").axiom(type=PROP)
        assert axiom.tokens({}) == [
            KEYWORD.emit("axiom"),
            PLAIN.emit(" "),
            DECL_NAME.emit("sorryAx"),
            PUNCT.emit(" : "),
            SORT.emit("Prop"),
        ]


class TestProj(object):
    Foo = Name.simple("Foo")
    mk = Foo.child("mk")
    ctor_type = forall(
        a.binder(type=NAT),
        x.binder(type=NAT),
        y.binder(type=NAT),
    )(Foo.const())
    mk_decl = mk.constructor(type=ctor_type)
    constants = {
        Foo: Foo.structure(type=TYPE, constructor=mk_decl),
        mk: mk_decl,
    }

    def test_fst(self):
        proj = self.Foo.proj(0, self.mk.app(NAT_ZERO, NAT_ZERO))
        assert (
            FORMAT_PLAIN(proj.tokens(self.constants)) == "(Foo.mk Nat.zero Nat.zero).a"
        )

    def test_third(self):
        proj = self.Foo.proj(2, self.mk.app(NAT_ZERO, NAT_ZERO, NAT_ZERO))
        assert (
            FORMAT_PLAIN(proj.tokens(self.constants))
            == "(Foo.mk Nat.zero Nat.zero Nat.zero).y"
        )

    def test_simple_const_no_parens(self):
        origin = Name.simple("origin").const()
        constants = dict(self.constants)
        constants[Name.simple("origin")] = Name.simple("origin").definition(
            type=self.Foo.const(),
            value=self.mk.app(NAT_ZERO, NAT_ZERO, NAT_ZERO),
        )
        proj = self.Foo.proj(0, origin)
        assert FORMAT_PLAIN(proj.tokens(constants)) == "origin.a"


def test_litnat():
    nat = W_LitNat.long(1000000000000000)
    assert nat.tokens({}) == [LITERAL.emit("1000000000000000")]


def test_litstr():
    hi = W_LitStr("hi")
    assert hi.tokens({}) == [LITERAL.emit('"hi"')]


@pytest.mark.parametrize(
    "input_str,expected",
    [
        ('with"quotes"', '"with\\"quotes\\""'),
        ("with\nnewlines", '"with\\nnewlines"'),
        ("with\ttabs", '"with\\ttabs"'),
    ],
    ids=[
        "escapes_quotes",
        "escapes_newlines",
        "escapes_tabs",
    ],
)
def test_litstr_escapes(input_str, expected):
    assert FORMAT_PLAIN(W_LitStr(input_str).tokens({})) == expected


class TestLambda(object):
    @pytest.mark.parametrize(
        "binder, expected",
        [
            (a.binder, "fun a ↦ Nat.zero"),
            (a.implicit_binder, "fun {a} ↦ Nat.zero"),
            (a.instance_binder, "fun [Nat] ↦ Nat.zero"),
            (a.strict_implicit_binder, "fun ⦃a⦄ ↦ Nat.zero"),
        ],
    )
    def test_simple(self, binder, expected):
        if "[Nat]" in expected:
            pytest.xfail(
                "Instance binder pretty-printing doesn't yet hide unused "
                "names when pretty printing.",
            )
        assert FORMAT_PLAIN(fun(binder(type=NAT))(NAT_ZERO).tokens({})) == expected

    def test_mapsto_uses_operator_token(self):
        lam = fun(x.binder(type=NAT))(NAT_ZERO)
        tokens = lam.tokens({})
        arrows = [(tag, text) for tag, text in tokens if "↦" in text]
        assert arrows == [OPERATOR.emit(" ↦ ")]

    def test_nested_default(self):
        nested = fun(
            x.binder(type=NAT),
            y.binder(type=NAT),
        )(f.app(b1, b0))
        assert FORMAT_PLAIN(nested.tokens({})) == "fun x y ↦ f x y"

    def test_nested_implicit(self):
        nested = fun(
            x.implicit_binder(type=NAT),
            y.implicit_binder(type=NAT),
        )(f.app(b1, b0))
        assert FORMAT_PLAIN(nested.tokens({})) == "fun {x y} ↦ f x y"

    def test_nested_instance(self):
        nested = fun(
            x.instance_binder(type=NAT),
            y.instance_binder(type=NAT),
        )(f.app(b1, b0))
        assert FORMAT_PLAIN(nested.tokens({})) == "fun [x : Nat] [y : Nat] ↦ f x y"

    def test_mixed_default_implicit(self):
        nested = fun(
            x.binder(type=NAT),
            y.implicit_binder(type=NAT),
        )(f.app(b1, b0))
        assert FORMAT_PLAIN(nested.tokens({})) == "fun x {y} ↦ f x y"

    def test_mixed_implicit_default(self):
        nested = fun(
            x.implicit_binder(type=NAT),
            y.binder(type=NAT),
        )(f.app(b1, b0))
        assert FORMAT_PLAIN(nested.tokens({})) == "fun {x} y ↦ f x y"

    def test_more_nested(self):
        nested = fun(
            x.binder(type=NAT),
            y.binder(type=NAT),
            a.binder(type=NAT),
        )(f.app(f.app(b2, b1), b0))
        assert FORMAT_PLAIN(nested.tokens({})) == "fun x y a ↦ f (f x y) a"

    def test_more_nested_mixed(self):
        nested = fun(
            x.binder(type=NAT),
            y.implicit_binder(type=NAT),
            a.instance_binder(type=NAT),
            f.binder(type=NAT),
        )(b0)
        pytest.xfail(
            "Instance binder pretty-printing doesn't yet hide unused "
            "names when pretty printing.",
        )
        assert FORMAT_PLAIN(nested.tokens({}, [])) == "fun x {y} [Nat] f ↦ f"

    def test_nested_non_lambda_body(self):
        let = y.let(type=NAT, value=NAT_ZERO, body=b0)
        nested = fun(x.binder(type=NAT))(let)
        assert FORMAT_PLAIN(nested.tokens({})) == "fun x ↦ let y : Nat := Nat.zero\ny"

    def test_definition(self):
        f = Name.simple("f").definition(
            type=forall(a.binder(type=NAT))(NAT),
            value=fun(a.binder(type=NAT))(b0),
        )
        assert FORMAT_PLAIN(f.tokens({Name.simple("Nat"): Nat})) == dedent(
            """\
            def f : Nat → Nat :=
              fun a ↦ a
            """,
        ).rstrip("\n")

    def test_let(self):
        f = Name.simple("f").definition(
            type=NAT,
            value=a.let(type=NAT, value=NAT_ZERO, body=NAT_ZERO),
        )
        assert FORMAT_PLAIN(f.tokens({})) == dedent(
            """\
            def f : Nat :=
              let a : Nat := Nat.zero
              Nat.zero
            """,
        ).rstrip("\n")

    def test_let_inside_lambda(self):
        f = Name.simple("f").definition(
            type=forall(a.binder(type=NAT))(NAT),
            value=fun(a.binder(type=NAT))(x.let(type=NAT, value=NAT_ZERO, body=b1)),
        )
        assert FORMAT_PLAIN(f.tokens({Name.simple("Nat"): Nat})) == dedent(
            """\
            def f : Nat → Nat :=
              fun a ↦ let x : Nat := Nat.zero
              a
            """,
        ).rstrip("\n")


class TestApp(object):
    def test_simple(self):
        app = f.app(a.const())
        assert FORMAT_PLAIN(app.tokens({})) == "f a"

    def test_nested_application_left_associative(self):
        app = f.app(a.const()).app(x.const())
        assert FORMAT_PLAIN(app.tokens({})) == "f a x"

    def test_application_with_parentheses_needed(self):
        g = Name.simple("g").const()
        outer = f.app(g.app(a.const()))
        assert FORMAT_PLAIN(outer.tokens({})) == "f (g a)"

    def test_lambda_app(self):
        id = fun(x.binder(type=NAT))(b0)
        app = id.app(a.const())
        assert FORMAT_PLAIN(app.tokens({})) == "(fun x ↦ x) a"

    def test_app_lambda(self):
        id = fun(x.binder(type=NAT))(b0)
        app = f.app(id)
        assert FORMAT_PLAIN(app.tokens({})) == "f fun x ↦ x"

    def test_lambda_lambda_app(self):
        fun_fn = fun(f.binder(type=NAT), x.binder(type=NAT))(b0)
        fun_arg = fun(y.binder(type=NAT))(b0)
        app = fun_fn.app(fun_arg, NAT_ZERO)
        assert FORMAT_PLAIN(app.tokens({})) == "(fun f x ↦ x) (fun y ↦ y) Nat.zero"

    def test_app_multiple_lambda(self):
        fun1 = fun(x.binder(type=NAT))(b0)
        fun2 = fun(y.binder(type=NAT))(b0)
        fun3 = fun(a.binder(type=NAT))(b0)
        app = f.app(fun1, fun2, fun3)
        assert FORMAT_PLAIN(app.tokens({})) == "f (fun x ↦ x) (fun y ↦ y) fun a ↦ a"

    def test_app_forall(self):
        arrow = forall(x.binder(type=NAT))(NAT)  # Nat → Nat
        app = f.app(arrow)
        assert FORMAT_PLAIN(app.tokens({Name.simple("Nat"): Nat})) == "f (Nat → Nat)"
