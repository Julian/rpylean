from textwrap import dedent

import pytest

from rpylean._tokens import FORMAT_PLAIN, MESSAGE
from rpylean.environment import Environment
from rpylean.exceptions import AlreadyDeclared, DuplicateLevels, W_InvalidDeclaration
from rpylean.objects import (
    NAT,
    PROP,
    TYPE,
    Name,
    W_BVar,
    W_ConstructorFieldCountMismatch,
    W_InvalidConstructorResult,
    W_LevelParam,
    W_NonPositiveOccurrence,
    W_NotAProp,
    W_UniverseTooHigh,
    W_Sort,
    W_TypeError,
    forall,
    fun,
    names,
)


a, x, y, f, T = names("a", "x", "y", "f", "T")
b0, b1 = W_BVar(0), W_BVar(1)


def type_check(declarations=(), env=Environment.EMPTY):
    """
    Non-lazy type checking.
    """
    if not declarations:
        declarations = env.all()
    return list(env.type_check(declarations))


class TestTypeCheck(object):
    def test_valid_def(self):
        """
        Prop : Type
        """
        valid = Name.ANONYMOUS.definition(type=TYPE, value=PROP)
        assert type_check([valid]) == []

    def test_invalid_def(self):
        """
        Type is not a Prop.
        """

        invalid = Name.ANONYMOUS.definition(type=PROP, value=TYPE)

        error = invalid.type_check(Environment.EMPTY)
        assert error is not None

        assert error.expected_type == PROP

    def test_theorem_type_must_be_prop(self):
        """
        The type of a theorem must itself be a proposition (Sort 0).
        """
        non_prop_value = forall(x.binder(type=PROP))(W_BVar(0))
        invalid = Name.simple("nonPropThm").theorem(type=PROP, value=non_prop_value)

        error = invalid.type_check(Environment.EMPTY)

        assert isinstance(error, W_NotAProp)

    def test_definition_type_must_be_sort(self):
        """
        A definition's type must be a Sort (Type or Prop), not a function type.
        """
        constType = Name.simple("constType")
        constType_decl = constType.definition(
            type=forall(a.binder(type=TYPE))(TYPE),
            value=fun(x.binder(type=TYPE))(b0),
        )
        env = Environment.having([constType_decl])

        nonTypeType = Name.simple("nonTypeType").definition(
            type=constType.const(), value=PROP
        )

        error = nonTypeType.type_check(env)
        assert str(error) == dedent(
            """\
            def nonTypeType : constType :=
              Prop
            has type
              Type → Type
            but is expected to be a Sort (Type or Prop)""",
        )

    def test_axiom_type_must_be_sort(self):
        """
        An axiom's type must infer to a Sort.

        If its type is not a Sort, type checking should report an error.
        """
        constType = Name.simple("constType")
        constType_decl = constType.definition(
            type=forall(a.binder(type=TYPE))(TYPE),
            value=fun(x.binder(type=TYPE))(b0),
        )
        env = Environment.having([constType_decl])

        bad_axiom = Name.simple("badAxiom").axiom(type=constType.const())
        error = bad_axiom.type_check(env)
        assert error is not None
        assert error.as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            axiom badAxiom : constType
                             ^^^^^^^^^
                             has type
                               Type → Type
                             but is expected to be a Sort (Type or Prop)""",
        )

    def test_binder_type_with_non_sort_definition_raises(self):
        """
        A binder type must be a Sort (Type or Prop), not a function type.
        """
        constType_type = forall(a.binder(type=TYPE))(TYPE)
        constType_decl = Name.simple("constType").definition(
            type=constType_type,
            value=fun(a.binder(type=TYPE))(TYPE),
        )
        env = Environment.having([constType_decl])

        bad_forall = Name.simple("forallSortBad").definition(
            type=forall(x.binder(type=constType_decl.const()))(PROP),
            value=PROP,
        )

        error = bad_forall.type_check(env)
        assert error is not None


class TestApp(object):
    def test_apply_const_definition(self):
        # def T : Type := Nat → Nat
        fn_type = T.definition(
            type=TYPE,
            value=forall(Name.simple("_").binder(type=NAT))(NAT),
        )

        # def apply : T → Nat → Nat := fun f x ↦ f x
        apply = Name.simple("apply").definition(
            type=forall(f.binder(type=T.const()), x.binder(type=NAT))(NAT),
            value=fun(f.binder(type=T.const()), x.binder(type=NAT))(
                b1.app(b0),
            ),
        )

        env = Environment.having(
            [NAT.name.inductive(type=TYPE), fn_type, apply],
        )
        assert type_check(env=env) == []


class TestInductive(object):
    def test_with_param(self):
        alpha = Name.simple("α")
        a = Name.simple("a")
        Eq = Name.simple("Eq")
        refl = Eq.child("refl")

        body_type = forall(
            a.binder(type=W_BVar(0)),
        )(PROP)

        inductive_type = forall(alpha.binder(type=TYPE))(body_type)

        refl_body = forall(
            a.binder(type=W_BVar(0)),
        )(Eq.const().app(W_BVar(1)).app(W_BVar(0)).app(W_BVar(0)))

        refl_ctor_type = forall(alpha.binder(type=TYPE))(refl_body)

        refl_ctor = refl.constructor(
            type=refl_ctor_type, num_params=1, num_fields=1,
        )
        Eq_decl = Eq.inductive(
            type=inductive_type,
            constructors=[refl_ctor],
            num_params=1,
            num_indices=1,
        )

        env = Environment.having([Eq_decl, refl_ctor])
        assert type_check(env=env) == []


    def test_too_few_params(self):
        """Rejects an inductive claiming more params than its type has binders."""
        Foo = Name.simple("Foo")
        decl = Foo.inductive(
            type=forall(Name.simple("x").binder(type=PROP))(PROP),
            num_params=2,
        )
        env = Environment.having([decl])
        assert type_check(env=env) != []

    def test_non_sort_result(self):
        """Rejects an inductive whose result type is not a Sort."""
        aType = Name.simple("aType").axiom(type=TYPE)
        Foo = Name.simple("Foo")
        decl = Foo.inductive(type=aType.const())
        env = Environment.having([decl, aType])
        assert type_check(env=env) != []


class TestTypeError(object):
    def test_with_name(self):
        invalid = Name.simple("foo").definition(type=PROP, value=TYPE)

        error = invalid.type_check(Environment.EMPTY)
        assert str(error) == (
            "def foo : Prop :=\n"
            "  Type\n"
            "has type\n"
            "  Type 1\n"
            "but is expected to have type\n"
            "  Prop"
        )

    def test_anonymous(self):
        invalid = Name.ANONYMOUS.definition(type=PROP, value=TYPE)

        error = invalid.type_check(Environment.EMPTY)
        assert str(error) == (
            "def [anonymous] : Prop :=\n"
            "  Type\n"
            "has type\n"
            "  Type 1\n"
            "but is expected to have type\n"
            "  Prop"
        )

    def test_constructor_too_few_param_binders(self):
        """Rejects a constructor claiming more params than its type has binders."""
        ind_name = Name.simple("Ind")
        ind_type = forall(x.binder(type=PROP))(TYPE)

        # mk : Ind   (no binders, but claims 1 param)
        ctor = ind_name.child("mk").constructor(
            type=ind_name.const(),
            num_params=1,
            num_fields=0,
        )
        ind = ind_name.inductive(
            type=ind_type, constructors=[ctor], num_params=1,
        )
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_result_head_not_const(self):
        """Rejects a constructor whose result type head is not a constant."""
        ind_name = Name.simple("Ind")
        ind_type = forall(x.binder(type=PROP))(TYPE)

        # mk : (x : Prop) → x   (result head is a variable, not Ind)
        ctor_type = forall(x.binder(type=PROP))(W_BVar(0))
        ctor = ind_name.child("mk").constructor(
            type=ctor_type,
            num_params=1,
            num_fields=0,
        )
        ind = ind_name.inductive(
            type=ind_type, constructors=[ctor], num_params=1,
        )
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_result_head_wrong_inductive(self):
        """Rejects a constructor whose result type names a different inductive."""
        ind_name = Name.simple("Ind")
        other_name = Name.simple("Other")
        ind_type = forall(x.binder(type=PROP))(TYPE)

        # mk : (x : Prop) → Other x   (wrong inductive name)
        ctor_type = forall(x.binder(type=PROP))(
            other_name.const().app(W_BVar(0)),
        )
        ctor = ind_name.child("mk").constructor(
            type=ctor_type,
            num_params=1,
            num_fields=0,
        )
        other = other_name.inductive(type=ind_type, num_params=1)
        ind = ind_name.inductive(
            type=ind_type, constructors=[ctor], num_params=1,
        )
        env = Environment.having([other, ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_result_too_few_args(self):
        """Rejects a constructor whose result type applies too few arguments."""
        ind_name = Name.simple("Ind")
        ind_type = forall(x.binder(type=PROP))(TYPE)

        # mk : (x : Prop) → Ind   (missing the param argument)
        ctor_type = forall(x.binder(type=PROP))(ind_name.const())
        ctor = ind_name.child("mk").constructor(
            type=ctor_type,
            num_params=1,
            num_fields=0,
        )
        ind = ind_name.inductive(
            type=ind_type, constructors=[ctor], num_params=1,
        )
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_params_must_match_inductive_params(self):
        """Constructor result must apply the inductive to its parameter variables."""
        aProp = Name.simple("aProp").axiom(type=PROP)
        aProp_const = aProp.const()

        ind_name = Name.simple("Ind")
        # Ind : Prop → Type
        ind_type = forall(x.binder(type=PROP))(TYPE)

        # mk : (x : Prop) → Ind aProp   (wrong: should be Ind x)
        ctor_type = forall(x.binder(type=PROP))(
            ind_name.const().app(aProp_const),
        )
        ctor = ind_name.child("mk").constructor(
            type=ctor_type,
            num_params=1,
            num_fields=0,
        )

        ind = ind_name.inductive(
            type=ind_type,
            constructors=[ctor],
            num_params=1,
        )

        env = Environment.having([aProp, ctor, ind])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert isinstance(errors[0], W_InvalidConstructorResult)
        assert errors[0].name == ind_name

    def test_constructor_result_wrong_level_with_zero_params(self):
        """Rejects wrong universe levels even when the constructor has no term params."""
        u = Name.simple("u")
        v = Name.simple("v")
        ind_name = Name.simple("Foo")

        # Foo.{u} : Type (u+1)
        ind_type = W_Sort(u.level().succ())

        # mk.{u} : Foo.{v}   (wrong: should be Foo.{u})
        ctor = ind_name.child("mk").constructor(
            type=ind_name.const(levels=[v.level()]),
            num_params=0,
            num_fields=0,
            levels=[u],
        )
        ind = ind_name.inductive(
            type=ind_type,
            constructors=[ctor],
            num_params=0,
            levels=[u],
        )
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_result_level_params_must_match(self):
        """Rejects a constructor whose result type swaps the inductive's level params."""
        u1, u2 = Name.simple("u1"), Name.simple("u2")
        ind_name = Name.simple("Ind")

        # Ind.{u1, u2} : Sort u1 → Sort u2 → Type
        ind_type = forall(
            x.binder(type=W_Sort(u1.level())),
            y.binder(type=W_Sort(u2.level())),
        )(TYPE)

        # mk.{u1, u2} : (x : Sort u1) → (y : Sort u2) → Ind.{u2, u1} x y
        #   wrong: levels are swapped
        ctor_type = forall(
            x.binder(type=W_Sort(u1.level())),
            y.binder(type=W_Sort(u2.level())),
        )(ind_name.const(levels=[u2.level(), u1.level()])
            .app(W_BVar(1)).app(W_BVar(0)))

        ctor = ind_name.child("mk").constructor(
            type=ctor_type,
            num_params=2,
            num_fields=0,
            levels=[u1, u2],
        )
        ind = ind_name.inductive(
            type=ind_type,
            constructors=[ctor],
            num_params=2,
            levels=[u1, u2],
        )
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_inductive_in_own_index(self):
        """Rejects a constructor whose result type has the inductive in an index."""
        ind_name = Name.simple("Ind")
        aProp = Name.simple("aProp").axiom(type=PROP)

        # Ind : Prop → Prop
        ind_type = forall(x.binder(type=PROP))(PROP)

        # mk : Ind (Ind aProp)   (inductive in its own index)
        ctor = ind_name.child("mk").constructor(
            type=ind_name.const().app(ind_name.const().app(aProp.const())),
            num_params=0,
            num_fields=0,
        )
        ind = ind_name.inductive(
            type=ind_type,
            constructors=[ctor],
            num_params=0,
            num_indices=1,
        )
        env = Environment.having([aProp, ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_inductive_in_field_index(self):
        """Rejects a constructor whose field type has the inductive in an index."""
        ind_name = Name.simple("Ind")
        nat = Name.simple("Nat").inductive(type=TYPE)

        # Ind : Nat → Type (1 index)
        ind_type = forall(x.binder(type=NAT))(TYPE)

        # mk : (x : Nat) → Ind (Ind x)  (Ind in its own index)
        ctor_type = forall(
            x.binder(type=NAT),
        )(ind_name.const().app(ind_name.const().app(W_BVar(0))))

        ctor = ind_name.child("mk").constructor(
            type=ctor_type,
            num_params=0,
            num_fields=1,
        )
        ind = ind_name.inductive(
            type=ind_type,
            constructors=[ctor],
            num_params=0,
            num_indices=1,
        )
        env = Environment.having([nat, ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_InvalidConstructorResult)

    def test_constructor_non_positive_occurrence(self):
        """Rejects a constructor where the inductive occurs in a negative position."""
        ind_name = Name.simple("Ind")

        # Ind : Type
        # mk : (Ind → Ind) → Ind   (Ind in negative position)
        ctor = ind_name.child("mk").constructor(
            type=forall(f.binder(type=forall(x.binder(type=ind_name.const()))(ind_name.const())))(
                ind_name.const(),
            ),
            num_params=0,
            num_fields=1,
        )
        ind = ind_name.inductive(type=TYPE, constructors=[ctor])
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == (
            "inductive Ind : Type\n"
            "| mk : (Ind → Ind) → Ind\n"
            "        ^^^^^^^^^\n"
            "        arg #1 has a non-positive occurrence"
            " of the datatype being declared"
        )

    def test_constructor_non_positive_occurrence_behind_let(self):
        """Rejects a non-positive occurrence hidden behind a let expression."""
        ind_name = Name.simple("Ind")
        ind_const = ind_name.const()

        # The field type is: let T := Ind → Ind in T
        # which whnf-reduces to Ind → Ind (non-positive).
        arrow = forall(x.binder(type=ind_const))(ind_const)
        field_type = T.let(type=TYPE, value=arrow, body=b0)
        ctor = ind_name.child("mk").constructor(
            type=forall(f.binder(type=field_type))(ind_const),
            num_params=0,
            num_fields=1,
        )
        ind = ind_name.inductive(type=TYPE, constructors=[ctor])
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert isinstance(errors[0], W_NonPositiveOccurrence)

    def test_constructor_field_universe_too_high(self):
        """Rejects a constructor whose field lives in a universe above the inductive."""
        ind_name = Name.simple("Ind")

        # Ind : Type  (Sort 1)
        # mk : Type → Ind  (field Type has sort Sort 2, too high for Sort 1)
        ctor = ind_name.child("mk").constructor(
            type=forall(x.binder(type=TYPE))(ind_name.const()),
            num_params=0,
            num_fields=1,
        )
        ind = ind_name.inductive(type=TYPE, constructors=[ctor])
        env = Environment.having([ctor, ind])
        errors = type_check(env=env)
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == (
            "inductive Ind : Type\n"
            "| mk : Type → Ind\n"
            "       ^^^^^^^^^^\n"
            "       has field of type\n"
            "         Type\n"
            "       at universe level 2,"
            " but the inductive is at universe level 1"
        )

    def test_constructor_num_fields_mismatch(self):
        """Rejects a constructor whose num_fields doesn't match its type's binders."""
        nat = Name.simple("Nat").inductive(type=TYPE)
        ind_name = Name.simple("Ind")

        # Ind : Type
        # mk : Nat → Nat → Ind   (2 fields in the type)
        # but we declare num_fields=1 (wrong)
        ctor = ind_name.child("mk").constructor(
            type=forall(
                x.binder(type=NAT),
                y.binder(type=NAT),
            )(ind_name.const()),
            num_params=0,
            num_fields=1,
        )
        ind = ind_name.inductive(type=TYPE, constructors=[ctor])
        env = Environment.having([nat, ctor, ind])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert isinstance(errors[0], W_ConstructorFieldCountMismatch)
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == (
            "inductive Ind : Type\n"
            "| mk : Nat → Nat → Ind\n"
            "       ^^^^^^^^^^^^^^^\n"
            "       constructor declares 1 field but type has 2"
        )

    def test_constructor_num_fields_mismatch_with_params(self):
        """The diagnostic highlights the fields, not the params."""
        nat = Name.simple("Nat").inductive(type=TYPE)
        ind_name = Name.simple("Ind")

        # Ind : Type → Type   (1 param)
        ind_type = forall(x.binder(type=TYPE))(TYPE)

        # mk : (α : Type) → Nat → Nat → Ind α   (2 fields)
        # but we declare num_fields=3 (wrong)
        alpha = Name.simple("α")
        ctor = ind_name.child("mk").constructor(
            type=forall(
                alpha.binder(type=TYPE),
                x.binder(type=NAT),
                y.binder(type=NAT),
            )(ind_name.const().app(W_BVar(2))),
            num_params=1,
            num_fields=3,
        )
        ind = ind_name.inductive(
            type=ind_type, constructors=[ctor], num_params=1,
        )
        env = Environment.having([nat, ctor, ind])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert isinstance(errors[0], W_ConstructorFieldCountMismatch)
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == (
            "inductive Ind : Type → Type\n"
            "| mk : (α : Type) → Nat → Nat → Ind α\n"
            "       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
            "       constructor declares 3 fields but type has 2"
        )

    def test_prop_inductive_allows_type_field(self):
        """Prop inductives are exempt from the universe level check."""
        ind_name = Name.simple("Ind")

        # Ind : Prop
        # mk : Type → Ind  (field in Sort 2, but Prop is exempt)
        ctor = ind_name.child("mk").constructor(
            type=forall(x.binder(type=TYPE))(ind_name.const()),
            num_params=0,
            num_fields=1,
        )
        ind = ind_name.inductive(type=PROP, constructors=[ctor])
        env = Environment.having([ctor, ind])
        assert type_check(env=env) == []

    def test_inductive_type_must_be_sort(self):
        fnType = Name.simple("fnType").definition(
            type=forall(a.binder(type=TYPE))(TYPE),
            value=fun(x.binder(type=TYPE))(b0),
        )
        bad_inductive = Name.simple("BadInd").inductive(type=fnType.const())

        env = Environment.having([fnType, bad_inductive])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert str(errors[0]) == (
            "inductive BadInd : fnType\n"
            "has type\n"
            "  Type → Type\n"
            "but is expected to be a Sort (Type or Prop)"
        )


class TestDiagnosticTokens(object):
    def test_type_error_diagnostic(self):
        invalid = Name.simple("foo").definition(type=PROP, value=TYPE)
        error = invalid.type_check(Environment.EMPTY)

        assert error.as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def foo : Prop :=
              Type
              ^^^^
              has type
                Type 1
              but is expected to have type
                Prop""",
        )

    def test_not_a_sort_diagnostic(self):
        constType = Name.simple("constType").definition(
            type=forall(a.binder(type=TYPE))(TYPE),
            value=fun(x.binder(type=TYPE))(b0),
        )
        env = Environment.having([constType])
        nonTypeType = Name.simple("nonTypeType").definition(
            type=constType.const(), value=PROP
        )
        error = nonTypeType.type_check(env)

        assert error.as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def nonTypeType : constType :=
                              ^^^^^^^^^
                              has type
                                Type → Type
                              but is expected to be a Sort (Type or Prop)""",
        )

    def test_raised_not_a_sort_diagnostic(self):
        """W_NotASort raised during inference still gets carets."""
        bad = Name.simple("bad").definition(
            type=PROP,
            value=forall(x.binder(type=PROP))(
                forall(y.binder(type=b0))(forall(a.binder(type=b0))(b1)),
            ),
        )
        error = bad.type_check(Environment.EMPTY)

        assert error.as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : Prop :=
              ∀ (x : Prop), ∀ (y : x), y → y
                                   ^
                                   has type
                                     x
                                   but is expected to be a Sort (Type or Prop)""",
        )

    def test_not_a_prop_diagnostic(self):
        non_prop_value = forall(x.binder(type=PROP))(W_BVar(0))
        invalid = Name.simple("nonPropThm").theorem(type=PROP, value=non_prop_value)
        error = invalid.type_check(Environment.EMPTY)

        assert error.as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            theorem nonPropThm : Prop := ∀ (x : Prop), x
                                 ^^^^
                                 has sort
                                   Type
                                 but the type of a theorem must be a proposition (Prop)""",
        )


    def test_type_error_message_prose_uses_message_token(self):
        invalid = Name.simple("foo").definition(type=PROP, value=TYPE)
        error = invalid.type_check(Environment.EMPTY)
        message = error.as_diagnostic().message
        prose = [(tag, text) for tag, text in message if "has type" in text]
        assert prose == [MESSAGE.emit("\nhas type\n  ")]


class TestInvalidDeclaration(object):
    def test_not_a_structure_diagnostic(self):
        N = Name.simple("N")
        zero = N.child("zero")
        succ = N.child("succ")
        zero_decl = zero.constructor(type=N.const())
        succ_decl = succ.constructor(
            type=forall(a.binder(type=N.const()))(N.const()),
            num_fields=1,
        )
        N_decl = N.inductive(type=TYPE, constructors=[zero_decl, succ_decl])
        bad = Name.simple("bad").definition(
            type=N.const(),
            value=fun(x.binder(type=N.const()))(N.proj(0, b0)),
        )
        env = Environment.having([N_decl, zero_decl, succ_decl, bad])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : N :=
              fun x ↦ x.0
                      ^^^
                      N is not a structure (it has 2 constructors)""",
        )

    def test_invalid_projection_out_of_bounds_diagnostic(self):
        Foo = Name.simple("Foo")
        mk = Foo.child("mk")
        ctor_type = forall(a.binder(type=PROP))(Foo.const())
        mk_decl = mk.constructor(type=ctor_type, num_fields=1)
        Foo_decl = Foo.inductive(type=TYPE, constructors=[mk_decl])
        bad = Name.simple("bad").definition(
            type=PROP,
            value=Foo.proj(3, mk.app(PROP)),
        )
        env = Environment.having([Foo_decl, mk_decl, bad])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : Prop :=
              (Foo.mk Prop).3
              ^^^^^^^^^^^^^^^
              Foo has only 2 fields""",
        )

    def test_nested_lambda_projection_marks_value(self):
        """Projection inside nested lambdas marks the whole value."""
        z = Name.simple("z")
        And = Name.simple("And")
        intro = And.child("intro")
        intro_decl = intro.constructor(
            type=forall(
                a.binder(type=PROP), x.binder(type=PROP),
                Name.simple("left").binder(type=b1),
                Name.simple("right").binder(type=b1),
            )(And.app(W_BVar(3), W_BVar(2))),
            num_params=2,
            num_fields=2,
        )
        And_decl = And.inductive(
            type=forall(a.binder(type=PROP), x.binder(type=PROP))(PROP),
            constructors=[intro_decl],
            num_params=2,
        )
        # z's binder type refers to both outer binders, so instantiation
        # copies the inner lambda and its binder, breaking fvar identity.
        bad = Name.simple("bad").definition(
            type=PROP,
            value=fun(
                a.binder(type=PROP),
                x.binder(type=PROP),
                z.binder(type=And.app(b1, b0)),
            )(And.proj(2, b0)),
        )
        env = Environment.having([And_decl, intro_decl, bad])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : Prop :=
              fun a x z ↦ z.left
              ^^^^^^^^^^^^^^^^^^
              invalid projection And.2: And has only 2 fields""",
        )

    def test_unknown_structure_diagnostic(self):
        Foo = Name.simple("Foo")
        Bar = Name.simple("Bar")
        bar_decl = Bar.axiom(type=TYPE)
        bad = Name.simple("bad").definition(
            type=PROP,
            value=Foo.proj(0, bar_decl.const()),
        )
        env = Environment.having([bar_decl, bad])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : Prop :=
              Bar.0
              ^^^^^
              unknown structure Foo""",
        )


def test_pp():
    good = Name.simple("GoodDef").definition(type=TYPE, value=PROP)
    env = Environment.having([good])

    printed = []

    def pp(env, decl):
        printed.append((env, decl))

    list(env.type_check(env.all(), pp=pp))
    assert printed == [(env, good)]


class TestHeartbeat(object):
    def test_heartbeat_resets_per_declaration(self):
        """Heartbeat counter resets before each declaration."""
        a = Name.simple("A").definition(type=TYPE, value=PROP)
        b = Name.simple("B").definition(type=TYPE, value=PROP)
        env = Environment.having([a, b])
        env.max_heartbeat = 100000

        assert type_check(env=env) == []

    def test_heartbeat_exceeded_is_an_error(self):
        """Exceeding the heartbeat limit raises HeartbeatExceeded."""
        from rpylean.exceptions import HeartbeatExceeded

        env = Environment.having([])
        env.max_heartbeat = 3
        env._current_decl = Name.simple("Test").definition(type=TYPE, value=PROP)

        # First 3 calls succeed
        env.def_eq(PROP, PROP)
        env.def_eq(PROP, PROP)
        env.def_eq(PROP, PROP)
        assert env.heartbeat == 3

        with pytest.raises(HeartbeatExceeded) as exc_info:
            env.def_eq(PROP, PROP)
        error_str = str(exc_info.value)
        assert "in Test" in error_str
        assert "heartbeat limit exceeded" in error_str

    def test_check_one_resets_heartbeat(self):
        """_check_one resets the heartbeat counter before each declaration."""
        decl = Name.simple("OK").definition(type=TYPE, value=PROP)
        env = Environment.having([decl])
        env.max_heartbeat = 100
        env.heartbeat = 99  # would overflow on next def_eq

        assert type_check(env=env) == []

    def test_heartbeat_zero_means_unlimited(self):
        """A max_heartbeat of 0 (default) means no limit."""
        good = Name.simple("Good").definition(type=TYPE, value=PROP)
        env = Environment.having([good])
        assert env.max_heartbeat == 0

        assert type_check(env=env) == []


class TestDefEqCache(object):
    def test_cache_returns_same_result(self):
        """Repeated def_eq with the same objects returns the cached result."""
        env = Environment.having([])

        # First call computes the result
        assert env.def_eq(PROP, PROP) is True

        # Second call should hit the cache
        assert env.def_eq(PROP, PROP) is True

    def test_cache_cleared_per_declaration(self):
        """The cache is cleared before checking each declaration."""
        a = Name.simple("A").definition(type=TYPE, value=PROP)
        b = Name.simple("B").definition(type=TYPE, value=PROP)
        env = Environment.having([a, b])

        assert list(env.type_check(env.all())) == []


class TestNotRPython:
    """
    Environment behavior which isn't RPython, it's just for dev convenience.

    May as well check it works though.
    """

    def test_getitem_simple(self):
        Foo = Name.simple("Foo").definition(type=TYPE, value=PROP)
        env = Environment.having([Foo])
        assert env["Foo"] is Foo

    def test_getitem_multipart(self):
        bar = Name(["Foo", "bar"]).definition(type=TYPE, value=PROP)
        env = Environment.having([bar])
        assert env["Foo.bar"] is bar

    def test_getitem_name(self):
        Foobar = Name(["Foo.bar"])
        decl = Foobar.definition(type=TYPE, value=PROP)
        env = Environment.having([decl])
        assert env[Foobar] is decl

    def test_getitem_no_such_declaration(self):
        with pytest.raises(KeyError):
            Environment.EMPTY["DoesNotExist"]


class TestAlreadyDeclared(object):
    def test_message_includes_existing_declaration(self):
        ax = Name.simple("ax").axiom(type=PROP)
        with pytest.raises(AlreadyDeclared) as exc_info:
            Environment.having([ax, ax])
        assert str(exc_info.value) == (
            "Invalid declaration ax: already declared as axiom ax : Prop"
        )


class TestDuplicateLevels(object):
    def test_message_shows_level_params(self):
        u = Name.simple("u")
        ax = Name.simple("ax").axiom(type=PROP, levels=[u, u])
        with pytest.raises(DuplicateLevels) as exc_info:
            Environment.having([ax])
        assert str(exc_info.value) == (
            "Invalid declaration ax.{u, u}: duplicate level parameter u"
        )
