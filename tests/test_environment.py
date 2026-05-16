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
    W_LEVEL_ZERO,
    W_LevelParam,
    W_LitNat,
    W_NonPositiveOccurrence,
    W_NotAFunction,
    W_NotAProp,
    W_RecRule,
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


class TestRecursorRuleShape(object):
    """`W_Recursor.type_check`'s shape-level validation: rule count,
    ctor membership, and `num_fields` consistency."""

    def _build_unit_ind(self):
        """A trivial 1-ctor inductive `U` with `U.mk : U`."""
        U = Name.simple("U")
        mk = U.child("mk").constructor(
            type=U.const(), num_params=0, num_fields=0,
        )
        ind = U.inductive(type=TYPE, constructors=[mk])
        return U, mk, ind

    def test_rule_count_mismatch_rejected(self):
        from rpylean.objects import W_RecRule, W_InvalidRecursorRule
        U, mk, ind = self._build_unit_ind()
        # Recursor with zero rules but inductive has one ctor.
        bad_rec = U.child("rec").recursor(type=U.const(), rules=[], all=[U])
        env = Environment.having([ind, mk, bad_rec])
        errors = list(env.type_check([bad_rec]))
        assert len(errors) == 1
        assert isinstance(errors[0], W_InvalidRecursorRule)

    def test_rule_for_unknown_ctor_rejected(self):
        from rpylean.objects import W_RecRule, W_InvalidRecursorRule
        U, mk, ind = self._build_unit_ind()
        ghost = Name.of(["U", "ghost"])
        bad_rec = U.child("rec").recursor(
            type=U.const(),
            rules=[W_RecRule(ctor_name=ghost, num_fields=0, rhs=U.const())],
            all=[U],
        )
        env = Environment.having([ind, mk, bad_rec])
        errors = list(env.type_check([bad_rec]))
        assert len(errors) == 1
        assert isinstance(errors[0], W_InvalidRecursorRule)

    def test_rule_nfields_mismatch_rejected(self):
        from rpylean.objects import W_RecRule, W_InvalidRecursorRule
        U, mk, ind = self._build_unit_ind()
        # mk has 0 fields, but the rule claims 1.
        bad_rec = U.child("rec").recursor(
            type=U.const(),
            rules=[W_RecRule(ctor_name=mk.name, num_fields=1, rhs=U.const())],
            all=[U],
        )
        env = Environment.having([ind, mk, bad_rec])
        errors = list(env.type_check([bad_rec]))
        assert len(errors) == 1
        assert isinstance(errors[0], W_InvalidRecursorRule)

    def test_well_shaped_rule_accepted(self):
        from rpylean.objects import W_RecRule
        U, mk, ind = self._build_unit_ind()
        # Canonical rhs for the only ctor of a 1-ctor inductive with
        # num_params=0, num_motives=1, num_minors=1, num_fields=0:
        # `fun motive minor_mk => minor_mk` — bvar 0 inside two
        # lambdas. The binder types don't matter for the head check.
        motive_binder = Name.simple("motive").binder(type=TYPE)
        minor_binder = Name.simple("minor_mk").binder(type=U.const())
        good_rhs = fun(motive_binder, minor_binder)(b0)
        good_rec = U.child("rec").recursor(
            type=U.const(),
            num_motives=1,
            num_minors=1,
            rules=[W_RecRule(ctor_name=mk.name, num_fields=0, rhs=good_rhs)],
            all=[U],
        )
        env = Environment.having([ind, mk, good_rec])
        errors = list(env.type_check([good_rec]))
        assert errors == []

    def test_rhs_head_uses_wrong_minor_rejected(self):
        """The arena `nat-rec-rules` shape: rule has correct count/
        ctor/nfields but its body returns the wrong minor (Nat.succ's
        rule returns `zero_case` instead of `succ_case`)."""
        from rpylean.objects import W_RecRule, W_InvalidRecursorRule
        # Two-ctor inductive, recursor with num_minors=2.
        B = Name.simple("B")
        ff = B.child("false").constructor(
            type=B.const(), num_params=0, num_fields=0,
        )
        tt = B.child("true").constructor(
            type=B.const(), num_params=0, num_fields=0,
        )
        ind = B.inductive(type=PROP, constructors=[ff, tt])
        motive_binder = Name.simple("motive").binder(type=PROP)
        m_false = Name.simple("m_false").binder(type=B.const())
        m_true = Name.simple("m_true").binder(type=B.const())
        # The rule for `B.true` (ctor_idx=1) should return `m_true`
        # (bvar 0). Build it returning `m_false` (bvar 1) instead.
        bad_rhs = fun(motive_binder, m_false, m_true)(b1)
        good_false_rhs = fun(motive_binder, m_false, m_true)(b1)
        bad_rec = B.child("rec").recursor(
            type=B.const(),
            num_motives=1,
            num_minors=2,
            rules=[
                W_RecRule(ctor_name=ff.name, num_fields=0,
                          rhs=good_false_rhs),
                W_RecRule(ctor_name=tt.name, num_fields=0, rhs=bad_rhs),
            ],
            all=[B],
        )
        env = Environment.having([ind, ff, tt, bad_rec])
        errors = list(env.type_check([bad_rec]))
        assert len(errors) == 1
        assert isinstance(errors[0], W_InvalidRecursorRule)


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
        p = Name.simple("p").axiom(type=PROP)
        bad = Name.simple("bad").definition(
            type=PROP,
            value=Foo.proj(3, mk.app(p.const())),
        )
        env = Environment.having([Foo_decl, mk_decl, p, bad])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : Prop :=
              (Foo.mk p).3
              ^^^^^^^^^^^^
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
              fun a x z ↦ z.2
              ^^^^^^^^^^^^^^^
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

    def test_proj_of_prop_with_ill_typed_ctor_arg_rejected(self):
        """
        ``(Wrapper.mk True.intro).p`` is a "proof" of ``False`` only if the
        kernel skips checking ``Wrapper.mk``'s argument types: ``mk`` expects
        a ``False``, so passing ``True.intro : True`` must be rejected during
        application inference, before the projection ever reads back ``False``.

        See lean-kernel-arena's ``tests/proj-of-prop.lean``.
        """
        Wrapper = Name.simple("Wrapper")
        wrapper_mk = Wrapper.child("mk")
        p = Name.simple("p")
        True_ = Name.simple("True")
        true_intro = True_.child("intro")
        False_ = Name.simple("False")
        bad = Name.simple("badFalse")

        False_decl = False_.inductive(type=PROP, constructors=[])
        true_intro_decl = true_intro.constructor(type=True_.const())
        True_decl = True_.inductive(type=PROP, constructors=[true_intro_decl])
        wrapper_mk_decl = wrapper_mk.constructor(
            type=forall(p.binder(type=False_.const()))(Wrapper.const()),
            num_fields=1,
        )
        Wrapper_decl = Wrapper.inductive(
            type=PROP, constructors=[wrapper_mk_decl],
        )
        bad_decl = bad.theorem(
            type=False_.const(),
            value=Wrapper.proj(0, wrapper_mk.app(true_intro.const())),
        )

        env = Environment.having([
            False_decl,
            True_decl, true_intro_decl,
            Wrapper_decl, wrapper_mk_decl,
            bad_decl,
        ])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert isinstance(errors[0], W_TypeError)
        assert errors[0].expected_type == False_.const()
        assert errors[0].inferred_type == True_.const()
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            theorem badFalse : False := (Wrapper.mk True.intro).p
                                                    ^^^^^^^^^^
                                                    has type
                                                      True
                                                    but is expected to have type
                                                      False""",
        )

    def test_not_a_function_diagnostic(self):
        """Applying a non-function term must be rejected with a clear error."""
        Nat_decl = NAT.name.inductive(type=TYPE)
        n = Name.simple("n").axiom(type=NAT)
        bad = Name.simple("bad").definition(
            type=NAT,
            value=n.const().app(n.const()),
        )
        env = Environment.having([Nat_decl, n, bad])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert isinstance(errors[0], W_NotAFunction)
        assert errors[0].inferred_type == NAT
        assert errors[0].as_diagnostic().format_with(FORMAT_PLAIN) == dedent(
            """\
            def bad : Nat :=
              n n
              ^
              function expected, term has type
                Nat""",
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


class TestCheckResult(object):
    def test_success_has_no_error(self):
        decl = Name.simple("Good").definition(type=TYPE, value=PROP)
        env = Environment.having([decl])

        result = env.type_check_one(decl)
        assert result.error is None
        assert result.elapsed >= 0.0
        assert result.gc_elapsed >= 0.0
        assert result.bytes_allocated >= 0

    def test_failure_carries_error(self):
        bad = Name.simple("Bad").definition(type=PROP, value=PROP)
        env = Environment.having([bad])

        result = env.type_check_one(bad)
        assert result.error is not None

    def test_heartbeats_populated_when_counting(self):
        decl = Name.simple("Good").definition(type=TYPE, value=PROP)
        env = Environment.having([decl])
        env.count_heartbeats = True

        result = env.type_check_one(decl)
        assert result.heartbeats > 0

    def test_heartbeats_zero_when_not_counting(self):
        decl = Name.simple("Good").definition(type=TYPE, value=PROP)
        env = Environment.having([decl])

        result = env.type_check_one(decl)
        assert result.heartbeats == 0


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
        bar = Name.of(["Foo", "bar"]).definition(type=TYPE, value=PROP)
        env = Environment.having([bar])
        assert env["Foo.bar"] is bar

    def test_getitem_name(self):
        Foobar = Name.of(["Foo.bar"])
        decl = Foobar.definition(type=TYPE, value=PROP)
        env = Environment.having([decl])
        assert env[Foobar] is decl

    def test_getitem_no_such_declaration(self):
        with pytest.raises(KeyError):
            Environment.EMPTY["DoesNotExist"]


class TestRecursorRuleValidation(object):
    """
    Recursor rules provided in the export data must be validated against
    independently constructed rules.

    A checker that compares the imported rules against themselves (instead of
    against independently constructed ones) will accept arbitrary recursor
    reduction behavior, leading to inconsistency.

    See https://arena.lean-lang.org/checker/official-nightly/#test-nat-rec-rules
    """

    @pytest.mark.xfail(reason="recursor rule validation not yet implemented")
    def test_wrong_succ_rec_rule_proves_false(self):
        """
        Nat with a wrong Nat.rec succ rule that always returns h_zero
        (ignoring the induction hypothesis) should be rejected.

        The exploit works because rpylean has native nat kernel extensions
        (Nat.beq) that compute correctly for concrete NatLit values,
        but symbolic arguments fall back to the wrong Nat.rec rules.

        With correct rules:  Nat.beq 1 0 = false, motive 1 = False
        With wrong rules:    Nat.beq (succ n) 0 = true for symbolic n

        The h_succ minor (fun n ih => True.intro) type-checks because
        motive (succ n) = True (via wrong rec rule), but the overall
        proof_of_false : False type-checks because motive 1 = False
        (via native Nat.beq). This inconsistency is unsound.

        See https://arena.lean-lang.org/checker/official-nightly/#test-nat-rec-rules
        """
        # -- Names --
        Nat = Name.simple("Nat")
        Nat_zero = Nat.child("zero")
        Nat_succ = Nat.child("succ")
        Nat_rec = Nat.child("rec")
        Nat_beq = Nat.child("beq")

        Bool = Name.simple("Bool")
        Bool_false = Bool.child("false")
        Bool_true = Bool.child("true")
        Bool_rec = Bool.child("rec")

        True_ = Name.simple("True")
        True_intro = True_.child("intro")
        False_ = Name.simple("False")

        u = Name.simple("u")
        u_level = u.level()
        n = Name.simple("n")
        t = Name.simple("t")
        x = Name.simple("x")

        # -- False and True as axioms (their recursors aren't needed) --
        false_ax = False_.axiom(type=PROP)
        true_ax = True_.axiom(type=PROP)
        true_intro_ax = True_intro.axiom(type=True_.const())

        # -- Bool (inductive, needed for Bool.rec iota reduction) --
        bool_false_ctor = Bool_false.constructor(type=Bool.const())
        bool_true_ctor = Bool_true.constructor(type=Bool.const())
        bool_decl = Bool.inductive(
            type=TYPE,
            constructors=[bool_false_ctor, bool_true_ctor],
        )

        bmotive = forall(t.binder(type=Bool.const()))(u_level.sort())
        hf_ty = W_BVar(0).app(Bool_false.const())
        ht_ty = W_BVar(1).app(Bool_true.const())
        bool_rec_decl = Bool_rec.recursor(
            type=forall(
                Name.simple("motive").implicit_binder(type=bmotive),
                Name.simple("hf").binder(type=hf_ty),
                Name.simple("ht").binder(type=ht_ty),
                t.binder(type=Bool.const()),
            )(W_BVar(3).app(W_BVar(0))),
            rules=[
                W_RecRule(
                    ctor_name=Bool_false, num_fields=0,
                    val=fun(
                        Name.simple("motive").binder(type=bmotive),
                        Name.simple("hf").binder(type=hf_ty),
                        Name.simple("ht").binder(type=ht_ty),
                    )(W_BVar(1)),  # hf
                ),
                W_RecRule(
                    ctor_name=Bool_true, num_fields=0,
                    val=fun(
                        Name.simple("motive").binder(type=bmotive),
                        Name.simple("hf").binder(type=hf_ty),
                        Name.simple("ht").binder(type=ht_ty),
                    )(W_BVar(0)),  # ht
                ),
            ],
            num_motives=1, num_minors=2, levels=[u],
        )

        # -- Nat (inductive with WRONG rec rule) --
        nat_zero_ctor = Nat_zero.constructor(type=Nat.const())
        nat_succ_ctor = Nat_succ.constructor(
            type=forall(n.binder(type=Nat.const()))(Nat.const()),
            num_fields=1,
        )
        nat_decl = Nat.inductive(
            type=TYPE,
            constructors=[nat_zero_ctor, nat_succ_ctor],
            is_recursive=True,
        )

        nmotive = forall(t.binder(type=Nat.const()))(u_level.sort())
        hz_ty = W_BVar(0).app(Nat_zero.const())
        hs_ty = forall(
            n.binder(type=Nat.const()),
            Name.simple("ih").binder(type=W_BVar(1).app(W_BVar(0))),
        )(W_BVar(2).app(Nat_succ.const().app(W_BVar(1))))

        nat_rec_decl = Nat_rec.recursor(
            type=forall(
                Name.simple("motive").implicit_binder(type=nmotive),
                Name.simple("hz").binder(type=hz_ty),
                Name.simple("hs").binder(type=hs_ty),
                t.binder(type=Nat.const()),
            )(W_BVar(3).app(W_BVar(0))),
            rules=[
                # zero rule (correct): fun motive hz hs => hz
                W_RecRule(
                    ctor_name=Nat_zero, num_fields=0,
                    val=fun(
                        Name.simple("motive").binder(type=nmotive),
                        Name.simple("hz").binder(type=hz_ty),
                        Name.simple("hs").binder(type=hs_ty),
                    )(W_BVar(1)),
                ),
                # succ rule (WRONG): fun motive hz hs n => hz
                # Should be: fun motive hz hs n => hs n (rec motive hz hs n)
                W_RecRule(
                    ctor_name=Nat_succ, num_fields=1,
                    val=fun(
                        Name.simple("motive").binder(type=nmotive),
                        Name.simple("hz").binder(type=hz_ty),
                        Name.simple("hs").binder(type=hs_ty),
                        n.binder(type=Nat.const()),
                    )(W_BVar(2)),  # hz, ignoring hs and n
                ),
            ],
            num_motives=1, num_minors=2, levels=[u],
            is_recursive=True,
        )

        # -- Nat.beq (definition using Nat.rec, but natively reduced) --
        # Nat.beq a b = Nat.rec (fun _ => Bool) true (fun n _ => false) a
        # Native reduction: beq 1 0 = false (correct).
        # Wrong rec rule:   beq (succ n) 0 = true (wrong).
        nat_beq_decl = Nat_beq.definition(
            type=forall(
                Name.simple("a").binder(type=Nat.const()),
                Name.simple("b").binder(type=Nat.const()),
            )(Bool.const()),
            value=fun(
                Name.simple("a").binder(type=Nat.const()),
                Name.simple("b").binder(type=Nat.const()),
            )(
                Nat_rec.const(levels=[TYPE.level]).app(
                    fun(x.binder(type=Nat.const()))(Bool.const()),
                ).app(Bool_true.const()).app(
                    fun(
                        n.binder(type=Nat.const()),
                        x.binder(type=Bool.const()),
                    )(Bool_false.const()),
                ).app(W_BVar(1)),
            ),
        )

        # -- proof_of_false --
        # motive n = Bool.rec (fun _ => Prop) False True (Nat.beq n 0)
        #   correct:  motive 0 = True,  motive 1 = False
        #   wrong:    motive (succ n) = True  (for symbolic n)
        motive_body = (
            Bool_rec.const(levels=[TYPE.level])
            .app(fun(x.binder(type=Bool.const()))(PROP))
            .app(False_.const())
            .app(True_.const())
            .app(Nat_beq.const().app(W_BVar(0)).app(W_LitNat.int(0)))
        )
        proof_motive = fun(n.binder(type=Nat.const()))(motive_body)

        proof_of_false = Name.simple("proof_of_false").definition(
            type=False_.const(),
            value=(
                Nat_rec.const(levels=[W_LEVEL_ZERO])
                .app(proof_motive)
                .app(True_intro.const())
                .app(fun(
                    n.binder(type=Nat.const()),
                    Name.simple("ih").binder(type=motive_body),
                )(True_intro.const()))
                .app(W_LitNat.int(1))
            ),
        )

        env = Environment.having([
            false_ax, true_ax, true_intro_ax,
            bool_decl, bool_false_ctor, bool_true_ctor, bool_rec_decl,
            nat_decl, nat_zero_ctor, nat_succ_ctor, nat_rec_decl,
            nat_beq_decl,
            proof_of_false,
        ])
        errors = type_check(env=env)
        assert errors, (
            "proof_of_false should not type check: "
            "a wrong Nat.rec succ rule must be rejected"
        )


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
