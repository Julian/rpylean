from textwrap import dedent

import pytest

from rpylean.environment import Environment
from rpylean.exceptions import AlreadyDeclared
from rpylean.objects import (
    NAT,
    PROP,
    TYPE,
    Name,
    W_BVar,
    forall,
    fun,
    names,
)


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

    def test_definition_type_must_be_sort(self):
        """
        A definition's type must be a Sort (Type or Prop), not a function type.
        """
        a, x = names("a", "x")
        b0 = W_BVar(0)
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
            in nonTypeType:
              constType
            has type
              Type → Type
            but is expected to be a Sort (Type or Prop)
            """,
        ).rstrip("\n")

    def test_binder_type_with_non_sort_definition_raises(self):
        """
        A binder type must be a Sort (Type or Prop), not a function type.
        """
        a, x = names("a", "x")

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
        f, x, T = names("f", "x", "T")
        b0, b1 = W_BVar(0), W_BVar(1)
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
        )(W_BVar(1).app(W_BVar(0)).app(W_BVar(1)).app(W_BVar(0)))

        refl_ctor_type = forall(alpha.binder(type=TYPE))(refl_body)

        refl_ctor = refl.constructor(type=refl_ctor_type)
        Eq_decl = Eq.inductive(
            type=inductive_type,
            constructors=[refl_ctor],
            num_params=1,
        )

        env = Environment.having([Eq_decl, refl_ctor])
        assert type_check(env=env) == []


class TestTypeError(object):
    def test_with_name(self):
        invalid = Name.simple("foo").definition(type=PROP, value=TYPE)

        error = invalid.type_check(Environment.EMPTY)
        assert str(error) == (
            "Type mismatch in foo:\n"
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
            "Type mismatch in [anonymous]:\n"
            "  Type\n"
            "has type\n"
            "  Type 1\n"
            "but is expected to have type\n"
            "  Prop"
        )

    def test_inductive_type_must_be_sort(self):
        a, x = Name.simple("a"), Name.simple("x")
        b0 = W_BVar(0)
        fnType = Name.simple("fnType").definition(
            type=forall(a.binder(type=TYPE))(TYPE),
            value=fun(x.binder(type=TYPE))(b0),
        )
        bad_inductive = Name.simple("BadInd").inductive(type=fnType.const())

        env = Environment.having([fnType, bad_inductive])
        errors = type_check(env=env)
        assert len(errors) == 1
        assert str(errors[0]) == (
            "in BadInd:\n"
            "  fnType\n"
            "has type\n"
            "  Type → Type\n"
            "but is expected to be a Sort (Type or Prop)"
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
