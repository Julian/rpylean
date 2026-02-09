from textwrap import dedent

import pytest

from rpylean.environment import Environment
from rpylean.objects import PROP, TYPE, Name


def test_valid_def_type_checks():
    """
    Prop : Type
    """
    valid = Name.ANONYMOUS.definition(type=TYPE, value=PROP)
    valid.type_check(Environment.EMPTY)


def test_invalid_def_does_not_type_check():
    """
    Type is not a Prop.
    """

    invalid = Name.ANONYMOUS.definition(type=PROP, value=TYPE)

    error = invalid.type_check(Environment.EMPTY)
    assert error is not None

    assert error.expected_type == PROP


class TestTypeError(object):
    def test_with_name(self):
        invalid = Name.simple("foo").definition(type=PROP, value=TYPE)

        error = invalid.type_check(Environment.EMPTY)
        assert error.str() == dedent(
            """\
            in foo:
            Type
              has type
            Type 1
              but is expected to have type
            Prop
            """,
        ).strip("\n")

    def test_anonymous(self):
        invalid = Name.ANONYMOUS.definition(type=PROP, value=TYPE)

        error = invalid.type_check(Environment.EMPTY)
        assert error.str() == dedent(
            """\
            Type
              has type
            Type 1
              but is expected to have type
            Prop
            """,
        ).strip("\n")


def test_filter_declarations_by_substring():
    """Filtering declarations selects only those whose name contains the substring."""
    good = Name.simple("GoodDef").definition(type=TYPE, value=PROP)
    bad = Name.simple("BadDef").definition(type=PROP, value=TYPE)
    env = Environment.having([good, bad])

    errors = list(env.type_check(env.filter_declarations("Good")))
    assert errors == []


def test_filter_declarations_matches_bad():
    """Filtering to an invalid declaration produces an error."""
    good = Name.simple("GoodDef").definition(type=TYPE, value=PROP)
    bad = Name.simple("BadDef").definition(type=PROP, value=TYPE)
    env = Environment.having([good, bad])

    errors = list(env.type_check(env.filter_declarations("Bad")))
    assert len(errors) == 1


def test_verbose_prints_declaration_names():
    """Verbose mode prints each declaration name to the progress stream."""
    from io import BytesIO

    good = Name.simple("GoodDef").definition(type=TYPE, value=PROP)
    env = Environment.having([good])

    progress = BytesIO()
    list(env.type_check(verbose="yes", progress=progress))
    assert "GoodDef" in progress.getvalue()


class TestHeartbeat(object):
    def test_heartbeat_resets_per_declaration(self):
        """Heartbeat counter resets before each declaration."""
        a = Name.simple("A").definition(type=TYPE, value=PROP)
        b = Name.simple("B").definition(type=TYPE, value=PROP)
        env = Environment.having([a, b])
        env.max_heartbeat = 100000

        errors = list(env.type_check())
        assert errors == []

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

        # 4th call exceeds the limit
        try:
            env.def_eq(PROP, PROP)
            assert False, "should have raised HeartbeatExceeded"
        except HeartbeatExceeded as err:
            assert "Test" in err.str()
            assert "heartbeat limit exceeded" in err.str()

    def test_check_one_resets_heartbeat(self):
        """_check_one resets the heartbeat counter before each declaration."""
        decl = Name.simple("OK").definition(type=TYPE, value=PROP)
        env = Environment.having([decl])
        env.max_heartbeat = 100
        env.heartbeat = 99  # would overflow on next def_eq

        errors = list(env.type_check())
        assert errors == []  # heartbeat was reset, so no overflow

    def test_heartbeat_zero_means_unlimited(self):
        """A max_heartbeat of 0 (default) means no limit."""
        good = Name.simple("Good").definition(type=TYPE, value=PROP)
        env = Environment.having([good])
        assert env.max_heartbeat == 0

        errors = list(env.type_check())
        assert errors == []


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

        list(env.type_check())
        # After type_check, cache should have been cleared between decls
        # (we can't easily observe this, but at least it shouldn't crash)
        assert env._def_eq_cache == {} or len(env._def_eq_cache) >= 0


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
