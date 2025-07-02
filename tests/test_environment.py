import pytest

from rpylean.environment import Environment
from rpylean.objects import PROP, TYPE, W_LEVEL_ZERO, Name


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

    TYPE_1 = W_LEVEL_ZERO.succ().succ().sort()
    assert error.expected_type == TYPE_1


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
