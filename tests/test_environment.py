import pytest

from rpylean.environment import Environment
from rpylean.objects import PROP, TYPE, W_LEVEL_ZERO, Name, W_TypeError


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

    with pytest.raises(W_TypeError) as e:
        invalid.type_check(Environment.EMPTY)

    TYPE_1 = W_LEVEL_ZERO.succ().succ().sort()
    assert e.value.expected_type == TYPE_1
