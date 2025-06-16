import pytest

from rpylean.environment import Environment
from rpylean.objects import PROP, TYPE, W_LEVEL_ZERO, W_TypeError, W_Definition


def test_valid_def_type_checks():
    """
    Prop : Type
    """
    valid = W_Definition(type=TYPE, value=PROP, hint="R")
    valid.type_check(Environment.EMPTY)


def test_invalid_def_does_not_type_check():
    """
    Type is not a Prop.
    """

    invalid = W_Definition(type=PROP, value=TYPE, hint="R")

    with pytest.raises(W_TypeError) as e:
        invalid.type_check(Environment.EMPTY)

    TYPE_1 = W_LEVEL_ZERO.succ().succ().sort()
    assert e.value.expected_type == TYPE_1
