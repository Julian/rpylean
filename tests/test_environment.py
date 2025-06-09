from textwrap import dedent

import pytest

from rpylean.environment import Environment
from rpylean.objects import W_LEVEL_ZERO, Name, W_TypeError, W_Definition


def test_valid_def_type_checks():
    W_Type = W_LEVEL_ZERO.succ().sort()
    W_Type1 = W_LEVEL_ZERO.succ().succ().sort()

    valid = W_Definition(type=W_Type1, value=W_Type, hint="R")
    valid.type_check(Environment.having([]).inference_context())


def test_invalid_def_does_not_type_check():
    """
    def test : Type := Type is not type correct.
    """

    W_Prop = W_LEVEL_ZERO.sort()
    W_Type = W_LEVEL_ZERO.succ().sort()
    W_Type1 = W_LEVEL_ZERO.succ().succ().sort()

    invalid = W_Definition(type=W_Prop, value=W_Type, hint="R")

    ctx = Environment.having([]).inference_context()
    with pytest.raises(W_TypeError) as e:
        invalid.type_check(ctx)
    assert e.value.w_expected_type == W_Type1
