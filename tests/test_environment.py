from textwrap import dedent

import pytest

from rpylean.objects import (
    W_LEVEL_ZERO,
    W_TypeError,
    W_Definition,
    W_Sort,
    W_LevelSucc,
)
from rpylean.environment import Environment


def test_valid_def_type_checks():
    W_Type = W_LEVEL_ZERO.succ().sort()
    W_Type1 = W_LEVEL_ZERO.succ().succ().sort()

    valid = W_Definition(def_type=W_Type1, def_val=W_Type, hint="R")
    valid.type_check(Environment().inference_context())


def test_invalid_def_does_not_type_check():
    """
    def test : Type := Type is not type correct.
    """

    W_Prop = W_LEVEL_ZERO.sort()
    W_Type = W_LEVEL_ZERO.succ().sort()
    W_Type1 = W_LEVEL_ZERO.succ().succ().sort()

    invalid = W_Definition(def_type=W_Prop, def_val=W_Type, hint="R")

    ctx = Environment().inference_context()
    with pytest.raises(W_TypeError) as e:
        invalid.type_check(ctx)
    assert e.value.w_expected_type == W_Type1
