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


def from_lines(item_lines):
    lines = ["0.1.2"]
    lines.extend(dedent(item_lines).strip().splitlines())
    return Environment.from_lines(lines)


def test_valid_def_type_checks():
    W_Type = W_Sort(W_LevelSucc(W_LEVEL_ZERO))
    W_Type1 = W_Sort(W_LevelSucc(W_LevelSucc(W_LEVEL_ZERO)))

    valid = W_Definition(def_type=W_Type1, def_val=W_Type, hint="R")
    valid.type_check(Environment().inference_context())


def test_invalid_def_does_not_type_check():
    """
    def test : Type := Type is not type correct.
    """

    W_Prop = W_Sort(W_LEVEL_ZERO)
    W_Type = W_Sort(W_LevelSucc(W_LEVEL_ZERO))
    W_Type1 = W_Sort(W_LevelSucc(W_LevelSucc(W_LEVEL_ZERO)))

    invalid = W_Definition(def_type=W_Prop, def_val=W_Type, hint="R")

    ctx = Environment().inference_context()
    with pytest.raises(W_TypeError) as e:
        invalid.type_check(ctx)
    assert e.value.w_expected_type == W_Type1
