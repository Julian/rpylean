from textwrap import dedent

import pytest

from rpylean import objects
from rpylean.environment import Environment


def from_lines(item_lines):
    lines = ["0.1.2"]
    lines.extend(dedent(item_lines).strip().splitlines())
    return Environment.from_lines(lines)


def test_valid_def_type_checks():
    env = from_lines(
        """
        1 #NS 0 test
        1 #US 0
        2 #US 1
        0 #ES 2
        1 #ES 1
        #DEF 1 0 1 R 1
        """,
    )
    env["test"].type_check(env.inference_context())


def test_invalid_def_does_not_type_check():
    """
    def test : Type := Type is not type correct.
    """

    env = from_lines(
        """
        1 #NS 0 test
        1 #US 0
        2 #US 1
        0 #ES 2
        1 #ES 1
        #DEF 1 0 1 R 1
        """,
    )
    test = env["test"]
    test.type_check(env.inference_context())

    invalid = objects.W_Definition(  # Sort 1 == Type 0 == Type
        def_type=objects.W_Sort(level=env.levels["1"]),
        def_val=test.w_kind.def_val,
        hint=test.w_kind.hint,
    )

    ctx = env.inference_context()
    with pytest.raises(objects.W_TypeError) as e:
        invalid.type_check(ctx)
    assert e.value.w_expected_type == test.w_kind.def_type
