from textwrap import dedent

import pytest

from rpylean import objects
from rpylean.interpreter import Environment


def export(lines):
    return ("0.1.2\n" + dedent(lines).strip()).splitlines()


def test_type_check_valid_def():
    env = Environment.from_lines(
        export(
            """
            1 #NS 0 test
            1 #US 0
            2 #US 1
            0 #ES 2
            1 #ES 1
            #DEF 1 0 1 R 1
            """,
        ),
    )
    env["test"].type_check(env.inference_context())


def test_type_check_invalid_def():
    """
    def test : Type := Type is not type correct.
    """

    env = Environment.from_lines(
        export(
            """
            1 #NS 0 test
            1 #US 0
            2 #US 1
            0 #ES 2
            1 #ES 1
            #DEF 1 0 1 R 1
            """,
        ),
    )
    ctx = env.inference_context()

    test = env["test"]
    test.type_check(env.inference_context())

    invalid = objects.W_Definition(  # Sort 1 == Type 0 == Type
        def_type=objects.W_Sort(level=env.levels["1"]),
        def_val=test.w_kind.def_val,
        hint=test.w_kind.hint,
    )
    with pytest.raises(objects.W_TypeError) as e:
        invalid.type_check(ctx)
    assert e.value.w_expected_type == test.w_kind.def_type
