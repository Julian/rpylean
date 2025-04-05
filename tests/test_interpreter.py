from textwrap import dedent

import pytest

from rpylean import objects
from rpylean.interpreter import Environment, interpret
from tests import examples


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


XFAIL = dict(
    FreeVars=(
        "Something seems entirely wrong with this example, "
        "as the export.orig and export files are identical"
    ),
    UndeclaredUniv=(
        "Presumably this fails because we don't "
        "check for undeclared universes."
    )
)


@pytest.mark.parametrize("path", examples.VALID, ids=examples.name_of)
def test_interpret_valid_export(path):
    interpret(path.readlines())


@pytest.mark.parametrize("path", examples.INVALID, ids=examples.name_of)
def test_interpret_invalid_export(path):
    message = XFAIL.get(path.dirpath().basename)
    if message is not None:
        pytest.xfail(message)

    example_contents = path.readlines()

    with pytest.raises(Exception):
        interpret(example_contents)
