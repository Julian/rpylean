"""
Run our export file examples as tests.
"""
import pytest

from rpylean.interpreter import Environment
from tests import examples


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
    environment = Environment.from_lines(path.readlines())
    assert environment.type_check().succeeded()


@pytest.mark.parametrize("path", examples.INVALID, ids=examples.name_of)
def test_interpret_invalid_export(path):
    environment = Environment.from_lines(path.readlines())

    message = XFAIL.get(path.dirpath().basename)
    if message is not None:
        pytest.xfail(message)

    assert environment.type_check().succeeded()
