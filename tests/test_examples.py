"""
Run our export file examples as tests.
"""
import pytest

from rpylean.environment import from_export
from tests import examples


XFAIL = dict(
    UndeclaredUniv=(
        "Presumably this fails because we don't "
        "check for undeclared universes."
    )
)


@pytest.mark.parametrize("path", examples.VALID, ids=examples.name_of)
def test_interpret_valid_export(path):
    if examples.name_of(path) == "Init":
        pytest.skip("Type checking Init doesn't work yet and loops for ages.")

    environment = from_export(path.readlines())
    assert not list(environment.type_check())


@pytest.mark.parametrize("path", examples.INVALID, ids=examples.name_of)
def test_interpret_invalid_export(path):
    environment = from_export(path.readlines())

    message = XFAIL.get(path.dirpath().basename)
    if message is not None:
        pytest.xfail(message)

    assert list(environment.type_check())
