"""
Run our export file examples as tests.
"""
import pytest

from rpylean.environment import from_export
from tests import examples


@pytest.mark.parametrize("path", examples.VALID, ids=examples.name_of)
def test_interpret_valid_export(path):
    if examples.name_of(path) == "Init":
        pytest.skip("Type checking Init doesn't work yet and loops for ages.")

    environment = from_export(path.open())
    assert not list(environment.type_check())
