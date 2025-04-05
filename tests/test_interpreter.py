import pytest

from rpylean.interpreter import interpret
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


@pytest.mark.parametrize("path", examples.all_valid_examples())
def test_interpret_valid_export(path):
    interpret(path.readlines())


@pytest.mark.parametrize("path", examples.all_invalid_examples())
def test_interpret_invalid_export(path):
    message = XFAIL.get(path.dirpath().basename)
    if message is not None:
        pytest.xfail(message)

    example_contents = path.readlines()

    with pytest.raises(Exception):
        interpret(example_contents)
