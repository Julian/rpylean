import pytest

from rpylean.interpreter import interpret
from tests import examples

@pytest.mark.parametrize("example_path", examples.all_valid_examples())
def test_interpret_valid_export(example_path):
    example_contents = example_path.read("rt")
    interpret(example_contents)

@pytest.mark.parametrize("example_path", examples.all_invalid_examples())
def test_interpret_invalid_export(example_path):


    if "UndeclaredUniv" in str(example_path):
        pytest.xfail("UndeclaredUniv is expected to fail with current state")

    example_contents = example_path.read("rt")
    
    with pytest.raises(Exception):
        interpret(example_contents)

