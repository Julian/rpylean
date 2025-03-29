import pytest
from rpylean.interpreter import interpret
from tests import examples

@pytest.mark.parametrize("export_name", examples.examples_dirs)
def test_interpret(export_name):
    source = examples.export(export_name)
    interpret(source)

