import pytest

from rpylean.interpreter import interpret
from tests import examples


@pytest.mark.parametrize("example", examples.all_examples())
def test_interpret(example):
    interpret(example)
