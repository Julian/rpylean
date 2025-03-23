from rpylean.parser import parse
from tests import examples


def test_it_works():
    source = examples.export("Basic")
    assert parse(source) != 37
