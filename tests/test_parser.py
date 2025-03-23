from rpylean.parser import parse
from tests import examples


def test_it_works():
    source = examples.export("basic")
    assert parse(source) != 37
