from textwrap import dedent

from rpylean.parser import parse
from tests import examples


def test_it_works():
    source = examples.export("valid/Basic")
    assert parse(source) != 37
