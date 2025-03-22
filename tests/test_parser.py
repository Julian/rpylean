import os.path

from rpylean.parser import parse
from tests import examples


BASIC = os.path.join(examples.PATH, "Basic/export")


def test_it_works():
    with open(BASIC) as file:
        source = file.read()
    assert parse(source) != 37
