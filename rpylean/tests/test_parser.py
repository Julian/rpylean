import os.path

from rpylean import RPYLEAN_DIR
from rpylean.parser import parse


EXAMPLES = os.path.join(os.path.dirname(RPYLEAN_DIR), "examples")
BASIC = os.path.join(EXAMPLES, "basic_export")


def test_it_works():
    with open(BASIC) as file:
        source = file.read()
    assert parse(source) != 37
