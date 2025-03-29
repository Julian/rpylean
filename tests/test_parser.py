from textwrap import dedent

from rpylean import parser
from tests import examples
import pytest


def items(source):
    return list(parser.parse(dedent(source).lstrip("\n").splitlines()))


def test_ns():
    assert items(
        """
        0.1.2
        1 #NS 0 MyTrue
        2 #NS 1 intro
        """
    ) == [
        parser.NameStr(nidx="1", parent_nidx="0", name="MyTrue"),
        parser.NameStr(nidx="2", parent_nidx="1", name="intro"),
    ]


def test_es():
    assert items(
        """
        0.1.2
        0 #ES 0
        """
    ) == [
        parser.Expr(eidx="0", val=parser.Sort(level="0")),
    ]


def test_wrong_version():
    with pytest.raises(parser.ExportVersionError):
        parser.parse("1.2.3\n")


def test_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.parse("")


@pytest.mark.parametrize("example_path", examples.all_valid_examples())
def test_valid_examples_parse_successfully(example_path):
    """
    We don't get parse errors from our examples.
    """
    parser.parse(example_path.readlines())
