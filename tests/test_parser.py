from textwrap import dedent

from rpylean import parser
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


def test_wrong_version():
    with pytest.raises(parser.ExportVersionError):
        parser.parse("1.2.3\n")


def test_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.parse("")
