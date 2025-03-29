from textwrap import dedent

from rpylean.parser import ExportVersionError, parse
import pytest


def items(source):
    return list(parse(dedent(source).lstrip("\n").splitlines()))


def test_ns():
    assert items(
        """
        0.1.2
        1 #NS 0 MyTrue
        """
    ) == [
    ]


def test_wrong_version():
    with pytest.raises(ExportVersionError):
        parse("1.2.3\n")


def test_empty():
    with pytest.raises(ExportVersionError):
        parse("")
