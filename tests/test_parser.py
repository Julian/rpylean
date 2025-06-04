from textwrap import dedent

from rpylean import parser
from tests import examples
import pytest

from rpython.rlib.rbigint import rbigint


def items(source):
    return list(parser.to_items(dedent(source).lstrip("\n").splitlines()))


def test_ns():
    assert items(
        """
        1 #NS 0 MyTrue
        2 #NS 1 intro
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, name="MyTrue"),
        parser.NameStr(nidx=2, parent_nidx=1, name="intro"),
    ]


def test_es():
    assert items(
        """
        0 #ES 0
        """
    ) == [
        parser.Expr(eidx="0", val=parser.Sort(level=0)),
    ]


def test_large_litnat():
    assert items(
        """
        0 #ELN 18446744073709551616
        """
    ) == [
        parser.Expr(
            eidx="0",
            val=parser.LitNat(val=rbigint.fromlong(18446744073709551616)),
        ),
    ]


def test_empty():
    """
    Nothing to check, but that's fine.
    """
    items("") == []


def test_wrong_version():
    with pytest.raises(parser.ExportVersionError):
        parser.from_export("1.2.3\n")


def test_totally_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.from_export("")


@pytest.mark.parametrize("path", examples.VALID, ids=examples.name_of)
def test_valid_examples_parse_successfully(path):
    """
    We don't get parse errors from our examples.
    """
    parser.from_export(path.readlines())
