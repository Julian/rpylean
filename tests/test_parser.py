from textwrap import dedent

from rpylean import parser
from tests import examples
import pytest

from rpython.rlib.rbigint import rbigint


def items(source):
    export = dedent(source.replace("⏎", "")).lstrip("\n").splitlines()
    return list(parser.to_items(export))


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
        parser.Expr(eidx=0, val=parser.Sort(level=0)),
    ]


def test_inductive():
    assert items(
        """
        1 #NS 0 Empty
        1 #US 0
        0 #ES 1
        #IND 1 0 0 0 0 0 0 1 1 0 ⏎
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, name="Empty"),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.Declaration(
            decl=parser.Inductive(
                name_idx=1,
                type_idx=0,
                name_idxs=[1],
                ctor_name_idxs=[],
                level_params=[],
                is_reflexive=False,
                is_recursive=False,
                num_nested=0,
                num_params=0,
                num_indices=0,
            ),
        ),
    ]


def test_constructor():
    assert items(
        """
        1 #NS 0 True
        2 #NS 1 intro
        1 #US 0
        0 #ES 1
        #IND 1 0 0 0 0 0 0 1 1 1 2 ⏎
        1 #EC 1 ⏎
        #CTOR 2 1 1 0 0 0 ⏎
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, name="True"),
        parser.NameStr(nidx=2, parent_nidx=1, name="intro"),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.Declaration(
            decl=parser.Inductive(
                name_idx=1,
                type_idx=0,
                name_idxs=[1],
                ctor_name_idxs=[2],
                level_params=[],
                is_reflexive=False,
                is_recursive=False,
                num_nested=0,
                num_params=0,
                num_indices=0,
            ),
        ),
        parser.Expr(eidx=1, val=parser.Const(name=1, levels=[])),
        parser.Declaration(
            decl=parser.Constructor(
                name_idx=2,
                type_idx=1,
                inductive_nidx=1,
                cidx=0,
                num_fields=0,
                num_params=0,
                level_params=[],
            ),
        ),
    ]
    from rpylean.environment import Environment
    print(Environment().from_items(items("""
        1 #NS 0 True
        2 #NS 1 intro
        1 #US 0
        0 #ES 1
        #IND 1 0 0 0 0 0 0 1 1 1 2 ⏎
        1 #EC 1 ⏎
        #CTOR 2 1 1 0 0 0 ⏎
    """)))


def test_large_litnat():
    assert items(
        """
        0 #ELN 18446744073709551616
        """
    ) == [
        parser.Expr(
            eidx=0,
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
