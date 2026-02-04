from StringIO import StringIO
from textwrap import dedent

from rpython.rlib.rbigint import rbigint
import pytest
from rpylean import parser
from tests import examples


def ndjson_items(source):
    return list(parser.from_str(source))


def test_ns():
    assert ndjson_items(
        """
        {"in":1,"str":{"pre":0,"str":"MyTrue"}}
        {"in":2,"str":{"pre":1,"str":"intro"}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="MyTrue"),
        parser.NameStr(nidx=2, parent_nidx=1, part="intro"),
    ]


def test_es():
    assert ndjson_items(
        """
        {"ie":0,"sort":0}
        """
    ) == [
        parser.Expr(eidx=0, val=parser.Sort(level=0)),
    ]


def test_inductive():
    assert ndjson_items(
        """
        {"in":1,"str":{"pre":0,"str":"Empty"}}
        {"il":1,"succ":0}
        {"ie":0,"sort":1}
        {"inductive":{"ctors":[],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[3],"name":2,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":8}],"types":[{"all":[1],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="Empty"),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.Inductive(
            nidx=1,
            type_idx=0,
            name_idxs=[1],
            constructors=[],
            recursors=[
                parser.Recursor(
                    nidx=2,
                    type_idx=8,
                    k=False,
                    levels=[3],
                    num_indices=0,
                    num_minors=0,
                    num_motives=1,
                    num_params=0,
                    ind_name_idxs=[1],
                    rules=[],
                ),
            ],
            levels=[],
            is_reflexive=False,
            is_recursive=False,
            num_nested=0,
            num_params=0,
            num_indices=0,
        ),
    ]


def test_constructor():
    assert ndjson_items(
        """
        {"in":1,"str":{"pre":0,"str":"True"}}
        {"in":2,"str":{"pre":1,"str":"intro"}}
        {"il":1,"succ":0}
        {"ie":0,"sort":1}
        {"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":1}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[4],"name":3,"numIndices":0,"numMinors":1,"numMotives":1,"numParams":0,"rules":[{"ctor":2,"nfields":0,"rhs":13}],"type":11}],"types":[{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="True"),
        parser.NameStr(nidx=2, parent_nidx=1, part="intro"),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.Inductive(
            nidx=1,
            type_idx=0,
            name_idxs=[1],
            constructors=[
                parser.Constructor(
                    nidx=2,
                    type_idx=1,
                    inductive_nidx=1,
                    cidx=0,
                    num_fields=0,
                    num_params=0,
                    levels=[],
                ),
            ],
            recursors=[
                parser.Recursor(
                    nidx=3,
                    type_idx=11,
                    k=False,
                    levels=[4],
                    num_indices=0,
                    num_minors=1,
                    num_motives=1,
                    num_params=0,
                    ind_name_idxs=[1],
                    rules=[
                        parser.RecRule(ctor_name_idx=2, num_fields=0, val=13),
                    ],
                ),
            ],
            levels=[],
            is_reflexive=False,
            is_recursive=False,
            num_nested=0,
            num_params=0,
            num_indices=0,
        ),
    ]


def test_large_litnat():
    assert ndjson_items(
        """
        {"ie":0,"natVal":"18446744073709551616"}
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
    assert ndjson_items("") == []


def test_wrong_version():
    with pytest.raises(parser.ExportVersionError):
        parser.from_export(
            StringIO('{"meta":{"format":{"version":"2.0.0"}}}\n'),
        )


def test_totally_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.from_export(StringIO(""))


def test_lambda_strict_implicit():
    assert ndjson_items(
        """
        {"in":1,"str":{"pre":0,"str":"a"}}
        {"bvar":0,"ie":0}
        {"ie":1,"lam":{"binderInfo":"strictImplicit","body":0,"name":1,"type":0}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="a"),
        parser.Expr(eidx=0, val=parser.BVar(id=0)),
        parser.Expr(
            eidx=1,
            val=parser.Lambda(
                name=1,
                type=0,
                binder_info="strictImplicit",
                body=0,
            ),
        ),
    ]


def test_opaque():
    assert ndjson_items(
        """
        {"in":1,"str":{"pre":0,"str":"foo"}}
        {"ie":0,"sort":1}
        {"il":1,"succ":0}
        {"ie":1,"sort":0}
        {"opaque":{"all":[1],"isUnsafe":false,"levelParams":[1],"name":1,"type":0,"value":1}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="foo"),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=1, val=parser.Sort(level=0)),
        parser.Opaque(
            nidx=1,
            type=0,
            value=1,
            levels=[1],
        ),
    ]


def test_axiom():
    assert ndjson_items(
        """
        {"in":1,"str":{"pre":0,"str":"ax"}}
        {"ie":0,"sort":1}
        {"il":1,"succ":0}
        {"axiom":{"levelParams":[1],"name":1,"type":0}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="ax"),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Axiom(nidx=1, type=0, levels=[1]),
    ]


@pytest.mark.parametrize("path", examples.VALID, ids=examples.name_of)
def test_valid_examples_parse_successfully(path):
    """
    We don't get parse errors from our examples.
    """
    parser.from_export(path.open())
