from StringIO import StringIO
from textwrap import dedent

from rpython.rlib.rbigint import rbigint
import pytest
from rpylean import parser
from tests import examples


def ndjson_items(source):
    export = StringIO(dedent(source).strip())
    return list(parser.from_ndjson(export))


def test_ns():
    assert ndjson_items(
        """
        {"i":1,"str":{"pre":0,"str":"MyTrue"}}
        {"i":2,"str":{"pre":1,"str":"intro"}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="MyTrue"),
        parser.NameStr(nidx=2, parent_nidx=1, part="intro"),
    ]


def test_es():
    assert ndjson_items(
        """
        {"i":0,"sort":{"u":0}}
        """
    ) == [
        parser.Expr(eidx=0, val=parser.Sort(level=0)),
    ]


def test_inductive():
    assert ndjson_items(
        """
        {"i":1,"str":{"pre":0,"str":"Empty"}}
        {"i":1,"succ":0}
        {"i":0,"sort":{"u":1}}
        {"inductInfo":{"all":[1],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="Empty"),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.InductiveSkeleton(
            nidx=1,
            type_idx=0,
            name_idxs=[1],
            ctor_name_idxs=[],
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
        {"i":1,"str":{"pre":0,"str":"True"}}
        {"i":2,"str":{"pre":1,"str":"intro"}}
        {"i":1,"succ":0}
        {"i":0,"sort":{"u":1}}
        {"inductInfo":{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}}
        {"const":{"declName":1,"us":[]},"i":1}
        {"ctorInfo":{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":1}}
        """
    ) == [
        parser.NameStr(nidx=1, parent_nidx=0, part="True"),
        parser.NameStr(nidx=2, parent_nidx=1, part="intro"),
        parser.UniverseSucc(uidx=1, parent=0),
        parser.Expr(eidx=0, val=parser.Sort(level=1)),
        parser.InductiveSkeleton(
            nidx=1,
            type_idx=0,
            name_idxs=[1],
            ctor_name_idxs=[2],
            levels=[],
            is_reflexive=False,
            is_recursive=False,
            num_nested=0,
            num_params=0,
            num_indices=0,
        ),
        parser.Expr(eidx=1, val=parser.Const(nidx=1, levels=[])),
        parser.Constructor(
            nidx=2,
            type_idx=1,
            inductive_nidx=1,
            cidx=0,
            num_fields=0,
            num_params=0,
            levels=[],
        ),
    ]


def test_large_litnat():
    assert ndjson_items(
        """
        {"i":0,"natVal":"18446744073709551616"}
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
        parser.from_ndjson(
            '{"meta":{"exporter":{"name":"lean4export","version":"3.0.0"},"lean":{"githash":"2fcce7258eeb6e324366bc25f9058293b04b7547","version":"4.27.0-rc1"}}}',
        )


def test_totally_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.from_ndjson("")


@pytest.mark.parametrize("path", examples.VALID, ids=examples.name_of)
def test_valid_examples_parse_successfully(path):
    """
    We don't get parse errors from our examples.
    """
    parser.from_ndjson(path.readlines())
