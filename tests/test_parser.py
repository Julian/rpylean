"""
Tests of the lean4export NDJSON parser.

The parser now applies each line directly to an EnvironmentBuilder via
its ``register_*`` methods, so these tests assert on the resulting
builder state rather than on intermediate AST nodes.
"""

from StringIO import StringIO

from rpython.rlib.rbigint import rbigint
import pytest

from rpylean import parser
from rpylean.environment import EnvironmentBuilder
from rpylean.objects import Name, W_LEVEL_ZERO, W_BVar, W_LitNat, W_LitStr


def parse(source):
    """Parse an NDJSON snippet (no metadata header) into a fresh builder."""
    return parser.from_str(source)


def test_names():
    builder = parse(
        """
        {"in":1,"str":{"pre":0,"str":"MyTrue"}}
        {"in":2,"str":{"pre":1,"str":"intro"}}
        """,
    )
    assert builder.names == [
        Name.ANONYMOUS,
        Name(["MyTrue"]),
        Name(["MyTrue", "intro"]),
    ]


def test_sort_expr():
    builder = parse('{"ie":0,"sort":0}')
    assert builder.exprs == [W_LEVEL_ZERO.sort()]


def test_bvar_expr_disc_first():
    """Lines may emit the discriminator before ``"ie"`` — `{"bvar":N,"ie":N}`."""
    builder = parse('{"bvar":3,"ie":0}')
    assert builder.exprs == [W_BVar(id=3)]


def test_lambda_strict_implicit():
    builder = parse(
        """
        {"in":1,"str":{"pre":0,"str":"a"}}
        {"bvar":0,"ie":0}
        {"ie":1,"lam":{"binderInfo":"strictImplicit","body":0,"name":1,"type":0}}
        """,
    )
    assert builder.names[1] == Name(["a"])
    assert len(builder.exprs) == 2
    assert builder.exprs[0] == W_BVar(id=0)


def test_axiom():
    builder = parse(
        """
        {"in":1,"str":{"pre":0,"str":"ax"}}
        {"il":1,"succ":0}
        {"ie":0,"sort":1}
        {"axiom":{"levelParams":[1],"name":1,"type":0}}
        """,
    )
    assert len(builder.declarations) == 1
    decl = builder.declarations[0]
    assert decl.name == Name(["ax"])


def test_opaque():
    builder = parse(
        """
        {"in":1,"str":{"pre":0,"str":"foo"}}
        {"il":1,"succ":0}
        {"ie":0,"sort":1}
        {"ie":1,"sort":0}
        {"opaque":{"all":[1],"isUnsafe":false,"levelParams":[1],"name":1,"type":0,"value":1}}
        """,
    )
    assert len(builder.declarations) == 1
    assert builder.declarations[0].name == Name(["foo"])


def test_large_litnat():
    builder = parse('{"ie":0,"natVal":"18446744073709551616"}')
    assert builder.exprs == [
        W_LitNat(val=rbigint.fromlong(18446744073709551616)),
    ]


def test_empty():
    """An empty body parses to an empty builder."""
    builder = parse("")
    assert len(builder.names) == 1  # just Name.ANONYMOUS
    assert len(builder.exprs) == 0
    assert builder.levels == [W_LEVEL_ZERO]
    assert len(builder.declarations) == 0


def test_wrong_version():
    with pytest.raises(parser.ExportVersionError):
        parser.validate_export_metadata(
            StringIO('{"meta":{"format":{"version":"2.0.0"}}}\n'),
        )


def test_totally_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.validate_export_metadata(StringIO(""))
