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
from rpylean.objects import (
    Name, W_LEVEL_ZERO, W_BVar, W_LitNat, W_LitStr,
    SAFETY_PARTIAL, SAFETY_SAFE, SAFETY_UNSAFE,
)


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
        Name.of(["MyTrue"]),
        Name.of(["MyTrue", "intro"]),
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
    assert builder.names[1] == Name.of(["a"])
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
    assert decl.name == Name.of(["ax"])


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
    assert builder.declarations[0].name == Name.of(["foo"])


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


class TestSafety(object):
    def test_definition_safety(self):
        builder = parse(
            """
            {"in":1,"str":{"pre":0,"str":"T"}}
            {"in":2,"str":{"pre":0,"str":"s"}}
            {"in":3,"str":{"pre":0,"str":"u"}}
            {"in":4,"str":{"pre":0,"str":"p"}}
            {"ie":0,"sort":0}
            {"const":{"name":1,"us":[]},"ie":1}
            {"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}
            {"def":{"all":[2],"hints":"opaque","levelParams":[],"name":2,"safety":"safe","type":1,"value":1}}
            {"def":{"all":[3],"hints":"opaque","levelParams":[],"name":3,"safety":"unsafe","type":1,"value":1}}
            {"def":{"all":[4],"hints":"opaque","levelParams":[],"name":4,"safety":"partial","type":1,"value":1}}
            """,
        )
        env = builder.env
        assert env["s"].safety == SAFETY_SAFE
        assert env["u"].safety == SAFETY_UNSAFE
        assert env["p"].safety == SAFETY_PARTIAL
        assert env["s"].w_kind.all is None
        assert [env[n].index for n in ("T", "s", "u", "p")] == [0, 1, 2, 3]
        # An unsafe definition forms a block by itself; nothing else does.
        assert env["u"].group == 2
        assert env["s"].group == -1
        assert env["p"].group == -1

    def test_mutual_definition_block(self):
        builder = parse(
            """
            {"in":1,"str":{"pre":0,"str":"T"}}
            {"in":2,"str":{"pre":0,"str":"ping"}}
            {"in":3,"str":{"pre":0,"str":"pong"}}
            {"ie":0,"sort":0}
            {"const":{"name":1,"us":[]},"ie":1}
            {"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}
            {"def":{"all":[2,3],"hints":"opaque","levelParams":[],"name":2,"safety":"partial","type":1,"value":1}}
            {"def":{"all":[2,3],"hints":"opaque","levelParams":[],"name":3,"safety":"partial","type":1,"value":1}}
            """,
        )
        env = builder.env
        assert env["ping"].w_kind.all == [Name.simple("ping"), Name.simple("pong")]
        assert env["ping"].group == env["pong"].group == 1

    def test_unsafe_axiom_and_opaque(self):
        builder = parse(
            """
            {"in":1,"str":{"pre":0,"str":"T"}}
            {"in":2,"str":{"pre":0,"str":"ax"}}
            {"in":3,"str":{"pre":0,"str":"op"}}
            {"ie":0,"sort":0}
            {"const":{"name":1,"us":[]},"ie":1}
            {"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}
            {"axiom":{"isUnsafe":true,"levelParams":[],"name":2,"type":1}}
            {"opaque":{"all":[3],"isUnsafe":true,"levelParams":[],"name":3,"type":1,"value":1}}
            """,
        )
        env = builder.env
        assert env["ax"].is_unsafe()
        assert env["op"].is_unsafe()
        assert not env["T"].is_unsafe()

    def test_inductive_block_shares_a_group(self):
        builder = parse(
            """
            {"in":1,"str":{"pre":0,"str":"MyTrue"}}
            {"in":2,"str":{"pre":1,"str":"intro"}}
            {"in":3,"str":{"pre":1,"str":"rec"}}
            {"in":4,"str":{"pre":0,"str":"motive"}}
            {"in":5,"str":{"pre":0,"str":"t"}}
            {"ie":0,"sort":0}
            {"const":{"name":1,"us":[]},"ie":1}
            {"ie":2,"sort":0}
            {"bvar":0,"ie":3}
            {"forallE":{"binderInfo":"default","body":3,"name":5,"type":1},"ie":4}
            {"forallE":{"binderInfo":"default","body":4,"name":4,"type":2},"ie":5}
            {"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":1}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[],"name":3,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":5}],"types":[{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}
            """,
        )
        env = builder.env
        groups = [env[n].group for n in ("MyTrue", "MyTrue.intro", "MyTrue.rec")]
        assert groups == [0, 0, 0]
        assert sorted(env[n].index for n in ("MyTrue", "MyTrue.intro", "MyTrue.rec")) == [0, 1, 2]
