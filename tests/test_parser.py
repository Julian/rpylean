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
from rpylean.parser import EnvironmentBuilder
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


def test_metadata_format_takes_precedence_over_exporter():
    # Key order must not let `exporter.version` (e.g. Lean 4.35.0) overwrite
    # `format.version` (3.1.0), nor let a matching `exporter.version` mask a
    # mismatched `format.version`.
    for line in (
        '{"meta":{"exporter":{"name":"leanexport","version":"4.35.0"},"format":{"version":"3.1.0"}}}\n',
        '{"meta":{"format":{"version":"3.1.0"},"exporter":{"name":"leanexport","version":"4.35.0"}}}\n',
        '{"meta":{"format":{},"exporter":{"name":"leanexport","version":"4.35.0"}}}\n',
        '{"meta":{"format":{"version":"3.1.0"},"exporter":"leanexport"}}\n',
        '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"}}}\n',
        '{"meta":{}}\n',
        '{}\n',
    ):
        parser.validate_export_metadata(StringIO(line))

    for bad in (
        '{"meta":{"format":{"version":"2.0.0"},"exporter":{"name":"lean4export","version":"3.1.0"}}}\n',
        '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"2.0.0"}}}\n',
        '{"meta":{"exporter":{"name":"lean4export","version":"2.0.0"}}}\n',
    ):
        with pytest.raises(parser.ExportVersionError) as exc:
            parser.validate_export_metadata(StringIO(bad))
        assert exc.value.got == "2.0.0"


def test_totally_empty():
    with pytest.raises(parser.ExportVersionError):
        parser.validate_export_metadata(StringIO(""))


def test_mdata_unwraps_inner_expr_and_prescans():
    body = "\n".join([
        '{"in":1,"str":{"pre":0,"str":"P"}}',
        '{"il":1,"succ":0}',
        '{"ie":0,"sort":1}',
        '{"ie":1,"mdata":{"data":{"float":1.5,"exp":-2e+3,"flag":true,"nil":null,"arr":[1,false],"nested":{"esc\\"k":"v"}},"expr":0}}',
        '{"mdata":{"expr":1,"data":{}},"ie":2}',
        '{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":2}}',
    ]) + "\n"

    expected = EnvironmentBuilder()
    expected.start_scan()
    expected.consume(StringIO(body))
    got_rc = parser.prescan_refcounts(StringIO(body))
    assert got_rc == expected._refcount

    b = EnvironmentBuilder()
    b.set_refcount(got_rc)
    b.consume(StringIO(body))
    assert len(b.declarations) == 1
    assert b.declarations[0].name == Name.simple("P")
    assert b.declarations[0].type == b.levels[1].sort()

    got_rc.free()
    expected._refcount.free()


def test_mdata_missing_expr_rejected():
    from rpylean.exceptions import MalformedLine

    with pytest.raises(MalformedLine):
        parse('{"ie":0,"mdata":{"data":{}}}')
    with pytest.raises(MalformedLine):
        parser.prescan_refcounts(StringIO('{"ie":0,"mdata":{"data":{}}}\n'))


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


def test_prescan_refcounts_matches_scan_builder():
    body = "\n".join([
        '{"in":1,"str":{"pre":0,"str":"MyTrue"}}',
        '{"in":2,"str":{"pre":1,"str":"intro"}}',
        '{"in":3,"str":{"pre":1,"str":"rec"}}',
        '{"in":4,"str":{"pre":0,"str":"x"}}',
        '{"in":5,"str":{"pre":0,"str":"d"}}',
        '{"in":6,"str":{"pre":0,"str":"t"}}',
        '{"il":1,"succ":0}',
        '{"ie":0,"sort":0}',
        '{"const":{"name":1,"us":[]},"ie":1}',
        '{"bvar":0,"ie":2}',
        '{"app":{"arg":2,"fn":1},"ie":3}',
        '{"ie":4,"lam":{"binderInfo":"default","body":3,"name":4,"type":1}}',
        '{"forallE":{"binderInfo":"implicit","body":3,"name":4,"type":1},"ie":5}',
        '{"ie":6,"letE":{"body":2,"name":4,"nondep":false,"type":1,"value":3}}',
        '{"ie":7,"proj":{"idx":0,"struct":3,"typeName":1}}',
        '{"ie":8,"natVal":"42"}',
        '{"ie":9,"strVal":"hello \\"type\\":1"}',
        # Whitespace + reordered keys fallback
        ' { "ie" : 10 , "app" : { "fn" : 4 , "arg" : 5 } } ',
        '{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":1}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[],"name":3,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[{"ctor":2,"nfields":0,"rhs":4}],"type":5}],"types":[{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}',
        '{"def":{"all":[5],"hints":{"regular":1},"levelParams":[],"name":5,"safety":"safe","type":5,"value":6}}',
        '{"thm":{"levelParams":[],"name":6,"type":0,"value":7}}',
    ]) + "\n"
    expected = EnvironmentBuilder()
    expected.start_scan()
    expected.consume(StringIO(body))
    got = parser.prescan_refcounts(StringIO(body))
    assert got == expected._refcount
    got.free()
    expected._refcount.free()


class _TinyChunkStream(object):
    def __init__(self, data, step):
        self._data = data
        self._pos = 0
        self._step = step

    def read(self, n):
        end = self._pos + self._step
        if end > len(self._data):
            end = len(self._data)
        chunk = self._data[self._pos:end]
        self._pos = end
        return chunk


def test_chunked_consume_and_prescan_boundary_splits():
    body = (
        '{"in":1,"str":{"pre":0,"str":"P"}}\r\n'
        '{"ie":0,"sort":0}\r\n'
        '{"const":{"name":1,"us":[]},"ie":1}\n'
        '{"axiom":{"levelParams":[],"name":1,"type":0}}'
    )
    for step in (1, 2, 7, 19, 37, 4096):
        rc = parser.prescan_refcounts(_TinyChunkStream(body, step))
        b = EnvironmentBuilder()
        b.set_refcount(rc)
        b.consume(_TinyChunkStream(body, step))
        assert len(b.declarations) == 1
        assert b.declarations[0].name == Name.simple("P")
        rc.free()


def test_compact_fast_paths_all_record_kinds():
    """Verify word-matched compact parse and prescan match general parser across
    all canonical lean4export 3.1.0 record formats (including thm with 'all',
    def hints/safety/mutual, opaque, strVal, in:str/num, il, letE, proj, etc.)."""
    body = "\n".join([
        '{"in":1,"str":{"pre":0,"str":"T"}}',
        '{"in":2,"str":{"pre":1,"str":"x"}}',
        '{"in":3,"num":{"i":7,"pre":1}}',
        '{"in":4,"str":{"pre":0,"str":"d1"}}',
        '{"in":5,"str":{"pre":0,"str":"d2"}}',
        '{"in":6,"str":{"pre":0,"str":"d3"}}',
        '{"in":7,"str":{"pre":0,"str":"t1"}}',
        '{"in":8,"str":{"pre":0,"str":"t2"}}',
        '{"in":9,"str":{"pre":0,"str":"op1"}}',
        '{"in":10,"str":{"pre":0,"str":"op2"}}',
        '{"in":11,"str":{"pre":0,"str":"u"}}',
        '{"in":12,"str":{"pre":0,"str":"v"}}',
        '{"in":13,"str":{"pre":0,"str":"esc\\"name"}}',
        '{"il":1,"param":11}',
        '{"il":2,"param":12}',
        '{"il":3,"succ":1}',
        '{"il":4,"max":[1,2]}',
        '{"il":5,"imax":[3,4]}',
        '{"ie":0,"sort":0}',
        '{"ie":1,"sort":5}',
        '{"bvar":0,"ie":2}',
        '{"const":{"name":1,"us":[]},"ie":3}',
        '{"const":{"name":1,"us":[1]},"ie":4}',
        '{"const":{"name":1,"us":[1,2]},"ie":5}',
        '{"const":{"name":1,"us":[1,2,3]},"ie":6}',
        '{"app":{"arg":2,"fn":3},"ie":7}',
        '{"ie":8,"lam":{"binderInfo":"default","body":7,"name":2,"type":0}}',
        '{"ie":9,"lam":{"binderInfo":"implicit","body":7,"name":2,"type":0}}',
        '{"ie":10,"lam":{"binderInfo":"instImplicit","body":7,"name":2,"type":0}}',
        '{"ie":11,"lam":{"binderInfo":"strictImplicit","body":7,"name":2,"type":0}}',
        '{"forallE":{"binderInfo":"default","body":7,"name":2,"type":0},"ie":12}',
        '{"forallE":{"binderInfo":"instImplicit","body":7,"name":2,"type":0},"ie":13}',
        '{"ie":14,"letE":{"body":2,"name":2,"nondep":false,"type":0,"value":3}}',
        '{"ie":15,"letE":{"body":2,"name":2,"nondep":true,"type":0,"value":3}}',
        '{"ie":16,"proj":{"idx":1,"struct":7,"typeName":1}}',
        '{"ie":17,"natVal":"123456"}',
        '{"ie":18,"strVal":"plain_text"}',
        '{"ie":19,"strVal":"escaped \\"quote\\""}',
        '{"def":{"all":[4],"hints":"abbrev","levelParams":[],"name":4,"safety":"safe","type":0,"value":8}}',
        '{"def":{"all":[5,6],"hints":{"regular":42},"levelParams":[11],"name":5,"safety":"partial","type":0,"value":9}}',
        '{"def":{"all":[5,6],"hints":"opaque","levelParams":[11,12],"name":6,"safety":"unsafe","type":0,"value":10}}',
        '{"thm":{"all":[7],"levelParams":[],"name":7,"type":0,"value":11}}',
        '{"thm":{"levelParams":[11],"name":8,"type":12,"value":13}}',
        '{"opaque":{"all":[9],"isUnsafe":false,"levelParams":[],"name":9,"type":14,"value":15}}',
        '{"opaque":{"isUnsafe":true,"levelParams":[11],"name":10,"type":16,"value":18}}',
    ]) + "\n"
    # Verify prescan_refcounts matches scanning builder identically
    expected = EnvironmentBuilder()
    expected.start_scan()
    expected.consume(StringIO(body))
    got_rc = parser.prescan_refcounts(StringIO(body))
    assert got_rc == expected._refcount

    # Verify compact-parsed builder matches general-parsed builder identically
    b_compact = EnvironmentBuilder()
    b_compact.set_refcount(got_rc)
    b_compact.consume(StringIO(body))

    b_general = EnvironmentBuilder()
    for line in body.splitlines():
        cur = parser.LineCursor(line)
        parser.parse_cursor_general(cur, b_general)

    assert len(b_compact.declarations) == len(b_general.declarations) == 7
    assert b_compact.names == b_general.names
    assert b_compact.levels == b_general.levels
    for d1, d2 in zip(b_compact.declarations, b_general.declarations):
        assert d1.name == d2.name
        assert d1.levels == d2.levels
        assert d1.safety == d2.safety
        assert d1.type == d2.type
        assert d1.group == d2.group
    assert b_compact.env["d1"].w_kind.all is None
    assert b_compact.env["d2"].w_kind.all == [Name.simple("d2"), Name.simple("d3")]
    assert b_compact.env["d2"].w_kind.hint == 42
    assert b_compact.env["op1"].is_unsafe() is False
    assert b_compact.env["op2"].is_unsafe() is True
    assert b_general.exprs[18] == W_LitStr("plain_text")
    assert b_general.exprs[19] == W_LitStr('escaped "quote"')
    # Also verify every unescaped compact line stays on the fast path (no fallback)
    unescaped_lines = [l for l in body.splitlines() if '\\' not in l]
    compact_chunk = "\n".join(unescaped_lines) + "\n"
    rc_fast = parser.RefCountTable(64)
    assert parser._prescan_chunk_fast(
        compact_chunk, 0, len(compact_chunk), rc_fast,
    ) == len(compact_chunk)
    b_fast = EnvironmentBuilder()
    assert parser._parse_chunk_fast(
        compact_chunk, 0, len(compact_chunk), b_fast, False,
    ) == len(compact_chunk)
    rc_fast.free()
    got_rc.free()
    expected._refcount.free()


def test_prescan_malformed_const_does_not_cross_newline():
    """Regression: malformed compact `const` missing `]` must fall back cleanly
    instead of scanning past `\\n` into the next line."""
    from rpylean.exceptions import MalformedLine

    bad = (
        '{"const":{"name":1,"us":[1}\n'
        '{"const":{"name":2,"us":[]},"ie":0}\n'
    )
    with pytest.raises(MalformedLine):
        parser.prescan_refcounts(StringIO(bad))


def test_mutual_inductive_wires_recursors():
    """Regression: mutual inductive block members must wire both constructors
    and recursors back onto each `W_Inductive`."""
    builder = parse(
        """
        {"in":1,"str":{"pre":0,"str":"Even"}}
        {"in":2,"str":{"pre":0,"str":"Odd"}}
        {"in":3,"str":{"pre":1,"str":"zero"}}
        {"in":4,"str":{"pre":2,"str":"succ"}}
        {"in":5,"str":{"pre":1,"str":"rec"}}
        {"ie":0,"sort":0}
        {"const":{"name":1,"us":[]},"ie":1}
        {"const":{"name":2,"us":[]},"ie":2}
        {"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":3,"numFields":0,"numParams":0,"type":1},{"cidx":0,"induct":2,"isUnsafe":false,"levelParams":[],"name":4,"numFields":0,"numParams":0,"type":2}],"recs":[{"all":[1,2],"isUnsafe":false,"k":false,"levelParams":[],"name":5,"numIndices":0,"numMinors":0,"numMotives":2,"numParams":0,"rules":[],"type":0}],"types":[{"all":[1,2],"ctors":[3],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0},{"all":[1,2],"ctors":[4],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":2,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}
        """,
    )
    env = builder.env
    even = env["Even"].w_kind
    odd = env["Odd"].w_kind
    rec = env["Even.rec"]
    assert [c.name for c in even.constructors] == [Name.from_str("Even.zero")]
    assert [c.name for c in odd.constructors] == [Name.from_str("Odd.succ")]
    assert even.recursors == [rec]
    assert odd.recursors == [rec]


def test_disc_first_expr_with_spaces_around_colon():
    builder = parse(' { "bvar" : 3 , "ie" : 0 } ')
    assert builder.exprs == [W_BVar(id=3)]


def test_swar_read_and_skip_uint_edge_cases():
    # Cover 1..10 digits, leading zeros, all delimiter byte classes (<0x30,
    # 0x3A..0x7F, 0x80..0xFF), and near-EOF lengths (p + 8 > end).
    cases = [
        ("0,xxxxxxx", 0, 1),
        ("9}xxxxxxx", 9, 1),
        ("42,xxxxxx", 42, 2),
        ("123}xxxxx", 123, 3),
        ("9876,xxxx", 9876, 4),
        ("54321}xxx", 54321, 5),
        ("123456,xx", 123456, 6),
        ("7654321}x", 7654321, 7),
        ("12345678,", 12345678, 8),
        ("99999999}", 99999999, 8),
        ("123456789,", 123456789, 9),
        ("1234567890}", 1234567890, 10),
        ("0007,xxxx", 7, 4),
        # Near-EOF (< 8 bytes remaining)
        ("0", 0, 1),
        ("7}", 7, 1),
        ("1234567", 1234567, 7),
        ("12345678", 12345678, 8),
        # High-bit & low-byte delimiters right after digits
        ("5\x00xxxxxxx", 5, 1),
        ("5\x2fxxxxxxx", 5, 1),
        ("5\x3axxxxxxx", 5, 1),
        ("5\x7fxxxxxxx", 5, 1),
        ("5\x80xxxxxxx", 5, 1),
        ("5\xafxxxxxxx", 5, 1),
        ("5\xb0xxxxxxx", 5, 1),
        ("5\xffxxxxxxx", 5, 1),
        ("123\xff56789", 123, 3),
    ]
    for buf, expected_val, expected_pos in cases:
        val, pos = parser._read_uint(buf, 0, len(buf))
        assert (val, pos) == (expected_val, expected_pos), (buf, val, pos)
        spos = parser._skip_uint(buf, 0, len(buf))
        assert spos == expected_pos, (buf, spos)

    # Non-digit at offset 0 across every byte value outside '0'..'9'
    for b in range(256):
        if 48 <= b <= 57:
            continue
        buf = chr(b) + "12345678"
        assert parser._read_uint(buf, 0, len(buf)) == (-1, 0), hex(b)
        assert parser._skip_uint(buf, 0, len(buf)) == -1, hex(b)
    assert parser._read_uint("", 0, 0) == (-1, 0)
    assert parser._skip_uint("", 0, 0) == -1


def test_swar_find_nl_every_offset():
    for off in range(17):
        buf = ("a" * off) + "\n" + ("b" * 16)
        assert parser._find_nl(buf, 0, len(buf)) == off + 1
    buf_no_nl = "x" * 20
    assert parser._find_nl(buf_no_nl, 0, len(buf_no_nl)) == len(buf_no_nl)
