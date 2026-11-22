"""
Parse lean4export NDJSON exports directly into an EnvironmentBuilder.

See https://ammkrn.github.io/type_checking_in_lean4/export_format.html

Each line is a self-describing record (a name, a level, an expression, or
a declaration). We walk the bytes of each line directly via ``LineCursor``
and call ``builder.register_X`` immediately — no intermediate AST nodes,
no JSON tree, no per-line ``compile()`` step.
"""

from __future__ import print_function

from StringIO import StringIO
import sys
from textwrap import dedent

from rpython.rlib.objectmodel import always_inline, dont_inline, newlist_hint, we_are_translated
from rpython.rlib.rarithmetic import r_uint
from rpython.rlib.rbigint import rbigint
from rpython.rtyper.annlowlevel import llstr
from rpython.rtyper.lltypesystem import llmemory, lltype, rffi
from rpython.rtyper.lltypesystem.lloperation import llop
from rpython.rtyper.lltypesystem.rstr import STR

from rpylean import objects
from rpylean._line_parser import LineCursor
from rpylean.exceptions import ExportError, MalformedLine, ReflexiveKError


_RC_U32_ARRAY = rffi.CArray(rffi.UINT)


class RefCountTable(object):
    """
    Unmanaged 32-bit expression reference-count table (4 bytes/slot, zero GC
    pressure). Pre-sized from file length to avoid resize/memmove churn on
    large exports, and explicitly freed after streaming completes.
    """

    _attrs_ = ['data', 'length', 'cap', '_freed']

    def __init__(self, initial_cap=4096):
        cap = initial_cap if initial_cap >= 64 else 64
        self.data = lltype.malloc(_RC_U32_ARRAY, cap, flavor='raw', zero=True)
        self.length = 0
        self.cap = cap
        self._freed = False

    @dont_inline
    def _grow(self, min_cap):
        cap = self.cap
        while cap < min_cap:
            cap *= 2
        new_data = lltype.malloc(_RC_U32_ARRAY, cap, flavor='raw', zero=True)
        used = self.length
        if used > 0:
            if we_are_translated():
                rffi.c_memcpy(
                    rffi.cast(rffi.VOIDP, new_data),
                    rffi.cast(rffi.CONST_VOIDP, self.data),
                    used * rffi.sizeof(rffi.UINT),
                )
            else:
                i = 0
                while i < used:
                    new_data[i] = self.data[i]
                    i += 1
        lltype.free(self.data, flavor='raw')
        self.data = new_data
        self.cap = cap

    @dont_inline
    def _ensure_slow(self, idx):
        if idx < 0:
            raise MalformedLine("negative expr index")
        if idx >= self.cap:
            self._grow(idx + 1)
        self.length = idx + 1

    @always_inline
    def ensure(self, idx):
        if r_uint(idx) >= r_uint(self.length):
            if idx == self.length and idx < self.cap:
                self.length = idx + 1
            else:
                self._ensure_slow(idx)

    @dont_inline
    def _bump_slow(self, idx):
        self._ensure_slow(idx)
        self.data[idx] = rffi.cast(
            rffi.UINT, rffi.cast(lltype.Signed, self.data[idx]) + 1,
        )

    @always_inline
    def bump(self, idx):
        if r_uint(idx) < r_uint(self.length):
            self.data[idx] = rffi.cast(
                rffi.UINT, rffi.cast(lltype.Signed, self.data[idx]) + 1,
            )
        else:
            self._bump_slow(idx)

    @always_inline
    def set_zero(self, idx):
        self.ensure(idx)
        self.data[idx] = rffi.cast(rffi.UINT, 0)

    @always_inline
    def dec(self, idx):
        c = rffi.cast(lltype.Signed, self.data[idx])
        assert c > 0
        c -= 1
        self.data[idx] = rffi.cast(rffi.UINT, c)
        return c

    def free(self):
        if not self._freed:
            lltype.free(self.data, flavor='raw')
            self._freed = True

    def __eq__(self, other):
        if not isinstance(other, RefCountTable):
            return NotImplemented
        if self.length != other.length:
            return False
        i = 0
        n = self.length
        while i < n:
            if (rffi.cast(lltype.Signed, self.data[i])
                    != rffi.cast(lltype.Signed, other.data[i])):
                return False
            i += 1
        return True

    def __ne__(self, other):
        if not isinstance(other, RefCountTable):
            return NotImplemented
        return not (self == other)


EXPORT_VERSION = "3.1.0"


class ExportVersionError(ExportError):
    """
    The export file version doesn't match one we know how to parse.
    """

    _attrs_ = ['got']

    def __init__(self, got):
        self.got = got

    def tokens(self):
        from rpylean._tokens import ERROR

        return [
            ERROR.emit(
                "Expected export format version %s but got %s"
                % (
                    EXPORT_VERSION,
                    "no export metadata" if self.got is None else self.got,
                )
            ),
        ]


# ---- Public entry points -------------------------------------------------

def from_str(text):
    """
    Parse a lean4export-formatted string (no metadata header) into a fresh
    ``EnvironmentBuilder`` and return it.
    """
    from rpylean.environment import EnvironmentBuilder

    return EnvironmentBuilder().consume(StringIO(dedent(text).strip()))


def validate_export_metadata(stream):
    """
    Read and validate the metadata line of an export. Raises
    ``ExportVersionError`` on mismatch.

    A metadata line carrying no version at all (e.g. the bare ``{}``
    of hand-written arena fixtures) is accepted: only an explicitly
    different version is grounds for rejecting the export.
    """
    line = stream.readline()
    if not line:
        raise ExportVersionError(None)
    version = _parse_metadata_version(line)
    if version != "" and version != EXPORT_VERSION:
        raise ExportVersionError(version)


# ---- Per-line dispatch ---------------------------------------------------

def parse_line(line, builder):
    """
    Parse a single lean4export NDJSON line and apply it to ``builder``
    via the appropriate ``register_*`` call.
    """
    cursor = LineCursor(line)
    parse_cursor(cursor, builder)


_IS_LITTLE_ENDIAN = sys.byteorder == "little"
_IS_64BIT = sys.maxint > 2147483647
_USE_FAST_WORDS = _IS_LITTLE_ENDIAN and _IS_64BIT
_STR_BASE_OFS = (
    llmemory.offsetof(STR, 'chars') + llmemory.itemoffsetof(STR.chars, 0)
)
_CHAR_SCALE = llmemory.sizeof(lltype.Char)


def _w2(s):
    assert len(s) == 2
    return r_uint(ord(s[0])) | (r_uint(ord(s[1])) << 8)


def _w4(s):
    assert len(s) == 4
    return (
        r_uint(ord(s[0]))
        | (r_uint(ord(s[1])) << 8)
        | (r_uint(ord(s[2])) << 16)
        | (r_uint(ord(s[3])) << 24)
    )


def _w6(s):
    assert len(s) == 6
    if not _IS_64BIT:
        return r_uint(0)
    return (
        r_uint(ord(s[0]))
        | (r_uint(ord(s[1])) << 8)
        | (r_uint(ord(s[2])) << 16)
        | (r_uint(ord(s[3])) << 24)
        | (r_uint(ord(s[4])) << 32)
        | (r_uint(ord(s[5])) << 40)
    )


def _w8(s):
    assert len(s) == 8
    if not _IS_64BIT:
        return r_uint(0)
    return (
        r_uint(ord(s[0]))
        | (r_uint(ord(s[1])) << 8)
        | (r_uint(ord(s[2])) << 16)
        | (r_uint(ord(s[3])) << 24)
        | (r_uint(ord(s[4])) << 32)
        | (r_uint(ord(s[5])) << 40)
        | (r_uint(ord(s[6])) << 48)
        | (r_uint(ord(s[7])) << 56)
    )


_MASK48 = r_uint(0xffffffffffff) if _IS_64BIT else r_uint(0)
_U64_NL = r_uint(0x0a0a0a0a0a0a0a0a) if _IS_64BIT else r_uint(0)
_U64_01 = r_uint(0x0101010101010101) if _IS_64BIT else r_uint(0)
_U64_80 = r_uint(0x8080808080808080) if _IS_64BIT else r_uint(0)

# Compile-time packed little-endian word literals for canonical compact lines.
_W8_APP_0 = _w8('{"app":{')
_W8_APP_1 = _w8(':{"arg":')
_W4_FN_0 = _w4(',"fn')
_W2_COLON = _w2('":')
_W4_IE_0 = _w4('},"i')
_W4_IE_1 = _w4('ie":')

_W6_IE = _w6('{"ie":')
_W6_IN = _w6('{"in":')
_W6_IL = _w6('{"il":')

_W8_LAM_0 = _w8(',"lam":{')
_W8_LAM_1 = _w8('"binderI')
_W8_LAM_2 = _w8('rInfo":"')

_W8_FORALL_0 = _w8('{"forall')
_W8_FORALL_1 = _w8('E":{"bin')
_W8_FORALL_2 = _w8('derInfo"')
_W2_COL_Q = _w2(':"')

_W8_BINFO_DEF = _w8('default"')
_W8_BINFO_IMP = _w8('implicit')
_W8_BINFO_INST0 = _w8('instImpl')
_W8_BINFO_INST1 = _w8('mplicit"')
_W8_BINFO_STR0 = _w8('strictIm')

_W8_BODY = _w8(',"body":')
_W8_NAME = _w8(',"name":')
_W8_TYPE = _w8(',"type":')
_W8_VAL0 = _w8(',"value"')

_W8_CONST_0 = _w8('{"const"')
_W8_CONST_1 = _w8(':{"name"')
_W4_US_0 = _w4(',"us')
_W4_US_1 = _w4('s":[')

_W8_IN_STR_0 = _w8(',"str":{')
_W8_IN_STR_1 = _w8(':{"pre":')
_W8_IN_STR_2 = _w8(',"str":"')
_W8_IN_NUM_0 = _w8(',"num":{')
_W4_IN_NUM_1 = _w4('"i":')
_W4_PRE_0 = _w4(',"pr')
_W4_PRE_1 = _w4('re":')
_W2_CLOSE2 = _w2('}}')

_W8_THM_0 = _w8('{"thm":{')
_W8_DEF_0 = _w8('{"def":{')
_W8_OPQ_0 = _w8('{"opaque')
_W4_OPQ_1 = _w4('e":{')
_W4_ALL_0 = _w4('"all')
_W4_ALL_1 = _w4('l":[')
_W8_LPAR_0 = _w8('"levelPa')
_W8_LPAR_1 = _w8('arams":[')
_W8_CLPAR_0 = _w8(',"levelP')
_W8_CLPAR_1 = _w8('Params":')

_W8_HINTS_0 = _w8(',"hints"')
_W8_H_ABBREV = _w8('"abbrev"')
_W8_H_OPAQUE = _w8('"opaque"')
_W8_H_REG_0 = _w8('{"regula')
_W4_H_REG_1 = _w4('ar":')
_W8_SAF_0 = _w8(',"safety')
_W4_SAF_1 = _w4('y":"')
_W4_SAFE = _w4('safe')
_W8_PARTIAL = _w8('partial"')
_W4_UNSA = _w4('unsa')
_W4_AFE_Q = _w4('afe"')

_W8_ISUN_0 = _w8('"isUnsaf')
_W4_ISUN_1 = _w4('fe":')
_W4_ALSE = _w4('alse')
_W4_TRUE = _w4('true')

_W8_BVAR_0 = _w8('{"bvar":')
_W4_BVAR_IE0 = _w4(',"ie')
_W8_SORT = _w8(',"sort":')
_W8_LETE_0 = _w8(',"letE":')
_W8_LETE_1 = _w8('{"body":')
_W8_NDEP_0 = _w8(',"nondep')
_W8_NDEP_F = _w8('":false,')
_W8_NDEP_T = _w8('":true,"')
_W8_PROJ_0 = _w8(',"proj":')
_W8_PROJ_1 = _w8(':{"idx":')
_W8_STRUCT_0 = _w8(',"struct')
_W4_STRUCT_1 = _w4('ct":')
_W8_TNAME_0 = _w8(',"typeNa')
_W4_TNAME_1 = _w4('me":')
_W8_STRV_0 = _w8(',"strVal')
_W8_NATV_0 = _w8(',"natVal')
_W4_VAL_Q = _w4('l":"')

_W8_SUCC = _w8(',"succ":')
_W8_PARAM_0 = _w8(',"param"')
_W8_MAX = _w8(',"max":[')
_W8_IMAX_0 = _w8(',"imax":')


@always_inline
def _load_u64(s, p):
    if we_are_translated():
        lls = llstr(s)
        return llop.gc_load_indexed(
            lltype.Unsigned,
            lltype.cast_opaque_ptr(llmemory.GCREF, lls),
            p,
            _CHAR_SCALE,
            _STR_BASE_OFS,
        )
    return (
        r_uint(ord(s[p]))
        | (r_uint(ord(s[p + 1])) << 8)
        | (r_uint(ord(s[p + 2])) << 16)
        | (r_uint(ord(s[p + 3])) << 24)
        | (r_uint(ord(s[p + 4])) << 32)
        | (r_uint(ord(s[p + 5])) << 40)
        | (r_uint(ord(s[p + 6])) << 48)
        | (r_uint(ord(s[p + 7])) << 56)
    )


@always_inline
def _load_u32(s, p):
    if we_are_translated():
        lls = llstr(s)
        return rffi.cast(
            lltype.Unsigned,
            llop.gc_load_indexed(
                rffi.UINT,
                lltype.cast_opaque_ptr(llmemory.GCREF, lls),
                p,
                _CHAR_SCALE,
                _STR_BASE_OFS,
            ),
        )
    return (
        r_uint(ord(s[p]))
        | (r_uint(ord(s[p + 1])) << 8)
        | (r_uint(ord(s[p + 2])) << 16)
        | (r_uint(ord(s[p + 3])) << 24)
    )


@always_inline
def _load_u16(s, p):
    if we_are_translated():
        lls = llstr(s)
        return rffi.cast(
            lltype.Unsigned,
            llop.gc_load_indexed(
                rffi.USHORT,
                lltype.cast_opaque_ptr(llmemory.GCREF, lls),
                p,
                _CHAR_SCALE,
                _STR_BASE_OFS,
            ),
        )
    return r_uint(ord(s[p])) | (r_uint(ord(s[p + 1])) << 8)


@always_inline
def _load_u8(s, p):
    if we_are_translated():
        lls = llstr(s)
        return rffi.cast(
            lltype.Signed,
            llop.gc_load_indexed(
                rffi.UCHAR,
                lltype.cast_opaque_ptr(llmemory.GCREF, lls),
                p,
                _CHAR_SCALE,
                _STR_BASE_OFS,
            ),
        )
    return ord(s[p])


@always_inline
def _find_nl(line, p, end):
    """Return the index right after the next '\\n' in line[p:end], or ``end``."""
    while p + 8 <= end:
        x = _load_u64(line, p) ^ _U64_NL
        if ((x - _U64_01) & (~x) & _U64_80) != r_uint(0):
            break
        p += 8
    while p < end:
        if _load_u8(line, p) == 10:
            return p + 1
        p += 1
    return end


@always_inline
def _read_uint(line, p, end):
    if p >= end:
        return -1, p
    d = _load_u8(line, p) - 48
    if r_uint(d) > r_uint(9):
        return -1, p
    val = d
    p += 1
    while p < end:
        d = _load_u8(line, p) - 48
        if r_uint(d) > r_uint(9):
            break
        val = val * 10 + d
        p += 1
    return val, p


@always_inline
def _at_eol_pos(line, p, end):
    if p < end:
        c = _load_u8(line, p)
        if c == 10:
            return p + 1
        if c == 13 and p + 1 < end and _load_u8(line, p + 1) == 10:
            return p + 2
        return -1
    return p


@always_inline
def _match_binfo_at(line, p, end):
    if p + 8 > end:
        return -1, p
    w = _load_u64(line, p)
    if w == _W8_BINFO_DEF:
        return 0, p + 8
    if w == _W8_BINFO_IMP:
        if p + 9 <= end and _load_u8(line, p + 8) == 34:
            return 1, p + 9
    elif w == _W8_BINFO_INST0:
        if p + 13 <= end and _load_u64(line, p + 5) == _W8_BINFO_INST1:
            return 2, p + 13
    elif w == _W8_BINFO_STR0:
        if p + 15 <= end and _load_u64(line, p + 7) == _W8_BINFO_INST1:
            return 3, p + 15
    return -1, p


@always_inline
def _skip_uint_array(line, q, end):
    """Skip ``]`` or ``N(,N)*]`` starting just after ``[``.
    Returns position right after ``]``, or -1 on mismatch."""
    if q < end and _load_u8(line, q) == 93:
        return q + 1
    while True:
        v, q = _read_uint(line, q, end)
        if v < 0 or q >= end:
            return -1
        ch = _load_u8(line, q)
        if ch == 93:
            return q + 1
        if ch != 44:
            return -1
        q += 1


@always_inline
def _read_level_names(line, q, end, builder):
    """Read ``]`` or ``N(,N)*]`` of name indices into a list of Names."""
    if q < end and _load_u8(line, q) == 93:
        return objects._EMPTY_LEVEL_NAMES, q + 1
    levels = []
    while True:
        lidx, q = _read_uint(line, q, end)
        if lidx < 0 or q >= end:
            return None, -1
        levels.append(builder.names[lidx])
        ch = _load_u8(line, q)
        if ch == 93:
            return levels, q + 1
        if ch != 44:
            return None, -1
        q += 1


@always_inline
def _ref_expr_rc(exprs, rc_data, eidx):
    assert eidx >= 0
    e = exprs[eidx]
    assert e is not None
    c = rffi.cast(lltype.Signed, rc_data[eidx]) - 1
    assert c >= 0
    rc_data[eidx] = rffi.cast(rffi.UINT, c)
    if c == 0:
        exprs[eidx] = None
    return e


@always_inline
def _reg_expr_rc(builder, exprs, eidx, w_expr):
    if eidx == len(exprs):
        exprs.append(w_expr)
    else:
        builder.register_expr(eidx, w_expr)


@always_inline
def _ref_expr_fast(builder, eidx):
    counts = builder._refcount
    if counts is None:
        e = builder.exprs[eidx]
        assert e is not None
        return e
    if builder._scanning:
        return builder.ref_expr(eidx)
    e = builder.exprs[eidx]
    assert e is not None
    if counts.dec(eidx) == 0:
        builder.exprs[eidx] = None
    return e


@always_inline
def _binder_from_code(name, code, type):
    return objects.Binder(name, type, style=code)


@dont_inline
def _try_parse_compact_rare(line, pos, end, builder):
    """Compact word-matched parser for non-app/lam/forallE canonical records:
    ordered by frequency: ``in``, ``const``, ``thm``, ``ie:*``, ``def``,
    ``opaque``, ``il``, ``bvar``.

    Returns an integer ``(next_pos << 1) | (1 if is_decl else 0)`` on match
    (zero tuple allocation), or ``-1`` to fall back to ``parse_cursor_general``.
    """
    if pos + 8 > end:
        return -1
    w0 = _load_u64(line, pos)
    w6 = w0 & _MASK48
    if w6 == _W6_IN:
        # {"in":N,"str":{"pre":P,"str":"..."}} or {"in":N,"num":{"i":I,"pre":P}}
        nidx, q = _read_uint(line, pos + 6, end)
        if nidx >= 0 and q + 12 <= end:
            dw = _load_u64(line, q)
            if (dw == _W8_IN_STR_0 and q + 14 <= end
                    and _load_u64(line, q + 6) == _W8_IN_STR_1):
                pre, q = _read_uint(line, q + 14, end)
                if pre >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_IN_STR_2:
                    s = q + 8
                    q = s
                    while q < end:
                        ch = _load_u8(line, q)
                        if ch == 34:
                            break
                        if ch == 92 or ch == 10:
                            q = -1
                            break
                        q += 1
                    if (q >= 0 and q + 3 <= end and _load_u8(line, q) == 34
                            and _load_u16(line, q + 1) == _W2_CLOSE2):
                        np = _at_eol_pos(line, q + 3, end)
                        if np >= 0:
                            assert s >= 0 and q >= s
                            builder.register_name(
                                nidx, builder.names[pre].child(line[s:q]),
                            )
                            return np << 1
            elif dw == _W8_IN_NUM_0 and _load_u32(line, q + 8) == _W4_IN_NUM_1:
                id_val, q = _read_uint(line, q + 12, end)
                if (id_val >= 0 and q + 7 <= end
                        and _load_u32(line, q) == _W4_PRE_0
                        and _load_u32(line, q + 3) == _W4_PRE_1):
                    pre, q = _read_uint(line, q + 7, end)
                    if (pre >= 0 and q + 2 <= end
                            and _load_u16(line, q) == _W2_CLOSE2):
                        np = _at_eol_pos(line, q + 2, end)
                        if np >= 0:
                            builder.register_name(
                                nidx,
                                builder.names[pre].num_child_int(id_val),
                            )
                            return np << 1
        return -1
    if w0 == _W8_CONST_0:
        # {"const":{"name":N,"us":[...]},"ie":E}
        if (pos + 17 <= end
                and _load_u64(line, pos + 8) == _W8_CONST_1
                and _load_u8(line, pos + 16) == 58):
            nidx, q = _read_uint(line, pos + 17, end)
            if (nidx >= 0 and q + 7 <= end
                    and _load_u32(line, q) == _W4_US_0
                    and _load_u32(line, q + 3) == _W4_US_1):
                q += 7
                if q < end and _load_u8(line, q) == 93:
                    q += 1
                    if (q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                builder.register_expr(
                                    eidx, builder.names[nidx].const_empty(),
                                )
                                return np << 1
                    return -1
                l0, q = _read_uint(line, q, end)
                if l0 < 0 or q >= end:
                    return -1
                ch = _load_u8(line, q)
                if ch == 93:
                    q += 1
                    if (q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                builder.register_expr(
                                    eidx,
                                    objects._mk_w_const1(
                                        builder.names[nidx],
                                        builder.levels[l0],
                                    ),
                                )
                                return np << 1
                    return -1
                if ch != 44:
                    return -1
                l1, q = _read_uint(line, q + 1, end)
                if l1 < 0 or q >= end:
                    return -1
                ch = _load_u8(line, q)
                if ch == 93:
                    q += 1
                    if (q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                builder.register_expr(
                                    eidx,
                                    objects._mk_w_const2(
                                        builder.names[nidx],
                                        builder.levels[l0],
                                        builder.levels[l1],
                                    ),
                                )
                                return np << 1
                    return -1
                if ch != 44:
                    return -1
                q += 1
                levels = [builder.levels[l0], builder.levels[l1]]
                while True:
                    lidx, q = _read_uint(line, q, end)
                    if lidx < 0 or q >= end:
                        return -1
                    levels.append(builder.levels[lidx])
                    ch = _load_u8(line, q)
                    if ch == 93:
                        q += 1
                        break
                    if ch != 44:
                        return -1
                    q += 1
                if (q + 7 <= end
                        and _load_u32(line, q) == _W4_IE_0
                        and _load_u32(line, q + 3) == _W4_IE_1):
                    eidx, q = _read_uint(line, q + 7, end)
                    if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                        np = _at_eol_pos(line, q + 1, end)
                        if np >= 0:
                            builder.register_expr(
                                eidx, builder.names[nidx].const(levels),
                            )
                            return np << 1
        return -1
    if w0 == _W8_THM_0:
        # {"thm":{"all":[...],"levelParams":[...],"name":N,"type":T,"value":V}}
        # (also accepts missing "all" key)
        q = pos + 8
        if (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                and _load_u32(line, q + 3) == _W4_ALL_1):
            q = _skip_uint_array(line, q + 7, end)
            if q < 0 or q >= end or _load_u8(line, q) != 44:
                return -1
            q += 1
        if (q + 15 <= end and _load_u64(line, q) == _W8_LPAR_0
                and _load_u64(line, q + 7) == _W8_LPAR_1):
            levels, q = _read_level_names(line, q + 15, end, builder)
            if levels is not None and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                name_idx, q = _read_uint(line, q + 8, end)
                if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                    type_eidx, q = _read_uint(line, q + 8, end)
                    if (type_eidx >= 0 and q + 9 <= end
                            and _load_u64(line, q) == _W8_VAL0
                            and _load_u8(line, q + 8) == 58):
                        value_eidx, q = _read_uint(line, q + 9, end)
                        if (value_eidx >= 0 and q + 2 <= end
                                and _load_u16(line, q) == _W2_CLOSE2):
                            np = _at_eol_pos(line, q + 2, end)
                            if np >= 0:
                                decl = builder.names[name_idx].theorem(
                                    levels=levels,
                                    type=_ref_expr_fast(builder, type_eidx),
                                    value=_ref_expr_fast(builder, value_eidx),
                                )
                                builder.register_declaration(decl)
                                return (np << 1) | 1
        return -1
    if w6 == _W6_IE:
        eidx, q = _read_uint(line, pos + 6, end)
        if eidx < 0 or q + 8 > end:
            return -1
        dw = _load_u64(line, q)
        if dw == _W8_LETE_0:
            # ,"letE":{"body":B,"name":N,"nondep":false|true,"type":T,"value":V}}
            if q + 16 <= end and _load_u64(line, q + 8) == _W8_LETE_1:
                body_eidx, q = _read_uint(line, q + 16, end)
                if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                    name_idx, q = _read_uint(line, q + 8, end)
                    if name_idx >= 0 and q + 22 <= end and _load_u64(line, q) == _W8_NDEP_0:
                        nw = _load_u64(line, q + 8)
                        if (nw == _W8_NDEP_F and q + 23 <= end
                                and _load_u64(line, q + 15) == _W8_TYPE):
                            q += 23
                        elif nw == _W8_NDEP_T and _load_u64(line, q + 14) == _W8_TYPE:
                            q += 22
                        else:
                            return -1
                        type_eidx, q = _read_uint(line, q, end)
                        if (type_eidx >= 0 and q + 9 <= end
                                and _load_u64(line, q) == _W8_VAL0
                                and _load_u8(line, q + 8) == 58):
                            value_eidx, q = _read_uint(line, q + 9, end)
                            if (value_eidx >= 0 and q + 2 <= end
                                    and _load_u16(line, q) == _W2_CLOSE2):
                                np = _at_eol_pos(line, q + 2, end)
                                if np >= 0:
                                    builder.register_expr(
                                        eidx,
                                        objects.W_Let(
                                            builder.names[name_idx],
                                            _ref_expr_fast(builder, type_eidx),
                                            _ref_expr_fast(builder, value_eidx),
                                            _ref_expr_fast(builder, body_eidx),
                                        ),
                                    )
                                    return np << 1
            return -1
        if dw == _W8_PROJ_0:
            # ,"proj":{"idx":I,"struct":S,"typeName":N}}
            if q + 15 <= end and _load_u64(line, q + 7) == _W8_PROJ_1:
                idx, q = _read_uint(line, q + 15, end)
                if (idx >= 0 and q + 10 <= end
                        and _load_u64(line, q) == _W8_STRUCT_0
                        and _load_u32(line, q + 6) == _W4_STRUCT_1):
                    struct_eidx, q = _read_uint(line, q + 10, end)
                    if (struct_eidx >= 0 and q + 12 <= end
                            and _load_u64(line, q) == _W8_TNAME_0
                            and _load_u32(line, q + 8) == _W4_TNAME_1):
                        tname_idx, q = _read_uint(line, q + 12, end)
                        if (tname_idx >= 0 and q + 2 <= end
                                and _load_u16(line, q) == _W2_CLOSE2):
                            np = _at_eol_pos(line, q + 2, end)
                            if np >= 0:
                                builder.register_expr(
                                    eidx,
                                    builder.names[tname_idx].proj(
                                        idx, _ref_expr_fast(builder, struct_eidx),
                                    ),
                                )
                                return np << 1
            return -1
        if dw == _W8_STRV_0:
            # ,"strVal":"..."}
            if q + 11 <= end and _load_u32(line, q + 7) == _W4_VAL_Q:
                s = q + 11
                q = s
                while q < end:
                    ch = _load_u8(line, q)
                    if ch == 34:
                        break
                    if ch == 92 or ch == 10:
                        return -1
                    q += 1
                if (q + 2 <= end and _load_u8(line, q) == 34
                        and _load_u8(line, q + 1) == 125):
                    np = _at_eol_pos(line, q + 2, end)
                    if np >= 0:
                        assert s >= 0 and q >= s
                        builder.register_expr(
                            eidx, objects._mk_w_litstr(line[s:q]),
                        )
                        return np << 1
            return -1
        if dw == _W8_SORT:
            # ,"sort":L}
            lidx, q = _read_uint(line, q + 8, end)
            if lidx >= 0 and q < end and _load_u8(line, q) == 125:
                np = _at_eol_pos(line, q + 1, end)
                if np >= 0:
                    builder.register_expr(eidx, builder.levels[lidx].sort())
                    return np << 1
            return -1
        if dw == _W8_NATV_0:
            # ,"natVal":"..."}
            if q + 11 <= end and _load_u32(line, q + 7) == _W4_VAL_Q:
                q2 = q + 11
                val = 0
                digits = 0
                while q2 < end and digits < 18:
                    dd = _load_u8(line, q2) - 48
                    if r_uint(dd) > r_uint(9):
                        break
                    val = val * 10 + dd
                    q2 += 1
                    digits += 1
                if (digits > 0 and q2 + 2 <= end
                        and _load_u8(line, q2) == 34
                        and _load_u8(line, q2 + 1) == 125):
                    np = _at_eol_pos(line, q2 + 2, end)
                    if np >= 0:
                        builder.register_expr(
                            eidx, objects._mk_w_litnat(rbigint.fromint(val)),
                        )
                        return np << 1
            return -1
        return -1
    if w0 == _W8_DEF_0:
        # {"def":{"all":[...],"hints":...,"levelParams":[...],"name":N,"safety":"...","type":T,"value":V}}
        q = pos + 8
        if not (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                and _load_u32(line, q + 3) == _W4_ALL_1):
            return -1
        q += 7
        all_names = None
        if q < end and _load_u8(line, q) == 93:
            q += 1
        else:
            a0, q = _read_uint(line, q, end)
            if a0 < 0 or q >= end:
                return -1
            ch = _load_u8(line, q)
            if ch == 93:
                q += 1
            elif ch == 44:
                all_names = [builder.names[a0]]
                q += 1
                while True:
                    ak, q = _read_uint(line, q, end)
                    if ak < 0 or q >= end:
                        return -1
                    all_names.append(builder.names[ak])
                    ch = _load_u8(line, q)
                    if ch == 93:
                        q += 1
                        break
                    if ch != 44:
                        return -1
                    q += 1
            else:
                return -1
        if not (q + 9 <= end and _load_u64(line, q) == _W8_HINTS_0
                and _load_u8(line, q + 8) == 58):
            return -1
        q += 9
        if q + 8 > end:
            return -1
        hw = _load_u64(line, q)
        if hw == _W8_H_ABBREV:
            hint = objects.HINT_ABBREV
            q += 8
        elif hw == _W8_H_OPAQUE:
            hint = objects.HINT_OPAQUE
            q += 8
        elif (hw == _W8_H_REG_0 and q + 11 <= end
                and _load_u32(line, q + 7) == _W4_H_REG_1):
            hint, q = _read_uint(line, q + 11, end)
            if hint < 0 or q >= end or _load_u8(line, q) != 125:
                return -1
            q += 1
        else:
            return -1
        if not (q + 16 <= end and _load_u64(line, q) == _W8_CLPAR_0
                and _load_u64(line, q + 7) == _W8_CLPAR_1
                and _load_u8(line, q + 15) == 91):
            return -1
        levels, q = _read_level_names(line, q + 16, end, builder)
        if levels is None or q + 8 > end or _load_u64(line, q) != _W8_NAME:
            return -1
        name_idx, q = _read_uint(line, q + 8, end)
        if (name_idx < 0 or q + 11 > end
                or _load_u64(line, q) != _W8_SAF_0
                or _load_u32(line, q + 7) != _W4_SAF_1):
            return -1
        q += 11
        if q + 5 <= end and _load_u32(line, q) == _W4_SAFE and _load_u8(line, q + 4) == 34:
            safety = objects.SAFETY_SAFE
            q += 5
        elif q + 8 <= end and _load_u64(line, q) == _W8_PARTIAL:
            safety = objects.SAFETY_PARTIAL
            q += 8
        elif (q + 7 <= end and _load_u32(line, q) == _W4_UNSA
                and _load_u32(line, q + 3) == _W4_AFE_Q):
            safety = objects.SAFETY_UNSAFE
            q += 7
        else:
            return -1
        if q + 8 > end or _load_u64(line, q) != _W8_TYPE:
            return -1
        type_eidx, q = _read_uint(line, q + 8, end)
        if (type_eidx < 0 or q + 9 > end
                or _load_u64(line, q) != _W8_VAL0
                or _load_u8(line, q + 8) != 58):
            return -1
        value_eidx, q = _read_uint(line, q + 9, end)
        if value_eidx < 0 or q + 2 > end or _load_u16(line, q) != _W2_CLOSE2:
            return -1
        np = _at_eol_pos(line, q + 2, end)
        if np < 0:
            return -1
        decl = builder.names[name_idx].definition(
            levels=levels,
            type=_ref_expr_fast(builder, type_eidx),
            value=_ref_expr_fast(builder, value_eidx),
            hint=hint,
            safety=safety,
            all=all_names,
        )
        builder.register_declaration(decl)
        return (np << 1) | 1
    if w0 == _W8_OPQ_0:
        # {"opaque":{"all":[...],"isUnsafe":false|true,"levelParams":[...],"name":N,"type":T,"value":V}}
        if pos + 11 <= end and _load_u32(line, pos + 7) == _W4_OPQ_1:
            q = pos + 11
            if (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                    and _load_u32(line, q + 3) == _W4_ALL_1):
                q = _skip_uint_array(line, q + 7, end)
                if q < 0 or q >= end or _load_u8(line, q) != 44:
                    return -1
                q += 1
            if (q + 11 <= end and _load_u64(line, q) == _W8_ISUN_0
                    and _load_u32(line, q + 7) == _W4_ISUN_1):
                q += 11
                if (q + 6 <= end and _load_u8(line, q) == 102
                        and _load_u32(line, q + 1) == _W4_ALSE
                        and _load_u8(line, q + 5) == 44):
                    is_unsafe = False
                    q += 6
                elif (q + 5 <= end and _load_u32(line, q) == _W4_TRUE
                        and _load_u8(line, q + 4) == 44):
                    is_unsafe = True
                    q += 5
                else:
                    return -1
                if (q + 15 <= end and _load_u64(line, q) == _W8_LPAR_0
                        and _load_u64(line, q + 7) == _W8_LPAR_1):
                    levels, q = _read_level_names(line, q + 15, end, builder)
                    if (levels is not None and q + 8 <= end
                            and _load_u64(line, q) == _W8_NAME):
                        name_idx, q = _read_uint(line, q + 8, end)
                        if (name_idx >= 0 and q + 8 <= end
                                and _load_u64(line, q) == _W8_TYPE):
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 9 <= end
                                    and _load_u64(line, q) == _W8_VAL0
                                    and _load_u8(line, q + 8) == 58):
                                value_eidx, q = _read_uint(line, q + 9, end)
                                if (value_eidx >= 0 and q + 2 <= end
                                        and _load_u16(line, q) == _W2_CLOSE2):
                                    np = _at_eol_pos(line, q + 2, end)
                                    if np >= 0:
                                        decl = builder.names[name_idx].opaque(
                                            levels=levels,
                                            type=_ref_expr_fast(builder, type_eidx),
                                            value=_ref_expr_fast(builder, value_eidx),
                                            is_unsafe=is_unsafe,
                                        )
                                        builder.register_declaration(decl)
                                        return (np << 1) | 1
        return -1
    if w6 == _W6_IL:
        # {"il":U,"succ":P | "param":N | "max":[L,R] | "imax":[L,R]}
        uidx, q = _read_uint(line, pos + 6, end)
        if uidx < 0 or q + 8 > end:
            return -1
        dw = _load_u64(line, q)
        if dw == _W8_SUCC:
            parent, q = _read_uint(line, q + 8, end)
            if parent >= 0 and q < end and _load_u8(line, q) == 125:
                np = _at_eol_pos(line, q + 1, end)
                if np >= 0:
                    builder.register_level(uidx, builder.levels[parent].succ())
                    return np << 1
        elif dw == _W8_PARAM_0 and q + 9 <= end and _load_u8(line, q + 8) == 58:
            nidx, q = _read_uint(line, q + 9, end)
            if nidx >= 0 and q < end and _load_u8(line, q) == 125:
                np = _at_eol_pos(line, q + 1, end)
                if np >= 0:
                    builder.register_level(
                        uidx, builder.names[nidx].as_level_param(),
                    )
                    return np << 1
        elif dw == _W8_MAX:
            lhs, q = _read_uint(line, q + 8, end)
            if lhs >= 0 and q < end and _load_u8(line, q) == 44:
                rhs, q = _read_uint(line, q + 1, end)
                if (rhs >= 0 and q + 2 <= end
                        and _load_u8(line, q) == 93
                        and _load_u8(line, q + 1) == 125):
                    np = _at_eol_pos(line, q + 2, end)
                    if np >= 0:
                        builder.register_level(
                            uidx,
                            objects.level_max(
                                builder.levels[lhs], builder.levels[rhs],
                            ),
                        )
                        return np << 1
        elif dw == _W8_IMAX_0 and q + 9 <= end and _load_u8(line, q + 8) == 91:
            lhs, q = _read_uint(line, q + 9, end)
            if lhs >= 0 and q < end and _load_u8(line, q) == 44:
                rhs, q = _read_uint(line, q + 1, end)
                if (rhs >= 0 and q + 2 <= end
                        and _load_u8(line, q) == 93
                        and _load_u8(line, q + 1) == 125):
                    np = _at_eol_pos(line, q + 2, end)
                    if np >= 0:
                        builder.register_level(
                            uidx,
                            objects.level_imax(
                                builder.levels[lhs], builder.levels[rhs],
                            ),
                        )
                        return np << 1
        return -1
    if w0 == _W8_BVAR_0:
        # {"bvar":B,"ie":E}
        bidx, q = _read_uint(line, pos + 8, end)
        if (bidx >= 0 and q + 6 <= end
                and _load_u32(line, q) == _W4_BVAR_IE0
                and _load_u16(line, q + 4) == _W2_COLON):
            eidx, q = _read_uint(line, q + 6, end)
            if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                np = _at_eol_pos(line, q + 1, end)
                if np >= 0:
                    builder.register_expr(eidx, objects._mk_w_bvar(bidx))
                    return np << 1
        return -1
    return -1


def _parse_chunk_fast_rc(line, pos, end, builder, stop_on_decl):
    """Ultra-tight 3-arm chunk loop (app/lam/forallE = ~91% of all lines) with
    refcount table, exprs list, and names list hoisted into registers."""
    counts = builder._refcount
    assert counts is not None
    rc_data = counts.data
    exprs = builder.exprs
    names = builder.names
    while pos < end:
        if pos + 8 > end:
            return ~pos
        w0 = _load_u64(line, pos)
        if w0 == _W8_APP_0:
            # {"app":{"arg":A,"fn":F},"ie":E}  (~73% of all lines)
            if pos + 14 <= end and _load_u64(line, pos + 6) == _W8_APP_1:
                arg_eidx, q = _read_uint(line, pos + 14, end)
                if (arg_eidx >= 0 and q + 6 <= end
                        and _load_u32(line, q) == _W4_FN_0
                        and _load_u16(line, q + 4) == _W2_COLON):
                    fn_eidx, q = _read_uint(line, q + 6, end)
                    if (fn_eidx >= 0 and q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                _reg_expr_rc(
                                    builder, exprs, eidx,
                                    objects.W_App(
                                        _ref_expr_rc(exprs, rc_data, fn_eidx),
                                        _ref_expr_rc(exprs, rc_data, arg_eidx),
                                    ),
                                )
                                pos = np
                                continue
            return ~pos
        w6 = w0 & _MASK48
        if w6 == _W6_IE:
            # {"ie":E,"lam":{"binderInfo":"...","body":B,"name":N,"type":T}}
            eidx, q = _read_uint(line, pos + 6, end)
            if (eidx >= 0 and q + 22 <= end
                    and _load_u64(line, q) == _W8_LAM_0
                    and _load_u64(line, q + 8) == _W8_LAM_1
                    and _load_u64(line, q + 14) == _W8_LAM_2):
                bcode, q = _match_binfo_at(line, q + 22, end)
                if bcode >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_BODY:
                    body_eidx, q = _read_uint(line, q + 8, end)
                    if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 2 <= end
                                    and _load_u16(line, q) == _W2_CLOSE2):
                                np = _at_eol_pos(line, q + 2, end)
                                if np >= 0:
                                    bound = _binder_from_code(
                                        names[name_idx],
                                        bcode,
                                        _ref_expr_rc(exprs, rc_data, type_eidx),
                                    )
                                    _reg_expr_rc(
                                        builder, exprs, eidx,
                                        objects.W_Lambda(
                                            bound,
                                            _ref_expr_rc(exprs, rc_data, body_eidx),
                                        ),
                                    )
                                    pos = np
                                    continue
            rr = _try_parse_compact_rare(line, pos, end, builder)
            if rr >= 0:
                pos = rr >> 1
                if (rr & 1) and stop_on_decl:
                    return pos
                continue
            return ~pos
        if w0 == _W8_FORALL_0:
            # {"forallE":{"binderInfo":"...","body":B,"name":N,"type":T},"ie":E}
            if (pos + 26 <= end
                    and _load_u64(line, pos + 8) == _W8_FORALL_1
                    and _load_u64(line, pos + 16) == _W8_FORALL_2
                    and _load_u16(line, pos + 24) == _W2_COL_Q):
                bcode, q = _match_binfo_at(line, pos + 26, end)
                if bcode >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_BODY:
                    body_eidx, q = _read_uint(line, q + 8, end)
                    if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 7 <= end
                                    and _load_u32(line, q) == _W4_IE_0
                                    and _load_u32(line, q + 3) == _W4_IE_1):
                                eidx, q = _read_uint(line, q + 7, end)
                                if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                                    np = _at_eol_pos(line, q + 1, end)
                                    if np >= 0:
                                        bound = _binder_from_code(
                                            names[name_idx],
                                            bcode,
                                            _ref_expr_rc(exprs, rc_data, type_eidx),
                                        )
                                        _reg_expr_rc(
                                            builder, exprs, eidx,
                                            objects.W_ForAll(
                                                bound,
                                                _ref_expr_rc(exprs, rc_data, body_eidx),
                                            ),
                                        )
                                        pos = np
                                        continue
            return ~pos
        rr = _try_parse_compact_rare(line, pos, end, builder)
        if rr >= 0:
            pos = rr >> 1
            if (rr & 1) and stop_on_decl:
                return pos
            continue
        return ~pos
    return pos


def _parse_chunk_fast(line, pos, end, builder, stop_on_decl):
    """Tight chunk-level word-at-a-time parser for canonical compact lines.

    Advances through as many lines in ``line[pos:end]`` as possible without
    returning to the outer loop. Returns:
      - ``new_pos >= 0`` if ``end`` was reached or a declaration was parsed
        with ``stop_on_decl=True``;
      - ``~pos`` (< 0) if the line at ``pos`` requires ``parse_cursor_general``.
    """
    if not _USE_FAST_WORDS:
        return ~pos
    if builder._refcount is not None and not builder._scanning:
        return _parse_chunk_fast_rc(line, pos, end, builder, stop_on_decl)
    while pos < end:
        if pos + 8 > end:
            return ~pos
        w0 = _load_u64(line, pos)
        if w0 == _W8_APP_0:
            if pos + 14 <= end and _load_u64(line, pos + 6) == _W8_APP_1:
                arg_eidx, q = _read_uint(line, pos + 14, end)
                if (arg_eidx >= 0 and q + 6 <= end
                        and _load_u32(line, q) == _W4_FN_0
                        and _load_u16(line, q + 4) == _W2_COLON):
                    fn_eidx, q = _read_uint(line, q + 6, end)
                    if (fn_eidx >= 0 and q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                builder.register_expr(
                                    eidx,
                                    objects.W_App(
                                        _ref_expr_fast(builder, fn_eidx),
                                        _ref_expr_fast(builder, arg_eidx),
                                    ),
                                )
                                pos = np
                                continue
            return ~pos
        w6 = w0 & _MASK48
        if w6 == _W6_IE:
            eidx, q = _read_uint(line, pos + 6, end)
            if (eidx >= 0 and q + 22 <= end
                    and _load_u64(line, q) == _W8_LAM_0
                    and _load_u64(line, q + 8) == _W8_LAM_1
                    and _load_u64(line, q + 14) == _W8_LAM_2):
                bcode, q = _match_binfo_at(line, q + 22, end)
                if bcode >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_BODY:
                    body_eidx, q = _read_uint(line, q + 8, end)
                    if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 2 <= end
                                    and _load_u16(line, q) == _W2_CLOSE2):
                                np = _at_eol_pos(line, q + 2, end)
                                if np >= 0:
                                    bound = _binder_from_code(
                                        builder.names[name_idx],
                                        bcode,
                                        _ref_expr_fast(builder, type_eidx),
                                    )
                                    builder.register_expr(
                                        eidx,
                                        objects.W_Lambda(
                                            bound,
                                            _ref_expr_fast(builder, body_eidx),
                                        ),
                                    )
                                    pos = np
                                    continue
            rr = _try_parse_compact_rare(line, pos, end, builder)
            if rr >= 0:
                pos = rr >> 1
                if (rr & 1) and stop_on_decl:
                    return pos
                continue
            return ~pos
        if w0 == _W8_FORALL_0:
            if (pos + 26 <= end
                    and _load_u64(line, pos + 8) == _W8_FORALL_1
                    and _load_u64(line, pos + 16) == _W8_FORALL_2
                    and _load_u16(line, pos + 24) == _W2_COL_Q):
                bcode, q = _match_binfo_at(line, pos + 26, end)
                if bcode >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_BODY:
                    body_eidx, q = _read_uint(line, q + 8, end)
                    if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 7 <= end
                                    and _load_u32(line, q) == _W4_IE_0
                                    and _load_u32(line, q + 3) == _W4_IE_1):
                                eidx, q = _read_uint(line, q + 7, end)
                                if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                                    np = _at_eol_pos(line, q + 1, end)
                                    if np >= 0:
                                        bound = _binder_from_code(
                                            builder.names[name_idx],
                                            bcode,
                                            _ref_expr_fast(builder, type_eidx),
                                        )
                                        builder.register_expr(
                                            eidx,
                                            objects.W_ForAll(
                                                bound,
                                                _ref_expr_fast(builder, body_eidx),
                                            ),
                                        )
                                        pos = np
                                        continue
            return ~pos
        rr = _try_parse_compact_rare(line, pos, end, builder)
        if rr >= 0:
            pos = rr >> 1
            if (rr & 1) and stop_on_decl:
                return pos
            continue
        return ~pos
    return pos


def parse_cursor(cursor, builder):
    """
    Parse a single lean4export NDJSON record from ``cursor`` and apply it to
    ``builder`` via the appropriate ``register_*`` call.
    """
    start = cursor.pos
    res = _parse_chunk_fast(cursor.line, start, cursor.length, builder, True)
    if res >= 0:
        cursor.pos = res
        return
    cursor.pos = start
    parse_cursor_general(cursor, builder)


def parse_cursor_general(cursor, builder):
    """General NDJSON line parser (whitespace/key-order agnostic)."""
    cursor.expect('{')
    first_key = cursor.read_key()

    if first_key == "in":
        _parse_name(cursor, builder)
    elif first_key == "il":
        _parse_universe(cursor, builder)
    elif first_key == "ie":
        _parse_expr_ie_first(cursor, builder)
    elif first_key == "axiom":
        _parse_axiom(cursor, builder)
    elif first_key == "def":
        _parse_definition(cursor, builder)
    elif first_key == "opaque":
        _parse_opaque(cursor, builder)
    elif first_key == "thm":
        _parse_theorem(cursor, builder)
    elif first_key == "quot":
        _parse_quot(cursor, builder)
    elif first_key == "inductive":
        _parse_inductive(cursor, builder)
    elif first_key == "rec":
        type_data = _parse_recursor_record(cursor)
        cursor.expect('}')
        _register_recursor(builder, type_data)
    else:
        # An expression where the discriminator (app, bvar, const, ...)
        # came before "ie" in this line.
        _parse_expr_disc_first(cursor, builder, first_key)


# ---- Names ---------------------------------------------------------------

def _parse_name(cursor, builder):
    """Parse `{"in":N,"str":...}` or `{"in":N,"num":...}` after `"in":`."""
    nidx = cursor.read_int()
    cursor.expect(',')
    second_key = cursor.read_key()
    if second_key == "str":
        parent_nidx, part = _parse_name_str_inner(cursor)
        cursor.expect('}')
        parent = builder.names[parent_nidx]
        builder.register_name(nidx, parent.child(part))
    elif second_key == "num":
        parent_nidx, id_val = _parse_name_num_inner(cursor)
        cursor.expect('}')
        parent = builder.names[parent_nidx]
        if id_val >= 0:
            builder.register_name(nidx, parent.num_child_int(id_val))
        else:
            builder.register_name(nidx, parent.num_child(rbigint.fromint(id_val)))
    else:
        raise MalformedLine("unknown name discriminator: %s" % second_key)


def _parse_name_str_inner(cursor):
    cursor.expect('{')
    parent_nidx = 0
    part = ""
    while True:
        key = cursor.read_key()
        if key == "pre":
            parent_nidx = cursor.read_int()
        elif key == "str":
            part = cursor.read_string()
        else:
            raise MalformedLine("unexpected key %s in name str" % key)
        if cursor.maybe('}'):
            return parent_nidx, part
        cursor.expect(',')


def _parse_name_num_inner(cursor):
    cursor.expect('{')
    parent_nidx = 0
    id_val = 0
    while True:
        key = cursor.read_key()
        if key == "pre":
            parent_nidx = cursor.read_int()
        elif key == "i":
            id_val = cursor.read_int()
        else:
            raise MalformedLine("unexpected key %s in name num" % key)
        if cursor.maybe('}'):
            return parent_nidx, id_val
        cursor.expect(',')


# ---- Universes -----------------------------------------------------------

def _parse_universe(cursor, builder):
    """Parse `{"il":N,"<succ|max|imax|param>":...}` after `"il":`."""
    uidx = cursor.read_int()
    cursor.expect(',')
    disc = cursor.read_key()
    if disc == "succ":
        parent = cursor.read_int()
        cursor.expect('}')
        builder.register_level(uidx, builder.levels[parent].succ())
    elif disc == "max":
        cursor.expect('[')
        lhs = cursor.read_int()
        cursor.expect(',')
        rhs = cursor.read_int()
        cursor.expect(']')
        cursor.expect('}')
        builder.register_level(
            uidx, objects.level_max(builder.levels[lhs], builder.levels[rhs]),
        )
    elif disc == "imax":
        cursor.expect('[')
        lhs = cursor.read_int()
        cursor.expect(',')
        rhs = cursor.read_int()
        cursor.expect(']')
        cursor.expect('}')
        builder.register_level(
            uidx, objects.level_imax(builder.levels[lhs], builder.levels[rhs]),
        )
    elif disc == "param":
        nidx = cursor.read_int()
        cursor.expect('}')
        builder.register_level(uidx, builder.names[nidx].as_level_param())
    else:
        raise MalformedLine("unknown universe discriminator: %s" % disc)


# ---- Expressions ---------------------------------------------------------

def _parse_expr_ie_first(cursor, builder):
    """Parse expression lines whose first key is ``"ie"``."""
    eidx = cursor.read_int()
    cursor.expect(',')
    disc = cursor.read_key()
    w_expr = _read_expr_value(cursor, builder, disc)
    cursor.expect('}')
    builder.register_expr(eidx, w_expr)


def _parse_expr_disc_first(cursor, builder, disc):
    """Parse expression lines whose first key is the discriminator."""
    w_expr = _read_expr_value(cursor, builder, disc)
    cursor.expect(',')
    cursor.expect_key("ie")
    eidx = cursor.read_int()
    cursor.expect('}')
    builder.register_expr(eidx, w_expr)


def _read_expr_value(cursor, builder, disc):
    """Read the value of an expression's discriminator and return its
    fully-resolved ``W_Expr``. The cursor is positioned just after the
    ``:`` following the discriminator key."""
    if disc == "bvar":
        return objects._mk_w_bvar(cursor.read_int())
    if disc == "sort":
        return builder.levels[cursor.read_int()].sort()
    if disc == "app":
        return _read_app(cursor, builder)
    if disc == "const":
        return _read_const(cursor, builder)
    if disc == "lam":
        return _read_binder_expr(cursor, builder, is_lam=True)
    if disc == "forallE":
        return _read_binder_expr(cursor, builder, is_lam=False)
    if disc == "letE":
        return _read_let(cursor, builder)
    if disc == "natVal":
        nat = rbigint.fromstr(cursor.read_string())
        assert nat.int_ge(0)
        return objects._mk_w_litnat(nat)
    if disc == "strVal":
        return objects._mk_w_litstr(cursor.read_string())
    if disc == "proj":
        return _read_proj(cursor, builder)
    if disc == "mdata":
        return _read_mdata(cursor, builder)
    raise MalformedLine("unknown expr discriminator: %s" % disc)


def _read_app(cursor, builder):
    cursor.expect('{')
    fn_eidx = 0
    arg_eidx = 0
    while True:
        key = cursor.read_key()
        if key == "fn":
            fn_eidx = cursor.read_int()
        elif key == "arg":
            arg_eidx = cursor.read_int()
        else:
            raise MalformedLine("unexpected key %s in app" % key)
        if cursor.maybe('}'):
            return builder.ref_expr(fn_eidx).app(builder.ref_expr(arg_eidx))
        cursor.expect(',')


def _read_const(cursor, builder):
    cursor.expect('{')
    nidx = 0
    level_idxs = None
    while True:
        key = cursor.read_key()
        if key == "name":
            nidx = cursor.read_int()
        elif key == "us":
            level_idxs = cursor.read_int_array()
        else:
            raise MalformedLine("unexpected key %s in const" % key)
        if cursor.maybe('}'):
            if level_idxs is None:
                level_idxs = []
            return builder.names[nidx].const(
                [builder.levels[i] for i in level_idxs],
            )
        cursor.expect(',')


def _read_binder_expr(cursor, builder, is_lam):
    cursor.expect('{')
    binder_info = ""
    body_eidx = 0
    name_idx = 0
    type_eidx = 0
    while True:
        key = cursor.read_key()
        if key == "binderInfo":
            binder_info = cursor.read_string()
        elif key == "body":
            body_eidx = cursor.read_int()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "type":
            type_eidx = cursor.read_int()
        else:
            raise MalformedLine("unexpected key %s in binder" % key)
        if cursor.maybe('}'):
            bound = _binder(
                builder.names[name_idx],
                binder_info,
                builder.ref_expr(type_eidx),
            )
            body = builder.ref_expr(body_eidx)
            if is_lam:
                return objects.fun(bound)(body)
            return objects.forall(bound)(body)
        cursor.expect(',')


def _binder(name, info, type):
    if info == "default":
        return name.binder(type=type)
    if info == "implicit":
        return name.implicit_binder(type=type)
    if info == "strictImplicit":
        return name.strict_implicit_binder(type=type)
    if info == "instImplicit":
        return name.instance_binder(type=type)
    raise MalformedLine("Unknown binder info %s" % info)


def _read_let(cursor, builder):
    cursor.expect('{')
    body_eidx = 0
    name_idx = 0
    type_eidx = 0
    value_eidx = 0
    while True:
        key = cursor.read_key()
        if key == "body":
            body_eidx = cursor.read_int()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "nondep":
            _skip_value(cursor)
        elif key == "type":
            type_eidx = cursor.read_int()
        elif key == "value":
            value_eidx = cursor.read_int()
        else:
            raise MalformedLine("unexpected key %s in letE" % key)
        if cursor.maybe('}'):
            return builder.names[name_idx].let(
                type=builder.ref_expr(type_eidx),
                value=builder.ref_expr(value_eidx),
                body=builder.ref_expr(body_eidx),
            )
        cursor.expect(',')


def _read_proj(cursor, builder):
    cursor.expect('{')
    idx = 0
    struct_eidx = 0
    type_name_idx = 0
    while True:
        key = cursor.read_key()
        if key == "idx":
            idx = cursor.read_int()
        elif key == "struct":
            struct_eidx = cursor.read_int()
        elif key == "typeName":
            type_name_idx = cursor.read_int()
        else:
            raise MalformedLine("unexpected key %s in proj" % key)
        if cursor.maybe('}'):
            return builder.names[type_name_idx].proj(
                idx, builder.ref_expr(struct_eidx),
            )
        cursor.expect(',')


def _read_mdata(cursor, builder):
    cursor.expect('{')
    expr_eidx = -1
    while True:
        key = cursor.read_key()
        if key == "expr":
            expr_eidx = cursor.read_int()
        elif key == "data":
            _skip_value(cursor)
        else:
            raise MalformedLine("unexpected key %s in mdata" % key)
        if cursor.maybe('}'):
            if expr_eidx < 0:
                raise MalformedLine("mdata missing `expr`")
            return builder.ref_expr(expr_eidx)
        cursor.expect(',')


def _skip_value(cursor):
    """Skip a JSON value of any shape (for fields the parser ignores)."""
    cursor.skip_ws()
    if cursor.pos >= cursor.length:
        raise MalformedLine("unexpected end of input")
    c = cursor.line[cursor.pos]
    if c == '"':
        cursor.read_string()
    elif c == '-' or ('0' <= c <= '9'):
        cursor.skip_number()
    elif c == 't':
        if not cursor.match_lit("true"):
            raise MalformedLine("expected true at pos %d" % cursor.pos)
    elif c == 'f':
        if not cursor.match_lit("false"):
            raise MalformedLine("expected false at pos %d" % cursor.pos)
    elif c == 'n':
        if not cursor.match_lit("null"):
            raise MalformedLine("expected null at pos %d" % cursor.pos)
    elif c == '[':
        cursor.pos += 1
        if cursor.maybe(']'):
            return
        while True:
            _skip_value(cursor)
            if cursor.maybe(']'):
                return
            cursor.expect(',')
    elif c == '{':
        cursor.pos += 1
        if cursor.maybe('}'):
            return
        while True:
            cursor.read_key()
            _skip_value(cursor)
            if cursor.maybe('}'):
                return
            cursor.expect(',')
    else:
        raise MalformedLine("unsupported value at pos %d" % cursor.pos)


# ---- Declarations (axiom/def/opaque/thm/quot) ----------------------------

def _parse_axiom(cursor, builder):
    """Parse `{"axiom":{...}}` after `"axiom":`."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    is_unsafe = False
    while True:
        key = cursor.read_key()
        if key == "isUnsafe":
            is_unsafe = cursor.read_bool()
        elif key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "type":
            type_eidx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            decl = builder.names[name_idx].axiom(
                levels=[builder.names[i] for i in levels],
                type=builder.ref_expr(type_eidx),
                is_unsafe=is_unsafe,
            )
            builder.register_declaration(decl)
            return
        cursor.expect(',')


def _parse_quot(cursor, builder):
    """Parse `{"quot":{...}}` after `"quot":`."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    kind = -1
    while True:
        key = cursor.read_key()
        if key == "kind":
            kind = objects.W_Quotient.kind_from_str(cursor.read_string())
        elif key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "type":
            type_eidx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            if kind < 0:
                raise MalformedLine("quot record missing `kind`")
            builder.register_quotient(
                builder.names[name_idx],
                builder.ref_expr(type_eidx),
                [builder.names[i] for i in levels],
                kind,
            )
            return
        cursor.expect(',')


def _parse_theorem(cursor, builder):
    """Parse `{"thm":{...}}` after `"thm":`."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    value_eidx = 0
    while True:
        key = cursor.read_key()
        if key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "type":
            type_eidx = cursor.read_int()
        elif key == "value":
            value_eidx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            decl = builder.names[name_idx].theorem(
                levels=[builder.names[i] for i in levels],
                type=builder.ref_expr(type_eidx),
                value=builder.ref_expr(value_eidx),
            )
            builder.register_declaration(decl)
            return
        cursor.expect(',')


def _parse_opaque(cursor, builder):
    """Parse `{"opaque":{...}}` after `"opaque":`."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    value_eidx = 0
    is_unsafe = False
    while True:
        key = cursor.read_key()
        if key == "isUnsafe":
            is_unsafe = cursor.read_bool()
        elif key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "type":
            type_eidx = cursor.read_int()
        elif key == "value":
            value_eidx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            decl = builder.names[name_idx].opaque(
                levels=[builder.names[i] for i in levels],
                type=builder.ref_expr(type_eidx),
                value=builder.ref_expr(value_eidx),
                is_unsafe=is_unsafe,
            )
            builder.register_declaration(decl)
            return
        cursor.expect(',')


def _parse_definition(cursor, builder):
    """Parse `{"def":{...}}` after `"def":`."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    value_eidx = 0
    hint = objects.HINT_OPAQUE
    safety = objects.SAFETY_SAFE
    all_idxs = None
    while True:
        key = cursor.read_key()
        if key == "all":
            all_idxs = cursor.read_int_array()
        elif key == "hints":
            hint = _parse_def_hint(cursor)
        elif key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "safety":
            safety = _parse_safety(cursor)
        elif key == "type":
            type_eidx = cursor.read_int()
        elif key == "value":
            value_eidx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            all = None
            if all_idxs is not None and len(all_idxs) > 1:
                all = [builder.names[i] for i in all_idxs]
            decl = builder.names[name_idx].definition(
                levels=[builder.names[i] for i in levels],
                type=builder.ref_expr(type_eidx),
                value=builder.ref_expr(value_eidx),
                hint=hint,
                safety=safety,
                all=all,
            )
            builder.register_declaration(decl)
            return
        cursor.expect(',')


def _parse_safety(cursor):
    """Parse a definition's ``"safety"`` field."""
    raw = cursor.read_string()
    if raw == "safe":
        return objects.SAFETY_SAFE
    if raw == "unsafe":
        return objects.SAFETY_UNSAFE
    if raw == "partial":
        return objects.SAFETY_PARTIAL
    raise MalformedLine("unknown definition safety: %s" % raw)


def _parse_def_hint(cursor):
    """Parse the polymorphic ``"hints"`` field — string or `{"regular":N}`."""
    cursor.skip_ws()
    if cursor.pos < cursor.length and cursor.line[cursor.pos] == '"':
        raw = cursor.read_string()
        if raw == "opaque":
            return objects.HINT_OPAQUE
        if raw == "abbrev":
            return objects.HINT_ABBREV
        raise MalformedLine("unknown def hint: %s" % raw)
    cursor.expect('{')
    cursor.expect_key("regular")
    n = cursor.read_int()
    cursor.expect('}')
    return n


# ---- Inductives + recursors ---------------------------------------------
#
# Inductive lines carry nested arrays of constructor and recursor records,
# so we can't directly stream them into the builder while parsing. Instead
# we collect the records into lightweight value carriers, then apply them
# after the close brace in the order the existing compile flow used:
#   - reflexive sanity check
#   - register each constructor
#   - register each recursor
#   - register the inductive itself
# (For mutual inductives, all inductives are registered first, then all
# constructors, then all recursors — matching MutualInductive.compile.)


class _IndType(object):
    """Fields of one entry in an inductive line's ``types`` array."""

    _attrs_ = [
        'nidx', 'type_idx', 'is_reflexive', 'is_recursive', 'is_unsafe',
        'num_nested', 'num_params', 'num_indices',
        'name_idxs', 'ctor_nidxs', 'levels',
    ]

    def __init__(self):
        self.nidx = 0
        self.type_idx = 0
        self.is_reflexive = False
        self.is_recursive = False
        self.is_unsafe = False
        self.num_nested = 0
        self.num_params = 0
        self.num_indices = 0
        self.name_idxs = []
        self.ctor_nidxs = []
        self.levels = []


class _IndCtor(object):
    """Fields of one entry in an inductive line's ``ctors`` array."""

    _attrs_ = [
        'nidx', 'induct_nidx', 'type_idx', 'is_unsafe',
        'num_params', 'num_fields', 'cidx', 'levels',
    ]

    def __init__(self):
        self.nidx = 0
        self.induct_nidx = 0
        self.type_idx = 0
        self.is_unsafe = False
        self.num_params = 0
        self.num_fields = 0
        self.cidx = 0
        self.levels = []


class _IndRec(object):
    """Fields of one entry in an inductive line's ``recs`` array, or of a
    standalone ``rec`` line."""

    _attrs_ = [
        'nidx', 'type_idx', 'k', 'is_unsafe',
        'num_params', 'num_indices', 'num_motives', 'num_minors',
        'ind_name_idxs', 'rules', 'levels',
    ]

    def __init__(self):
        self.nidx = 0
        self.type_idx = 0
        self.k = False
        self.is_unsafe = False
        self.num_params = 0
        self.num_indices = 0
        self.num_motives = 0
        self.num_minors = 0
        self.ind_name_idxs = []
        self.rules = []
        self.levels = []


class _IndRule(object):
    """Fields of one entry in a recursor's ``rules`` array."""

    _attrs_ = ['ctor_nidx', 'num_fields', 'rhs_eidx']

    def __init__(self, ctor_nidx, num_fields, rhs_eidx):
        self.ctor_nidx = ctor_nidx
        self.num_fields = num_fields
        self.rhs_eidx = rhs_eidx


def _parse_inductive(cursor, builder):
    """Parse `{"inductive":{...}}` after `"inductive":`."""
    cursor.expect('{')
    types = []
    ctors = []
    recs = []
    while True:
        key = cursor.read_key()
        if key == "types":
            types = _parse_inductive_type_array(cursor)
        elif key == "ctors":
            ctors = _parse_constructor_array(cursor)
        elif key == "recs":
            recs = _parse_recursor_array(cursor)
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            break
        cursor.expect(',')

    # The kernel generates each member's recursor itself, so its name
    # must be free before the block is added, whether or not the export
    # includes it — `check_inductive_types` (lean4 inductive.cpp)
    # checks both names up front. Without the `.rec` check an export
    # can park a foreign declaration at the recursor's name and present
    # its "real" recursor under some other name.
    for type_data in types:
        name = builder.names[type_data.nidx]
        builder.check_name(name)
        builder.check_name(name.child("rec"))

    # Every member of the record shares one block: constructors and
    # recursors refer to the types, recursors to the constructors, and
    # the members of a mutual block to each other.
    block = len(builder.declarations)
    if len(types) == 1:
        _register_single_inductive(builder, types[0], ctors, recs, block)
    else:
        _register_mutual_inductive(builder, types, ctors, recs, block)


def _register_single_inductive(
    builder, type_data, ctor_records, rec_records, block,
):
    name = builder.names[type_data.nidx]
    if type_data.is_reflexive:
        for rec in rec_records:
            if rec.k:
                raise ReflexiveKError(name, builder.names[rec.nidx])

    ctor_names = [builder.names[i] for i in type_data.ctor_nidxs]
    allowed = objects.name_dict()
    for ctor_name in ctor_names:
        allowed[ctor_name] = True
    ctor_decls = []
    for c in ctor_records:
        decl = _register_constructor(builder, c, block)
        if (
            builder.names[c.induct_nidx].syntactic_eq(name)
            and decl.name in allowed
        ):
            ctor_decls.append(decl)
    rec_decls = [_register_recursor(builder, r, block) for r in rec_records]

    inductive = name.inductive(
        levels=[builder.names[i] for i in type_data.levels],
        type=builder.ref_expr(type_data.type_idx),
        all=[builder.names[i] for i in type_data.name_idxs],
        constructors=ctor_decls,
        recursors=rec_decls,
        num_nested=type_data.num_nested,
        num_params=type_data.num_params,
        num_indices=type_data.num_indices,
        is_reflexive=type_data.is_reflexive,
        is_recursive=type_data.is_recursive,
        ctor_names=ctor_names,
        is_unsafe=type_data.is_unsafe,
    )
    builder.register_declaration(inductive, group=block)


def _register_mutual_inductive(
    builder, types, ctor_records, rec_records, block,
):
    # Track each block-member's W_Inductive by name so we can wire each
    # constructor back to its parent below — `_iota_reduce` / W_Proj
    # both index into `inductive_decl.w_kind.constructors` and crash if
    # we leave it empty for mutual blocks.
    induct_by_name = objects.name_dict()
    for type_data in types:
        name = builder.names[type_data.nidx]
        if type_data.is_reflexive:
            for rec in rec_records:
                if rec.k:
                    raise ReflexiveKError(name, builder.names[rec.nidx])
        inductive = name.inductive(
            levels=[builder.names[i] for i in type_data.levels],
            type=builder.ref_expr(type_data.type_idx),
            all=[builder.names[i] for i in type_data.name_idxs],
            constructors=[],
            recursors=[],
            num_nested=type_data.num_nested,
            num_params=type_data.num_params,
            num_indices=type_data.num_indices,
            is_reflexive=type_data.is_reflexive,
            is_recursive=type_data.is_recursive,
            ctor_names=[builder.names[i] for i in type_data.ctor_nidxs],
            is_unsafe=type_data.is_unsafe,
        )
        builder.register_declaration(inductive, group=block)
        induct_by_name[name] = inductive

    for ctor in ctor_records:
        ctor_decl = _register_constructor(builder, ctor, block)
        induct_name = builder.names[ctor.induct_nidx]
        parent = induct_by_name.get(induct_name, None)
        if parent is not None:
            parent_kind = parent.w_kind
            assert isinstance(parent_kind, objects.W_Inductive)
            for cname in parent_kind.ctor_names:
                if cname.syntactic_eq(ctor_decl.name):
                    parent_kind.constructors.append(ctor_decl)
                    break
    for rec in rec_records:
        _register_recursor(builder, rec, block)


def _register_constructor(builder, ctor, block):
    decl = builder.names[ctor.nidx].constructor(
        levels=[builder.names[i] for i in ctor.levels],
        type=builder.ref_expr(ctor.type_idx),
        num_params=ctor.num_params,
        num_fields=ctor.num_fields,
        cidx=ctor.cidx,
        is_unsafe=ctor.is_unsafe,
        induct=builder.names[ctor.induct_nidx],
    )
    builder.register_declaration(decl, group=block)
    return decl


def _register_recursor(builder, rec, block=-1):
    decl = builder.names[rec.nidx].recursor(
        levels=[builder.names[i] for i in rec.levels],
        type=builder.ref_expr(rec.type_idx),
        all=[builder.names[i] for i in rec.ind_name_idxs],
        rules=[
            objects.W_RecRule(
                ctor_name=builder.names[r.ctor_nidx],
                num_fields=r.num_fields,
                rhs=builder.ref_expr(r.rhs_eidx),
            ) for r in rec.rules
        ],
        k=rec.k,
        num_params=rec.num_params,
        num_indices=rec.num_indices,
        num_motives=rec.num_motives,
        num_minors=rec.num_minors,
        is_unsafe=rec.is_unsafe,
    )
    builder.register_declaration(decl, group=block)
    return decl


def _parse_inductive_type_array(cursor):
    cursor.expect('[')
    result = []
    if cursor.maybe(']'):
        return result
    while True:
        result.append(_parse_inductive_type(cursor))
        if cursor.maybe(']'):
            return result
        cursor.expect(',')


def _parse_inductive_type(cursor):
    cursor.expect('{')
    type_data = _IndType()
    while True:
        key = cursor.read_key()
        if key == "all":
            type_data.name_idxs = cursor.read_int_array()
        elif key == "ctors":
            type_data.ctor_nidxs = cursor.read_int_array()
        elif key == "isRec":
            type_data.is_recursive = cursor.read_bool()
        elif key == "isReflexive":
            type_data.is_reflexive = cursor.read_bool()
        elif key == "isUnsafe":
            type_data.is_unsafe = cursor.read_bool()
        elif key == "levelParams":
            type_data.levels = cursor.read_int_array()
        elif key == "name":
            type_data.nidx = cursor.read_int()
        elif key == "numIndices":
            type_data.num_indices = cursor.read_int()
        elif key == "numNested":
            type_data.num_nested = cursor.read_int()
        elif key == "numParams":
            type_data.num_params = cursor.read_int()
        elif key == "type":
            type_data.type_idx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return type_data
        cursor.expect(',')


def _parse_constructor_array(cursor):
    cursor.expect('[')
    result = []
    if cursor.maybe(']'):
        return result
    while True:
        result.append(_parse_constructor(cursor))
        if cursor.maybe(']'):
            return result
        cursor.expect(',')


def _parse_constructor(cursor):
    cursor.expect('{')
    ctor = _IndCtor()
    while True:
        key = cursor.read_key()
        if key == "cidx":
            ctor.cidx = cursor.read_int()
        elif key == "induct":
            ctor.induct_nidx = cursor.read_int()
        elif key == "isUnsafe":
            ctor.is_unsafe = cursor.read_bool()
        elif key == "levelParams":
            ctor.levels = cursor.read_int_array()
        elif key == "name":
            ctor.nidx = cursor.read_int()
        elif key == "numFields":
            ctor.num_fields = cursor.read_int()
        elif key == "numParams":
            ctor.num_params = cursor.read_int()
        elif key == "type":
            ctor.type_idx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return ctor
        cursor.expect(',')


def _parse_recursor_array(cursor):
    cursor.expect('[')
    result = []
    if cursor.maybe(']'):
        return result
    while True:
        result.append(_parse_recursor_record(cursor))
        if cursor.maybe(']'):
            return result
        cursor.expect(',')


def _parse_recursor_record(cursor):
    """Parse one recursor record. Used both inside an inductive's ``recs``
    array and as the body of a top-level ``rec`` line."""
    cursor.expect('{')
    rec = _IndRec()
    while True:
        key = cursor.read_key()
        if key == "all":
            rec.ind_name_idxs = cursor.read_int_array()
        elif key == "isUnsafe":
            rec.is_unsafe = cursor.read_bool()
        elif key == "k":
            rec.k = cursor.read_bool()
        elif key == "levelParams":
            rec.levels = cursor.read_int_array()
        elif key == "name":
            rec.nidx = cursor.read_int()
        elif key == "numIndices":
            rec.num_indices = cursor.read_int()
        elif key == "numMinors":
            rec.num_minors = cursor.read_int()
        elif key == "numMotives":
            rec.num_motives = cursor.read_int()
        elif key == "numParams":
            rec.num_params = cursor.read_int()
        elif key == "rules":
            rec.rules = _parse_rec_rule_array(cursor)
        elif key == "type":
            rec.type_idx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return rec
        cursor.expect(',')


def _parse_rec_rule_array(cursor):
    cursor.expect('[')
    result = []
    if cursor.maybe(']'):
        return result
    while True:
        result.append(_parse_rec_rule(cursor))
        if cursor.maybe(']'):
            return result
        cursor.expect(',')


def _parse_rec_rule(cursor):
    cursor.expect('{')
    ctor = 0
    nfields = 0
    rhs = 0
    while True:
        key = cursor.read_key()
        if key == "ctor":
            ctor = cursor.read_int()
        elif key == "nfields":
            nfields = cursor.read_int()
        elif key == "rhs":
            rhs = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return _IndRule(ctor, nfields, rhs)
        cursor.expect(',')


# ---- Metadata header -----------------------------------------------------

def _parse_metadata_version(line):
    """Read the ``version`` from the export's metadata line. Returns ``""``
    if no version is present."""
    cursor = LineCursor(line)
    cursor.expect('{')
    version = ""
    if cursor.maybe('}'):
        return version
    while True:
        key = cursor.read_key()
        if key == "meta":
            version = _parse_meta_inner(cursor)
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return version
        cursor.expect(',')


def _parse_meta_inner(cursor):
    cursor.expect('{')
    has_format = False
    format_version = ""
    exporter_version = ""
    if cursor.maybe('}'):
        return ""
    while True:
        key = cursor.read_key()
        if key == "format":
            has_format = True
            format_version = _parse_format_inner(cursor)
        elif key == "exporter":
            cursor.skip_ws()
            if cursor.pos < cursor.length and cursor.line[cursor.pos] == '{':
                exporter_version = _parse_format_inner(cursor)
            else:
                _skip_value(cursor)
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return format_version if has_format else exporter_version
        cursor.expect(',')


def _parse_format_inner(cursor):
    cursor.expect('{')
    version = ""
    if cursor.maybe('}'):
        return version
    while True:
        key = cursor.read_key()
        if key == "version":
            version = cursor.read_string()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return version
        cursor.expect(',')


# ---- Raw-byte expression refcount pre-scanner ----------------------------

@always_inline
def _ensure_refcount_slot(counts, idx):
    counts.ensure(idx)


@always_inline
def _bump_refcount_slot(counts, idx):
    counts.bump(idx)


@dont_inline
def _try_prescan_compact_rare(line, pos, end, counts):
    """Word-matched prescan for less frequent canonical record types, ordered
    by frequency: ``const``, ``thm``, ``def``, ``ie:*``, ``opaque``, ``bvar``.
    Returns ``next_pos >= 0`` on match or ``-1``."""
    if pos + 8 > end:
        return -1
    w0 = _load_u64(line, pos)
    if w0 == _W8_CONST_0:
        # {"const":{"name":N,"us":[...]},"ie":E} -> zero expr refs, need E!
        if (pos + 17 <= end
                and _load_u64(line, pos + 8) == _W8_CONST_1
                and _load_u8(line, pos + 16) == 58):
            nidx, q = _read_uint(line, pos + 17, end)
            if (nidx >= 0 and q + 7 <= end
                    and _load_u32(line, q) == _W4_US_0
                    and _load_u32(line, q + 3) == _W4_US_1):
                q += 7
                while q < end and _load_u8(line, q) != 93:
                    q += 1
                if q < end:
                    q += 1
                    if (q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                _ensure_refcount_slot(counts, eidx)
                                return np
        return -1
    if w0 == _W8_THM_0:
        # {"thm":{"all":[...],"levelParams":[...],"name":N,"type":T,"value":V}}
        q = pos + 8
        if (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                and _load_u32(line, q + 3) == _W4_ALL_1):
            q = _skip_uint_array(line, q + 7, end)
            if q < 0 or q >= end or _load_u8(line, q) != 44:
                return -1
            q += 1
        if (q + 15 <= end and _load_u64(line, q) == _W8_LPAR_0
                and _load_u64(line, q + 7) == _W8_LPAR_1):
            q = _skip_uint_array(line, q + 15, end)
            if q >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                name_idx, q = _read_uint(line, q + 8, end)
                if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                    type_eidx, q = _read_uint(line, q + 8, end)
                    if (type_eidx >= 0 and q + 9 <= end
                            and _load_u64(line, q) == _W8_VAL0
                            and _load_u8(line, q + 8) == 58):
                        value_eidx, q = _read_uint(line, q + 9, end)
                        if (value_eidx >= 0 and q + 2 <= end
                                and _load_u16(line, q) == _W2_CLOSE2):
                            np = _at_eol_pos(line, q + 2, end)
                            if np >= 0:
                                _bump_refcount_slot(counts, type_eidx)
                                _bump_refcount_slot(counts, value_eidx)
                                return np
        return -1
    w6 = w0 & _MASK48
    if w6 == _W6_IE:
        eidx, q = _read_uint(line, pos + 6, end)
        if eidx < 0 or q + 8 > end:
            return -1
        dw = _load_u64(line, q)
        if dw == _W8_LETE_0:
            if q + 16 <= end and _load_u64(line, q + 8) == _W8_LETE_1:
                body_eidx, q = _read_uint(line, q + 16, end)
                if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                    name_idx, q = _read_uint(line, q + 8, end)
                    if name_idx >= 0 and q + 22 <= end and _load_u64(line, q) == _W8_NDEP_0:
                        nw = _load_u64(line, q + 8)
                        if (nw == _W8_NDEP_F and q + 23 <= end
                                and _load_u64(line, q + 15) == _W8_TYPE):
                            q += 23
                        elif nw == _W8_NDEP_T and _load_u64(line, q + 14) == _W8_TYPE:
                            q += 22
                        else:
                            return -1
                        type_eidx, q = _read_uint(line, q, end)
                        if (type_eidx >= 0 and q + 9 <= end
                                and _load_u64(line, q) == _W8_VAL0
                                and _load_u8(line, q + 8) == 58):
                            value_eidx, q = _read_uint(line, q + 9, end)
                            if (value_eidx >= 0 and q + 2 <= end
                                    and _load_u16(line, q) == _W2_CLOSE2):
                                np = _at_eol_pos(line, q + 2, end)
                                if np >= 0:
                                    _ensure_refcount_slot(counts, eidx)
                                    _bump_refcount_slot(counts, type_eidx)
                                    _bump_refcount_slot(counts, value_eidx)
                                    _bump_refcount_slot(counts, body_eidx)
                                    return np
            return -1
        if dw == _W8_PROJ_0:
            if q + 15 <= end and _load_u64(line, q + 7) == _W8_PROJ_1:
                idx, q = _read_uint(line, q + 15, end)
                if (idx >= 0 and q + 10 <= end
                        and _load_u64(line, q) == _W8_STRUCT_0
                        and _load_u32(line, q + 6) == _W4_STRUCT_1):
                    struct_eidx, q = _read_uint(line, q + 10, end)
                    if (struct_eidx >= 0 and q + 12 <= end
                            and _load_u64(line, q) == _W8_TNAME_0
                            and _load_u32(line, q + 8) == _W4_TNAME_1):
                        tname_idx, q = _read_uint(line, q + 12, end)
                        if (tname_idx >= 0 and q + 2 <= end
                                and _load_u16(line, q) == _W2_CLOSE2):
                            np = _at_eol_pos(line, q + 2, end)
                            if np >= 0:
                                _ensure_refcount_slot(counts, eidx)
                                _bump_refcount_slot(counts, struct_eidx)
                                return np
            return -1
        if dw == _W8_SORT or dw == _W8_STRV_0 or dw == _W8_NATV_0:
            # sort / strVal / natVal: zero expr refs!
            np = _find_nl(line, q + 8, end)
            _ensure_refcount_slot(counts, eidx)
            return np
        return -1
    if w0 == _W8_DEF_0:
        # {"def":{"all":[...],"hints":...,"levelParams":[...],"name":N,"safety":"...","type":T,"value":V}}
        q = pos + 8
        if not (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                and _load_u32(line, q + 3) == _W4_ALL_1):
            return -1
        q = _skip_uint_array(line, q + 7, end)
        if q < 0 or q + 9 > end or _load_u64(line, q) != _W8_HINTS_0 or _load_u8(line, q + 8) != 58:
            return -1
        q += 9
        if q + 8 > end:
            return -1
        hw = _load_u64(line, q)
        if hw == _W8_H_ABBREV or hw == _W8_H_OPAQUE:
            q += 8
        elif (hw == _W8_H_REG_0 and q + 11 <= end
                and _load_u32(line, q + 7) == _W4_H_REG_1):
            hv, q = _read_uint(line, q + 11, end)
            if hv < 0 or q >= end or _load_u8(line, q) != 125:
                return -1
            q += 1
        else:
            return -1
        if not (q + 16 <= end and _load_u64(line, q) == _W8_CLPAR_0
                and _load_u64(line, q + 7) == _W8_CLPAR_1
                and _load_u8(line, q + 15) == 91):
            return -1
        q = _skip_uint_array(line, q + 16, end)
        if q < 0 or q + 8 > end or _load_u64(line, q) != _W8_NAME:
            return -1
        name_idx, q = _read_uint(line, q + 8, end)
        if (name_idx < 0 or q + 11 > end
                or _load_u64(line, q) != _W8_SAF_0
                or _load_u32(line, q + 7) != _W4_SAF_1):
            return -1
        q += 11
        if q + 5 <= end and _load_u32(line, q) == _W4_SAFE and _load_u8(line, q + 4) == 34:
            q += 5
        elif q + 8 <= end and _load_u64(line, q) == _W8_PARTIAL:
            q += 8
        elif (q + 7 <= end and _load_u32(line, q) == _W4_UNSA
                and _load_u32(line, q + 3) == _W4_AFE_Q):
            q += 7
        else:
            return -1
        if q + 8 > end or _load_u64(line, q) != _W8_TYPE:
            return -1
        type_eidx, q = _read_uint(line, q + 8, end)
        if (type_eidx < 0 or q + 9 > end
                or _load_u64(line, q) != _W8_VAL0
                or _load_u8(line, q + 8) != 58):
            return -1
        value_eidx, q = _read_uint(line, q + 9, end)
        if value_eidx < 0 or q + 2 > end or _load_u16(line, q) != _W2_CLOSE2:
            return -1
        np = _at_eol_pos(line, q + 2, end)
        if np >= 0:
            _bump_refcount_slot(counts, type_eidx)
            _bump_refcount_slot(counts, value_eidx)
            return np
        return -1
    if w0 == _W8_OPQ_0:
        if pos + 11 <= end and _load_u32(line, pos + 7) == _W4_OPQ_1:
            q = pos + 11
            if (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                    and _load_u32(line, q + 3) == _W4_ALL_1):
                q = _skip_uint_array(line, q + 7, end)
                if q < 0 or q >= end or _load_u8(line, q) != 44:
                    return -1
                q += 1
            if (q + 11 <= end and _load_u64(line, q) == _W8_ISUN_0
                    and _load_u32(line, q + 7) == _W4_ISUN_1):
                q += 11
                if (q + 6 <= end and _load_u8(line, q) == 102
                        and _load_u32(line, q + 1) == _W4_ALSE
                        and _load_u8(line, q + 5) == 44):
                    q += 6
                elif (q + 5 <= end and _load_u32(line, q) == _W4_TRUE
                        and _load_u8(line, q + 4) == 44):
                    q += 5
                else:
                    return -1
                if (q + 15 <= end and _load_u64(line, q) == _W8_LPAR_0
                        and _load_u64(line, q + 7) == _W8_LPAR_1):
                    q = _skip_uint_array(line, q + 15, end)
                    if q >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if (name_idx >= 0 and q + 8 <= end
                                and _load_u64(line, q) == _W8_TYPE):
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 9 <= end
                                    and _load_u64(line, q) == _W8_VAL0
                                    and _load_u8(line, q + 8) == 58):
                                value_eidx, q = _read_uint(line, q + 9, end)
                                if (value_eidx >= 0 and q + 2 <= end
                                        and _load_u16(line, q) == _W2_CLOSE2):
                                    np = _at_eol_pos(line, q + 2, end)
                                    if np >= 0:
                                        _bump_refcount_slot(counts, type_eidx)
                                        _bump_refcount_slot(counts, value_eidx)
                                        return np
        return -1
    if w0 == _W8_BVAR_0:
        bidx, q = _read_uint(line, pos + 8, end)
        if (bidx >= 0 and q + 6 <= end
                and _load_u32(line, q) == _W4_BVAR_IE0
                and _load_u16(line, q + 4) == _W2_COLON):
            eidx, q = _read_uint(line, q + 6, end)
            if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                np = _at_eol_pos(line, q + 1, end)
                if np >= 0:
                    _ensure_refcount_slot(counts, eidx)
                    return np
        return -1
    return -1


def _prescan_chunk_fast(line, pos, end, counts):
    """Tight chunk-level word-at-a-time prescanner for canonical compact lines.

    Returns ``end`` when the whole chunk slice was handled, or ``~pos`` (< 0)
    when the line at ``pos`` needs ``_prescan_line_general``.
    """
    if not _USE_FAST_WORDS:
        return ~pos
    while pos < end:
        if pos + 8 > end:
            return ~pos
        w0 = _load_u64(line, pos)
        if w0 == _W8_APP_0:
            # {"app":{"arg":A,"fn":F},"ie":E}
            if pos + 14 <= end and _load_u64(line, pos + 6) == _W8_APP_1:
                arg_eidx, q = _read_uint(line, pos + 14, end)
                if (arg_eidx >= 0 and q + 6 <= end
                        and _load_u32(line, q) == _W4_FN_0
                        and _load_u16(line, q + 4) == _W2_COLON):
                    fn_eidx, q = _read_uint(line, q + 6, end)
                    if (fn_eidx >= 0 and q + 7 <= end
                            and _load_u32(line, q) == _W4_IE_0
                            and _load_u32(line, q + 3) == _W4_IE_1):
                        eidx, q = _read_uint(line, q + 7, end)
                        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                            np = _at_eol_pos(line, q + 1, end)
                            if np >= 0:
                                _ensure_refcount_slot(counts, eidx)
                                _bump_refcount_slot(counts, fn_eidx)
                                _bump_refcount_slot(counts, arg_eidx)
                                pos = np
                                continue
            return ~pos
        w6 = w0 & _MASK48
        if w6 == _W6_IE:
            eidx, q = _read_uint(line, pos + 6, end)
            if (eidx >= 0 and q + 22 <= end
                    and _load_u64(line, q) == _W8_LAM_0
                    and _load_u64(line, q + 8) == _W8_LAM_1
                    and _load_u64(line, q + 14) == _W8_LAM_2):
                bcode, q = _match_binfo_at(line, q + 22, end)
                if bcode >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_BODY:
                    body_eidx, q = _read_uint(line, q + 8, end)
                    if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 2 <= end
                                    and _load_u16(line, q) == _W2_CLOSE2):
                                np = _at_eol_pos(line, q + 2, end)
                                if np >= 0:
                                    _ensure_refcount_slot(counts, eidx)
                                    _bump_refcount_slot(counts, type_eidx)
                                    _bump_refcount_slot(counts, body_eidx)
                                    pos = np
                                    continue
            np = _try_prescan_compact_rare(line, pos, end, counts)
            if np >= 0:
                pos = np
                continue
            return ~pos
        if w0 == _W8_FORALL_0:
            if (pos + 26 <= end
                    and _load_u64(line, pos + 8) == _W8_FORALL_1
                    and _load_u64(line, pos + 16) == _W8_FORALL_2
                    and _load_u16(line, pos + 24) == _W2_COL_Q):
                bcode, q = _match_binfo_at(line, pos + 26, end)
                if bcode >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_BODY:
                    body_eidx, q = _read_uint(line, q + 8, end)
                    if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                        name_idx, q = _read_uint(line, q + 8, end)
                        if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                            type_eidx, q = _read_uint(line, q + 8, end)
                            if (type_eidx >= 0 and q + 7 <= end
                                    and _load_u32(line, q) == _W4_IE_0
                                    and _load_u32(line, q + 3) == _W4_IE_1):
                                eidx, q = _read_uint(line, q + 7, end)
                                if eidx >= 0 and q < end and _load_u8(line, q) == 125:
                                    np = _at_eol_pos(line, q + 1, end)
                                    if np >= 0:
                                        _ensure_refcount_slot(counts, eidx)
                                        _bump_refcount_slot(counts, type_eidx)
                                        _bump_refcount_slot(counts, body_eidx)
                                        pos = np
                                        continue
            return ~pos
        if w6 == _W6_IN or w6 == _W6_IL:
            # Name / Level lines have zero expr definitions and zero expr refs.
            pos = _find_nl(line, pos + 6, end)
            continue
        np = _try_prescan_compact_rare(line, pos, end, counts)
        if np >= 0:
            pos = np
            continue
        return ~pos
    return pos


def _skip_value_noalloc(cursor):
    """Skip any JSON value without allocating strings or lists."""
    cursor.skip_ws()
    if cursor.pos >= cursor.length:
        raise MalformedLine("unexpected end of input")
    c = cursor.line[cursor.pos]
    if c == '"':
        cursor.skip_string()
    elif c == '-' or ('0' <= c <= '9'):
        cursor.skip_number()
    elif c == 't':
        if not cursor.match_lit("true"):
            raise MalformedLine("expected true at pos %d" % cursor.pos)
    elif c == 'f':
        if not cursor.match_lit("false"):
            raise MalformedLine("expected false at pos %d" % cursor.pos)
    elif c == 'n':
        if not cursor.match_lit("null"):
            raise MalformedLine("expected null at pos %d" % cursor.pos)
    elif c == '[':
        cursor.pos += 1
        if cursor.maybe(']'):
            return
        while True:
            _skip_value_noalloc(cursor)
            if cursor.maybe(']'):
                return
            cursor.expect(',')
    elif c == '{':
        cursor.pos += 1
        if cursor.maybe('}'):
            return
        while True:
            cursor.skip_string()
            cursor.expect(':')
            _skip_value_noalloc(cursor)
            if cursor.maybe('}'):
                return
            cursor.expect(',')
    else:
        raise MalformedLine("unsupported value at pos %d" % cursor.pos)


def _prescan_expr_value(cursor, counts, ks, ke):
    if cursor.span_eq(ks, ke, "bvar") or cursor.span_eq(ks, ke, "sort"):
        cursor.read_int()
        return
    if cursor.span_eq(ks, ke, "natVal") or cursor.span_eq(ks, ke, "strVal"):
        cursor.skip_string()
        return
    if cursor.span_eq(ks, ke, "const"):
        _skip_value_noalloc(cursor)
        return
    if cursor.span_eq(ks, ke, "app"):
        cursor.expect('{')
        fn_eidx = 0
        arg_eidx = 0
        while True:
            s, e = cursor.read_key_span()
            if cursor.span_eq(s, e, "fn"):
                fn_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "arg"):
                arg_eidx = cursor.read_int()
            else:
                raise MalformedLine("unexpected key in app")
            if cursor.maybe('}'):
                _bump_refcount_slot(counts, fn_eidx)
                _bump_refcount_slot(counts, arg_eidx)
                return
            cursor.expect(',')
    if cursor.span_eq(ks, ke, "lam") or cursor.span_eq(ks, ke, "forallE"):
        cursor.expect('{')
        type_eidx = 0
        body_eidx = 0
        while True:
            s, e = cursor.read_key_span()
            if cursor.span_eq(s, e, "type"):
                type_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "body"):
                body_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "binderInfo"):
                cursor.skip_string()
            elif cursor.span_eq(s, e, "name"):
                cursor.read_int()
            else:
                raise MalformedLine("unexpected key in binder")
            if cursor.maybe('}'):
                _bump_refcount_slot(counts, type_eidx)
                _bump_refcount_slot(counts, body_eidx)
                return
            cursor.expect(',')
    if cursor.span_eq(ks, ke, "letE"):
        cursor.expect('{')
        type_eidx = 0
        value_eidx = 0
        body_eidx = 0
        while True:
            s, e = cursor.read_key_span()
            if cursor.span_eq(s, e, "type"):
                type_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "value"):
                value_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "body"):
                body_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "name"):
                cursor.read_int()
            elif cursor.span_eq(s, e, "nondep"):
                _skip_value_noalloc(cursor)
            else:
                raise MalformedLine("unexpected key in letE")
            if cursor.maybe('}'):
                _bump_refcount_slot(counts, type_eidx)
                _bump_refcount_slot(counts, value_eidx)
                _bump_refcount_slot(counts, body_eidx)
                return
            cursor.expect(',')
    if cursor.span_eq(ks, ke, "proj"):
        cursor.expect('{')
        struct_eidx = 0
        while True:
            s, e = cursor.read_key_span()
            if cursor.span_eq(s, e, "struct"):
                struct_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "idx") or cursor.span_eq(s, e, "typeName"):
                cursor.read_int()
            else:
                raise MalformedLine("unexpected key in proj")
            if cursor.maybe('}'):
                _bump_refcount_slot(counts, struct_eidx)
                return
            cursor.expect(',')
    if cursor.span_eq(ks, ke, "mdata"):
        cursor.expect('{')
        expr_eidx = -1
        while True:
            s, e = cursor.read_key_span()
            if cursor.span_eq(s, e, "expr"):
                expr_eidx = cursor.read_int()
            elif cursor.span_eq(s, e, "data"):
                _skip_value_noalloc(cursor)
            else:
                raise MalformedLine("unexpected key in mdata")
            if cursor.maybe('}'):
                if expr_eidx < 0:
                    raise MalformedLine("mdata missing `expr`")
                _bump_refcount_slot(counts, expr_eidx)
                return
            cursor.expect(',')
    raise MalformedLine("unknown expr discriminator")


def _prescan_decl_type_only(cursor, counts):
    cursor.expect('{')
    type_eidx = 0
    while True:
        s, e = cursor.read_key_span()
        if cursor.span_eq(s, e, "type"):
            type_eidx = cursor.read_int()
        else:
            _skip_value_noalloc(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            _bump_refcount_slot(counts, type_eidx)
            return
        cursor.expect(',')


def _prescan_decl_type_and_value(cursor, counts):
    cursor.expect('{')
    type_eidx = 0
    value_eidx = 0
    while True:
        s, e = cursor.read_key_span()
        if cursor.span_eq(s, e, "type"):
            type_eidx = cursor.read_int()
        elif cursor.span_eq(s, e, "value"):
            value_eidx = cursor.read_int()
        else:
            _skip_value_noalloc(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            _bump_refcount_slot(counts, type_eidx)
            _bump_refcount_slot(counts, value_eidx)
            return
        cursor.expect(',')


def _prescan_recursor_record(cursor, counts):
    cursor.expect('{')
    type_eidx = 0
    while True:
        s, e = cursor.read_key_span()
        if cursor.span_eq(s, e, "type"):
            type_eidx = cursor.read_int()
        elif cursor.span_eq(s, e, "rules"):
            cursor.expect('[')
            if not cursor.maybe(']'):
                while True:
                    cursor.expect('{')
                    rhs_eidx = 0
                    while True:
                        rs, re_ = cursor.read_key_span()
                        if cursor.span_eq(rs, re_, "rhs"):
                            rhs_eidx = cursor.read_int()
                        else:
                            _skip_value_noalloc(cursor)
                        if cursor.maybe('}'):
                            _bump_refcount_slot(counts, rhs_eidx)
                            break
                        cursor.expect(',')
                    if cursor.maybe(']'):
                        break
                    cursor.expect(',')
        else:
            _skip_value_noalloc(cursor)
        if cursor.maybe('}'):
            _bump_refcount_slot(counts, type_eidx)
            return
        cursor.expect(',')


def _prescan_type_array(cursor, counts):
    cursor.expect('[')
    if cursor.maybe(']'):
        return
    while True:
        cursor.expect('{')
        type_eidx = 0
        while True:
            s, e = cursor.read_key_span()
            if cursor.span_eq(s, e, "type"):
                type_eidx = cursor.read_int()
            else:
                _skip_value_noalloc(cursor)
            if cursor.maybe('}'):
                _bump_refcount_slot(counts, type_eidx)
                break
            cursor.expect(',')
        if cursor.maybe(']'):
            return
        cursor.expect(',')


def _prescan_inductive(cursor, counts):
    cursor.expect('{')
    while True:
        s, e = cursor.read_key_span()
        if cursor.span_eq(s, e, "types") or cursor.span_eq(s, e, "ctors"):
            _prescan_type_array(cursor, counts)
        elif cursor.span_eq(s, e, "recs"):
            cursor.expect('[')
            if not cursor.maybe(']'):
                while True:
                    _prescan_recursor_record(cursor, counts)
                    if cursor.maybe(']'):
                        break
                    cursor.expect(',')
        else:
            _skip_value_noalloc(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            return
        cursor.expect(',')


def _prescan_line(cursor, counts):
    start = cursor.pos
    res = _prescan_chunk_fast(cursor.line, start, cursor.length, counts)
    if res >= 0:
        cursor.pos = res
        return
    cursor.pos = start
    _prescan_line_general(cursor, counts)


def _prescan_line_general(cursor, counts):
    cursor.expect('{')
    ks, ke = cursor.read_key_span()
    if cursor.span_eq(ks, ke, "in") or cursor.span_eq(ks, ke, "il"):
        return
    if cursor.span_eq(ks, ke, "ie"):
        eidx = cursor.read_int()
        cursor.expect(',')
        ds, de = cursor.read_key_span()
        _prescan_expr_value(cursor, counts, ds, de)
        cursor.expect('}')
        _ensure_refcount_slot(counts, eidx)
        return
    if cursor.span_eq(ks, ke, "thm") or cursor.span_eq(ks, ke, "def") or cursor.span_eq(ks, ke, "opaque"):
        _prescan_decl_type_and_value(cursor, counts)
        return
    if cursor.span_eq(ks, ke, "axiom") or cursor.span_eq(ks, ke, "quot"):
        _prescan_decl_type_only(cursor, counts)
        return
    if cursor.span_eq(ks, ke, "inductive"):
        _prescan_inductive(cursor, counts)
        return
    if cursor.span_eq(ks, ke, "rec"):
        _prescan_recursor_record(cursor, counts)
        cursor.expect('}')
        return
    _prescan_expr_value(cursor, counts, ks, ke)
    cursor.expect(',')
    cursor.expect_key("ie")
    eidx = cursor.read_int()
    cursor.expect('}')
    _ensure_refcount_slot(counts, eidx)


def prescan_refcounts(stream, size_hint=65536):
    """Scan an export stream (positioned after its metadata line) at raw-byte
    level and return a ``RefCountTable`` of parse-time expression reference
    counts."""
    counts = RefCountTable(size_hint)
    try:
        cursor = LineCursor("")
        tail = ""
        while True:
            chunk = stream.read(262144)
            if not chunk:
                if tail:
                    end = len(tail)
                    if end > 0 and tail[end - 1] == '\r':
                        end -= 1
                    cursor.reset(tail, 0, end)
                    _prescan_line(cursor, counts)
                return counts
            clen = len(chunk)
            pos = 0
            if tail:
                nl = chunk.find('\n')
                if nl < 0:
                    tail = tail + chunk
                    continue
                line = tail + chunk[:nl]
                tail = ""
                llen = len(line)
                if llen > 0 and line[llen - 1] == '\r':
                    llen -= 1
                cursor.reset(line, 0, llen)
                _prescan_line(cursor, counts)
                pos = nl + 1
                if pos >= clen:
                    continue
            last_nl = chunk.rfind('\n', pos)
            if last_nl < 0:
                assert pos >= 0
                tail = chunk[pos:]
                continue
            limit = last_nl + 1
            cursor.line = chunk
            cursor.length = limit
            while pos <= last_nl:
                res = _prescan_chunk_fast(chunk, pos, limit, counts)
                if res >= 0:
                    pos = res
                else:
                    pos = ~res
                    assert pos >= 0
                    nl = chunk.find('\n', pos)
                    assert nl >= 0
                    end = nl
                    if end > pos and chunk[end - 1] == '\r':
                        end -= 1
                    cursor.pos = pos
                    cursor.length = end
                    _prescan_line_general(cursor, counts)
                    cursor.length = limit
                    pos = nl + 1
            if pos < clen:
                assert pos >= 0
                tail = chunk[pos:]
    except:
        counts.free()
        raise
