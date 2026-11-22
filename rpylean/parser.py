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
import errno
import sys
from textwrap import dedent

from rpython.rlib import rposix, streamio
from rpython.rlib.objectmodel import (
    always_inline, dont_inline, newlist_hint, specialize, we_are_translated,
)
from rpython.rlib.rarithmetic import r_uint
from rpython.rlib.rbigint import rbigint
from rpython.rtyper.lltypesystem import llmemory, lltype, rffi
from rpython.rtyper.lltypesystem.lloperation import llop

from rpylean import objects
from rpylean._line_parser import LineCursor
from rpylean.environment import Environment
from rpylean.exceptions import (
    ExportError, MalformedLine, ReflexiveKError, UnknownQuotient,
)


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


# ---- EnvironmentBuilder & public entry points ----------------------------

#: Write-only placeholder handed back by `EnvironmentBuilder.ref_expr` during
#: the counting pre-pass (`start_scan`), where sub-expressions are built only
#: to tally references and immediately discarded.
_SCAN_SCAFFOLD = objects._mk_w_bvar(0)


@specialize.call_location()
def _register_at(table, idx, value, placeholder):
    n = len(table)
    if idx == n:
        table.append(value)
    elif idx < n:
        table[idx] = value
    else:
        while len(table) < idx:
            table.append(placeholder)
        table.append(value)


class DeclarationHook(object):
    """
    Base class for streaming hooks invoked on each newly-registered declaration.
    """

    _attrs_ = []

    def on_declaration(self, decl):
        """Return a truthy value to abort the consume loop early."""
        return False


class EnvironmentBuilder(object):
    """
    A mutable environment builder.

    Incrementally builds up an environment as we parse an export file.
    """

    _attrs_ = [
        'levels', 'exprs', 'names', 'declarations', 'env',
        '_refcount', '_scanning', 'ordered',
    ]

    def __init__(self, levels=None, exprs=None, names=[], env=None):
        self.levels = [objects.W_LEVEL_ZERO] if levels is None else levels
        self.exprs = [] if exprs is None else exprs
        self.names = [objects.Name.ANONYMOUS] + names
        self.declarations = []
        self.env = (
            Environment(declarations=objects.name_dict())
            if env is None else env
        )
        # Whether registration order is declaration order. True for exports,
        # which list each declaration after everything it uses.
        self.ordered = True
        # Expr-pool pruning (see `ref_expr`). `_refcount` is `None` on the
        # default path (no pruning — REPL, tests, stdin); a `RefCountTable`
        # when a pre-scan has run. While `_scanning` is True this builder IS
        # that counting pre-pass (used as a test oracle for `prescan_refcounts`).
        self._refcount = None
        self._scanning = False

    def start_scan(self):
        """Configure this builder as the reference-counting pre-pass."""
        self._scanning = True
        self._refcount = RefCountTable(4096)

    def set_refcount(self, counts):
        """Attach pre-scanned reference counts and pre-size the expr/name pools."""
        self._refcount = counts
        n = counts.length
        if not self.exprs and n > 0:
            self.exprs = newlist_hint(n)
        if len(self.names) == 1 and n > 16384:
            nhint = n >> 4
            names = newlist_hint(nhint if nhint >= 1024 else 1024)
            names.append(objects.Name.ANONYMOUS)
            self.names = names

    def ref_expr(self, eidx):
        """
        Resolve one parse-time reference to expression index ``eidx``.

        Every ``builder.exprs[...]`` read in the parser goes through here,
        enabling expr-pool pruning when `_refcount` is attached: once a
        slot's count hits 0, the pool drops its hold so checked proof terms
        can be reclaimed.
        """
        counts = self._refcount
        if counts is None:
            e = self.exprs[eidx]
            assert e is not None
            return e
        if self._scanning:
            counts.bump(eidx)
            return _SCAN_SCAFFOLD
        e = self.exprs[eidx]
        assert e is not None
        if counts.dec(eidx) == 0:
            self.exprs[eidx] = None
        return e

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return (
            self.levels == other.levels
            and self.exprs == other.exprs
            and self.names == other.names
            and self.declarations == other.declarations
        )

    def __ne__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return not self == other

    def __repr__(self):
        return "<EnvironmentBuilder with %s declarations>" % (len(self.declarations),)

    def consume(self, stream, hook=None):
        """
        Parse NDJSON lines from ``stream`` directly into this builder.

        If ``hook`` is given, its ``on_declaration`` is invoked for each
        declaration as it is registered, with the partially-built environment
        available at ``self.env`` for streaming type-checking. Returning a
        truthy value from ``on_declaration`` aborts the loop early.

        Returns self.
        """
        _consume_stream(stream, self, hook)
        return self

    # Skipped `in`/`ie`/`il` indices are padded with a same-typed placeholder
    # so the tables stay homogeneous lists rather than `Optional` ones.
    def register_name(self, nidx, name):
        _register_at(self.names, nidx, name, objects.Name.ANONYMOUS)

    def register_expr(self, eidx, w_expr):
        if self._scanning:
            self._refcount.set_zero(eidx)
            return
        exprs = self.exprs
        if eidx == len(exprs):
            exprs.append(w_expr)
        else:
            _register_at(exprs, eidx, w_expr, objects.PROP)

    def register_level(self, uidx, level):
        _register_at(self.levels, uidx, level, objects.W_LEVEL_ZERO)

    def register_quotient(self, name, type, levels, kind):
        # Allowed: Quot, Quot.mk, Quot.ind, Quot.lift (all `Name.str` chains
        # rooted at the anonymous name).
        if not isinstance(name, objects.StrName):
            raise UnknownQuotient(name, type)
        parent = name.parent
        if parent.is_anonymous():
            if name.suffix != "Quot":
                raise UnknownQuotient(name, type)
        elif (
            isinstance(parent, objects.StrName)
            and parent.parent.is_anonymous()
            and parent.suffix == "Quot"
            and name.suffix in ("mk", "ind", "lift")
        ):
            pass
        else:
            raise UnknownQuotient(name, type)
        self.register_declaration(
            name.quotient(type=type, kind=kind, levels=levels),
        )

    def check_name(self, name):
        self.env.check_name(name)

    def register_declaration(self, decl, group=-1):
        self.env.register_declaration(decl, group=group, ordered=self.ordered)
        self.declarations.append(decl)

    def finish(self):
        """
        Finish building, returning the live environment.
        """
        return self.env


def from_export(export):
    """
    Load an environment out of some lean4export-formatted export.
    """
    validate_export_metadata(export)
    return EnvironmentBuilder().consume(export).finish()


def from_str(text):
    """
    Parse a lean4export-formatted string (no metadata header) into a fresh
    ``EnvironmentBuilder`` and return it.
    """
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


# ---- SWAR word-at-a-time compact record parsing & prescanning ------------

_IS_LITTLE_ENDIAN = sys.byteorder == "little"
_IS_64BIT = sys.maxint > 2147483647
_USE_FAST_WORDS = _IS_LITTLE_ENDIAN and _IS_64BIT
_STREAM_BUF_CAP = 262144


def _w(s):
    if len(s) > 4 and not _IS_64BIT:
        return r_uint(0)
    val = r_uint(0)
    for i, ch in enumerate(s):
        val |= r_uint(ord(ch)) << (8 * i)
    return val


_w2 = _w4 = _w6 = _w8 = _w


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
def _load_u64(buf, p):
    if we_are_translated():
        return llop.raw_load(
            lltype.Unsigned, rffi.cast(llmemory.Address, buf), p,
        )
    return (
        r_uint(ord(buf[p]))
        | (r_uint(ord(buf[p + 1])) << 8)
        | (r_uint(ord(buf[p + 2])) << 16)
        | (r_uint(ord(buf[p + 3])) << 24)
        | (r_uint(ord(buf[p + 4])) << 32)
        | (r_uint(ord(buf[p + 5])) << 40)
        | (r_uint(ord(buf[p + 6])) << 48)
        | (r_uint(ord(buf[p + 7])) << 56)
    )


@always_inline
def _load_u32(buf, p):
    if we_are_translated():
        return rffi.cast(
            lltype.Unsigned,
            llop.raw_load(rffi.UINT, rffi.cast(llmemory.Address, buf), p),
        )
    return (
        r_uint(ord(buf[p]))
        | (r_uint(ord(buf[p + 1])) << 8)
        | (r_uint(ord(buf[p + 2])) << 16)
        | (r_uint(ord(buf[p + 3])) << 24)
    )


@always_inline
def _load_u16(buf, p):
    if we_are_translated():
        return rffi.cast(
            lltype.Unsigned,
            llop.raw_load(rffi.USHORT, rffi.cast(llmemory.Address, buf), p),
        )
    return r_uint(ord(buf[p])) | (r_uint(ord(buf[p + 1])) << 8)


@always_inline
def _load_u8(buf, p):
    if we_are_translated():
        return rffi.cast(
            lltype.Signed,
            llop.raw_load(rffi.UCHAR, rffi.cast(llmemory.Address, buf), p),
        )
    return ord(buf[p])


def _slice_buf(buf, s, q):
    n = q - s
    if n <= 0:
        return ""
    if we_are_translated():
        return rffi.charpsize2str(rffi.ptradd(buf, s), n)
    return buf[s:q]


@always_inline
def _rfind_nl(buf, start, end):
    """Return index of the last '\\n' in buf[start:end], or ``-1``."""
    p = end - 1
    while p >= start:
        if _load_u8(buf, p) == 10:
            return p
        p -= 1
    return -1


def _raw_read_fd(fd, dst, count):
    void_buf = rffi.cast(rffi.VOIDP, dst)
    while True:
        try:
            return rposix.handle_posix_error(
                'read', rposix.c_read(fd, void_buf, count),
            )
        except OSError as e:
            if e.errno != errno.EINTR:
                raise


@dont_inline
def _grow_raw_buf(buf, used, min_cap):
    cap = min_cap
    new_buf = lltype.malloc(rffi.CCHARP.TO, cap, flavor='raw')
    if used > 0:
        if we_are_translated():
            rffi.c_memcpy(
                rffi.cast(rffi.VOIDP, new_buf),
                rffi.cast(rffi.CONST_VOIDP, buf),
                used,
            )
        else:
            k = 0
            while k < used:
                new_buf[k] = buf[k]
                k += 1
    lltype.free(buf, flavor='raw')
    return new_buf


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
        return objects._BINDER_DEFAULT, p + 8
    if w == _W8_BINFO_IMP:
        if p + 9 <= end and _load_u8(line, p + 8) == 34:
            return objects._BINDER_IMPLICIT, p + 9
    elif w == _W8_BINFO_INST0:
        if p + 13 <= end and _load_u64(line, p + 5) == _W8_BINFO_INST1:
            return objects._BINDER_INSTANCE, p + 13
    elif w == _W8_BINFO_STR0:
        if p + 15 <= end and _load_u64(line, p + 7) == _W8_BINFO_INST1:
            return objects._BINDER_STRICT_IMPLICIT, p + 15
    return -1, p


@always_inline
def _match_close_ie_eol(line, q, end):
    """Match ``},"ie":E}\\n`` starting at ``q``. Returns ``(eidx, next_pos)`` or ``(-1, -1)``."""
    if (q + 7 <= end
            and _load_u32(line, q) == _W4_IE_0
            and _load_u32(line, q + 3) == _W4_IE_1):
        eidx, q = _read_uint(line, q + 7, end)
        if eidx >= 0 and q < end and _load_u8(line, q) == 125:
            np = _at_eol_pos(line, q + 1, end)
            if np >= 0:
                return eidx, np
    return -1, -1


@always_inline
def _match_binder_fields(line, q, end):
    """Match ``,"body":B,"name":N,"type":T`` starting at ``q``.
    Returns ``(body_eidx, name_idx, type_eidx, q)`` or ``(-1, -1, -1, -1)``."""
    if q + 8 <= end and _load_u64(line, q) == _W8_BODY:
        body_eidx, q = _read_uint(line, q + 8, end)
        if body_eidx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
            name_idx, q = _read_uint(line, q + 8, end)
            if name_idx >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
                type_eidx, q = _read_uint(line, q + 8, end)
                if type_eidx >= 0:
                    return body_eidx, name_idx, type_eidx, q
    return -1, -1, -1, -1


@always_inline
def _match_type_value_eol(line, q, end):
    """Match ``,"type":T,"value":V}}\\n`` starting at ``q``.
    Returns ``(type_eidx, value_eidx, next_pos)`` or ``(-1, -1, -1)``."""
    if q + 8 <= end and _load_u64(line, q) == _W8_TYPE:
        type_eidx, q = _read_uint(line, q + 8, end)
        if (type_eidx >= 0 and q + 9 <= end
                and _load_u64(line, q) == _W8_VAL0
                and _load_u8(line, q + 8) == 58):
            value_eidx, q = _read_uint(line, q + 9, end)
            if (value_eidx >= 0 and q + 2 <= end
                    and _load_u16(line, q) == _W2_CLOSE2):
                np = _at_eol_pos(line, q + 2, end)
                if np >= 0:
                    return type_eidx, value_eidx, np
    return -1, -1, -1


@always_inline
def _skip_optional_all(line, q, end):
    """Skip optional ``"all":[...],`` prefix. Returns next pos or ``-1`` on mismatch."""
    if (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
            and _load_u32(line, q + 3) == _W4_ALL_1):
        q = _skip_uint_array(line, q + 7, end)
        if q < 0 or q >= end or _load_u8(line, q) != 44:
            return -1
        q += 1
    return q


@always_inline
def _match_pair_close_eol(line, q, end):
    """Match ``L,R]}\\n`` starting at ``q``. Returns ``(lhs, rhs, next_pos)`` or ``(-1, -1, -1)``."""
    lhs, q = _read_uint(line, q, end)
    if lhs >= 0 and q < end and _load_u8(line, q) == 44:
        rhs, q = _read_uint(line, q + 1, end)
        if (rhs >= 0 and q + 2 <= end
                and _load_u8(line, q) == 93
                and _load_u8(line, q + 1) == 125):
            np = _at_eol_pos(line, q + 2, end)
            if np >= 0:
                return lhs, rhs, np
    return -1, -1, -1


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


@always_inline
def _scan_plain_str(line, start, end):
    """Scan an unescaped single-line JSON string body starting at ``start``.
    Returns the index of the closing ``"``, or ``-1`` on escape/newline/EOF."""
    q = start
    while q < end:
        ch = _load_u8(line, q)
        if ch == 34:
            return q
        if ch == 92 or ch == 10:
            return -1
        q += 1
    return -1


@always_inline
def _match_def_hint(line, q, end):
    if q + 8 > end:
        return -1, -1
    hw = _load_u64(line, q)
    if hw == _W8_H_ABBREV:
        return objects.HINT_ABBREV, q + 8
    if hw == _W8_H_OPAQUE:
        return objects.HINT_OPAQUE, q + 8
    if (hw == _W8_H_REG_0 and q + 11 <= end
            and _load_u32(line, q + 7) == _W4_H_REG_1):
        hint, q = _read_uint(line, q + 11, end)
        if hint >= 0 and q < end and _load_u8(line, q) == 125:
            return hint, q + 1
    return -1, -1


@always_inline
def _match_def_safety(line, q, end):
    if q + 5 <= end and _load_u32(line, q) == _W4_SAFE and _load_u8(line, q + 4) == 34:
        return objects.SAFETY_SAFE, q + 5
    if q + 8 <= end and _load_u64(line, q) == _W8_PARTIAL:
        return objects.SAFETY_PARTIAL, q + 8
    if (q + 7 <= end and _load_u32(line, q) == _W4_UNSA
            and _load_u32(line, q + 3) == _W4_AFE_Q):
        return objects.SAFETY_UNSAFE, q + 7
    return -1, -1


@always_inline
def _parse_compact_in(line, pos, end, builder):
    # {"in":N,"str":{"pre":P,"str":"..."}} or {"in":N,"num":{"i":I,"pre":P}}
    nidx, q = _read_uint(line, pos + 6, end)
    if nidx < 0 or q + 12 > end:
        return -1
    dw = _load_u64(line, q)
    if (dw == _W8_IN_STR_0 and q + 14 <= end
            and _load_u64(line, q + 6) == _W8_IN_STR_1):
        pre, q = _read_uint(line, q + 14, end)
        if pre >= 0 and q + 8 <= end and _load_u64(line, q) == _W8_IN_STR_2:
            s = q + 8
            q = _scan_plain_str(line, s, end)
            if q >= 0 and q + 3 <= end and _load_u16(line, q + 1) == _W2_CLOSE2:
                np = _at_eol_pos(line, q + 3, end)
                if np >= 0:
                    assert s >= 0 and q >= s
                    builder.register_name(
                        nidx, builder.names[pre].child(_slice_buf(line, s, q)),
                    )
                    return np << 1
    elif dw == _W8_IN_NUM_0 and _load_u32(line, q + 8) == _W4_IN_NUM_1:
        id_val, q = _read_uint(line, q + 12, end)
        if (id_val >= 0 and q + 7 <= end
                and _load_u32(line, q) == _W4_PRE_0
                and _load_u32(line, q + 3) == _W4_PRE_1):
            pre, q = _read_uint(line, q + 7, end)
            if pre >= 0 and q + 2 <= end and _load_u16(line, q) == _W2_CLOSE2:
                np = _at_eol_pos(line, q + 2, end)
                if np >= 0:
                    builder.register_name(
                        nidx, builder.names[pre].num_child_int(id_val),
                    )
                    return np << 1
    return -1


@always_inline
def _parse_compact_il(line, pos, end, builder):
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
        lhs, rhs, np = _match_pair_close_eol(line, q + 8, end)
        if np >= 0:
            builder.register_level(
                uidx, objects.level_max(builder.levels[lhs], builder.levels[rhs]),
            )
            return np << 1
    elif dw == _W8_IMAX_0 and q + 9 <= end and _load_u8(line, q + 8) == 91:
        lhs, rhs, np = _match_pair_close_eol(line, q + 9, end)
        if np >= 0:
            builder.register_level(
                uidx, objects.level_imax(builder.levels[lhs], builder.levels[rhs]),
            )
            return np << 1
    return -1


@always_inline
def _parse_compact_ie_leaf(line, q, end, dw, eidx, builder):
    if dw == _W8_STRV_0:
        # ,"strVal":"..."}
        if q + 11 <= end and _load_u32(line, q + 7) == _W4_VAL_Q:
            s = q + 11
            q = _scan_plain_str(line, s, end)
            if q >= 0 and q + 2 <= end and _load_u8(line, q + 1) == 125:
                np = _at_eol_pos(line, q + 2, end)
                if np >= 0:
                    assert s >= 0 and q >= s
                    builder.register_expr(
                        eidx, objects._mk_w_litstr(_slice_buf(line, s, q)),
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


def _make_compact_rare(prescan):
    """Import-time factory generating the monomorphic SWAR rare-record parser
    (``prescan=False``, target is ``EnvironmentBuilder``) and prescanner
    (``prescan=True``, target is ``RefCountTable``)."""

    @dont_inline
    def _compact_rare(line, pos, end, target):
        if pos + 8 > end:
            return -1
        w0 = _load_u64(line, pos)
        w6 = w0 & _MASK48
        if not prescan and w6 == _W6_IN:
            return _parse_compact_in(line, pos, end, target)
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
                    if prescan:
                        q = _skip_uint_array(line, q, end)
                        if q >= 0:
                            eidx, np = _match_close_ie_eol(line, q, end)
                            if np >= 0:
                                target.ensure(eidx)
                                return np
                        return -1
                    nlev = 0
                    l0 = 0
                    l1 = 0
                    levels = None
                    if q < end and _load_u8(line, q) == 93:
                        q += 1
                    else:
                        l0, q = _read_uint(line, q, end)
                        if l0 < 0 or q >= end:
                            return -1
                        ch = _load_u8(line, q)
                        if ch == 93:
                            nlev = 1
                            q += 1
                        elif ch == 44:
                            l1, q = _read_uint(line, q + 1, end)
                            if l1 < 0 or q >= end:
                                return -1
                            ch = _load_u8(line, q)
                            if ch == 93:
                                nlev = 2
                                q += 1
                            elif ch == 44:
                                nlev = 3
                                q += 1
                                levels = [target.levels[l0], target.levels[l1]]
                                while True:
                                    lidx, q = _read_uint(line, q, end)
                                    if lidx < 0 or q >= end:
                                        return -1
                                    levels.append(target.levels[lidx])
                                    ch = _load_u8(line, q)
                                    if ch == 93:
                                        q += 1
                                        break
                                    if ch != 44:
                                        return -1
                                    q += 1
                            else:
                                return -1
                        else:
                            return -1
                    eidx, np = _match_close_ie_eol(line, q, end)
                    if np >= 0:
                        name = target.names[nidx]
                        if nlev == 0:
                            w_const = name.const_empty()
                        elif nlev == 1:
                            w_const = objects._mk_w_const1(
                                name, target.levels[l0],
                            )
                        elif nlev == 2:
                            w_const = objects._mk_w_const2(
                                name, target.levels[l0], target.levels[l1],
                            )
                        else:
                            assert levels is not None
                            w_const = name.const(levels)
                        target.register_expr(eidx, w_const)
                        return np << 1
            return -1
        if w0 == _W8_THM_0:
            # {"thm":{"all":[...],"levelParams":[...],"name":N,"type":T,"value":V}}
            q = _skip_optional_all(line, pos + 8, end)
            if (q >= 0 and q + 15 <= end and _load_u64(line, q) == _W8_LPAR_0
                    and _load_u64(line, q + 7) == _W8_LPAR_1):
                if prescan:
                    q = _skip_uint_array(line, q + 15, end)
                    ok = q >= 0
                else:
                    levels, q = _read_level_names(line, q + 15, end, target)
                    ok = levels is not None
                if ok and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                    name_idx, q = _read_uint(line, q + 8, end)
                    if name_idx >= 0:
                        type_eidx, value_eidx, np = _match_type_value_eol(
                            line, q, end,
                        )
                        if np >= 0:
                            if prescan:
                                target.bump(type_eidx)
                                target.bump(value_eidx)
                                return np
                            decl = target.names[name_idx].theorem(
                                levels=levels,
                                type=_ref_expr_fast(target, type_eidx),
                                value=_ref_expr_fast(target, value_eidx),
                            )
                            target.register_declaration(decl)
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
                            if nw == _W8_NDEP_F:
                                q += 15
                            elif nw == _W8_NDEP_T:
                                q += 14
                            else:
                                return -1
                            type_eidx, value_eidx, np = _match_type_value_eol(
                                line, q, end,
                            )
                            if np >= 0:
                                if prescan:
                                    target.ensure(eidx)
                                    target.bump(type_eidx)
                                    target.bump(value_eidx)
                                    target.bump(body_eidx)
                                    return np
                                target.register_expr(
                                    eidx,
                                    objects.W_Let(
                                        target.names[name_idx],
                                        _ref_expr_fast(target, type_eidx),
                                        _ref_expr_fast(target, value_eidx),
                                        _ref_expr_fast(target, body_eidx),
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
                                    if prescan:
                                        target.ensure(eidx)
                                        target.bump(struct_eidx)
                                        return np
                                    target.register_expr(
                                        eidx,
                                        target.names[tname_idx].proj(
                                            idx,
                                            _ref_expr_fast(target, struct_eidx),
                                        ),
                                    )
                                    return np << 1
                return -1
            if prescan:
                if dw == _W8_SORT or dw == _W8_STRV_0 or dw == _W8_NATV_0:
                    np = _find_nl(line, q + 8, end)
                    target.ensure(eidx)
                    return np
                return -1
            return _parse_compact_ie_leaf(line, q, end, dw, eidx, target)
        if w0 == _W8_DEF_0:
            # {"def":{"all":[...],"hints":...,"levelParams":[...],"name":N,"safety":"...","type":T,"value":V}}
            q = pos + 8
            if not (q + 7 <= end and _load_u32(line, q) == _W4_ALL_0
                    and _load_u32(line, q + 3) == _W4_ALL_1):
                return -1
            q += 7
            if prescan:
                q = _skip_uint_array(line, q, end)
                if q < 0:
                    return -1
            else:
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
                        all_names = [target.names[a0]]
                        q += 1
                        while True:
                            ak, q = _read_uint(line, q, end)
                            if ak < 0 or q >= end:
                                return -1
                            all_names.append(target.names[ak])
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
            hint, q = _match_def_hint(line, q + 9, end)
            if q < 0:
                return -1
            if not (q + 16 <= end and _load_u64(line, q) == _W8_CLPAR_0
                    and _load_u64(line, q + 7) == _W8_CLPAR_1
                    and _load_u8(line, q + 15) == 91):
                return -1
            if prescan:
                q = _skip_uint_array(line, q + 16, end)
                if q < 0:
                    return -1
            else:
                levels, q = _read_level_names(line, q + 16, end, target)
                if levels is None:
                    return -1
            if q + 8 > end or _load_u64(line, q) != _W8_NAME:
                return -1
            name_idx, q = _read_uint(line, q + 8, end)
            if (name_idx < 0 or q + 11 > end
                    or _load_u64(line, q) != _W8_SAF_0
                    or _load_u32(line, q + 7) != _W4_SAF_1):
                return -1
            safety, q = _match_def_safety(line, q + 11, end)
            if q < 0:
                return -1
            type_eidx, value_eidx, np = _match_type_value_eol(line, q, end)
            if np < 0:
                return -1
            if prescan:
                target.bump(type_eidx)
                target.bump(value_eidx)
                return np
            decl = target.names[name_idx].definition(
                levels=levels,
                type=_ref_expr_fast(target, type_eidx),
                value=_ref_expr_fast(target, value_eidx),
                hint=hint,
                safety=safety,
                all=all_names,
            )
            target.register_declaration(decl)
            return (np << 1) | 1
        if w0 == _W8_OPQ_0:
            # {"opaque":{"all":[...],"isUnsafe":false|true,"levelParams":[...],"name":N,"type":T,"value":V}}
            if pos + 11 <= end and _load_u32(line, pos + 7) == _W4_OPQ_1:
                q = _skip_optional_all(line, pos + 11, end)
                if (q >= 0 and q + 11 <= end and _load_u64(line, q) == _W8_ISUN_0
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
                        if prescan:
                            q = _skip_uint_array(line, q + 15, end)
                            ok = q >= 0
                        else:
                            levels, q = _read_level_names(
                                line, q + 15, end, target,
                            )
                            ok = levels is not None
                        if ok and q + 8 <= end and _load_u64(line, q) == _W8_NAME:
                            name_idx, q = _read_uint(line, q + 8, end)
                            if name_idx >= 0:
                                type_eidx, value_eidx, np = _match_type_value_eol(
                                    line, q, end,
                                )
                                if np >= 0:
                                    if prescan:
                                        target.bump(type_eidx)
                                        target.bump(value_eidx)
                                        return np
                                    decl = target.names[name_idx].opaque(
                                        levels=levels,
                                        type=_ref_expr_fast(target, type_eidx),
                                        value=_ref_expr_fast(target, value_eidx),
                                        is_unsafe=is_unsafe,
                                    )
                                    target.register_declaration(decl)
                                    return (np << 1) | 1
            return -1
        if not prescan and w6 == _W6_IL:
            return _parse_compact_il(line, pos, end, target)
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
                        if prescan:
                            target.ensure(eidx)
                            return np
                        target.register_expr(eidx, objects._mk_w_bvar(bidx))
                        return np << 1
            return -1
        return -1

    _compact_rare.__name__ = (
        "_try_prescan_compact_rare" if prescan else "_try_parse_compact_rare"
    )
    return _compact_rare


_try_parse_compact_rare = _make_compact_rare(False)
_try_prescan_compact_rare = _make_compact_rare(True)

_CHUNK_RC = 0
_CHUNK_PLAIN = 1
_CHUNK_PRESCAN = 2


def _make_chunk_fast(mode):
    """Import-time factory generating the 3 monomorphic hot SWAR chunk loops:
    ``_parse_chunk_fast_rc`` (hoisted refcount registers), ``_parse_chunk_fast``
    (plain / scanning), and ``_prescan_chunk_fast`` (refcount pre-scanner)."""
    is_rc = mode == _CHUNK_RC
    is_plain = mode == _CHUNK_PLAIN
    is_prescan = mode == _CHUNK_PRESCAN

    def _chunk_fast(line, pos, end, target, stop_on_decl=False):
        if is_plain or is_prescan:
            if not _USE_FAST_WORDS:
                return ~pos
        if is_plain:
            if target._refcount is not None and not target._scanning:
                return _parse_chunk_fast_rc_raw(
                    line, pos, end, target, stop_on_decl,
                )
        if is_rc:
            counts = target._refcount
            assert counts is not None
            rc_data = counts.data
            exprs = target.exprs
            names = target.names
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
                        if fn_eidx >= 0:
                            eidx, np = _match_close_ie_eol(line, q, end)
                            if np >= 0:
                                if is_prescan:
                                    target.ensure(eidx)
                                    target.bump(fn_eidx)
                                    target.bump(arg_eidx)
                                elif is_rc:
                                    _reg_expr_rc(
                                        target, exprs, eidx,
                                        objects.W_App(
                                            _ref_expr_rc(exprs, rc_data, fn_eidx),
                                            _ref_expr_rc(exprs, rc_data, arg_eidx),
                                        ),
                                    )
                                else:
                                    target.register_expr(
                                        eidx,
                                        objects.W_App(
                                            _ref_expr_fast(target, fn_eidx),
                                            _ref_expr_fast(target, arg_eidx),
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
                    if bcode >= 0:
                        body_eidx, name_idx, type_eidx, q = _match_binder_fields(
                            line, q, end,
                        )
                        if (q >= 0 and q + 2 <= end
                                and _load_u16(line, q) == _W2_CLOSE2):
                            np = _at_eol_pos(line, q + 2, end)
                            if np >= 0:
                                if is_prescan:
                                    target.ensure(eidx)
                                    target.bump(type_eidx)
                                    target.bump(body_eidx)
                                elif is_rc:
                                    bound = _binder_from_code(
                                        names[name_idx],
                                        bcode,
                                        _ref_expr_rc(exprs, rc_data, type_eidx),
                                    )
                                    _reg_expr_rc(
                                        target, exprs, eidx,
                                        objects.W_Lambda(
                                            bound,
                                            _ref_expr_rc(exprs, rc_data, body_eidx),
                                        ),
                                    )
                                else:
                                    bound = _binder_from_code(
                                        target.names[name_idx],
                                        bcode,
                                        _ref_expr_fast(target, type_eidx),
                                    )
                                    target.register_expr(
                                        eidx,
                                        objects.W_Lambda(
                                            bound,
                                            _ref_expr_fast(target, body_eidx),
                                        ),
                                    )
                                pos = np
                                continue
                if is_prescan:
                    np = _try_prescan_compact_rare(line, pos, end, target)
                    if np >= 0:
                        pos = np
                        continue
                else:
                    rr = _try_parse_compact_rare(line, pos, end, target)
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
                    if bcode >= 0:
                        body_eidx, name_idx, type_eidx, q = _match_binder_fields(
                            line, q, end,
                        )
                        if q >= 0:
                            eidx, np = _match_close_ie_eol(line, q, end)
                            if np >= 0:
                                if is_prescan:
                                    target.ensure(eidx)
                                    target.bump(type_eidx)
                                    target.bump(body_eidx)
                                elif is_rc:
                                    bound = _binder_from_code(
                                        names[name_idx],
                                        bcode,
                                        _ref_expr_rc(exprs, rc_data, type_eidx),
                                    )
                                    _reg_expr_rc(
                                        target, exprs, eidx,
                                        objects.W_ForAll(
                                            bound,
                                            _ref_expr_rc(exprs, rc_data, body_eidx),
                                        ),
                                    )
                                else:
                                    bound = _binder_from_code(
                                        target.names[name_idx],
                                        bcode,
                                        _ref_expr_fast(target, type_eidx),
                                    )
                                    target.register_expr(
                                        eidx,
                                        objects.W_ForAll(
                                            bound,
                                            _ref_expr_fast(target, body_eidx),
                                        ),
                                    )
                                pos = np
                                continue
                return ~pos
            if is_prescan and (w6 == _W6_IN or w6 == _W6_IL):
                # Name / Level lines have zero expr definitions and zero expr refs.
                pos = _find_nl(line, pos + 6, end)
                continue
            if is_prescan:
                np = _try_prescan_compact_rare(line, pos, end, target)
                if np >= 0:
                    pos = np
                    continue
            else:
                rr = _try_parse_compact_rare(line, pos, end, target)
                if rr >= 0:
                    pos = rr >> 1
                    if (rr & 1) and stop_on_decl:
                        return pos
                    continue
            return ~pos
        return pos

    if is_rc:
        _chunk_fast.__name__ = "_parse_chunk_fast_rc"
    elif is_plain:
        _chunk_fast.__name__ = "_parse_chunk_fast"
    else:
        _chunk_fast.__name__ = "_prescan_chunk_fast"
    return _chunk_fast


_parse_chunk_fast_rc_raw = _make_chunk_fast(_CHUNK_RC)
_parse_chunk_fast_raw = _make_chunk_fast(_CHUNK_PLAIN)
_prescan_chunk_fast_raw = _make_chunk_fast(_CHUNK_PRESCAN)


def _parse_chunk_fast(line, pos, end, target, stop_on_decl=False):
    if not _USE_FAST_WORDS:
        return ~pos
    assert line is not None
    if not we_are_translated():
        return _parse_chunk_fast_raw(line, pos, end, target, stop_on_decl)
    with rffi.scoped_nonmovingbuffer(line) as buf:
        return _parse_chunk_fast_raw(buf, pos, end, target, stop_on_decl)


def _prescan_chunk_fast(line, pos, end, target):
    if not _USE_FAST_WORDS:
        return ~pos
    assert line is not None
    if not we_are_translated():
        return _prescan_chunk_fast_raw(line, pos, end, target)
    with rffi.scoped_nonmovingbuffer(line) as buf:
        return _prescan_chunk_fast_raw(buf, pos, end, target)


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
    elif (first_key == "axiom" or first_key == "def" or first_key == "opaque"
            or first_key == "thm" or first_key == "quot"):
        _parse_simple_decl(cursor, builder, first_key)
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
    elif disc == "max" or disc == "imax":
        cursor.expect('[')
        lhs = cursor.read_int()
        cursor.expect(',')
        rhs = cursor.read_int()
        cursor.expect(']')
        cursor.expect('}')
        left = builder.levels[lhs]
        right = builder.levels[rhs]
        level = (
            objects.level_max(left, right)
            if disc == "max"
            else objects.level_imax(left, right)
        )
        builder.register_level(uidx, level)
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
                return objects._mk_w_lambda(bound, body)
            return objects._mk_w_forall(bound, body)
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
            _skip_value(cursor)
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
            _skip_value(cursor)
            if cursor.maybe('}'):
                return
            cursor.expect(',')
    else:
        raise MalformedLine("unsupported value at pos %d" % cursor.pos)


# ---- Declarations (axiom/def/opaque/thm/quot) ----------------------------

def _parse_simple_decl(cursor, builder, decl_kind):
    """Parse ``axiom``, ``quot``, ``thm``, ``opaque``, or ``def`` after its key."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    value_eidx = 0
    is_unsafe = False
    quot_kind = -1
    hint = objects.HINT_OPAQUE
    safety = objects.SAFETY_SAFE
    all_idxs = None
    while True:
        key = cursor.read_key()
        if key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name_idx = cursor.read_int()
        elif key == "type":
            type_eidx = cursor.read_int()
        elif key == "value" and (
            decl_kind == "thm" or decl_kind == "opaque" or decl_kind == "def"
        ):
            value_eidx = cursor.read_int()
        elif key == "isUnsafe" and (
            decl_kind == "axiom" or decl_kind == "opaque"
        ):
            is_unsafe = cursor.read_bool()
        elif key == "kind" and decl_kind == "quot":
            quot_kind = objects.W_Quotient.kind_from_str(cursor.read_string())
        elif key == "all" and decl_kind == "def":
            all_idxs = cursor.read_int_array()
        elif key == "hints" and decl_kind == "def":
            hint = _parse_def_hint(cursor)
        elif key == "safety" and decl_kind == "def":
            safety = _parse_safety(cursor)
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            level_names = (
                [builder.names[i] for i in levels] if levels is not None else []
            )
            name = builder.names[name_idx]
            type_expr = builder.ref_expr(type_eidx)
            if decl_kind == "axiom":
                decl = name.axiom(
                    levels=level_names, type=type_expr, is_unsafe=is_unsafe,
                )
            elif decl_kind == "quot":
                if quot_kind < 0:
                    raise MalformedLine("quot record missing `kind`")
                builder.register_quotient(name, type_expr, level_names, quot_kind)
                return
            elif decl_kind == "thm":
                decl = name.theorem(
                    levels=level_names,
                    type=type_expr,
                    value=builder.ref_expr(value_eidx),
                )
            elif decl_kind == "opaque":
                decl = name.opaque(
                    levels=level_names,
                    type=type_expr,
                    value=builder.ref_expr(value_eidx),
                    is_unsafe=is_unsafe,
                )
            else:
                all_names = None
                if all_idxs is not None and len(all_idxs) > 1:
                    all_names = [builder.names[i] for i in all_idxs]
                decl = name.definition(
                    levels=level_names,
                    type=type_expr,
                    value=builder.ref_expr(value_eidx),
                    hint=hint,
                    safety=safety,
                    all=all_names,
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
            types = _read_array(cursor, _parse_inductive_type)
        elif key == "ctors":
            ctors = _read_array(cursor, _parse_constructor)
        elif key == "recs":
            recs = _read_array(cursor, _parse_recursor_record)
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
    _register_inductive_block(builder, types, ctors, recs, block)


def _register_inductive_block(
    builder, types, ctor_records, rec_records, block,
):
    for type_data in types:
        if type_data.is_reflexive:
            name = builder.names[type_data.nidx]
            for rec in rec_records:
                if rec.k:
                    raise ReflexiveKError(name, builder.names[rec.nidx])

    allowed_by_ind = objects.name_dict()
    ctors_by_ind = objects.name_dict()
    recs_by_ind = objects.name_dict()
    for type_data in types:
        name = builder.names[type_data.nidx]
        allowed = objects.name_dict()
        for ci in type_data.ctor_nidxs:
            allowed[builder.names[ci]] = True
        allowed_by_ind[name] = allowed
        ctors_by_ind[name] = []
        recs_by_ind[name] = []

    for ctor in ctor_records:
        decl = _register_constructor(builder, ctor, block)
        induct_name = builder.names[ctor.induct_nidx]
        allowed = allowed_by_ind.get(induct_name, None)
        if allowed is not None and decl.name in allowed:
            ctors_by_ind[induct_name].append(decl)

    for rec in rec_records:
        decl = _register_recursor(builder, rec, block)
        matched = False
        for ind_nidx in rec.ind_name_idxs:
            bucket = recs_by_ind.get(builder.names[ind_nidx], None)
            if bucket is not None:
                bucket.append(decl)
                matched = True
        if not matched and len(types) == 1:
            recs_by_ind[builder.names[types[0].nidx]].append(decl)

    for type_data in types:
        name = builder.names[type_data.nidx]
        ctor_names = [builder.names[i] for i in type_data.ctor_nidxs]
        inductive = name.inductive(
            levels=[builder.names[i] for i in type_data.levels],
            type=builder.ref_expr(type_data.type_idx),
            all=[builder.names[i] for i in type_data.name_idxs],
            constructors=ctors_by_ind[name],
            recursors=recs_by_ind[name],
            num_nested=type_data.num_nested,
            num_params=type_data.num_params,
            num_indices=type_data.num_indices,
            is_reflexive=type_data.is_reflexive,
            is_recursive=type_data.is_recursive,
            ctor_names=ctor_names,
            is_unsafe=type_data.is_unsafe,
        )
        builder.register_declaration(inductive, group=block)


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


@specialize.arg(1)
def _read_array(cursor, parse_item):
    cursor.expect('[')
    result = []
    if cursor.maybe(']'):
        return result
    while True:
        result.append(parse_item(cursor))
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
            rec.rules = _read_array(cursor, _parse_rec_rule)
        elif key == "type":
            rec.type_idx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return rec
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


# ---- General expression refcount pre-scanner -----------------------------

def _prescan_expr_value(cursor, counts, ks, ke):
    if cursor.span_eq(ks, ke, "bvar") or cursor.span_eq(ks, ke, "sort"):
        cursor.read_int()
        return
    if cursor.span_eq(ks, ke, "natVal") or cursor.span_eq(ks, ke, "strVal"):
        cursor.skip_string()
        return
    if cursor.span_eq(ks, ke, "const"):
        _skip_value(cursor)
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
                counts.bump(fn_eidx)
                counts.bump(arg_eidx)
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
                counts.bump(type_eidx)
                counts.bump(body_eidx)
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
                _skip_value(cursor)
            else:
                raise MalformedLine("unexpected key in letE")
            if cursor.maybe('}'):
                counts.bump(type_eidx)
                counts.bump(value_eidx)
                counts.bump(body_eidx)
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
                counts.bump(struct_eidx)
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
                _skip_value(cursor)
            else:
                raise MalformedLine("unexpected key in mdata")
            if cursor.maybe('}'):
                if expr_eidx < 0:
                    raise MalformedLine("mdata missing `expr`")
                counts.bump(expr_eidx)
                return
            cursor.expect(',')
    raise MalformedLine("unknown expr discriminator")


def _prescan_decl(cursor, counts, has_value):
    cursor.expect('{')
    type_eidx = 0
    value_eidx = 0
    while True:
        s, e = cursor.read_key_span()
        if cursor.span_eq(s, e, "type"):
            type_eidx = cursor.read_int()
        elif has_value and cursor.span_eq(s, e, "value"):
            value_eidx = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            counts.bump(type_eidx)
            if has_value:
                counts.bump(value_eidx)
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
                            _skip_value(cursor)
                        if cursor.maybe('}'):
                            counts.bump(rhs_eidx)
                            break
                        cursor.expect(',')
                    if cursor.maybe(']'):
                        break
                    cursor.expect(',')
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            counts.bump(type_eidx)
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
                _skip_value(cursor)
            if cursor.maybe('}'):
                counts.bump(type_eidx)
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
            _skip_value(cursor)
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
        counts.ensure(eidx)
        return
    if cursor.span_eq(ks, ke, "thm") or cursor.span_eq(ks, ke, "def") or cursor.span_eq(ks, ke, "opaque"):
        _prescan_decl(cursor, counts, True)
        return
    if cursor.span_eq(ks, ke, "axiom") or cursor.span_eq(ks, ke, "quot"):
        _prescan_decl(cursor, counts, False)
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
    counts.ensure(eidx)


def _make_stream_driver(prescan):
    """Import-time factory generating both 256KB raw-buffer chunk-streaming loops
    (``_consume_stream`` for `EnvironmentBuilder.consume`, ``_prescan_stream``
    for `prescan_refcounts`) with zero per-chunk GC string allocations."""

    def _stream_lines(stream, target, hook=None):
        cursor = LineCursor("")
        n = 0
        stop_on_decl = (not prescan) and (hook is not None)
        if not we_are_translated():
            tail = ""
            while True:
                chunk = stream.read(_STREAM_BUF_CAP)
                if not chunk:
                    if tail:
                        end = len(tail)
                        if end > 0 and tail[end - 1] == '\r':
                            end -= 1
                        cursor.reset(tail, 0, end)
                        if prescan:
                            _prescan_line(cursor, target)
                        else:
                            parse_cursor(cursor, target)
                            if hook is not None:
                                while n < len(target.declarations):
                                    if hook.on_declaration(target.declarations[n]):
                                        return
                                    n += 1
                    return
                if tail:
                    chunk = tail + chunk
                    tail = ""
                clen = len(chunk)
                last_nl = chunk.rfind('\n')
                if last_nl < 0:
                    tail = chunk
                    continue
                limit = last_nl + 1
                pos = 0
                while pos <= last_nl:
                    if prescan:
                        res = _prescan_chunk_fast_raw(chunk, pos, limit, target)
                    else:
                        res = _parse_chunk_fast_raw(
                            chunk, pos, limit, target, stop_on_decl,
                        )
                    if res >= 0:
                        pos = res
                    else:
                        pos = ~res
                        nl = chunk.find('\n', pos)
                        end = nl - 1 if nl > pos and chunk[nl - 1] == '\r' else nl
                        cursor.reset(chunk, pos, end)
                        if prescan:
                            _prescan_line_general(cursor, target)
                        else:
                            parse_cursor_general(cursor, target)
                        pos = nl + 1
                    if not prescan and hook is not None:
                        while n < len(target.declarations):
                            if hook.on_declaration(target.declarations[n]):
                                return
                            n += 1
                if pos < clen:
                    tail = chunk[pos:]
        fd = -1
        if isinstance(stream, streamio.DiskFile) and stream.signal_checker is None:
            fd = stream.fd
        cap = _STREAM_BUF_CAP
        buf = lltype.malloc(rffi.CCHARP.TO, cap, flavor='raw')
        rem = 0
        try:
            while True:
                avail = cap - rem
                if fd >= 0:
                    got = _raw_read_fd(fd, rffi.ptradd(buf, rem), avail)
                else:
                    chunk = stream.read(avail)
                    if not chunk:
                        got = 0
                    else:
                        assert chunk is not None
                        got = len(chunk)
                        if rem + got > cap:
                            new_cap = cap * 2
                            while new_cap < rem + got:
                                new_cap *= 2
                            buf = _grow_raw_buf(buf, rem, new_cap)
                            cap = new_cap
                        with rffi.scoped_nonmovingbuffer(chunk) as src:
                            rffi.c_memcpy(
                                rffi.cast(rffi.VOIDP, rffi.ptradd(buf, rem)),
                                rffi.cast(rffi.CONST_VOIDP, src),
                                got,
                            )
                if got == 0:
                    if rem > 0:
                        end = rem
                        if _load_u8(buf, end - 1) == 13:
                            end -= 1
                        tail = _slice_buf(buf, 0, end)
                        cursor.reset(tail, 0, end)
                        if prescan:
                            _prescan_line(cursor, target)
                        else:
                            parse_cursor(cursor, target)
                            if hook is not None:
                                while n < len(target.declarations):
                                    if hook.on_declaration(target.declarations[n]):
                                        return
                                    n += 1
                    return
                clen = rem + got
                last_nl = _rfind_nl(buf, 0, clen)
                if last_nl < 0:
                    if clen == cap:
                        buf = _grow_raw_buf(buf, clen, cap * 2)
                        cap *= 2
                    rem = clen
                    continue
                limit = last_nl + 1
                pos = 0
                while pos <= last_nl:
                    if prescan:
                        res = _prescan_chunk_fast_raw(buf, pos, limit, target)
                    else:
                        res = _parse_chunk_fast_raw(
                            buf, pos, limit, target, stop_on_decl,
                        )
                    if res >= 0:
                        pos = res
                    else:
                        pos = ~res
                        assert pos >= 0
                        nl_next = _find_nl(buf, pos, limit)
                        nl = nl_next - 1
                        end = nl
                        if end > pos and _load_u8(buf, end - 1) == 13:
                            end -= 1
                        line = _slice_buf(buf, pos, end)
                        cursor.reset(line, 0, len(line))
                        if prescan:
                            _prescan_line_general(cursor, target)
                        else:
                            parse_cursor_general(cursor, target)
                        pos = nl_next
                    if not prescan and hook is not None:
                        while n < len(target.declarations):
                            if hook.on_declaration(target.declarations[n]):
                                return
                            n += 1
                rem = clen - pos
                if rem > 0:
                    if we_are_translated() and rem <= pos:
                        rffi.c_memcpy(
                            rffi.cast(rffi.VOIDP, buf),
                            rffi.cast(rffi.CONST_VOIDP, rffi.ptradd(buf, pos)),
                            rem,
                        )
                    else:
                        k = 0
                        while k < rem:
                            buf[k] = buf[pos + k]
                            k += 1
        finally:
            lltype.free(buf, flavor='raw')

    _stream_lines.__name__ = (
        "_prescan_stream" if prescan else "_consume_stream"
    )
    return _stream_lines


_consume_stream = _make_stream_driver(False)
_prescan_stream = _make_stream_driver(True)


def prescan_refcounts(stream, size_hint=65536):
    """Scan an export stream (positioned after its metadata line) at raw-byte
    level and return a ``RefCountTable`` of parse-time expression reference
    counts."""
    counts = RefCountTable(size_hint)
    try:
        _prescan_stream(stream, counts)
        return counts
    except:
        counts.free()
        raise
