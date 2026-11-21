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
from textwrap import dedent

from rpython.rlib.objectmodel import newlist_hint
from rpython.rlib.rbigint import rbigint

from rpylean import objects
from rpylean._line_parser import LineCursor
from rpylean.exceptions import ExportError, MalformedLine, ReflexiveKError


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


def _match_binder_info_compact(cursor):
    """Match a compact ``binderInfo`` string value + closing quote without
    allocating. Returns 0=default, 1=implicit, 2=instImplicit,
    3=strictImplicit, or -1 on mismatch."""
    p = cursor.pos
    if p >= cursor.length:
        return -1
    c = cursor.line[p]
    if c == 'd':
        if cursor.match_lit('default"'):
            return 0
    elif c == 'i':
        if cursor.match_lit('implicit"'):
            return 1
        if cursor.match_lit('instImplicit"'):
            return 2
    elif c == 's':
        if cursor.match_lit('strictImplicit"'):
            return 3
    return -1


def _binder_from_code(name, code, type):
    if code == 0:
        return name.binder(type=type)
    if code == 1:
        return name.implicit_binder(type=type)
    if code == 2:
        return name.instance_binder(type=type)
    return name.strict_implicit_binder(type=type)


def _try_parse_compact(cursor, builder):
    """Fast zero-key-allocation path for canonical compact lean4export lines
    (no whitespace, alphabetical keys). Returns True if handled; on any
    deviation the caller rewinds ``cursor.pos`` and uses the general path."""
    line = cursor.line
    p = cursor.pos
    end = cursor.length
    if p + 6 > end or line[p] != '{' or line[p + 1] != '"':
        return False
    c2 = line[p + 2]
    if c2 == 'a':
        # {"app":{"arg":A,"fn":F},"ie":E}
        if cursor.match_lit('{"app":{"arg":'):
            arg_eidx = cursor.read_uint_compact()
            if arg_eidx >= 0 and cursor.match_lit(',"fn":'):
                fn_eidx = cursor.read_uint_compact()
                if fn_eidx >= 0 and cursor.match_lit('},"ie":'):
                    eidx = cursor.read_uint_compact()
                    if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                        builder.register_expr(
                            eidx,
                            objects.W_App(
                                builder.ref_expr(fn_eidx),
                                builder.ref_expr(arg_eidx),
                            ),
                        )
                        return True
        return False
    if c2 == 'c':
        # {"const":{"name":N,"us":[...]},"ie":E}
        if cursor.match_lit('{"const":{"name":'):
            nidx = cursor.read_uint_compact()
            if nidx >= 0 and cursor.match_lit(',"us":['):
                if cursor.pos < end and line[cursor.pos] == ']':
                    cursor.pos += 1
                    if cursor.match_lit('},"ie":'):
                        eidx = cursor.read_uint_compact()
                        if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            builder.register_expr(
                                eidx, builder.names[nidx].const_empty(),
                            )
                            return True
                    return False
                l0 = cursor.read_uint_compact()
                if l0 < 0 or cursor.pos >= end:
                    return False
                ch = line[cursor.pos]
                if ch == ']':
                    cursor.pos += 1
                    if cursor.match_lit('},"ie":'):
                        eidx = cursor.read_uint_compact()
                        if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            builder.register_expr(
                                eidx,
                                objects._mk_w_const1(
                                    builder.names[nidx], builder.levels[l0],
                                ),
                            )
                            return True
                    return False
                if ch != ',':
                    return False
                cursor.pos += 1
                l1 = cursor.read_uint_compact()
                if l1 < 0 or cursor.pos >= end:
                    return False
                ch = line[cursor.pos]
                if ch == ']':
                    cursor.pos += 1
                    if cursor.match_lit('},"ie":'):
                        eidx = cursor.read_uint_compact()
                        if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            builder.register_expr(
                                eidx,
                                objects._mk_w_const2(
                                    builder.names[nidx],
                                    builder.levels[l0],
                                    builder.levels[l1],
                                ),
                            )
                            return True
                    return False
                if ch != ',':
                    return False
                cursor.pos += 1
                levels = [builder.levels[l0], builder.levels[l1]]
                while True:
                    lidx = cursor.read_uint_compact()
                    if lidx < 0:
                        return False
                    levels.append(builder.levels[lidx])
                    if cursor.pos >= end:
                        return False
                    ch = line[cursor.pos]
                    if ch == ']':
                        cursor.pos += 1
                        break
                    if ch != ',':
                        return False
                    cursor.pos += 1
                if cursor.match_lit('},"ie":'):
                    eidx = cursor.read_uint_compact()
                    if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                        builder.register_expr(
                            eidx, builder.names[nidx].const(levels),
                        )
                        return True
        return False
    if c2 == 'i':
        c3 = line[p + 3]
        if c3 == 'e':
            # {"ie":E,"lam":... | "letE":... | "natVal":... | "sort":L | "proj":...}
            if cursor.match_lit('{"ie":'):
                eidx = cursor.read_uint_compact()
                if eidx < 0 or cursor.pos + 4 >= end or line[cursor.pos] != ',' or line[cursor.pos + 1] != '"':
                    return False
                d0 = line[cursor.pos + 2]
                if d0 == 'l':
                    if cursor.match_lit(',"lam":{"binderInfo":"'):
                        bcode = _match_binder_info_compact(cursor)
                        if bcode >= 0 and cursor.match_lit(',"body":'):
                            body_eidx = cursor.read_uint_compact()
                            if body_eidx >= 0 and cursor.match_lit(',"name":'):
                                name_idx = cursor.read_uint_compact()
                                if name_idx >= 0 and cursor.match_lit(',"type":'):
                                    type_eidx = cursor.read_uint_compact()
                                    if type_eidx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                        bound = _binder_from_code(
                                            builder.names[name_idx],
                                            bcode,
                                            builder.ref_expr(type_eidx),
                                        )
                                        builder.register_expr(
                                            eidx,
                                            objects.W_Lambda(
                                                bound,
                                                builder.ref_expr(body_eidx),
                                            ),
                                        )
                                        return True
                    elif cursor.match_lit(',"letE":{"body":'):
                        body_eidx = cursor.read_uint_compact()
                        if body_eidx >= 0 and cursor.match_lit(',"name":'):
                            name_idx = cursor.read_uint_compact()
                            if name_idx >= 0 and (
                                    cursor.match_lit(',"nondep":false,"type":')
                                    or cursor.match_lit(',"nondep":true,"type":')):
                                type_eidx = cursor.read_uint_compact()
                                if type_eidx >= 0 and cursor.match_lit(',"value":'):
                                    value_eidx = cursor.read_uint_compact()
                                    if value_eidx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                        builder.register_expr(
                                            eidx,
                                            objects.W_Let(
                                                builder.names[name_idx],
                                                builder.ref_expr(type_eidx),
                                                builder.ref_expr(value_eidx),
                                                builder.ref_expr(body_eidx),
                                            ),
                                        )
                                        return True
                elif d0 == 's':
                    if cursor.match_lit(',"sort":'):
                        lidx = cursor.read_uint_compact()
                        if lidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            builder.register_expr(
                                eidx, builder.levels[lidx].sort(),
                            )
                            return True
                elif d0 == 'p':
                    if cursor.match_lit(',"proj":{"idx":'):
                        idx = cursor.read_uint_compact()
                        if idx >= 0 and cursor.match_lit(',"struct":'):
                            struct_eidx = cursor.read_uint_compact()
                            if struct_eidx >= 0 and cursor.match_lit(',"typeName":'):
                                tname_idx = cursor.read_uint_compact()
                                if tname_idx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                    builder.register_expr(
                                        eidx,
                                        builder.names[tname_idx].proj(
                                            idx, builder.ref_expr(struct_eidx),
                                        ),
                                    )
                                    return True
                elif d0 == 'n':
                    if cursor.match_lit(',"natVal":"'):
                        q = cursor.pos
                        val = 0
                        zero = ord('0')
                        digits = 0
                        while q < end and digits < 18:
                            ch = line[q]
                            if ch < '0' or ch > '9':
                                break
                            val = val * 10 + ord(ch) - zero
                            q += 1
                            digits += 1
                        if digits > 0 and q < end and line[q] == '"':
                            cursor.pos = q
                            if cursor.match_lit('"}') and cursor.at_eol():
                                builder.register_expr(
                                    eidx, objects._mk_w_litnat(rbigint.fromint(val)),
                                )
                                return True
            return False
        if c3 == 'n':
            # {"in":N,"str":{"pre":P,"str":"..."}} or {"in":N,"num":{"i":I,"pre":P}}
            if cursor.match_lit('{"in":'):
                nidx = cursor.read_uint_compact()
                if nidx >= 0:
                    if cursor.match_lit(',"str":{"pre":'):
                        pre = cursor.read_uint_compact()
                        if pre >= 0 and cursor.match_lit(',"str":'):
                            part = cursor.read_string()
                            if cursor.match_lit('}}') and cursor.at_eol():
                                builder.register_name(
                                    nidx, builder.names[pre].child(part),
                                )
                                return True
                    elif cursor.match_lit(',"num":{"i":'):
                        id_val = cursor.read_uint_compact()
                        if id_val >= 0 and cursor.match_lit(',"pre":'):
                            pre = cursor.read_uint_compact()
                            if pre >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                builder.register_name(
                                    nidx,
                                    builder.names[pre].num_child(
                                        rbigint.fromint(id_val),
                                    ),
                                )
                                return True
            return False
        if c3 == 'l':
            # {"il":U,"succ":P | "param":N | "max":[L,R] | "imax":[L,R]}
            if cursor.match_lit('{"il":'):
                uidx = cursor.read_uint_compact()
                if uidx >= 0:
                    if cursor.match_lit(',"succ":'):
                        parent = cursor.read_uint_compact()
                        if parent >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            builder.register_level(
                                uidx, builder.levels[parent].succ(),
                            )
                            return True
                    elif cursor.match_lit(',"param":'):
                        nidx = cursor.read_uint_compact()
                        if nidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            builder.register_level(
                                uidx, builder.names[nidx].as_level_param(),
                            )
                            return True
                    elif cursor.match_lit(',"max":['):
                        lhs = cursor.read_uint_compact()
                        if lhs >= 0 and cursor.match_lit(','):
                            rhs = cursor.read_uint_compact()
                            if rhs >= 0 and cursor.match_lit(']}') and cursor.at_eol():
                                builder.register_level(
                                    uidx,
                                    objects.level_max(
                                        builder.levels[lhs],
                                        builder.levels[rhs],
                                    ),
                                )
                                return True
                    elif cursor.match_lit(',"imax":['):
                        lhs = cursor.read_uint_compact()
                        if lhs >= 0 and cursor.match_lit(','):
                            rhs = cursor.read_uint_compact()
                            if rhs >= 0 and cursor.match_lit(']}') and cursor.at_eol():
                                builder.register_level(
                                    uidx,
                                    objects.level_imax(
                                        builder.levels[lhs],
                                        builder.levels[rhs],
                                    ),
                                )
                                return True
            return False
        return False
    if c2 == 'f':
        # {"forallE":{"binderInfo":"...","body":B,"name":N,"type":T},"ie":E}
        if cursor.match_lit('{"forallE":{"binderInfo":"'):
            bcode = _match_binder_info_compact(cursor)
            if bcode >= 0 and cursor.match_lit(',"body":'):
                body_eidx = cursor.read_uint_compact()
                if body_eidx >= 0 and cursor.match_lit(',"name":'):
                    name_idx = cursor.read_uint_compact()
                    if name_idx >= 0 and cursor.match_lit(',"type":'):
                        type_eidx = cursor.read_uint_compact()
                        if type_eidx >= 0 and cursor.match_lit('},"ie":'):
                            eidx = cursor.read_uint_compact()
                            if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                                bound = _binder_from_code(
                                    builder.names[name_idx],
                                    bcode,
                                    builder.ref_expr(type_eidx),
                                )
                                builder.register_expr(
                                    eidx,
                                    objects.W_ForAll(
                                        bound,
                                        builder.ref_expr(body_eidx),
                                    ),
                                )
                                return True
        return False
    if c2 == 'b':
        # {"bvar":B,"ie":E}
        if cursor.match_lit('{"bvar":'):
            bidx = cursor.read_uint_compact()
            if bidx >= 0 and cursor.match_lit(',"ie":'):
                eidx = cursor.read_uint_compact()
                if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                    builder.register_expr(eidx, objects._mk_w_bvar(bidx))
                    return True
        return False
    if c2 == 't':
        # {"thm":{"levelParams":[...],"name":N,"type":T,"value":V}}
        if cursor.match_lit('{"thm":{"levelParams":['):
            if cursor.pos < end and line[cursor.pos] == ']':
                cursor.pos += 1
                levels = []
            else:
                levels = []
                while True:
                    lidx = cursor.read_uint_compact()
                    if lidx < 0:
                        return False
                    levels.append(builder.names[lidx])
                    if cursor.pos >= end:
                        return False
                    ch = line[cursor.pos]
                    if ch == ']':
                        cursor.pos += 1
                        break
                    if ch != ',':
                        return False
                    cursor.pos += 1
            if cursor.match_lit(',"name":'):
                name_idx = cursor.read_uint_compact()
                if name_idx >= 0 and cursor.match_lit(',"type":'):
                    type_eidx = cursor.read_uint_compact()
                    if type_eidx >= 0 and cursor.match_lit(',"value":'):
                        value_eidx = cursor.read_uint_compact()
                        if value_eidx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                            decl = builder.names[name_idx].theorem(
                                levels=levels,
                                type=builder.ref_expr(type_eidx),
                                value=builder.ref_expr(value_eidx),
                            )
                            builder.register_declaration(decl)
                            return True
        return False
    return False


def parse_cursor(cursor, builder):
    """
    Parse a single lean4export NDJSON record from ``cursor`` and apply it to
    ``builder`` via the appropriate ``register_*`` call.
    """
    start = cursor.pos
    if _try_parse_compact(cursor, builder):
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


def _skip_value(cursor):
    """Skip a JSON value of any shape (for fields the parser ignores)."""
    cursor.skip_ws()
    if cursor.pos >= cursor.length:
        raise MalformedLine("unexpected end of input")
    c = cursor.line[cursor.pos]
    if c == '"':
        cursor.read_string()
    elif c == '-' or ('0' <= c <= '9'):
        cursor.read_int()
    elif c == 't':
        cursor.pos += 4
    elif c == 'f':
        cursor.pos += 5
    elif c == 'n':
        cursor.pos += 4
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
    version = ""
    if cursor.maybe('}'):
        return version
    while True:
        key = cursor.read_key()
        if key == "format" or key == "exporter":
            version = _parse_format_inner(cursor)
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return version
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

def _ensure_refcount_slot(counts, idx):
    if idx < 0:
        raise MalformedLine("negative expr index")
    n = len(counts)
    if idx >= n:
        if idx == n:
            counts.append(0)
        else:
            delta = idx - n + 1
            assert delta > 0
            counts.extend([0] * delta)


def _bump_refcount_slot(counts, idx):
    if idx < 0:
        raise MalformedLine("negative expr index")
    n = len(counts)
    if idx >= n:
        delta = idx - n + 1
        assert delta > 0
        counts.extend([0] * delta)
    counts[idx] += 1


def _try_prescan_compact(cursor, counts):
    """Fast raw-byte prescan for compact canonical lean4export lines.
    Returns True if handled (advancing ``cursor.pos`` past EOL in chunk mode);
    otherwise the caller falls back to the general structural prescanner."""
    line = cursor.line
    p = cursor.pos
    end = cursor.length
    if p + 6 > end or line[p] != '{' or line[p + 1] != '"':
        return False
    c2 = line[p + 2]
    if c2 == 'a':
        # {"app":{"arg":A,"fn":F},"ie":E}
        if cursor.match_lit('{"app":{"arg":'):
            arg_eidx = cursor.read_uint_compact()
            if arg_eidx >= 0 and cursor.match_lit(',"fn":'):
                fn_eidx = cursor.read_uint_compact()
                if fn_eidx >= 0 and cursor.match_lit('},"ie":'):
                    eidx = cursor.read_uint_compact()
                    if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                        _ensure_refcount_slot(counts, eidx)
                        _bump_refcount_slot(counts, fn_eidx)
                        _bump_refcount_slot(counts, arg_eidx)
                        return True
        return False
    if c2 == 'i':
        c3 = line[p + 3]
        if c3 == 'n' or c3 == 'l':
            # Name / Level lines have zero expr definitions and zero expr refs.
            if line[p + 4] == '"' and line[p + 5] == ':':
                nl = line.find('\n', p + 6)
                cursor.pos = (nl + 1) if (nl >= 0 and nl < end) else end
                return True
            return False
        if c3 == 'e':
            if cursor.match_lit('{"ie":'):
                eidx = cursor.read_uint_compact()
                if eidx < 0 or cursor.pos + 4 >= end or line[cursor.pos] != ',' or line[cursor.pos + 1] != '"':
                    return False
                d0 = line[cursor.pos + 2]
                if d0 == 's' or d0 == 'n' or d0 == 'b' or d0 == 'c':
                    # sort / strVal / natVal / bvar / const: zero expr refs!
                    if (cursor.match_lit(',"sort":')
                            or cursor.match_lit(',"strVal":')
                            or cursor.match_lit(',"natVal":')
                            or cursor.match_lit(',"bvar":')
                            or cursor.match_lit(',"const":')):
                        nl = line.find('\n', cursor.pos)
                        cursor.pos = (nl + 1) if (nl >= 0 and nl < end) else end
                        _ensure_refcount_slot(counts, eidx)
                        return True
                elif d0 == 'l':
                    if cursor.match_lit(',"lam":{"binderInfo":"'):
                        if _match_binder_info_compact(cursor) >= 0 and cursor.match_lit(',"body":'):
                            body_eidx = cursor.read_uint_compact()
                            if body_eidx >= 0 and cursor.match_lit(',"name":'):
                                name_idx = cursor.read_uint_compact()
                                if name_idx >= 0 and cursor.match_lit(',"type":'):
                                    type_eidx = cursor.read_uint_compact()
                                    if type_eidx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                        _ensure_refcount_slot(counts, eidx)
                                        _bump_refcount_slot(counts, type_eidx)
                                        _bump_refcount_slot(counts, body_eidx)
                                        return True
                    elif cursor.match_lit(',"letE":{"body":'):
                        body_eidx = cursor.read_uint_compact()
                        if body_eidx >= 0 and cursor.match_lit(',"name":'):
                            name_idx = cursor.read_uint_compact()
                            if name_idx >= 0 and (
                                    cursor.match_lit(',"nondep":false,"type":')
                                    or cursor.match_lit(',"nondep":true,"type":')):
                                type_eidx = cursor.read_uint_compact()
                                if type_eidx >= 0 and cursor.match_lit(',"value":'):
                                    value_eidx = cursor.read_uint_compact()
                                    if value_eidx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                        _ensure_refcount_slot(counts, eidx)
                                        _bump_refcount_slot(counts, type_eidx)
                                        _bump_refcount_slot(counts, value_eidx)
                                        _bump_refcount_slot(counts, body_eidx)
                                        return True
                elif d0 == 'p':
                    if cursor.match_lit(',"proj":{"idx":'):
                        idx = cursor.read_uint_compact()
                        if idx >= 0 and cursor.match_lit(',"struct":'):
                            struct_eidx = cursor.read_uint_compact()
                            if struct_eidx >= 0 and cursor.match_lit(',"typeName":'):
                                tname_idx = cursor.read_uint_compact()
                                if tname_idx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                    _ensure_refcount_slot(counts, eidx)
                                    _bump_refcount_slot(counts, struct_eidx)
                                    return True
            return False
        return False
    if c2 == 'c':
        # {"const":{"name":N,"us":[...]},"ie":E} -> zero expr refs, just need E!
        if cursor.match_lit('{"const":{"name":'):
            if cursor.read_uint_compact() >= 0 and cursor.match_lit(',"us":['):
                q = cursor.pos
                while q < end and line[q] != ']':
                    q += 1
                if q < end:
                    cursor.pos = q + 1
                    if cursor.match_lit('},"ie":'):
                        eidx = cursor.read_uint_compact()
                        if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                            _ensure_refcount_slot(counts, eidx)
                            return True
        return False
    if c2 == 'f':
        # {"forallE":{"binderInfo":"...","body":B,"name":N,"type":T},"ie":E}
        if cursor.match_lit('{"forallE":{"binderInfo":"'):
            if _match_binder_info_compact(cursor) >= 0 and cursor.match_lit(',"body":'):
                body_eidx = cursor.read_uint_compact()
                if body_eidx >= 0 and cursor.match_lit(',"name":'):
                    name_idx = cursor.read_uint_compact()
                    if name_idx >= 0 and cursor.match_lit(',"type":'):
                        type_eidx = cursor.read_uint_compact()
                        if type_eidx >= 0 and cursor.match_lit('},"ie":'):
                            eidx = cursor.read_uint_compact()
                            if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                                _ensure_refcount_slot(counts, eidx)
                                _bump_refcount_slot(counts, type_eidx)
                                _bump_refcount_slot(counts, body_eidx)
                                return True
        return False
    if c2 == 'b':
        # {"bvar":B,"ie":E}
        if cursor.match_lit('{"bvar":'):
            bidx = cursor.read_uint_compact()
            if bidx >= 0 and cursor.match_lit(',"ie":'):
                eidx = cursor.read_uint_compact()
                if eidx >= 0 and cursor.match_lit('}') and cursor.at_eol():
                    _ensure_refcount_slot(counts, eidx)
                    return True
        return False
    if c2 == 't':
        # {"thm":{"levelParams":[...],"name":N,"type":T,"value":V}}
        if cursor.match_lit('{"thm":{"levelParams":['):
            q = cursor.pos
            while q < end and line[q] != ']':
                q += 1
            if q < end:
                cursor.pos = q + 1
                if cursor.match_lit(',"name":') and cursor.read_uint_compact() >= 0:
                    if cursor.match_lit(',"type":'):
                        type_eidx = cursor.read_uint_compact()
                        if type_eidx >= 0 and cursor.match_lit(',"value":'):
                            value_eidx = cursor.read_uint_compact()
                            if value_eidx >= 0 and cursor.match_lit('}}') and cursor.at_eol():
                                _bump_refcount_slot(counts, type_eidx)
                                _bump_refcount_slot(counts, value_eidx)
                                return True
        return False
    return False


def _skip_value_noalloc(cursor):
    """Skip any JSON value without allocating strings or lists."""
    cursor.skip_ws()
    if cursor.pos >= cursor.length:
        raise MalformedLine("unexpected end of input")
    c = cursor.line[cursor.pos]
    if c == '"':
        cursor.skip_string()
    elif c == '-' or ('0' <= c <= '9'):
        cursor.read_int()
    elif c == 't':
        cursor.pos += 4
    elif c == 'f':
        cursor.pos += 5
    elif c == 'n':
        cursor.pos += 4
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
            cursor.read_key_span()
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
    if _try_prescan_compact(cursor, counts):
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


def prescan_refcounts(stream):
    """Scan an export stream (positioned after its metadata line) at raw-byte
    level and return a ``list[int]`` of parse-time expression reference counts."""
    counts = newlist_hint(65536)
    cursor = LineCursor("")
    buf = ""
    while True:
        chunk = stream.read(262144)
        if not chunk:
            if buf:
                end = len(buf)
                if end > 0 and buf[end - 1] == '\r':
                    end -= 1
                cursor.reset(buf, 0, end)
                _prescan_line(cursor, counts)
            return counts
        if buf:
            buf = buf + chunk
        else:
            buf = chunk
        last_nl = buf.rfind('\n')
        if last_nl < 0:
            continue
        limit = last_nl + 1
        cursor.line = buf
        cursor.length = limit
        pos = 0
        while pos <= last_nl:
            cursor.pos = pos
            if _try_prescan_compact(cursor, counts):
                pos = cursor.pos
            else:
                nl = buf.find('\n', pos)
                assert nl >= 0
                end = nl
                if end > pos and buf[end - 1] == '\r':
                    end -= 1
                cursor.pos = pos
                cursor.length = end
                _prescan_line_general(cursor, counts)
                cursor.length = limit
                pos = nl + 1
        blen = len(buf)
        if pos < blen:
            assert pos >= 0
            buf = buf[pos:]
        else:
            buf = ""
