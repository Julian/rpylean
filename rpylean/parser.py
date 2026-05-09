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

from rpython.rlib.rbigint import rbigint

from rpylean import objects
from rpylean._line_parser import LineCursor
from rpylean.exceptions import ExportError, ReflexiveKError


EXPORT_VERSION = "3.1.0"


class ExportVersionError(ExportError):
    """
    The export file version doesn't match one we know how to parse.
    """

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
    """
    line = stream.readline()
    if not line:
        raise ExportVersionError(None)
    version = _parse_metadata_version(line)
    if version != EXPORT_VERSION:
        raise ExportVersionError(version)


# ---- Per-line dispatch ---------------------------------------------------

def parse_line(line, builder):
    """
    Parse a single lean4export NDJSON line and apply it to ``builder``
    via the appropriate ``register_*`` call. Lines come in 23 shapes:
    names (str/num), four kinds of universe expressions, ten kinds of
    expression atom, six declarations (axiom/def/opaque/thm/quot/inductive),
    and standalone recursors.
    """
    cursor = LineCursor(line)
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
        builder.register_name(nidx, parent.child(str(id_val)))
    else:
        raise ValueError("unknown name discriminator: %s" % second_key)


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
            raise ValueError("unexpected key %s in name str" % key)
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
            raise ValueError("unexpected key %s in name num" % key)
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
            uidx, builder.levels[lhs].max(builder.levels[rhs]),
        )
    elif disc == "imax":
        cursor.expect('[')
        lhs = cursor.read_int()
        cursor.expect(',')
        rhs = cursor.read_int()
        cursor.expect(']')
        cursor.expect('}')
        builder.register_level(
            uidx, builder.levels[lhs].imax(builder.levels[rhs]),
        )
    elif disc == "param":
        nidx = cursor.read_int()
        cursor.expect('}')
        builder.register_level(uidx, builder.names[nidx].level())
    else:
        raise ValueError("unknown universe discriminator: %s" % disc)


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
        return objects.W_BVar(id=cursor.read_int())
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
        return objects.W_LitNat(val=nat)
    if disc == "strVal":
        return objects.W_LitStr(val=cursor.read_string())
    if disc == "proj":
        return _read_proj(cursor, builder)
    raise ValueError("unknown expr discriminator: %s" % disc)


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
            raise ValueError("unexpected key %s in app" % key)
        if cursor.maybe('}'):
            return builder.exprs[fn_eidx].app(builder.exprs[arg_eidx])
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
            raise ValueError("unexpected key %s in const" % key)
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
            raise ValueError("unexpected key %s in binder" % key)
        if cursor.maybe('}'):
            bound = _binder(
                builder.names[name_idx],
                binder_info,
                builder.exprs[type_eidx],
            )
            body = builder.exprs[body_eidx]
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
    raise ValueError("Unknown binder info %s" % info)


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
            raise ValueError("unexpected key %s in letE" % key)
        if cursor.maybe('}'):
            return builder.names[name_idx].let(
                type=builder.exprs[type_eidx],
                value=builder.exprs[value_eidx],
                body=builder.exprs[body_eidx],
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
            raise ValueError("unexpected key %s in proj" % key)
        if cursor.maybe('}'):
            return builder.names[type_name_idx].proj(
                idx, builder.exprs[struct_eidx],
            )
        cursor.expect(',')


def _skip_value(cursor):
    """Skip a JSON value of any shape (for fields the parser ignores)."""
    cursor.skip_ws()
    if cursor.pos >= cursor.length:
        raise ValueError("unexpected end of input")
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
        raise ValueError("unsupported value at pos %d" % cursor.pos)


# ---- Declarations (axiom/def/opaque/thm/quot) ----------------------------

def _parse_axiom(cursor, builder):
    """Parse `{"axiom":{...}}` after `"axiom":`."""
    cursor.expect('{')
    levels = None
    name_idx = 0
    type_eidx = 0
    while True:
        key = cursor.read_key()
        if key == "levelParams":
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
                type=builder.exprs[type_eidx],
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
    while True:
        key = cursor.read_key()
        if key == "levelParams":
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
            builder.register_quotient(
                builder.names[name_idx],
                builder.exprs[type_eidx],
                [builder.names[i] for i in levels],
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
                type=builder.exprs[type_eidx],
                value=builder.exprs[value_eidx],
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
            decl = builder.names[name_idx].opaque(
                levels=[builder.names[i] for i in levels],
                type=builder.exprs[type_eidx],
                value=builder.exprs[value_eidx],
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
    while True:
        key = cursor.read_key()
        if key == "hints":
            hint = _parse_def_hint(cursor)
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
            decl = builder.names[name_idx].definition(
                levels=[builder.names[i] for i in levels],
                type=builder.exprs[type_eidx],
                value=builder.exprs[value_eidx],
                hint=hint,
            )
            builder.register_declaration(decl)
            return
        cursor.expect(',')


def _parse_def_hint(cursor):
    """Parse the polymorphic ``"hints"`` field — string or `{"regular":N}`."""
    cursor.skip_ws()
    if cursor.pos < cursor.length and cursor.line[cursor.pos] == '"':
        raw = cursor.read_string()
        if raw == "opaque":
            return objects.HINT_OPAQUE
        if raw == "abbrev":
            return objects.HINT_ABBREV
        raise ValueError("unknown def hint: %s" % raw)
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

    def __init__(self):
        self.nidx = 0
        self.type_idx = 0
        self.is_reflexive = False
        self.is_recursive = False
        self.num_nested = 0
        self.num_params = 0
        self.num_indices = 0
        self.name_idxs = []
        self.levels = []


class _IndCtor(object):
    """Fields of one entry in an inductive line's ``ctors`` array."""

    def __init__(self):
        self.nidx = 0
        self.type_idx = 0
        self.num_params = 0
        self.num_fields = 0
        self.levels = []


class _IndRec(object):
    """Fields of one entry in an inductive line's ``recs`` array, or of a
    standalone ``rec`` line."""

    def __init__(self):
        self.nidx = 0
        self.type_idx = 0
        self.k = False
        self.num_params = 0
        self.num_indices = 0
        self.num_motives = 0
        self.num_minors = 0
        self.ind_name_idxs = []
        self.rules = []
        self.levels = []


class _IndRule(object):
    """Fields of one entry in a recursor's ``rules`` array."""

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

    if len(types) == 1:
        _register_single_inductive(builder, types[0], ctors, recs)
    else:
        _register_mutual_inductive(builder, types, ctors, recs)


def _register_single_inductive(builder, type_data, ctor_records, rec_records):
    name = builder.names[type_data.nidx]
    if type_data.is_reflexive:
        for rec in rec_records:
            if rec.k:
                raise ReflexiveKError(name, builder.names[rec.nidx])

    ctor_decls = [_register_constructor(builder, c) for c in ctor_records]
    rec_decls = [_register_recursor(builder, r) for r in rec_records]

    inductive = name.inductive(
        levels=[builder.names[i] for i in type_data.levels],
        type=builder.exprs[type_data.type_idx],
        names=[builder.names[i] for i in type_data.name_idxs],
        constructors=ctor_decls,
        recursors=rec_decls,
        num_nested=type_data.num_nested,
        num_params=type_data.num_params,
        num_indices=type_data.num_indices,
        is_reflexive=type_data.is_reflexive,
        is_recursive=type_data.is_recursive,
    )
    builder.register_declaration(inductive)


def _register_mutual_inductive(builder, types, ctor_records, rec_records):
    for type_data in types:
        name = builder.names[type_data.nidx]
        if type_data.is_reflexive:
            for rec in rec_records:
                if rec.k:
                    raise ReflexiveKError(name, builder.names[rec.nidx])
        inductive = name.inductive(
            levels=[builder.names[i] for i in type_data.levels],
            type=builder.exprs[type_data.type_idx],
            names=[builder.names[i] for i in type_data.name_idxs],
            constructors=[],
            recursors=[],
            num_nested=type_data.num_nested,
            num_params=type_data.num_params,
            num_indices=type_data.num_indices,
            is_reflexive=type_data.is_reflexive,
            is_recursive=type_data.is_recursive,
        )
        builder.register_declaration(inductive)

    for ctor in ctor_records:
        _register_constructor(builder, ctor)
    for rec in rec_records:
        _register_recursor(builder, rec)


def _register_constructor(builder, ctor):
    decl = builder.names[ctor.nidx].constructor(
        levels=[builder.names[i] for i in ctor.levels],
        type=builder.exprs[ctor.type_idx],
        num_params=ctor.num_params,
        num_fields=ctor.num_fields,
    )
    builder.register_declaration(decl)
    return decl


def _register_recursor(builder, rec):
    decl = builder.names[rec.nidx].recursor(
        levels=[builder.names[i] for i in rec.levels],
        type=builder.exprs[rec.type_idx],
        names=[builder.names[i] for i in rec.ind_name_idxs],
        rules=[
            objects.W_RecRule(
                ctor_name=builder.names[r.ctor_nidx],
                num_fields=r.num_fields,
                val=builder.exprs[r.rhs_eidx],
            ) for r in rec.rules
        ],
        k=rec.k,
        num_params=rec.num_params,
        num_indices=rec.num_indices,
        num_motives=rec.num_motives,
        num_minors=rec.num_minors,
    )
    builder.register_declaration(decl)
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
        elif key == "isRec":
            type_data.is_recursive = cursor.read_bool()
        elif key == "isReflexive":
            type_data.is_reflexive = cursor.read_bool()
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
            cursor.read_int()  # not used
        elif key == "induct":
            cursor.read_int()  # not used
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
    while True:
        key = cursor.read_key()
        if key == "version":
            version = cursor.read_string()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            return version
        cursor.expect(',')
