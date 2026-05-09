"""
See https://ammkrn.github.io/type_checking_in_lean4/export_format.html
"""

from __future__ import print_function

from StringIO import StringIO
from pprint import pprint as pp  # noqa: F401
from textwrap import dedent

from rpython.rlib.rbigint import rbigint

from rpylean import objects
from rpylean._line_parser import LineCursor
from rpylean._rjson import loads as from_json, json_true as JSON_TRUE
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


class Node(object):
    """
    An AST node.
    """

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return vars(self) == vars(other)

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        contents = ("%s=%r" % (k, v) for k, v in self.__dict__.iteritems())
        return "<%s %s>" % (self.__class__.__name__, ", ".join(contents))


class NameStr(Node):
    @staticmethod
    def from_dict(value):
        string = value["str"].value_object()
        return NameStr(
            nidx=value["in"].value_int(),
            parent_nidx=string["pre"].value_int(),
            part=string["str"].value_string(),
        )

    def __init__(self, nidx, parent_nidx, part):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.part = part

    def compile(self, builder):
        parent = builder.names[self.parent_nidx]
        builder.register_name(nidx=self.nidx, name=parent.child(self.part))


class NameNum(Node):
    @staticmethod
    def from_dict(value):
        num = value["num"].value_object()
        return NameNum(
            nidx=value["in"].value_int(),
            parent_nidx=num["pre"].value_int(),
            id=num["i"].value_int(),
        )

    def __init__(self, nidx, parent_nidx, id):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.id = id

    def compile(self, builder):
        parent = builder.names[self.parent_nidx]
        builder.register_name(nidx=self.nidx, name=parent.child(str(self.id)))


class Universe(Node):
    pass


class UniverseSucc(Universe):
    @staticmethod
    def from_dict(value):
        return UniverseSucc(
            uidx=value["il"].value_int(),
            parent=value["succ"].value_int(),
        )

    def __init__(self, uidx, parent):
        self.uidx = uidx
        self.parent = parent

    def compile(self, builder):
        level = builder.levels[self.parent].succ()
        builder.register_level(self.uidx, level)


class UniverseMax(Universe):
    @staticmethod
    def from_dict(value):
        lhs, rhs = value["max"].value_array()
        return UniverseMax(
            uidx=value["il"].value_int(),
            lhs=lhs.value_int(),
            rhs=rhs.value_int(),
        )

    def __init__(self, uidx, lhs, rhs):
        self.uidx = uidx
        self.lhs = lhs
        self.rhs = rhs

    def compile(self, builder):
        level = builder.levels[self.lhs].max(builder.levels[self.rhs])
        builder.register_level(self.uidx, level)


class UniverseIMax(Universe):
    @staticmethod
    def from_dict(value):
        lhs, rhs = value["imax"].value_array()
        return UniverseIMax(
            uidx=value["il"].value_int(),
            lhs=lhs.value_int(),
            rhs=rhs.value_int(),
        )

    def __init__(self, uidx, lhs, rhs):
        self.uidx = uidx
        self.lhs = lhs
        self.rhs = rhs

    def compile(self, builder):
        level = builder.levels[self.lhs].imax(builder.levels[self.rhs])
        builder.register_level(self.uidx, level)


class UniverseParam(Universe):
    @staticmethod
    def from_dict(value):
        return UniverseParam(
            uidx=value["il"].value_int(),
            nidx=value["param"].value_int(),
        )

    def __init__(self, uidx, nidx):
        self.uidx = uidx
        self.nidx = nidx

    def compile(self, builder):
        level = builder.names[self.nidx].level()
        builder.register_level(self.uidx, level)


class Expr(Node):
    def __init__(self, eidx, val):
        self.eidx = eidx
        self.val = val

    def compile(self, builder):
        w_expr = self.val.to_w_expr(builder)
        builder.register_expr(self.eidx, w_expr)


class ExprVal(Node):
    pass


class BVar(ExprVal):
    @staticmethod
    def from_dict(value):
        val = BVar(id=value["bvar"].value_int())
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, id):
        self.id = id

    def to_w_expr(self, builder):
        return objects.W_BVar(id=self.id)


class LitStr(ExprVal):
    @staticmethod
    def from_dict(value):
        val = LitStr(val=value["strVal"].value_string())
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, val):
        self.val = val

    def to_w_expr(self, builder):
        return objects.W_LitStr(val=self.val)


class LitNat(ExprVal):
    @staticmethod
    def from_dict(value):
        nat = rbigint.fromstr(value["natVal"].value_string())
        assert nat.int_ge(0)
        return Expr(eidx=value["ie"].value_int(), val=LitNat(nat))

    def __init__(self, val):
        self.val = val

    def to_w_expr(self, builder):
        return objects.W_LitNat(val=self.val)


class Sort(ExprVal):
    @staticmethod
    def from_dict(value):
        val = Sort(level=value["sort"].value_int())
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, level):
        self.level = level

    def to_w_expr(self, builder):
        return builder.levels[self.level].sort()


class Const(ExprVal):
    @staticmethod
    def from_dict(value):
        info = value["const"].value_object()
        val = Const(
            nidx=info["name"].value_int(),
            levels=[each.value_int() for each in info["us"].value_array()],
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, nidx, levels):
        self.nidx = nidx
        self.levels = levels

    def to_w_expr(self, builder):
        levels = [builder.levels[level] for level in self.levels]
        return builder.names[self.nidx].const(levels)


class Let(ExprVal):
    @staticmethod
    def from_dict(value):
        let = value["letE"].value_object()
        val = Let(
            nidx=let["name"].value_int(),
            type=let["type"].value_int(),
            value=let["value"].value_int(),
            body=let["body"].value_int(),
            # TODO: nondep = ...
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, nidx, type, value, body):
        self.nidx = nidx
        self.type = type
        self.value = value
        self.body = body

    def to_w_expr(self, builder):
        return builder.names[self.nidx].let(
            type=builder.exprs[self.type],
            value=builder.exprs[self.value],
            body=builder.exprs[self.body],
        )


class App(ExprVal):
    @staticmethod
    def from_dict(value):
        info = value["app"].value_object()
        val = App(
            fn_eidx=info["fn"].value_int(),
            arg_eidx=info["arg"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, fn_eidx, arg_eidx):
        self.fn_eidx = fn_eidx
        self.arg_eidx = arg_eidx

    def to_w_expr(self, builder):
        fn = builder.exprs[self.fn_eidx]
        arg = builder.exprs[self.arg_eidx]
        return fn.app(arg)


def binder(name, info, type):
    if info == "default":
        return name.binder(type=type)
    elif info == "implicit":
        return name.implicit_binder(type=type)
    elif info == "strictImplicit":
        return name.strict_implicit_binder(type=type)
    elif info == "instImplicit":
        return name.instance_binder(type=type)
    else:
        assert False, "Unknown binder info %s" % info


class Lambda(ExprVal):
    @staticmethod
    def from_dict(value):
        lam = value["lam"].value_object()
        val = Lambda(
            name=lam["name"].value_int(),
            type=lam["type"].value_int(),
            binder_info=lam["binderInfo"].value_string(),
            body=lam["body"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, name, type, binder_info, body):
        self.name = name
        self.type = type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, builder):
        return objects.fun(
            binder(
                name=builder.names[self.name],
                type=builder.exprs[self.type],
                info=self.binder_info,
            ),
        )(builder.exprs[self.body])


class ForAll(ExprVal):
    @staticmethod
    def from_dict(value):
        forall = value["forallE"].value_object()
        val = ForAll(
            name=forall["name"].value_int(),
            type=forall["type"].value_int(),
            binder_info=forall["binderInfo"].value_string(),
            body=forall["body"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, name, type, binder_info, body):
        self.name = name
        self.type = type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, builder):
        return objects.forall(
            binder(
                name=builder.names[self.name],
                type=builder.exprs[self.type],
                info=self.binder_info,
            )
        )(builder.exprs[self.body])


class Proj(ExprVal):
    @staticmethod
    def from_dict(value):
        proj = value["proj"].value_object()
        val = Proj(
            type_name=proj["typeName"].value_int(),
            index=proj["idx"].value_int(),
            struct=proj["struct"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, type_name, index, struct):
        self.type_name = type_name
        self.index = index
        self.struct = struct

    def to_w_expr(self, builder):
        struct = builder.exprs[self.struct]
        return builder.names[self.type_name].proj(self.index, struct)


class Definition(Node):
    @staticmethod
    def from_dict(value):
        info = value["def"].value_object()
        hints = info["hints"]
        if hints.is_object:
            hint = hints.value_object()["regular"].value_int()
        else:
            raw = hints.value_string()
            if raw == "opaque":
                hint = objects.HINT_OPAQUE
            elif raw == "abbrev":
                hint = objects.HINT_ABBREV
            else:
                assert False, hints
        return Definition(
            nidx=info["name"].value_int(),
            type=info["type"].value_int(),
            value=info["value"].value_int(),
            hint=hint,
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(self, nidx, type, value, hint, levels):
        self.nidx = nidx
        self.type = type
        self.value = value
        self.hint = hint
        self.levels = levels

    def compile(self, builder):
        declaration = builder.names[self.nidx].definition(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type],
            value=builder.exprs[self.value],
            hint=self.hint,
        )
        builder.register_declaration(declaration)


class Opaque(Node):
    @staticmethod
    def from_dict(value):
        info = value["opaque"].value_object()
        return Opaque(
            nidx=info["name"].value_int(),
            type=info["type"].value_int(),
            value=info["value"].value_int(),
            # TODO: isUnsafe and name_idxs
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(self, nidx, type, value, levels):
        self.nidx = nidx
        self.type = type
        self.value = value
        self.levels = levels

    def compile(self, builder):
        declaration = builder.names[self.nidx].opaque(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type],
            value=builder.exprs[self.value],
        )
        builder.register_declaration(declaration)


class Theorem(Node):
    @staticmethod
    def from_dict(value):
        info = value["thm"].value_object()
        return Theorem(
            nidx=info["name"].value_int(),
            type=info["type"].value_int(),
            value=info["value"].value_int(),
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(self, nidx, type, value, levels):
        self.nidx = nidx
        self.type = type
        self.value = value
        self.levels = levels

    def compile(self, builder):
        declaration = builder.names[self.nidx].theorem(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type],
            value=builder.exprs[self.value],
        )
        builder.register_declaration(declaration)


class MutualTheorems(Node):
    """
    A block of mutually recursive theorems.
    """

    def __init__(self, theorems):
        self.theorems = theorems

    def compile(self, builder):
        for each in self.theorems:
            each.compile(builder)


class Axiom(Node):
    @staticmethod
    def from_dict(value):
        info = value["axiom"].value_object()
        return Axiom(
            nidx=info["name"].value_int(),
            type=info["type"].value_int(),
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(self, nidx, type, levels):
        self.nidx = nidx
        self.type = type
        self.levels = levels

    def compile(self, builder):
        declaration = builder.names[self.nidx].axiom(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type],
        )
        builder.register_declaration(declaration)


class Quot(Node):
    @staticmethod
    def from_dict(value):
        info = value["quot"].value_object()
        return Quot(
            nidx=info["name"].value_int(),
            type=info["type"].value_int(),
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(self, nidx, type, levels):
        self.nidx = nidx
        self.type = type
        self.levels = levels

    def compile(self, builder):
        name = builder.names[self.nidx]
        levels = [builder.names[nidx] for nidx in self.levels]
        builder.register_quotient(name, builder.exprs[self.type], levels)


class MutualInductive(Node):
    """
    Mutually inductive types.
    """

    def __init__(self, inductives, constructors, recursors):
        self.inductives = inductives
        self.constructors = constructors
        self.recursors = recursors

    def compile(self, builder):
        for each in self.inductives:
            each.compile(builder)
        for each in self.constructors:
            each.compile(builder)
        for each in self.recursors:
            each.compile(builder)


class Inductive(Node):
    """
    An inductive type.
    """

    @staticmethod
    def from_dict(value):
        info = value["inductive"].value_object()

        inductives = info["types"].value_array()
        constructors = [
            Constructor.from_dict(each.value_object())
            for each in info["ctors"].value_array()
        ]
        recursors = [
            Recursor.from_dict(each.value_object())
            for each in info["recs"].value_array()
        ]

        if len(inductives) == 1:
            inductive = inductives[0].value_object()
            return Inductive.single(inductive, constructors, recursors)
        return MutualInductive(
            inductives=[
                Inductive.single(each.value_object(), [], [])
                for each in inductives
            ],
            constructors=constructors,
            recursors=recursors,
        )

    @staticmethod
    def single(inductive, constructors, recursors):
        return Inductive(
            nidx=inductive["name"].value_int(),
            type_idx=inductive["type"].value_int(),
            is_reflexive=inductive["isReflexive"] is JSON_TRUE,
            is_recursive=inductive["isRec"] is JSON_TRUE,
            num_nested=inductive["numNested"].value_int(),
            num_params=inductive["numParams"].value_int(),
            num_indices=inductive["numIndices"].value_int(),
            name_idxs=[
                each.value_int() for each in inductive["all"].value_array()
            ],
            constructors=constructors,
            recursors=recursors,
            levels=[
                each.value_int()
                for each in inductive["levelParams"].value_array()
            ],
        )

    def __init__(
        self,
        nidx,
        type_idx,
        constructors,
        recursors,
        is_reflexive,
        is_recursive,
        num_nested,
        num_params,
        num_indices,
        name_idxs,
        levels,
    ):
        self.nidx = nidx
        self.type_idx = type_idx
        self.constructors = constructors
        self.recursors = recursors
        self.is_reflexive = is_reflexive
        self.is_recursive = is_recursive
        self.num_nested = num_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.name_idxs = name_idxs
        self.levels = levels

    def compile(self, builder):
        name = builder.names[self.nidx]
        if self.is_reflexive:
            for rec in self.recursors:
                if rec.k:
                    raise ReflexiveKError(name, builder.names[rec.nidx])
        declaration = name.inductive(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type_idx],
            names=[builder.names[nidx] for nidx in self.name_idxs],
            constructors=[each.compile(builder) for each in self.constructors],
            recursors=[each.compile(builder) for each in self.recursors],
            num_nested=self.num_nested,
            num_params=self.num_params,
            num_indices=self.num_indices,
            is_reflexive=self.is_reflexive,
            is_recursive=self.is_recursive,
        )
        builder.register_declaration(declaration)


class Constructor(Node):
    @staticmethod
    def from_dict(info):
        return Constructor(
            nidx=info["name"].value_int(),
            type_idx=info["type"].value_int(),
            inductive_nidx=info["induct"].value_int(),
            cidx=info["cidx"].value_int(),
            num_params=info["numParams"].value_int(),
            num_fields=info["numFields"].value_int(),
            # TODO: isUnsafe
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(
        self,
        nidx,
        type_idx,
        inductive_nidx,
        cidx,
        num_params,
        num_fields,
        levels,
    ):
        self.nidx = nidx
        self.type_idx = type_idx
        self.inductive_nidx = inductive_nidx
        self.cidx = cidx
        self.num_params = num_params
        self.num_fields = num_fields
        self.levels = levels

    def compile(self, builder):
        """
        Add this constructor to the environment.

        Then check whether our parent inductive type has all its constructors
        now set, in which case compile it too.
        """
        constructor = builder.names[self.nidx].constructor(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type_idx],
            num_params=self.num_params,
            num_fields=self.num_fields,
        )
        builder.register_declaration(constructor)
        return constructor


class Recursor(Node):
    @staticmethod
    def from_dict(info):
        return Recursor(
            nidx=info["name"].value_int(),
            type_idx=info["type"].value_int(),
            ind_name_idxs=[
                each.value_int() for each in info["all"].value_array()
            ],
            rules=[
                RecRule.from_dict(each.value_object())
                for each in info["rules"].value_array()
            ],
            k=info["k"] is JSON_TRUE,
            num_params=info["numParams"].value_int(),
            num_indices=info["numIndices"].value_int(),
            num_motives=info["numMotives"].value_int(),
            num_minors=info["numMinors"].value_int(),
            levels=[
                each.value_int() for each in info["levelParams"].value_array()
            ],
        )

    def __init__(
        self,
        nidx,
        type_idx,
        k,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ind_name_idxs,
        rules,
        levels,
    ):
        self.nidx = nidx
        self.type_idx = type_idx
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.ind_name_idxs = ind_name_idxs
        self.rules = rules
        self.levels = levels

    def compile(self, builder):
        declaration = builder.names[self.nidx].recursor(
            levels=[builder.names[nidx] for nidx in self.levels],
            type=builder.exprs[self.type_idx],
            names=[builder.names[nidx] for nidx in self.ind_name_idxs],
            rules=[each.to_w(builder) for each in self.rules],
            k=self.k,
            num_params=self.num_params,
            num_indices=self.num_indices,
            num_motives=self.num_motives,
            num_minors=self.num_minors,
        )
        builder.register_declaration(declaration)


class RecRule(Node):
    @staticmethod
    def from_dict(value):
        return RecRule(
            ctor_name_idx=value["ctor"].value_int(),
            num_fields=value["nfields"].value_int(),
            val=value["rhs"].value_int(),
        )

    def __init__(self, ctor_name_idx, num_fields, val):
        self.ctor_name_idx = ctor_name_idx
        self.num_fields = num_fields
        self.val = val

    def to_w(self, builder):
        return objects.W_RecRule(
            ctor_name=builder.names[self.ctor_name_idx],
            num_fields=self.num_fields,
            val=builder.exprs[self.val],
        )


for cls in [
    App,
    Axiom,
    BVar,
    Const,
    Constructor,
    Definition,
    ForAll,
    Inductive,
    Lambda,
    Let,
    LitNat,
    NameNum,
    NameStr,
    Opaque,
    Proj,
    Recursor,
    RecRule,
    Quot,
    Sort,
    Theorem,
    UniverseMax,
    UniverseIMax,
    UniverseParam,
    UniverseSucc,
]:
    cls.from_dict.func_name += "_" + cls.__name__


def from_export(stream):
    """
    Parse lean4export-format NDJSON from a stream.
    """
    meta_line = stream.readline()
    if not meta_line:
        raise ExportVersionError(None)

    obj = from_json(meta_line)
    meta = obj.value_object()["meta"].value_object()
    if "format" in meta:  # normal export file
        info = meta["format"].value_object()
    else:  # transition file, delete me when lean-kernel-arena updates
        info = meta["exporter"].value_object()
    version = info["version"].value_string()
    if version != EXPORT_VERSION:
        raise ExportVersionError(version)

    return from_ndjson(stream)


def from_ndjson(stream):
    """
    Parse NDJSON from a stream *without* the initial metadata line.
    """
    while True:
        line = stream.readline()
        if not line:
            return
        try:
            yield parse_line(line)
        except Exception:
            print(line)
            raise


def parse_line(line):
    """
    Parse a single lean4export NDJSON line directly into a Node, bypassing
    the generic JSON parser for the bulk of shapes.

    Inductive and Recursor lines (rare and structurally complex) fall back
    to the JSON-based path since they carry nested arrays of objects.
    """
    cursor = LineCursor(line)
    cursor.expect('{')
    first_key = cursor.read_key()

    if first_key == "in":
        return _parse_name(cursor)
    if first_key == "il":
        return _parse_universe(cursor)
    if first_key == "ie":
        return _parse_expr_ie_first(cursor)
    if first_key == "axiom":
        return _parse_axiom(cursor)
    if first_key == "def":
        return _parse_definition(cursor)
    if first_key == "opaque":
        return _parse_opaque(cursor)
    if first_key == "thm":
        return _parse_theorem(cursor)
    if first_key == "quot":
        return _parse_quot(cursor)
    if first_key == "inductive" or first_key == "rec":
        return _node_from_json(line, first_key)
    # Else: an expression where the discriminator (app, bvar, const, ...)
    # came before "ie" in this line.
    val = _parse_expr_value(cursor, first_key)
    cursor.expect(',')
    cursor.expect_key("ie")
    eidx = cursor.read_int()
    cursor.expect('}')
    return Expr(eidx=eidx, val=val)


def _node_from_json(line, first_key):
    """Fallback: parse via the generic JSON tree for complex shapes."""
    value = from_json(line)
    obj = value.value_object()
    if first_key == "inductive":
        return Inductive.from_dict(obj)
    if first_key == "rec":
        return Recursor.from_dict(obj)
    assert False, "unexpected fallback shape: %s" % first_key


# ---- Names ---------------------------------------------------------------

def _parse_name(cursor):
    """Parse `{"in":N,"str":...}` or `{"in":N,"num":...}` after `"in":`."""
    nidx = cursor.read_int()
    cursor.expect(',')
    second_key = cursor.read_key()
    if second_key == "str":
        parent_nidx, part = _parse_name_str_inner(cursor)
        cursor.expect('}')
        return NameStr(nidx=nidx, parent_nidx=parent_nidx, part=part)
    if second_key == "num":
        parent_nidx, id_val = _parse_name_num_inner(cursor)
        cursor.expect('}')
        return NameNum(nidx=nidx, parent_nidx=parent_nidx, id=id_val)
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

def _parse_universe(cursor):
    """Parse `{"il":N,"<succ|max|imax|param>":...}` after `"il":`."""
    uidx = cursor.read_int()
    cursor.expect(',')
    second_key = cursor.read_key()
    if second_key == "succ":
        parent = cursor.read_int()
        cursor.expect('}')
        return UniverseSucc(uidx=uidx, parent=parent)
    if second_key == "max":
        cursor.expect('[')
        lhs = cursor.read_int()
        cursor.expect(',')
        rhs = cursor.read_int()
        cursor.expect(']')
        cursor.expect('}')
        return UniverseMax(uidx=uidx, lhs=lhs, rhs=rhs)
    if second_key == "imax":
        cursor.expect('[')
        lhs = cursor.read_int()
        cursor.expect(',')
        rhs = cursor.read_int()
        cursor.expect(']')
        cursor.expect('}')
        return UniverseIMax(uidx=uidx, lhs=lhs, rhs=rhs)
    if second_key == "param":
        nidx = cursor.read_int()
        cursor.expect('}')
        return UniverseParam(uidx=uidx, nidx=nidx)
    raise ValueError("unknown universe discriminator: %s" % second_key)


# ---- Expressions ---------------------------------------------------------

def _parse_expr_ie_first(cursor):
    """Parse expr lines whose first key is ``"ie"``."""
    eidx = cursor.read_int()
    cursor.expect(',')
    second_key = cursor.read_key()
    val = _parse_expr_value(cursor, second_key)
    cursor.expect('}')
    return Expr(eidx=eidx, val=val)


def _parse_expr_value(cursor, disc):
    """Read the value of an expression's discriminator and return its ExprVal."""
    if disc == "bvar":
        return BVar(id=cursor.read_int())
    if disc == "sort":
        return Sort(level=cursor.read_int())
    if disc == "app":
        return _parse_app_inner(cursor)
    if disc == "const":
        return _parse_const_inner(cursor)
    if disc == "lam":
        return _parse_binder_expr(cursor, "lam")
    if disc == "forallE":
        return _parse_binder_expr(cursor, "forallE")
    if disc == "letE":
        return _parse_let_inner(cursor)
    if disc == "natVal":
        nat = rbigint.fromstr(cursor.read_string())
        assert nat.int_ge(0)
        return LitNat(val=nat)
    if disc == "strVal":
        return LitStr(val=cursor.read_string())
    if disc == "proj":
        return _parse_proj_inner(cursor)
    raise ValueError("unknown expr discriminator: %s" % disc)


def _parse_app_inner(cursor):
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
            return App(fn_eidx=fn_eidx, arg_eidx=arg_eidx)
        cursor.expect(',')


def _parse_const_inner(cursor):
    cursor.expect('{')
    nidx = 0
    levels = None
    while True:
        key = cursor.read_key()
        if key == "name":
            nidx = cursor.read_int()
        elif key == "us":
            levels = cursor.read_int_array()
        else:
            raise ValueError("unexpected key %s in const" % key)
        if cursor.maybe('}'):
            if levels is None:
                levels = []
            return Const(nidx=nidx, levels=levels)
        cursor.expect(',')


def _parse_binder_expr(cursor, kind):
    cursor.expect('{')
    binder_info = ""
    body = 0
    name = 0
    type_ = 0
    while True:
        key = cursor.read_key()
        if key == "binderInfo":
            binder_info = cursor.read_string()
        elif key == "body":
            body = cursor.read_int()
        elif key == "name":
            name = cursor.read_int()
        elif key == "type":
            type_ = cursor.read_int()
        else:
            raise ValueError("unexpected key %s in %s" % (key, kind))
        if cursor.maybe('}'):
            if kind == "lam":
                return Lambda(
                    name=name, type=type_, binder_info=binder_info, body=body,
                )
            return ForAll(
                name=name, type=type_, binder_info=binder_info, body=body,
            )
        cursor.expect(',')


def _parse_let_inner(cursor):
    cursor.expect('{')
    body = 0
    name = 0
    type_ = 0
    val = 0
    while True:
        key = cursor.read_key()
        if key == "body":
            body = cursor.read_int()
        elif key == "name":
            name = cursor.read_int()
        elif key == "nondep":
            # boolean — currently unused; just consume
            _skip_value(cursor)
        elif key == "type":
            type_ = cursor.read_int()
        elif key == "value":
            val = cursor.read_int()
        else:
            raise ValueError("unexpected key %s in letE" % key)
        if cursor.maybe('}'):
            return Let(nidx=name, type=type_, value=val, body=body)
        cursor.expect(',')


def _parse_proj_inner(cursor):
    cursor.expect('{')
    idx = 0
    struct = 0
    type_name = 0
    while True:
        key = cursor.read_key()
        if key == "idx":
            idx = cursor.read_int()
        elif key == "struct":
            struct = cursor.read_int()
        elif key == "typeName":
            type_name = cursor.read_int()
        else:
            raise ValueError("unexpected key %s in proj" % key)
        if cursor.maybe('}'):
            return Proj(type_name=type_name, index=idx, struct=struct)
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


# ---- Declarations --------------------------------------------------------

def _parse_axiom(cursor):
    """Parse `{"axiom":{...}}` after `"axiom":`."""
    cursor.expect('{')
    levels = None
    name = 0
    type_ = 0
    while True:
        key = cursor.read_key()
        if key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name = cursor.read_int()
        elif key == "type":
            type_ = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            return Axiom(nidx=name, type=type_, levels=levels)
        cursor.expect(',')


def _parse_quot(cursor):
    """Parse `{"quot":{...}}` after `"quot":`."""
    cursor.expect('{')
    levels = None
    name = 0
    type_ = 0
    while True:
        key = cursor.read_key()
        if key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name = cursor.read_int()
        elif key == "type":
            type_ = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            return Quot(nidx=name, type=type_, levels=levels)
        cursor.expect(',')


def _parse_theorem(cursor):
    """Parse `{"thm":{...}}` after `"thm":`."""
    cursor.expect('{')
    levels = None
    name = 0
    type_ = 0
    val = 0
    while True:
        key = cursor.read_key()
        if key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name = cursor.read_int()
        elif key == "type":
            type_ = cursor.read_int()
        elif key == "value":
            val = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            return Theorem(nidx=name, type=type_, value=val, levels=levels)
        cursor.expect(',')


def _parse_opaque(cursor):
    """Parse `{"opaque":{...}}` after `"opaque":`."""
    cursor.expect('{')
    levels = None
    name = 0
    type_ = 0
    val = 0
    while True:
        key = cursor.read_key()
        if key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name = cursor.read_int()
        elif key == "type":
            type_ = cursor.read_int()
        elif key == "value":
            val = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            return Opaque(nidx=name, type=type_, value=val, levels=levels)
        cursor.expect(',')


def _parse_definition(cursor):
    """Parse `{"def":{...}}` after `"def":`."""
    cursor.expect('{')
    levels = None
    name = 0
    type_ = 0
    val = 0
    hint = objects.HINT_OPAQUE
    while True:
        key = cursor.read_key()
        if key == "hints":
            hint = _parse_def_hint(cursor)
        elif key == "levelParams":
            levels = cursor.read_int_array()
        elif key == "name":
            name = cursor.read_int()
        elif key == "type":
            type_ = cursor.read_int()
        elif key == "value":
            val = cursor.read_int()
        else:
            _skip_value(cursor)
        if cursor.maybe('}'):
            cursor.expect('}')
            if levels is None:
                levels = []
            return Definition(
                nidx=name,
                type=type_,
                value=val,
                hint=hint,
                levels=levels,
            )
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


def from_str(text):
    """
    Parse NDJSON out of a lean4export-formatted string.
    """
    return from_ndjson(StringIO(dedent(text).strip()))
