"""
See https://ammkrn.github.io/type_checking_in_lean4/export_format.html
"""

from __future__ import print_function

from StringIO import StringIO
from pprint import pprint as pp  # noqa: F401
from textwrap import dedent

from rpython.rlib.rbigint import rbigint

from rpylean import objects
from rpylean._rjson import loads as from_json, json_true as JSON_TRUE


EXPORT_VERSION = "3.0.0"


class ParseError(Exception):
    def __init__(self, message, source_pos):
        self.message = message
        self.source_pos = source_pos

    def __str__(self):
        return self.message


class ExportVersionError(ParseError):
    """
    The export file version doesn't match one we know how to parse.
    """

    def __init__(self, got):
        self.got = got

    def __str__(self):
        return "Expected export format version {} but got {}".format(
            EXPORT_VERSION,
            self.got,
        )


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
            def_type=let["type"].value_int(),
            def_val=let["value"].value_int(),
            body=let["body"].value_int(),
            # TODO: nondep = ...
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, nidx, def_type, def_val, body):
        self.nidx = nidx
        self.def_type = def_type
        self.def_val = def_val
        self.body = body

    def to_w_expr(self, builder):
        return builder.names[self.nidx].let(
            type=builder.exprs[self.def_type],
            value=builder.exprs[self.def_val],
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
    elif info == "#BS":
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
            binder_name=lam["name"].value_int(),
            binder_type=lam["type"].value_int(),
            binder_info=lam["binderInfo"].value_string(),
            body=lam["body"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, builder):
        return objects.fun(
            binder(
                name=builder.names[self.binder_name],
                type=builder.exprs[self.binder_type],
                info=self.binder_info,
            ),
        )(builder.exprs[self.body])


class ForAll(ExprVal):
    @staticmethod
    def from_dict(value):
        forall = value["forallE"].value_object()
        val = ForAll(
            binder_name=forall["name"].value_int(),
            binder_type=forall["type"].value_int(),
            binder_info=forall["binderInfo"].value_string(),
            body=forall["body"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, builder):
        return objects.forall(
            binder(
                name=builder.names[self.binder_name],
                type=builder.exprs[self.binder_type],
                info=self.binder_info,
            )
        )(builder.exprs[self.body])


class Proj(ExprVal):
    @staticmethod
    def from_dict(value):
        proj = value["proj"].value_object()
        val = Proj(
            struct_name=proj["typeName"].value_int(),
            field_index=proj["idx"].value_int(),
            struct_expr=proj["struct"].value_int(),
        )
        return Expr(eidx=value["ie"].value_int(), val=val)

    def __init__(self, struct_name, field_index, struct_expr):
        self.struct_name = struct_name
        self.field_index = field_index
        self.struct_expr = struct_expr

    def to_w_expr(self, builder):
        return builder.names[self.struct_name].proj(
            self.field_index,
            builder.exprs[self.struct_expr],
        )


class Definition(Node):
    @staticmethod
    def from_dict(value):
        defs = value["def"].value_array()
        assert len(defs) == 1, "No mutual defs yet"
        info = defs[0].value_object()

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
            value=info["value"].value_int(),  # value value value value
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
        theorems = value["thm"].value_array()
        assert len(theorems) == 1, "No mutual theorems yet"
        info = theorems[0].value_object()

        return Theorem(
            nidx=info["name"].value_int(),
            type=info["type"].value_int(),
            value=info["value"].value_int(),  # value value value value
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
        info = value["quotInfo"].value_object()
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
        builder.register_quotient(name, builder.exprs[self.type])


class Mutual(Node):
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

        inductives = info["inductiveVals"].value_array()
        constructors = [
            Constructor.from_dict(each.value_object())
            for each in info["constructorVals"].value_array()
        ]
        recursors = [
            Recursor.from_dict(each.value_object())
            for each in info["recursorVals"].value_array()
        ]

        if len(inductives) == 1:
            inductive = inductives[0].value_object()
            return Inductive.single(inductive, constructors, recursors)
        return Mutual(
            inductives=[
                Inductive.single(each.value_object(), [], []) # XXX
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
                each.value_int()
                for each in inductive["all"].value_array()
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
        declaration = builder.names[self.nidx].inductive(
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
    info = obj.value_object()["meta"].value_object()["format"].value_object()
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
        value = from_json(line)
        assert value.is_object, line

        yield _to_item(value.value_object())


def from_str(text):
    """
    Parse NDJSON out of a lean4export-formatted string.
    """
    return from_ndjson(StringIO(dedent(text).strip()))


def _to_item(obj):
    if "str" in obj:
        cls = NameStr
    elif "app" in obj:
        cls = App
    elif "bvar" in obj:
        cls = BVar
    elif "const" in obj:
        cls = Const
    elif "num" in obj:
        cls = NameNum
    elif "max" in obj:
        cls = UniverseMax
    elif "imax" in obj:
        cls = UniverseIMax
    elif "succ" in obj:
        cls = UniverseSucc
    elif "param" in obj:
        cls = UniverseParam
    elif "sort" in obj:
        cls = Sort
    elif "axiom" in obj:
        cls = Axiom
    elif "def" in obj:
        cls = Definition
    elif "inductive" in obj:
        cls = Inductive
    elif "opaque" in obj:
        cls = Opaque
    elif "quotInfo" in obj:
        cls = Quot
    elif "rec" in obj:
        cls = Recursor
    elif "thm" in obj:
        cls = Theorem
    elif "forallE" in obj:
        cls = ForAll
    elif "letE" in obj:
        cls = Let
    elif "lam" in obj:
        cls = Lambda
    elif "proj" in obj:
        cls = Proj
    elif "natVal" in obj:
        cls = LitNat
    elif "strVal" in obj:
        cls = LitStr
    else:
        assert False, "unknown"
    return cls.from_dict(obj)
