"""
See https://ammkrn.github.io/type_checking_in_lean4/export_format.html
"""

from __future__ import print_function

from rpython.rlib.rbigint import rbigint

from rpylean import objects

#: The lean4export format we claim to be able to parse.
#: Should match https://github.com/ammkrn/lean4export/blob/v2025/Main.lean#L4
EXPORT_VERSION = "2.0.0"


class ParseError(Exception):
    def __init__(self, message, source_pos):
        self.message = message
        self.source_pos = source_pos


class ExportVersionError(ParseError):
    """
    The export file version doesn't match one we know how to parse.
    """
    def __init__(self, got):
        self.got = got

    def __str__(self):
        return "Expected lean4export version {} but got {}".format(
            EXPORT_VERSION,
            self.got,
        )


class Token(object):
    """
    A token in the export file.
    """

    def __init__(self, text, source_pos):
        self.text = text
        self.source_pos = source_pos

    def __repr__(self):
        return "<Token text={!r} source_pos={!r}>".format(
            self.text,
            self.source_pos,
        )

    def bool(self):
        """
        Convert 0 -> False and 1 -> True.
        """
        if self.text == "0":
            return False
        elif self.text == "1":
            return True
        raise ParseError(
            message="Expected 0|1 but got '%s'" % (self.text,),
            source_pos=self.source_pos,
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

    kind = "NS"

    @staticmethod
    def parse(tokens):
        nidx, _ns_token, parent_nidx, name = tokens
        return NameStr(
            nidx=int(nidx.text),
            parent_nidx=int(parent_nidx.text),
            name=name.text,
        )

    def __init__(self, nidx, parent_nidx, name):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.name = name

    def compile(self, builder):
        builder.register_name(self.nidx, self.parent_nidx, self.name)


class NameId(Node):

    kind = "NI"

    @staticmethod
    def parse(tokens):
        nidx, _ni_token, parent_nidx, id = tokens
        return NameId(
            nidx=int(nidx.text),
            parent_nidx=int(parent_nidx.text),
            id=id.text,  # TODO: do we care that this isn't an int?
        )

    def __init__(self, nidx, parent_nidx, id):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.id = id

    def compile(self, builder):
        builder.register_name(self.nidx, self.parent_nidx, self.id)


class Universe(Node):
    pass


class UniverseSucc(Universe):

    kind = "US"

    @staticmethod
    def parse(tokens):
        uidx, _us_token, parent = tokens
        return UniverseSucc(uidx=int(uidx.text), parent=int(parent.text))

    def __init__(self, uidx, parent):
        self.uidx = uidx
        self.parent = parent

    def compile(self, builder):
        level = builder.levels[self.parent].succ()
        builder.register_level(self.uidx, level)


class UniverseMax(Universe):

    kind = "UM"

    @staticmethod
    def parse(tokens):
        uidx, _um_token, lhs, rhs = tokens
        return UniverseMax(
            uidx=int(uidx.text),
            lhs=int(lhs.text),
            rhs=int(rhs.text),
        )

    def __init__(self, uidx, lhs, rhs):
        self.uidx = uidx
        self.lhs = lhs
        self.rhs = rhs

    def compile(self, builder):
        level = builder.levels[self.lhs].max(builder.levels[self.rhs])
        builder.register_level(self.uidx, level)


class UniverseIMax(Universe):

    kind = "UIM"

    @staticmethod
    def parse(tokens):
        uidx, _um_token, lhs, rhs = tokens
        return UniverseIMax(
            uidx=int(uidx.text),
            lhs=int(lhs.text),
            rhs=int(rhs.text),
        )

    def __init__(self, uidx, lhs, rhs):
        self.uidx = uidx
        self.lhs = lhs
        self.rhs = rhs

    def compile(self, builder):
        level = builder.levels[self.lhs].imax(builder.levels[self.rhs])
        builder.register_level(self.uidx, level)


class UniverseParam(Universe):

    kind = "UP"

    @staticmethod
    def parse(tokens):
        uidx, _up_token, nidx = tokens
        return UniverseParam(uidx=int(uidx.text), nidx=int(nidx.text))

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

    kind = "EV"

    @staticmethod
    def parse(tokens):
        eidx, _bval_tok, id = tokens
        val = BVar(id=int(id.text))
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, id):
        self.id = id

    def to_w_expr(self, builder):
        return objects.W_BVar(id=self.id)


class LitStr(ExprVal):

    kind = "ELS"

    @staticmethod
    def parse(tokens):
        eidx = tokens[0]
        _els_tok  = tokens[1]
        hex_tokens = tokens[2:]
        lit_val = "".join([chr(int(token.text, 16)) for token in hex_tokens]).decode('utf-8')
        val = LitStr(val=lit_val)
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, val):
        self.val = val

    def to_w_expr(self, builder):
        return objects.W_LitStr(val=self.val)


class LitNat(ExprVal):

    kind = "ELN"

    @staticmethod
    def parse(tokens):
        eidx, _eli_token, val = tokens
        val = LitNat(val=rbigint.fromstr(val.text))
        assert val.val.int_ge(0)
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, val):
        self.val = val

    def to_w_expr(self, builder):
        return objects.W_LitNat(val=self.val)


class Sort(ExprVal):

    kind = "ES"

    @staticmethod
    def parse(tokens):
        eidx, _sort_tok, level = tokens
        val = Sort(level=int(level.text))
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, level):
        self.level = level

    def to_w_expr(self, builder):
        return builder.levels[self.level].sort()


class Const(ExprVal):

    kind = "EC"

    @staticmethod
    def parse(tokens):
        eidx, _, name = tokens[:3]
        val = Const(
            name=int(name.text),
            levels=[int(level.text) for level in tokens[3:]],
        )
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, name, levels):
        self.name = name
        self.levels = levels

    def to_w_expr(self, builder):
        levels = [builder.levels[level] for level in self.levels]
        return builder.names[self.name].const(levels)


class Let(ExprVal):

    kind = "EZ"

    @staticmethod
    def parse(tokens):
        eidx, _let_token, name_idx, def_type, def_val, body = tokens
        val = Let(
            name_idx=int(name_idx.text),
            def_type=int(def_type.text),
            def_val=int(def_val.text),
            body=int(body.text),
        )
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, name_idx, def_type, def_val, body):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.body = body

    def to_w_expr(self, builder):
        return objects.W_Let(
            name=builder.names[self.name_idx],
            type=builder.exprs[self.def_type],
            value=builder.exprs[self.def_val],
            body=builder.exprs[self.body],
        )


class App(ExprVal):

    kind = "EA"

    @staticmethod
    def parse(tokens):
        eidx, _ea_token, fn_eidx, arg_eidx = tokens
        return Expr(eidx=int(eidx.text), val=App(
            fn_eidx=int(fn_eidx.text),
            arg_eidx=int(arg_eidx.text),
        ))

    def __init__(self, fn_eidx, arg_eidx):
        self.fn_eidx = fn_eidx
        self.arg_eidx = arg_eidx

    def to_w_expr(self, builder):
        fn = builder.exprs[self.fn_eidx]
        arg = builder.exprs[self.arg_eidx]
        return fn.app(arg=arg)


def binder(name, info, type):
    if info == "#BD":
        return name.binder(type=type)
    elif info == "#BI":
        return name.implicit_binder(type=type)
    elif info == "#BS":
        return name.strict_implicit_binder(type=type)
    elif info == "#BC":
        return name.instance_binder(type=type)
    else:
        assert False, "Unknown binder info %s" % info


class Lambda(ExprVal):

    kind = "EL"

    @staticmethod
    def parse(tokens):
        eidx, _lambda_tok, binder_info, binder_name, binder_type, body = tokens
        val = Lambda(
            binder_name=int(binder_name.text),
            binder_type=int(binder_type.text),
            binder_info=binder_info.text,
            body=int(body.text),
        )
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, builder):
        return binder(
                name=builder.names[self.binder_name],
                type=builder.exprs[self.binder_type],
                info=self.binder_info,
        ).fun(
            body=builder.exprs[self.body],
        )


class ForAll(ExprVal):

    kind = "EP"

    @staticmethod
    def parse(tokens):
        eidx, _forall_token, binder_info, binder_name, binder_type, body = tokens
        val = ForAll(
            binder_name=int(binder_name.text),
            binder_type=int(binder_type.text),
            binder_info=binder_info.text,
            body=int(body.text),
        )
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, builder):
        return binder(
                name=builder.names[self.binder_name],
                type=builder.exprs[self.binder_type],
                info=self.binder_info,
        ).forall(
            body=builder.exprs[self.body],
        )


class Proj(ExprVal):

    kind = "EJ"

    @staticmethod
    def parse(tokens):
        eidx, _, type_name, field_idx, struct_expr = tokens
        val = Proj(
            type_name=int(type_name.text),
            field_idx=int(field_idx.text),
            struct_expr=int(struct_expr.text),
        )
        return Expr(eidx=int(eidx.text), val=val)

    def __init__(self, type_name, field_idx, struct_expr):
        self.type_name = type_name
        self.field_idx = field_idx
        self.struct_expr = struct_expr

    def to_w_expr(self, builder):
        name = builder.names[self.type_name]
        return objects.W_Proj(
            struct_name=name,
            field_idx=self.field_idx,
            struct_expr=builder.exprs[self.struct_expr],
        )


class Declaration(Node):
    def __init__(self, decl):
        self.decl = decl

    def compile(self, builder):
        builder.register_declaration(self.decl.to_w_decl(builder))


class Definition(Node):

    kind = "DEF"

    @staticmethod
    def parse(tokens):
        _, name_idx, def_type, def_val, hint = tokens[:5]
        start = 5
        # TODO actually use the argument to 'R"
        if hint.text== "R":
            start += 1
        definition = Definition(
            name_idx=int(name_idx.text),
            def_type=int(def_type.text),
            def_val=int(def_val.text),
            hint=hint.text,
            levels=[int(each.text) for each in tokens[start:]],
        )
        return Declaration(definition)

    def __init__(self, name_idx, def_type, def_val, hint, levels):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.hint = hint
        self.levels = levels

    def to_w_decl(self, builder):
        return objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Definition(
                type=builder.exprs[self.def_type],
                value=builder.exprs[self.def_val],
                hint=self.hint,
            ),
        )


class Opaque(Node):

    kind = "OPAQ"

    @staticmethod
    def parse(tokens):
        _, name_idx, def_type, def_val = tokens[:4]
        opaque = Opaque(
            name_idx=int(name_idx.text),
            def_type=int(def_type.text),
            def_val=int(def_val.text),
            levels=[int(each.text) for each in tokens[4:]],
        )
        return Declaration(opaque)

    def __init__(self, name_idx, def_type, def_val, levels):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.levels = levels

    def to_w_decl(self, builder):
        return objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Opaque(
                type=builder.exprs[self.def_type],
                value=builder.exprs[self.def_val],
            ),
        )


class Theorem(Node):

    kind = "THM"

    @staticmethod
    def parse(tokens):
        _, name_idx, def_type, def_val = tokens[:4]
        theorem = Theorem(
            name_idx=int(name_idx.text),
            def_type=int(def_type.text),
            def_val=int(def_val.text),
            levels=[int(each.text) for each in tokens[4:]],
        )
        return Declaration(theorem)

    def __init__(self, name_idx, def_type, def_val, levels):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.levels = levels

    def to_w_decl(self, builder):
        return objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Theorem(
                type=builder.exprs[self.def_type],
                value=builder.exprs[self.def_val],
            ),
        )


class Axiom(Node):

    kind = "AX"

    @staticmethod
    def parse(tokens):
        _, name_idx, def_type = tokens[:3]
        axiom = Axiom(
            name_idx=int(name_idx.text),
            def_type=int(def_type.text),
            levels=[int(each.text) for each in tokens[3:]],
        )
        return Declaration(axiom)

    def __init__(self, name_idx, def_type, levels):
        self.name_idx = name_idx
        self.def_type = def_type
        self.levels = levels

    def to_w_decl(self, builder):
        return objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Axiom(type=builder.exprs[self.def_type]),
        )


class InductiveSkeleton(Node):
    """
    The skeleton of an inductive type.

    Here we mean the inductive type without its constructors.
    We don't add this to the environment until we see the constructors
    themselves, meaning we collect lines which will appear later in the export
    file until we see all constructors.
    """

    kind = "IND"

    @staticmethod
    def parse(tokens):
        pos = 9
        _, name_idx, type_idx, is_reflexive, is_recursive, num_nested, num_params, num_indices, num_name_idxs_str = tokens[:pos]
        num_name_idxs = int(num_name_idxs_str.text)
        assert num_name_idxs >= 0
        name_idxs = [
            int(nidx.text)
            for nidx in tokens[pos:(pos + num_name_idxs)]
        ]
        pos += num_name_idxs

        num_ctors = int(tokens[pos].text)
        assert num_ctors >= 0
        pos += 1

        ctor_name_idxs = [
            int(nidx.text)
            for nidx in tokens[pos:(pos + num_ctors)]
        ]
        pos += num_ctors
        # Hack for double space in the case of 0 ctors
        if num_ctors == 0:
            # If we have no level params, then we'll be at the end of the line
            if pos < len(tokens):
                assert tokens[pos].text == ""
            pos += 1

        if pos > len(tokens):
            levels = []
        else:
            levels = [int(each.text) for each in tokens[pos:]]

        return InductiveSkeleton(
            name_idx=int(name_idx.text),
            type_idx=int(type_idx.text),
            is_reflexive=is_reflexive.bool(),
            is_recursive=is_recursive.bool(),
            num_nested=int(num_nested.text),
            num_params=int(num_params.text),
            num_indices=int(num_indices.text),
            name_idxs=name_idxs,
            ctor_name_idxs=ctor_name_idxs,
            levels=levels,
        )

    def __init__(
        self,
        name_idx,
        type_idx,
        is_reflexive,
        is_recursive,
        num_nested,
        num_params,
        num_indices,
        name_idxs,
        ctor_name_idxs,
        levels,
    ):
        self.name_idx = name_idx
        self.type_idx = type_idx
        self.is_reflexive = is_reflexive
        self.is_recursive = is_recursive
        self.num_nested = num_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.name_idxs = name_idxs
        self.levels = levels

        self.ctor_name_idxs = ctor_name_idxs
        self.constructors = [None] * len(ctor_name_idxs)
        self.num_remaining_constructors = len(ctor_name_idxs)

    def compile(self, builder):
        if self.ctor_name_idxs:
            builder.register_inductive_skeleton(self)
        else:  # no constructors, just go!
            self.finish(builder)

    def finish(self, builder):
        """
        Finish defining this inductive type, adding it to the environment.

        Called once all constructors have been seen.
        """
        assert len(self.constructors) == len(self.ctor_name_idxs)
        assert None not in self.constructors
        declaration = objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Inductive(
                type=builder.exprs[self.type_idx],
                names=[builder.names[nidx] for nidx in self.name_idxs],
                constructors=self.constructors,
                num_nested=self.num_nested,
                num_params=self.num_params,
                num_indices=self.num_indices,
                is_reflexive=self.is_reflexive,
                is_recursive=self.is_recursive,
            ),
        )
        builder.register_declaration(declaration)


class Constructor(Node):

    kind = "CTOR"

    @staticmethod
    def parse(tokens):
        _, name_idx, type_idx, inductive_nidx, cidx, num_params, num_fields = tokens[:7]
        return Constructor(
            name_idx=int(name_idx.text),
            type_idx=int(type_idx.text),
            inductive_nidx=int(inductive_nidx.text),
            cidx=int(cidx.text),
            num_params=int(num_params.text),
            num_fields=int(num_fields.text),
            levels=[int(each.text) for each in tokens[7:]],
        )

    def __init__(
        self,
        name_idx,
        type_idx,
        inductive_nidx,
        cidx,
        num_params,
        num_fields,
        levels,
    ):
        self.name_idx = name_idx
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
        constructor = objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Constructor(
                type=builder.exprs[self.type_idx],
                num_params=self.num_params,
                num_fields=self.num_fields,
            ),
        )

        skeleton = builder.inductive_skeletons[self.inductive_nidx]
        assert skeleton.constructors[self.cidx] is None, (
            "Constructor %s.%s already defined at index %d" % (
                builder.names[self.inductive_nidx].pretty(),
                builder.names[self.name_idx].pretty(),
                self.cidx,
            )
        )
        skeleton.constructors[self.cidx] = constructor
        skeleton.num_remaining_constructors -= 1
        builder.register_declaration(constructor)

        if not skeleton.num_remaining_constructors:  # saw all of em!
            del builder.inductive_skeletons[self.inductive_nidx]
            skeleton.finish(builder)


class Recursor(Node):

    kind = "REC"

    @staticmethod
    def parse(tokens):
        _rec_token, name_idx, expr_idx, num_ind_name_idxs_str = tokens[:4]

        num_ind_name_idxs = int(num_ind_name_idxs_str.text)
        assert num_ind_name_idxs >= 0

        pos = 4
        ind_name_idxs = [
            int(nidx.text)
            for nidx in tokens[pos:(pos + num_ind_name_idxs)]
        ]
        pos += num_ind_name_idxs

        num_params, num_indices, num_motives, num_minors, num_rule_idxs_str = tokens[pos:pos + 5]

        num_rule_idxs = int(num_rule_idxs_str.text)
        assert num_rule_idxs >= 0
        pos += 5

        rule_idxs = [
            int(rule_idx.text)
            for rule_idx in tokens[pos:pos + num_rule_idxs]
        ]
        pos += num_rule_idxs

        # Hack for double space in the case of 0 rules
        if num_rule_idxs == 0:
            # If we have no level params, then we'll be at the end of the line
            if pos < len(tokens):
                assert tokens[pos].text == ""
            pos += 1

        k = tokens[pos].text
        pos += 1

        recursor = Recursor(
            name_idx=int(name_idx.text),
            type_idx=int(expr_idx.text),
            ind_name_idxs=ind_name_idxs,
            rule_idxs=rule_idxs,
            k=int(k),
            num_params=int(num_params.text),
            num_indices=int(num_indices.text),
            num_motives=int(num_motives.text),
            num_minors=int(num_minors.text),
            levels=[int(param.text) for param in tokens[pos:]],
        )
        return Declaration(recursor)

    def __init__(
        self,
        name_idx,
        type_idx,
        k,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ind_name_idxs,
        rule_idxs,
        levels,
    ):
        self.name_idx = name_idx
        self.type_idx = type_idx
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.ind_name_idxs = ind_name_idxs
        self.levels = levels

        self.rule_idxs = rule_idxs

    def to_w_decl(self, builder):
        return objects.W_Declaration(
            name=builder.names[self.name_idx],
            levels=[builder.names[nidx] for nidx in self.levels],
            w_kind=objects.W_Recursor(
                type=builder.exprs[self.type_idx],
                names=[builder.names[nidx] for nidx in self.ind_name_idxs],
                rules=[builder.rec_rules.pop(idx) for idx in self.rule_idxs],
                k=self.k,
                num_params=self.num_params,
                num_indices=self.num_indices,
                num_motives=self.num_motives,
                num_minors=self.num_minors,
            ),
        )


class RecRule(Node):

    kind = "RR"

    @staticmethod
    def parse(tokens):
        rule_idx, _, ctor_name, num_fields, val = tokens
        return RecRule(
            rule_idx=int(rule_idx.text),
            ctor_name_idx=int(ctor_name.text),
            num_fields=int(num_fields.text),
            val=int(val.text),
        )

    def __init__(self, rule_idx, ctor_name_idx, num_fields, val):
        self.rule_idx = rule_idx
        self.ctor_name_idx = ctor_name_idx
        self.num_fields = num_fields
        self.val = val

    def compile(self, builder):
        w_recrule = objects.W_RecRule(
            ctor_name=builder.names[self.ctor_name_idx],
            num_fields=self.num_fields,
            val=builder.exprs[self.val]
        )
        builder.register_rec_rule(self.rule_idx, w_recrule)


NODES = {}
for cls in [
    NameStr,
    NameId,
    App,
    Lambda,
    ForAll,
    Const,
    LitStr,
    LitNat,
    Sort,
    BVar,
    Proj,
    Let,
    RecRule,
    Recursor,
    UniverseParam,
    UniverseSucc,
    UniverseMax,
    UniverseIMax,
    Definition,
    Theorem,
    Constructor,
    InductiveSkeleton,
    Opaque,
    Axiom,
]:
    cls.parse.func_name += "_" + cls.__name__
    NODES["#" + cls.kind] = cls


def tokenize(line, lineno):
    tokens = []
    column = 0

    while True:
        rest = line.split(" ", 1)
        text = rest[0]
        tokens.append(Token(text=text, source_pos=(lineno, column)))
        if len(rest) != 2:
            return tokens
        line = rest[1]
        column += len(text)
    return tokens


def from_export(lines):
    """
    Parse a lean4export-formatted iterable of lines into its individial items.
    """
    rest = iter(lines)

    try:
        version = next(rest)
    except StopIteration:
        raise ExportVersionError(None)
    else:
        if version.strip() != EXPORT_VERSION:
            raise ExportVersionError(version)

    return to_items(rest)


def to_items(lines):
    """
    Parse a lean4export-formatted iterable of lines *without* version number.
    """
    lineno = 0  # enumerate() in rpython seems ill-equipped for iterators
    for line in lines:
        lineno += 1
        line = line.strip()
        if not line:
            continue

        tokens = tokenize(line, lineno=lineno)
        item = _to_item(tokens)
        if item:
            yield item


def _to_item(tokens):
    token = tokens[0] if tokens[0].text.startswith("#") else tokens[1]
    try:
        cls = NODES[token.text]
    except KeyError as e:
        print("Unimplemented token kind: %s" % e)
        return None

    return cls.parse(tokens)
