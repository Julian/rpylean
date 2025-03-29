from __future__ import print_function

from rpylean import objects

#: The lean4export format we claim to be able to parse.
#: Should match https://github.com/ammkrn/lean4export/blob/format2024/Main.lean#L4
EXPORT_VERSION = "0.1.2"


class ParseError(Exception):
    def __init__(self, line, lineno, column=0):
        Exception.__init__(self, (line, column))
        self.line = line
        self.column = column


class Token:
    def __init__(self, text, source_pos):
        self.text = text
        self.source_pos = source_pos

    def __repr__(self):
        return "<Token text={!r} source_pos={!r}>".format(
            self.text,
            self.source_pos,
        )


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


class Invalid(Exception):
    pass


class Node(object):
    """
    An AST node.
    """

    def __eq__(self, other):
        return (
            self.__class__ == other.__class__ and
            self.__dict__ == other.__dict__
        )

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        contents = ("%s=%r" % (k, v) for k, v in self.__dict__.iteritems())
        return "<%s %s>" % (self.__class__.__name__, ", ".join(contents))


class File(Node):
    def __init__(self, version, items=None):
        if items is None:
            items = []
        self.version = version
        self.items = items

    def compile(self, context):
        for item in self.items:
            item.compile(context)


class Version(Node):
    def __init__(self, major, minor, patch):
        self.major = int(major)
        self.minor = int(minor)
        self.patch = int(patch)


class NameStr(Node):
    @staticmethod
    def parse(tokens):
        nidx, _ns_token, parent_nidx, name = tokens
        return NameStr(
            nidx=nidx.text,
            parent_nidx=parent_nidx.text,
            name=name.text,
        )
    
    def __init__(self, nidx, parent_nidx, name):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.name = name

    def compile(self, environment):
        environment.register_name(self.nidx, self.parent_nidx, self.name)

class NameId(Node):
    @staticmethod
    def parse(tokens):
        nidx, _ni_token, parent_nidx, id = tokens
        return NameId(
            nidx=nidx.text,
            parent_nidx=parent_nidx.text,
            id=id.text,
        )
    
    def __init__(self, nidx, parent_nidx, id):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.id = id
        
    def compile(self, environment):
        # TODO - should we register id names separately (as ints)?
        environment.register_name(self.nidx, self.parent_nidx, self.id)


class Universe(Node):
    pass


class UniverseSucc(Universe):
    @staticmethod
    def parse(tokens):
        uidx, _us_token, parent = tokens
        return UniverseSucc(
            uidx=uidx.text,
            parent=parent.text,
        )
    
    def __init__(self, uidx, parent):
        self.uidx = uidx
        self.parent = parent

    def compile(self, environment):
        parent = environment.levels[self.parent]
        environment.register_level(self.uidx, objects.W_LevelSucc(parent))

class UniverseMax(Universe):
    @staticmethod
    def parse(tokens):
        uidx, _um_token, lhs, rhs = tokens
        return UniverseMax(
            uidx=uidx.text,
            lhs=lhs.text,
            rhs=rhs.text,
        )
    
    def __init__(self, uidx, lhs, rhs):
        self.uidx = uidx
        self.lhs = lhs
        self.rhs = rhs

    def compile(self, environment):
        environment.register_level(
            self.uidx,
            objects.W_LevelMax(
                lhs=environment.levels[self.lhs],
                rhs=environment.levels[self.rhs],
            ),
        )

class UniverseIMax(Universe):
    @staticmethod
    def parse(tokens):
        uidx, _um_token, lhs, rhs = tokens
        return UniverseIMax(
            uidx=uidx.text,
            lhs=lhs.text,
            rhs=rhs.text,
        )
    
    def __init__(self, uidx, lhs, rhs):
        self.uidx = uidx
        self.lhs = lhs
        self.rhs = rhs

    def compile(self, environment):
        environment.register_level(
            self.uidx,
            objects.W_LevelIMax(
                lhs=environment.levels[self.lhs],
                rhs=environment.levels[self.rhs],
            ),
        )

class UniverseParam(Universe):
    @staticmethod
    def parse(tokens):
        uidx, _up_token, nidx = tokens
        return UniverseParam(
            uidx=uidx.text,
            nidx=nidx.text,
        )
    def __init__(self, uidx, nidx):
        self.uidx = uidx
        self.nidx = nidx

    def compile(self, environment):
        name = environment.names[self.nidx]
        environment.register_level(self.uidx, objects.W_LevelParam(name=name))


class Expr(Node):
    def __init__(self, eidx, val):
        self.eidx = eidx
        self.val = val

    def compile(self, environment):
        w_expr = self.val.to_w_expr(environment)
        environment.register_expr(self.eidx, w_expr)


class ExprVal(Node):
    pass


class BVar(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _bval_tok, id = tokens
        val = BVar(id=int(id.text))
        return Expr(eidx=eidx.text, val=val)
    
    def __init__(self, id):
        self.id = id

    def to_w_expr(self, environment):
        return objects.W_BVar(id=self.id)

class LitStr(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx = tokens[0]
        _els_tok  = tokens[1]
        hex_tokens = tokens[2:]
        lit_val = "".join([chr(int(token.text, 16)) for token in hex_tokens]).decode('utf-8')
        val = LitStr(val=lit_val)
        return Expr(eidx=eidx.text, val=val)
    
    def __init__(self, val):
        self.val = val

    def to_w_expr(self, environment):
        return objects.W_LitStr(val=self.val)
    
class LitNat(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _eli_token, val = tokens
        val = LitNat(val=int(val.text))
        assert val.val >= 0
        return Expr(eidx=eidx.text, val=val)
    
    def __init__(self, val):
        self.val = val

    def to_w_expr(self, environment):
        return objects.W_LitNat(val=self.val)


class Sort(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _sort_tok, level = tokens
        val = Sort(level=level.text)
        return Expr(eidx=eidx.text, val=val)
    
    def __init__(self, level):
        self.level = level

    def to_w_expr(self, environment):
        return objects.W_Sort(level=environment.levels[self.level])


class Const(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _ec_token, name = tokens[:3]
        val = Const(
            name=name.text,
            levels=[
                level.text
                for level in tokens[3:]
            ],
        )
        return Expr(eidx=eidx.text, val=val)       
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels

    def to_w_expr(self, environment):
        return objects.W_Const(
            name=environment.names[self.name],
            levels=[environment.levels[level] for level in self.levels],
        )


class Let(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _let_token, name_idx, def_type, def_val, body = tokens
        val = Let(
            name_idx=name_idx.text,
            def_type=def_type.text,
            def_val=def_val.text,
            body=body.text,
        )
        return Expr(eidx=eidx.text, val=val)
    
    def __init__(self, name_idx, def_type, def_val, body):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.body = body

    def to_w_expr(self, environment):
        return objects.W_Let(
            name=environment.names[self.name_idx],
            def_type=environment.exprs[self.def_type],
            def_val=environment.exprs[self.def_val],
            body=environment.exprs[self.body],
        )

class App(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _ea_token, fn_eidx, arg_eidx = tokens
        return Expr(eidx=eidx.text, val=App(
            fn_eidx=fn_eidx.text,
            arg_eidx=arg_eidx.text,
        ))
    
    def __init__(self, fn_eidx, arg_eidx):
        self.fn_eidx = fn_eidx
        self.arg_eidx = arg_eidx

    def to_w_expr(self, environment):
        fn = environment.exprs[self.fn_eidx]
        arg = environment.exprs[self.arg_eidx]
        return objects.W_App(fn=fn, arg=arg)


class Lambda(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _lambda_tok, binder_info, binder_name, binder_type, body = tokens
        val = Lambda(
            binder_name=binder_name.text,
            binder_type=binder_type.text,
            binder_info=binder_info.text,
            body=body.text,
        )
        return Expr(eidx=eidx.text, val=val)
        
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, environment):
        return objects.W_Lambda(
            binder_name=environment.names[self.binder_name],
            binder_type=environment.exprs[self.binder_type],
            binder_info=self.binder_info,
            body=environment.exprs[self.body],
        )


class ForAll(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _forall_token, binder_info, binder_name, binder_type, body = tokens
        val = ForAll(
            binder_name=binder_name.text,
            binder_type=binder_type.text,
            binder_info=binder_info.text,
            body=body.text,
        )
        return Expr(eidx=eidx.text, val=val)

    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

    def to_w_expr(self, environment):
        return objects.W_ForAll(
            binder_name=environment.names[self.binder_name],
            binder_type=environment.exprs[self.binder_type],
            binder_info=self.binder_info,
            body=environment.exprs[self.body],
        )

class Proj(ExprVal):
    @staticmethod
    def parse(tokens):
        eidx, _ej_token, type_name, field_idx, struct_expr = tokens
        val = Proj(
            type_name=type_name.text,
            field_idx=int(field_idx.text),
            struct_expr=struct_expr.text,
        )
        return Expr(eidx=eidx.text, val=val)
    
    def __init__(self, type_name, field_idx, struct_expr):
        self.type_name = type_name
        self.field_idx = field_idx
        self.struct_expr = struct_expr

    def to_w_expr(self, environment):
        return objects.W_Proj(
            struct_type=environment.declarations[environment.names[self.type_name]],
            field_idx=self.field_idx,
            struct_expr=environment.exprs[self.struct_expr],
        )

class Declaration(Node):
    def __init__(self, decl):
        self.decl = decl

    def compile(self, environment):
        w_kind = self.decl.to_w_decl(environment)
        seen = {}
        for level in w_kind.level_params:
            if level in seen:
                raise Invalid(
                    "%s has duplicate level %s in all kind: %s" % (w_kind.name, level, w_kind.level_params),
                )
            seen[level] = True
        environment.register_declaration(
            self.decl.name_idx,
            w_kind,
        )


class Definition(Node):
    @staticmethod
    def parse(tokens):
        _, name_idx, def_type, def_val, hint = tokens[:5]
        start = 5
        # TODO actually use the argument to 'R"
        if hint.text== "R":
            start += 1
        return Declaration(Definition(
            name_idx=name_idx.text,
            def_type=def_type.text,
            def_val=def_val.text,
            hint=hint.text,
            level_params=[
                each.text for each in tokens[start:]
            ],
        ))
    
    def __init__(self, name_idx, def_type, def_val, hint, level_params):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.hint = hint
        self.level_params = level_params

    def to_w_decl(self, environment):

        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Definition(
                def_type=environment.exprs[self.def_type],
                def_val=environment.exprs[self.def_val],
                hint=self.hint,
            ),
        )

class Opaque(Node):
    @staticmethod
    def parse(tokens):
        _, name_idx, def_type, def_val = tokens[:4]
        return Declaration(Opaque(
            name_idx=name_idx.text,
            def_type=def_type.text,
            def_val=def_val.text,
            level_params=[
                each.text for each in tokens[4:]
            ],
        ))
    
    def __init__(self, name_idx, def_type, def_val, level_params):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.level_params = level_params

    def to_w_decl(self, environment):
        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Opaque(
                def_type=environment.exprs[self.def_type],
                def_val=environment.exprs[self.def_val],
            ),
        )    


class Theorem(Node):
    @staticmethod
    def parse(tokens):
        _, name_idx, def_type, def_val = tokens[:4]
        return Declaration(Theorem(
            name_idx=name_idx.text,
            def_type=def_type.text,
            def_val=def_val.text,
            level_params=[
                each.text for each in tokens[4:]
            ],
        ))
    
    def __init__(self, name_idx, def_type, def_val, level_params):
        self.name_idx = name_idx
        self.def_type = def_type
        self.def_val = def_val
        self.level_params = level_params

    def to_w_decl(self, environment):
        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Theorem(
                def_type=environment.exprs[self.def_type],
                def_val=environment.exprs[self.def_val],
            ),
        )

class Axiom(Node):
    @staticmethod
    def parse(tokens):
        _, name_idx, def_type = tokens[:3]
        return Declaration(Axiom(
            name_idx=name_idx.text,
            def_type=def_type.text,
            level_params=[
                each.text for each in tokens[3:]
            ],
        ))
    
    def __init__(self, name_idx, def_type, level_params):
        self.name_idx = name_idx
        self.def_type = def_type
        self.level_params = level_params

    def to_w_decl(self, environment):
        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Axiom(
                def_type=environment.exprs[self.def_type],
            ),
        )


class Inductive(Node):
    @staticmethod
    def parse(tokens):
        _, target_nidx, eidx, is_rec, is_nested, num_params, num_indices, num_ind_name_idxs_str = tokens[:8]
        num_ind_name_idxs = int(num_ind_name_idxs_str.text)
        assert num_ind_name_idxs >= 0
        pos = 8
        ind_name_idxs = [
            nidx.text
            for nidx in tokens[pos:(pos + num_ind_name_idxs)]
        ]
        pos += num_ind_name_idxs

        num_ctors = int(tokens[pos].text)
        assert num_ctors >= 0
        pos += 1

        ctor_name_idxs = [
            nidx.text
            for nidx in tokens[pos:(pos + num_ctors)]
        ]
        pos += num_ctors
        # Hack for double space in the case of 0 ctors
        if num_ctors == 0:
            # If we have no level params, then we'll be at the end of the line
            if pos < len(tokens):
                assert tokens[pos].text == ""
            pos += 1

        level_params = [
            each.text for each in tokens[pos:]
        ]

        return Declaration(Inductive(
            name_idx=target_nidx.text,
            expr_idx=eidx.text,
            is_rec=is_rec.text,
            is_nested=is_nested.text,
            num_params=int(num_params.text),
            num_indices=num_indices.text,
            ind_name_idxs=ind_name_idxs,
            ctor_name_idxs=ctor_name_idxs,
            level_params=level_params,
        ))
    
    def __init__(
        self,
        name_idx,
        expr_idx,
        is_rec,
        is_nested,
        num_params,
        num_indices,
        ind_name_idxs,
        ctor_name_idxs,
        level_params,
    ):
        self.name_idx = name_idx
        self.expr_idx = expr_idx
        self.is_rec = is_rec
        self.is_nested = is_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.ind_name_idxs = ind_name_idxs
        self.ctor_name_idxs = ctor_name_idxs
        self.level_params = level_params

    def to_w_decl(self, environment):
        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Inductive(
                expr=environment.exprs[self.expr_idx],
                is_rec=self.is_rec,
                is_nested=self.is_nested,
                num_params=int(self.num_params),
                num_indices=self.num_indices,
                ind_names=[environment.names[nidx] for nidx in self.ind_name_idxs],
                ctor_names=[
                    environment.names[nidx] for nidx in self.ctor_name_idxs
                ],
            ),
        )


class Constructor(Node):
    @staticmethod
    def parse(tokens):
        _, name_idx, ctype, induct, cidx, num_params, num_fields = tokens[:7]
        return Declaration(Constructor(
            name_idx=name_idx.text,
            ctype=ctype.text,
            induct=induct.text,
            cidx=cidx.text,
            num_params=int(num_params.text),
            num_fields=int(num_fields.text),
            level_params=[
                each.text for each in tokens[7:]
            ],
        ))
    
    def __init__(self, name_idx, ctype, induct, cidx, num_params, num_fields, level_params):
        self.name_idx = name_idx
        self.ctype = ctype
        self.induct = induct
        self.cidx = cidx
        self.num_params = num_params
        self.num_fields = num_fields
        self.level_params = level_params

    def to_w_decl(self, environment):
        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Constructor(
                ctype=environment.exprs[self.ctype],
                induct=self.induct,
                cidx=self.cidx,
                num_params=int(self.num_params),
                num_fields=int(self.num_fields),
            ),
        )


class Recursor(Node):
    @staticmethod
    def parse(tokens):
        _rec_token, name_idx, expr_idx, num_ind_name_idxs_str = tokens[:4]

        num_ind_name_idxs = int(num_ind_name_idxs_str.text)
        assert num_ind_name_idxs >= 0

        pos = 4
        ind_name_idxs = [
            nidx.text
            for nidx in tokens[pos:(pos + num_ind_name_idxs)]
        ]
        pos += num_ind_name_idxs

        num_params, num_indices, num_motives, num_minors, num_rule_idxs_str = tokens[pos:pos + 5]

        num_rule_idxs = int(num_rule_idxs_str.text)
        assert num_rule_idxs >= 0
        pos += 5

        rule_idxs = [
            rule_idx.text
            for rule_idx in tokens[pos:pos + num_rule_idxs]
        ]
        pos += num_rule_idxs

        k = tokens[pos].text
        level_params = [param.text for param in tokens[(pos + 1):]]

        return Declaration(Recursor(
            name_idx=name_idx.text,
            expr_idx=expr_idx.text,
            ind_name_idxs=ind_name_idxs,
            rule_idxs=rule_idxs,
            k=k,
            num_params=int(num_params.text),
            num_indices=num_indices.text,
            num_motives=num_motives.text,
            num_minors=num_minors.text,
            level_params=level_params
        ))
#         
    def __init__(
        self,
        name_idx,
        expr_idx,
        k,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ind_name_idxs,
        rule_idxs,
        level_params,
    ):
        self.name_idx = name_idx
        self.expr_idx = expr_idx
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.ind_name_idxs = ind_name_idxs
        self.rule_idxs = rule_idxs
        self.level_params = level_params

    def to_w_decl(self, environment):
        return objects.W_Declaration(
            name=environment.names[self.name_idx],
            level_params=[environment.names[nidx] for nidx in self.level_params],
            w_kind=objects.W_Recursor(
                expr=environment.exprs[self.expr_idx],
                k=self.k,
                num_params=int(self.num_params),
                num_indices=self.num_indices,
                num_motives=self.num_motives,
                num_minors=self.num_minors,
                ind_names=[environment.names[nidx] for nidx in self.ind_name_idxs],
                rule_idxs=self.rule_idxs,
            ),
        )


class RecRule(Node):
    @staticmethod
    def parse(tokens):
        ridx = int(tokens[0].text)
        _rr_token = tokens[1].text
        ctor_name = tokens[2].text
        n_fields = int(tokens[3].text)
        val = tokens[4].text
        return RecRule(ridx, ctor_name, n_fields, val)


    def __init__(self, ridx, ctor_name, n_fields, val):
        self.ridx = ridx
        self.ctor_name = ctor_name
        self.n_fields = n_fields
        self.val = val

    def compile(self, environment):
        w_recrule = objects.W_RecRule(
            ctor_name=environment.names[self.ctor_name],
            n_fields=self.n_fields,
            val=environment.exprs[self.val]
        )
        environment.register_rec_rule(self.ridx, w_recrule)


# class Transformer(RPythonVisitor):
#     def dispatch(self, node):
#         return getattr(self, "visit_%s" % node.symbol)(node)
#
#     def visit_file(self, node):
#         version = self.dispatch(node.children[0])
#         return File(
#             version=version,
#             items=[self.dispatch(each) for each in node.children[1].children]
#         )
#
#     def visit_export_format_version(self, node):
#         major, minor, patch = node.children
#         return Version(
#             major=major.additional_info,
#             minor=minor.additional_info,
#             patch=patch.additional_info,
#         )
#
#     def visit_item(self, node):
#         item, = node.children
#         return self.dispatch(item)
#
#     def visit_name(self, node):
#         nidx, kind, parent_nidx, id = node.children
#         if kind.additional_info == "#NS":
#             return NameStr(
#                 nidx=nidx.children[0].additional_info,
#                 parent_nidx=parent_nidx.children[0].additional_info,
#                 name=id.additional_info,
#             )
#         elif kind.additional_info == "#NI":
#             return NameId(
#                 nidx=nidx.children[0].additional_info,
#                 parent_nidx=parent_nidx.children[0].additional_info,
#                 id=id.additional_info,
#             )
#         else:
#             assert False, "unknown name kind: " + kind.additional_info
#
#     def visit_universe(self, node):
#         kind = node.children[1]
#         if kind.additional_info == "#UP":
#             uidx, _, nidx = node.children
#             return UniverseParam(
#                 uidx=uidx.children[0].additional_info,
#                 nidx=nidx.children[0].additional_info,
#             )
#         if kind.additional_info == "#US":
#             uidx, _, parent = node.children
#             return UniverseSucc(uidx=uidx.children[0].additional_info, parent=parent.children[0].additional_info)
#         if kind.additional_info == "#UM":
#             uidx, _, lhs, rhs = node.children
#             return UniverseMax(
#                 uidx=uidx.children[0].additional_info,
#                 lhs=lhs.children[0].additional_info,
#                 rhs=rhs.children[0].additional_info,
#             )
#         else:
#             assert False, "unknown universe kind: " + kind.additional_info
#
#     def visit_expr(self, node):
#         eidx = node.children[0].children[0].additional_info
#         kind = node.children[1]
#         if kind.additional_info == "#EV":
#             _, _, id = node.children
#             val = BVar(id=int(id.additional_info))
#         elif kind.additional_info == "#ES":
#             _, _, uidx = node.children
#             val = Sort(level=uidx.children[0].additional_info)
#         elif kind.additional_info == "#EC":
#             name = node.children[2].children[0].additional_info
#             val = Const(
#                 name=name,
#                 levels=[
#                     uidx.children[0].additional_info
#                     for uidx in node.children[3:]
#                 ],
#             )
#         elif kind.additional_info == "#EA":
#             _, _, fn_eidx, arg_eidx = node.children
#             val = App(
#                 fn_eidx=fn_eidx.children[0].additional_info,
#                 arg_eidx=arg_eidx.children[0].additional_info,
#             )
#         elif kind.additional_info == "#EL":
#             _, _, binder_info, binder_name, binder_type, body = node.children
#             val = Lambda(
#                 binder_name=binder_name.children[0].additional_info,
#                 binder_type=binder_type.children[0].additional_info,
#                 binder_info=binder_info.children[0].additional_info,
#                 body=body.children[0].additional_info,
#             )
#         elif kind.additional_info == "#EP":
#             _, _, binder_info, binder_name, binder_type, body = node.children
#             val = ForAll(
#                 binder_name=binder_name.children[0].additional_info,
#                 binder_type=binder_type.children[0].additional_info,
#                 binder_info=binder_info.children[0].additional_info,
#                 body=body.children[0].additional_info,
#             )
#         elif kind.additional_info == "#EJ":
#             _, _, type_name, field_idx, struct_expr = node.children
#             val = Proj(type_name=type_name.children[0].additional_info,
#                         field_idx=int(field_idx.additional_info),
#                         struct_expr=struct_expr.children[0].additional_info)
#         else:
#             assert False, "unknown expr kind: " + kind.additional_info
#         return Expr(eidx=eidx, val=val)
#
#     def visit_declaration(self, node):
#         child, = node.children
#         return Declaration(self.dispatch(child))
#
#     def visit_definition(self, node):
#         _, name_idx, def_type, def_val, hint = node.children[:5]
#         return Definition(
#             name_idx=name_idx.children[0].additional_info,
#             def_type=def_type.children[0].additional_info,
#             def_val=def_val.children[0].additional_info,
#             hint=hint.children[0].additional_info,
#             level_params=[
#                 each.children[0].additional_info for each in node.children[5:]
#             ],
#         )
#
#     def visit_theorem(self, node):
#         _, name_idx, def_type, def_val = node.children[:4]
#         return Theorem(
#             name_idx=name_idx.children[0].additional_info,
#             def_type=def_type.children[0].additional_info,
#             def_val=def_val.children[0].additional_info,
#             level_params=[
#                 each.children[0].additional_info for each in node.children[4:]
#             ],
#         )
#
#     def visit_inductive(self, node):
#         _, nidx, eidx, is_rec, is_nested, num_params, num_indices, num_ind_name_idxs_str = node.children[:8]
#         num_ind_name_idxs = int(num_ind_name_idxs_str.additional_info)
#         assert num_ind_name_idxs >= 0
#         pos = 8
#         ind_name_idxs = node.children[pos:pos + num_ind_name_idxs]
#         pos += num_ind_name_idxs
#
#         num_ctors = int(node.children[pos].additional_info)
#         assert num_ctors >= 0
#         pos += 1
#
#         ctor_name_idxs = node.children[pos:pos + num_ctors]
#         pos += num_ctors
#
#         level_params = node.children[pos:]
#         return Inductive(
#             name_idx=nidx.children[0].additional_info,
#             expr_idx=eidx.children[0].additional_info,
#             is_rec=is_rec.additional_info,
#             is_nested=is_nested.additional_info,
#             num_params=int(num_params.additional_info),
#             num_indices=num_indices.additional_info,
#             ind_name_idxs=[
#                 each.additional_info for each in ind_name_idxs
#             ],
#             ctor_name_idxs=[
#                 each.additional_info for each in ctor_name_idxs
#             ],
#             level_params=[
#                 each.additional_info
#                 for each in level_params
#             ],
#         )
#
#     def visit_constructor(self, node):
#         _, name_idx, ctype, induct, cidx, num_params, num_fields = node.children[:7]
#         return Constructor(
#             name_idx=name_idx.children[0].additional_info,
#             ctype=ctype.children[0].additional_info,
#             induct=induct.children[0].additional_info,
#             cidx=cidx.additional_info,
#             num_params=int(num_params.additional_info),
#             num_fields=num_fields.additional_info,
#             level_params=[
#                 each.children[0].additional_info for each in node.children[7:]
#             ],
#         )
#
#     def visit_recursor(self, node):
#         _, name_idx, expr_idx, num_ind_name_idxs_str = node.children[:4]
#
#         num_ind_name_idxs = int(num_ind_name_idxs_str.additional_info)
#         assert num_ind_name_idxs >= 0
#
#         pos = 4
#         ind_name_idxs = [
#             nidx.additional_info
#             for nidx in node.children[pos:(pos + num_ind_name_idxs)]
#         ]
#         pos += num_ind_name_idxs
#
#         num_params, num_indices, num_motives, num_minors, num_rule_idxs_str = node.children[pos:pos + 5]
#
#         num_rule_idxs = int(num_rule_idxs_str.additional_info)
#         assert num_rule_idxs >= 0
#         pos += 5
#
#         rule_idxs = [
#             rule_idx.additional_info
#             for rule_idx in node.children[pos:pos + num_rule_idxs]
#         ]
#         pos += num_rule_idxs
#
#         k = node.children[pos].additional_info
#         level_params = node.children[pos + 1:]
#
#         return Recursor(
#             name_idx=name_idx.children[0].additional_info,
#             expr_idx=expr_idx.children[0].additional_info,
#             ind_name_idxs=ind_name_idxs,
#             rule_idxs=rule_idxs,
#             k=k,
#             num_params=int(num_params.additional_info),
#             num_indices=num_indices.additional_info,
#             num_motives=num_motives.additional_info,
#             num_minors=num_minors.additional_info,
#             level_params=[
#                 each.additional_info for each in level_params
#             ],
#         )
#
#     def visit_recrule(self, node):
#         ridx, _, nidx, nat, eidx = node.children
#         return RecRule(
#             ridx=ridx.children[0].additional_info,
#             ctor_name=nidx.children[0].additional_info,
#             n_fields=nat.additional_info,
#             val=eidx.children[0].additional_info,
#         )

TOKEN_KINDS = {
    "#NS": NameStr,
    "#NI": NameId,
    "#EA": App,
    "#EL": Lambda,
    "#EP": ForAll,
    "#EC": Const,
    "#ELS": LitStr,
    "#ELN": LitNat,
    "#ES": Sort,
    "#EV": BVar,
    "#EJ": Proj,
    "#EZ": Let,
    "#RR": RecRule,
    "#REC": Recursor,
    "#UP": UniverseParam,
    "#US": UniverseSucc,
    "#UM": UniverseMax,
    "#UIM": UniverseIMax,
    "#DEF": Definition,
    "#THM": Theorem,
    "#CTOR": Constructor,
    "#IND": Inductive,
    "#OPAQ": Opaque,
    "#AX": Axiom,
}

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


def parse(lines):
    rest = iter(lines)

    try:
        version = next(rest)
    except StopIteration:
        raise ExportVersionError(None)
    else:
        if version.strip() != EXPORT_VERSION:
            raise ExportVersionError(version)

    lineno, items = 0, []
    while True:
        lineno += 1
        try:
            line = next(rest).strip()
        except StopIteration:
            break
        if not line:
            continue

        tokens = tokenize(line, lineno=lineno)
        item = to_item(tokens)
        if item:
            items.append(item)
    return items
    #
    # try:
    #     parsed = _parse(source)
    # except ParseError as error:
    #     print(error.nice_error_message(__file__, source), end="\n\n\n")
    #     raise
    #
    # ast = ToAST().transform(parsed)
    # return transformer.visit_file(ast)


def to_item(tokens):
    try:
        if tokens[0].text.isdigit():
            token_type = TOKEN_KINDS[tokens[1].text]
        else:
            token_type = TOKEN_KINDS[tokens[0].text]
    except KeyError as e:
        print("Unimplemented token kind: %s" % e)
        return None
    
    return token_type.parse(tokens)
