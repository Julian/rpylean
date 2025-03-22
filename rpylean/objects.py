class W_Item(object):
    def __repr__(self):
        fields = self.__dict__.iteritems()
        contents = ", ".join("%s=%r" % (k, v) for k, v in fields)
        return "<%s%s%s>" % (
            self.__class__.__name__,
            " " if contents else "",
            contents,
        )

    def pretty(self, bvar_context):
        return "<%s repr error>" % (self.__class__.__name__,)


class W_Level(W_Item):
    pass


class W_LevelZero(W_Level):
    def pretty(self, _):
        return "<W_LevelZero>"


W_LEVEL_ZERO = W_LevelZero()


class W_LevelParam(W_Level):
    def __init__(self, name):
        self.name = name

    def pretty(self, bvar_context):
        return self.name.pretty(bvar_context)


class W_Expr(W_Item):
    pass


class W_BVar(W_Expr):
    def __init__(self, id):
        self.id = int(id)

    def pretty(self, bvar_context):
        lookup = bvar_context.lookup(self)
        if lookup is None:
            return "(BVar [%s])" % (self.id,)
        return "{%s}" % (lookup.name.pretty(bvar_context),)


class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level

    def pretty(self, bvar_context):
        return "Sort %s" % (self.level.pretty(bvar_context),)


class W_Const(W_Expr):
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels

    def pretty(self, bvar_context):
        return "`" + self.name.pretty(bvar_context)

# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body

class W_ForAll(W_FunBase):
    def pretty(self, bvar_context):
        with bvar_context.in_binder(self):
            body_pretty = self.body.pretty(bvar_context)
        return "(∀ %s : %s, %s)" % (
            self.binder_name.pretty(bvar_context),
            self.binder_type.pretty(bvar_context),
            body_pretty
        )


class W_Lambda(W_FunBase):
    def pretty(self, bvar_context):
        with bvar_context.in_binder(self):
            body_pretty = self.body.pretty(bvar_context)
        return "(λ %s : %s => %s)" % (
            self.binder_name.pretty(bvar_context),
            self.binder_type.pretty(bvar_context),
            body_pretty
        )


class W_App(W_Expr):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg

    def pretty(self, bvar_context):
        return "(%s %s)" % (self.fn.pretty(bvar_context), self.arg.pretty(bvar_context))


class W_RecRule(W_Item):
    def __init__(self, ctor_name, n_fields, val):
        self.ctor_name = ctor_name
        self.n_fields = n_fields
        self.val = val

    def pretty(self, bvar_context):
        return "<RecRule ctor_name='%s' n_fields='%s' val='%s'>" % (
            self.ctor_name.pretty(bvar_context),
            self.n_fields,
            self.val.pretty(bvar_context),
        )


class W_Declaration(W_Item):
    def __init__(self, name, level_params, w_kind):
        self.name = name
        self.level_params = level_params
        self.w_kind = w_kind

    def pretty(self, bvar_context):
        return "<W_Declaration name='%s' level_params='%s' kind=%s>" % (
            self.name.pretty(bvar_context),
            self.level_params,
            self.w_kind.pretty(bvar_context),
        )


class W_DeclarationKind:
    pass


class W_Definition(W_DeclarationKind):
    def __init__(self, def_type, def_val, hint):
        self.def_type = def_type
        self.def_val = def_val
        self.hint = hint

    def pretty(self, bvar_context):
        return "<W_Definition def_type='%s' def_val='%s' hint='%s'>" % (
            self.def_type.pretty(bvar_context),
            self.def_val.pretty(bvar_context),
            self.hint,
        )


class W_Theorem(W_DeclarationKind):
    def __init__(self, def_type, def_val):
        self.def_type = def_type
        self.def_val = def_val

    def pretty(self, bvar_context):
        return "<W_Theorem def_type=%s def_val=%s>" % (
            self.def_type.pretty(bvar_context),
            self.def_val.pretty(bvar_context),
        )


class W_Inductive(W_DeclarationKind):
    def __init__(self, expr, is_rec, is_nested, num_params, num_indices, ind_names, ctor_names):
        self.expr = expr
        self.is_rec = is_rec
        self.is_nested = is_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.ind_names = ind_names
        self.ctor_names = ctor_names

    def pretty(self, bvar_context):
        return "<W_Inductive expr=%s is_rec=%s is_nested=%s num_params=%s num_indices=%s ind_names=%s ctor_names=%s>" % (
            self.expr.pretty(bvar_context),
            self.is_rec,
            self.is_nested,
            self.num_params,
            self.num_indices,
            [each.pretty(bvar_context) for each in self.ind_names],
            [each.pretty(bvar_context) for each in self.ctor_names],
        )


class W_Constructor(W_DeclarationKind):
    def __init__(self, ctype, induct, cidx, num_params, num_fields):
        self.ctype = ctype
        self.induct = induct
        self.cidx = cidx
        self.num_params = num_params
        self.num_fields = num_fields

    def pretty(self, bvar_context):
        return "<W_Constructor ctype='%s' induct='%s' cidx='%s' num_params='%s' num_fields='%s'>" % (
            self.ctype,
            self.induct,
            self.cidx,
            self.num_params,
            self.num_fields,
        )


class W_Recursor(W_DeclarationKind):
    def __init__(self,
        expr,
        k,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ind_names,
        rule_idxs,
    ):
        self.expr = expr
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.ind_names = ind_names
        self.rule_idxs = rule_idxs

    def pretty(self, bvar_context):
        return "<W_Recursor expr='%s' k='%s' num_params='%s' num_indices='%s' num_motives='%s' num_minors='%s' ind_names='%s' rule_idxs='%s'>" % (
            self.expr.pretty(bvar_context),
            self.k,
            self.num_params,
            self.num_indices,
            self.num_motives,
            self.num_minors,
            [each.pretty(bvar_context) for each in self.ind_names],
            self.rule_idxs,
        )
