from rpylean.check import check_no_duplicate_levels

class W_Item(object):
    def __repr__(self):
        fields = self.__dict__.iteritems()
        contents = ", ".join("%s=%r" % (k, v) for k, v in fields)
        return "<%s%s%s>" % (
            self.__class__.__name__,
            " " if contents else "",
            contents,
        )


class W_Level(W_Item):
    pass


class W_LevelZero(W_Level):
    pass


W_LEVEL_ZERO = W_LevelZero()


class W_LevelParam(W_Level):
    def __init__(self, name):
        self.name = name


class W_Expr(W_Item):
    pass


class W_BVar(W_Expr):
    def __init__(self, id):
        self.id = id


class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level


class W_Const(W_Expr):
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels


class W_ForAll(W_Expr):
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body


class W_Lambda(W_Expr):
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body


class W_App(W_Expr):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg


class W_RecRule(W_Item):
    def __init__(self, ctor_name, n_fields, val):
        self.ctor_name = ctor_name
        self.n_fields = n_fields
        self.val = val


class W_Declaration(W_Item):
    def check_declaration(self, env):
        pass


class W_Definition(W_Declaration):
    def __init__(self, name, def_type, def_val, hint, level_params):
        self.name = name
        self.def_type = def_type
        self.def_val = def_val
        self.hint = hint
        self.level_params = level_params

    def check_declaration(self, env):
        check_no_duplicate_levels(env, self.level_params)


class W_Theorem(W_Declaration):
    def __init__(self, name, def_type, def_val, level_params):
        self.name = name
        self.def_type = def_type
        self.def_val = def_val
        self.level_params = level_params


class W_Inductive(W_Declaration):
    def __init__(self, name, expr, is_rec, is_nested, num_params, num_indices, ind_names, ctor_names, level_params):
        self.name = name
        self.expr = expr
        self.is_rec = is_rec
        self.is_nested = is_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.ind_names = ind_names
        self.ctor_names = ctor_names
        self.level_params = level_params


class W_Constructor(W_Declaration):
    def __init__(self, name, ctype, induct, cidx, num_params, num_fields, level_params):
        self.name = name
        self.ctype = ctype
        self.induct = induct
        self.cidx = cidx
        self.num_params = num_params
        self.num_fields = num_fields
        self.level_params = level_params


class W_Recursor(W_Declaration):
    def __init__(self,
        name,
        expr,
        k,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ind_names,
        rule_idxs,
        level_params,
    ):
        self.name = name
        self.expr = expr
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.ind_names = ind_names
        self.rule_idxs = rule_idxs
        self.level_params = level_params
