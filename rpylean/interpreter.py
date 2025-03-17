from __future__ import print_function

from rpylean.parser import parse

class Level:
    pass

class LevelZero(Level):
    def __repr__(self):
        return "LevelZero()"


class LevelParam(Level):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "LevelParam(%s)" % (self.name,)


class Expr:
    pass


class RecRule:
    def __init__(self, name, nfields, rhs):
        self.name = name
        self.nfields = nfields
        self.rhs = rhs

    def __repr__(self):
        return "RecRule(%s, %s, %s)" % (self.name, self.nfields, self.rhs)


class ExprSort(Expr):
    def __init__(self, level):
        self.level = level

    def __repr__(self):
        return "ExprSort(%s)" % (self.level,)


class ExprConst(Expr):
    def __init__(self, const, levels):
        self.const = const
        self.levels = levels

    def __repr__(self):
        return "ExprConst(%s, %s)" % (self.const, self.levels)


class ExprForallE(Expr):
    def __init__(self, binder_info, binder_name, binder_type, body):
        self.binder_info = binder_info
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.body = body

    def __repr__(self):
        return "ExprForallE(%s, %s, %s, %s)" % (self.binder_info, self.binder_name, self.binder_type, self.body)

class ExprLambda(Expr):
    def __init__(self, binder_info, binder_name, binder_type, body):
        self.binder_info = binder_info
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.body = body

    def __repr__(self):
        return "ExprLambda(%s, %s, %s, %s)" % (self.binder_info, self.binder_name, self.binder_type, self.body)


class ExprBVar(Expr):
    def __init__(self, id):
        self.id = id

    def __repr__(self):
        return "ExprBVar(%s)" % (self.id,)


class ExprApp(Expr):
    def __init__(self, function, arg):
        self.function = function
        self.arg = arg

    def __repr__(self):
        return "ExprApp(%s, %s)" % (self.function, self.arg)


class Declaration(object):
    pass


class DeclarationInductive(Declaration):
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

    def __repr__(self):
        return "DeclarationInductive(%s, %s, %s, %s, %s, %s, %s, %s)" % (self.name, self.expr, self.is_rec, self.is_nested, self.num_params, self.num_indices, self.ind_names, self.ctor_names)


class DeclarationCtor(Declaration):
    def __init__(self, name, ctype, inductive, cidx, num_params, num_fields, level_params):
        self.name = name
        self.ctype = ctype
        self.inductive = inductive
        self.cidx = cidx
        self.num_params = num_params
        self.num_fields = num_fields
        self.level_params = level_params

    def __repr__(self):
        return "DeclarationCtor(%s, %s, %s, %s, %s, %s)" % (self.name, self.ctype, self.inductive, self.cidx, self.num_params, self.num_fields)


class DeclarationRecursor(Declaration):
    def __init__(self, name, expr, k, numParams, numIndices, numMotives, numMinors, indNames, ruleIdxs, levelParams):
        self.name = name
        self.expr = expr
        self.k = k
        self.numParams = numParams
        self.numIndices = numIndices
        self.numMotives = numMotives
        self.numMinors = numMinors
        self.indNames = indNames
        self.ruleIdxs = ruleIdxs
        self.levelParams = levelParams

    def __repr__(self):
        return "DeclarationRecursor(%s, %s, %s, %s, %s, %s, %s, %s, %s)" % (self.name, self.expr, self.k, self.numParams, self.numIndices, self.numMotives, self.numMinors, self.indNames, self.ruleIdxs)


class DeclarationDef(Declaration):
    def __init__(self, name, def_type, def_val, hint, level_params):
        self.name = name
        self.def_type = def_type
        self.def_val = def_val
        self.hint = hint
        self.level_params = level_params

    def __repr__(self):
        return "DeclarationDef(%s, %s, %s, %s, %s)" % (self.name, self.def_type, self.def_val, self.hint, self.level_params)


class DeclarationTheorem(Declaration):
    def __init__(self, name, def_type, def_val, level_params):
        self.name = name
        self.def_type = def_type
        self.def_val = def_val
        self.level_params = level_params

    def __repr__(self):
        return "DeclarationDef(%s, %s, %s, %s)" % (self.name, self.def_type, self.def_val, self.level_params)


class Environment:
    def __init__(self):
        self.levels = {"0": LevelZero()}
        self.exprs = {}
        self.names = {"0": []}
        self.constants = {}
        self.rec_rules = {}
        self.declarations = {}

    def __repr__(self):
        return "Environment()"

    def register_name(self, nidx, parent_nidx, name):
        assert nidx not in self.names
        parent = self.names[parent_nidx]
        self.names[nidx] = parent + [name]

    def register_expr(self, eidx, expr):
        assert eidx not in self.exprs
        self.exprs[eidx] = expr

    def register_constant(self, name, type):
        assert name not in self.constants
        self.constants[name] = type

    def register_level(self, uidx, level):
        assert uidx not in self.levels
        self.levels[uidx] = level

    def register_rec_rule(self, ridx, name, nfields, rhs):
        assert ridx not in self.rec_rules
        self.rec_rules[ridx] = RecRule(name, nfields, rhs)

    def register_declaration(self, name_idx, decl):
        assert name_idx not in self.declarations
        self.declarations[name_idx] = decl


def interpret(source):
    environment = Environment()
    ast = parse(source)
    ast.compile(environment)

    print("NAMES:")
    for name, value in environment.names.items():
        print(name, value)

    print("\nEXPRS:")
    for name, value in environment.exprs.items():
        print(name, repr(value))

    print("\nCONSTANTS:")
    for name, value in environment.constants.items():
        print(name, repr(value))

    print("\nLEVELS:")
    for name, value in environment.levels.items():
        print(name, repr(value))

    print("\nRECRULES:")
    for name, value in environment.rec_rules.items():
        print(name, repr(value))

    print("\nDECLARATIONS:")
    for name, value in environment.declarations.items():
        print(name, repr(value))
