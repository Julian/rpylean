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

    def add_name(self, nidx, segments):
        assert nidx not in self.names
        self.names[nidx] = segments

    def add_expr(self, eidx, expr):
        assert eidx not in self.exprs
        self.exprs[eidx] = expr

    def add_constant(self, name, type):
        assert name not in self.constants
        self.constants[name] = type

    def add_level(self, uidx, level):
        assert uidx not in self.levels
        self.levels[uidx] = level

    def add_rec_rule(self, ridx, name, nfields, rhs):
        assert ridx not in self.rec_rules
        self.rec_rules[ridx] = RecRule(name, nfields, rhs)

    def add_declaration(self, name_idx, decl):
        assert name_idx not in self.declarations
        self.declarations[name_idx] = decl


def interpret(source):
    items = parse(source)

    env = Environment()

    for each in items.children:
        item = each.children[0]
        if item.symbol == "name":
            symbol = item.children[0].children[0]
            new_nidx = symbol.additional_info
            parent_nidx = item.children[2].children[0].additional_info
            parent = env.names[parent_nidx]

            name = item.children[3].additional_info
            env.add_name(new_nidx, parent + [name])
        elif item.symbol == "expr":
            etype = item.children[1]
            if etype.additional_info == "#ES":
                eidx, etype, uidx = item.children
                level = env.levels[uidx.children[0].additional_info]
                env.add_expr(eidx.children[0].additional_info, ExprSort(level))
            elif etype.additional_info == "#EC":
                eidx = item.children[0].children[0].additional_info
                nidx = item.children[2].children[0].additional_info
                levels = []
                for child in item.children[3:]:
                    level = env.levels[child.children[0].additional_info]
                    levels.append(level)
                value = env.names[nidx]
                env.add_expr(eidx, ExprConst(value, levels))
            elif etype.additional_info == "#EP":
                eidx = item.children[0].children[0].additional_info
                info = item.children[2].children[0].additional_info
                binderName = env.names[item.children[3].children[0].additional_info]
                binderType = env.exprs[item.children[4].children[0].additional_info]
                body = env.exprs[item.children[5].children[0].additional_info]
                env.add_expr(eidx, ExprForallE(info, binderName, binderType, body))
            elif etype.additional_info == "#EV":
                eidx = item.children[0].children[0].additional_info
                id = item.children[2].additional_info
                env.add_expr(eidx, ExprBVar(id))
            elif etype.additional_info == "#EA":
                eidx = item.children[0].children[0].additional_info
                function = env.exprs[item.children[2].children[0].additional_info]
                arg = env.exprs[item.children[3].children[0].additional_info]
                env.add_expr(eidx, ExprApp(function, arg))
            elif etype.additional_info == "#EL":
                eidx = item.children[0].children[0].additional_info
                info = item.children[2].children[0].additional_info
                binderName = env.names[item.children[3].children[0].additional_info]
                binderType = env.exprs[item.children[4].children[0].additional_info]
                body = env.exprs[item.children[5].children[0].additional_info]
                env.add_expr(eidx, ExprLambda(info, binderName, binderType, body))
            else:
                assert False, etype
        elif item.symbol == "declaration":
            dec_kind = item.children[0].children[0].additional_info
            if dec_kind == "#IND":
                item = item.children[0]
                name_idx = item.children[1].children[0].additional_info
                name = env.names[name_idx]
                expr = env.exprs[item.children[2].children[0].additional_info]
                isRec = item.children[3].additional_info
                isNested = item.children[4].additional_info
                numParams = item.children[5].additional_info
                numIndices = item.children[6].additional_info
                numIndNameIdxs = int(item.children[7].additional_info)
                if numIndNameIdxs < 0:
                    raise RuntimeError("numIndNameIdxs must be non-negative")
                pos = 8
                indNameIdxs = item.children[pos:(pos + numIndNameIdxs)]
                pos += numIndNameIdxs

                numCtors = int(item.children[pos].additional_info)
                if numCtors < 0:
                    raise RuntimeError("numCtors must be non-negative")
                pos += 1

                ctorNameIdxs = item.children[pos:(pos + numCtors)]
                pos += numCtors

                levels = item.children[pos:]
                env.add_declaration(name_idx, DeclarationInductive(name, expr, isRec, isNested, numParams, numIndices, indNameIdxs, ctorNameIdxs, levels))
            elif dec_kind == "#CTOR":
                item = item.children[0]
                name_idx = item.children[1].children[0].additional_info
                name = env.names[name_idx]
                ctype = env.exprs[item.children[2].children[0].additional_info]
                induct = env.names[item.children[3].children[0].additional_info]
                cidx = item.children[4].additional_info
                numParams = item.children[5].additional_info
                numFields = item.children[6].additional_info
                levelsParamIds = item.children[7:]
                env.add_declaration(name_idx, DeclarationCtor(name, ctype, induct, cidx, numParams, numFields, levelsParamIds))
            elif dec_kind == "#REC":
                item = item.children[0]
                name_idx = item.children[1].children[0].additional_info
                name = env.names[name_idx]
                expr = env.exprs[item.children[2].children[0].additional_info]
                numIndNameIdxs = int(item.children[3].additional_info)
                if numIndNameIdxs < 0:
                    raise RuntimeError("numIndNameIdxs must be non-negative")
                pos = 4
                indNameIdxs = item.children[pos:(pos + numIndNameIdxs)]
                pos += numIndNameIdxs

                numParams = item.children[pos].additional_info
                numIndices = item.children[pos + 1].additional_info
                numMotives = item.children[pos + 2].additional_info
                numMinors = item.children[pos + 3].additional_info
                numRuleIdxs = int(item.children[pos + 4].additional_info)
                if numRuleIdxs < 0:
                    raise RuntimeError("numRuleIdxs must be non-negative")
                pos += 5

                ruleIdxs = item.children[pos:(pos + numRuleIdxs)]
                pos += numRuleIdxs

                k = item.children[pos].additional_info
                levelParams = item.children[(pos + 1):]
                env.add_declaration(name_idx, DeclarationRecursor(name, expr, k, numParams, numIndices, numMotives, numMinors, indNameIdxs, ruleIdxs, levelParams))
            elif dec_kind == "#DEF":
                item = item.children[0]
                name_idx = item.children[1].children[0].additional_info
                name = env.names[name_idx]
                def_type = env.exprs[item.children[2].children[0].additional_info]
                def_val = env.exprs[item.children[3].children[0].additional_info]
                hint = item.children[4]
                levelParams = item.children[5:]
                env.add_declaration(name_idx, DeclarationDef(name, def_type, def_val, hint, levelParams))
            elif dec_kind == "#THM":
                item = item.children[0]
                name_idx = item.children[1].children[0].additional_info
                name = env.names[name_idx]
                def_type = env.exprs[item.children[2].children[0].additional_info]
                def_val = env.exprs[item.children[3].children[0].additional_info]
                levelParams = item.children[4:]
                env.add_declaration(name_idx, DeclarationTheorem(name, def_type, def_val, levelParams))                
            else:
                assert False, "unknown declaration type %s" % (dec_kind,)
        elif item.symbol == "universe":
            target_uidx = item.children[0].children[0].additional_info
            utype = item.children[1]
            if utype.additional_info == "#UP":
                uname = item.children[2].children[0].additional_info
                env.add_level(target_uidx, LevelParam(uname))
            else:
                raise RuntimeError("unknown universe type %s" % (utype.additional_info,))
        elif item.symbol == "recrule":
            target_ridx = item.children[0].children[0].additional_info
            name = env.names[item.children[2].children[0].additional_info]
            nfields = item.children[3].additional_info
            rhs = env.exprs[item.children[4].children[0].additional_info]
            env.add_rec_rule(target_ridx, name, nfields, rhs)
            print("Rule", target_ridx, name, nfields, rhs)
        else:
            print("Symbol", item.symbol)
            assert False, each

    print("NAMES:")
    for name, value in env.names.items():
        print(name, value)

    print("\nEXPRS:")
    for name, value in env.exprs.items():
        print(name, value.__repr__())

    print("\nCONSTANTS:")
    for name, value in env.constants.items():
        print(name, value.__repr__())

    print("\nLEVELS:")
    for name, value in env.levels.items():
        print(name, value.__repr__())

    print("\nRECRULES:")
    for name, value in env.rec_rules.items():
        print(name, value.__repr__())

    print("\nDECLARATIONS:")
    for name, value in env.declarations.items():
        print(name, value.__repr__())
