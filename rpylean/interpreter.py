from __future__ import print_function

from rpylean.parser import parse

class Level:
    pass

class LevelZero:
    def __repr__(self):
        return "LevelZero()"

class LevelParam:
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

class Environment:
    def __init__(self):
        self.levels = {"0": LevelZero()}
        self.exprs = {}
        self.names = {"0": []}
        self.constants = {}
        self.rec_rules = {}

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
            nidx = item.children[0].children[1].children[0].additional_info
            eidx = item.children[0].children[2].children[0].additional_info
            name = env.names[nidx]
            type = env.exprs[eidx]
            key = ".".join(name)
            env.add_constant(key, type)
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
        print(name, value)
