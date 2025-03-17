from __future__ import print_function

from rpylean.parser import parse


class LevelZero:
    pass


class ExprSort:
    def __init__(self, level):
        self.level = level

    def __repr__(self):
        return "ExprSort(%s)" % (self.level,)


class ExprConst:
    def __init__(self, const):
        self.const = const

    def __repr__(self):
        return "ExprConst(%s)" % (self.const,)


class Environment:
    def __init__(self):
        self.levels = {"0": LevelZero()}
        self.exprs = {}
        self.names = {"0": []}
        self.constants = {}

    def __repr__(self):
        return "Environment()"

    def add_name(self, nidx, segments):
        assert nidx not in self.names
        self.names[nidx] = segments

    def add_expr(self, eidx, expr):
        assert eidx not in self.exprs
        self.exprs[eidx] = expr

    def add_constant(self, name, type):
        key = tuple(name)
        assert key not in self.constants
        self.constants[key] = type


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
                assert len(item.children) == 3, "uidxs present"
                value = env.names[nidx]
                env.add_expr(eidx, ExprConst(value))
            else:
                assert False, etype
        elif item.symbol == "declaration":
            nidx = item.children[0].children[1].children[0].additional_info
            eidx = item.children[0].children[2].children[0].additional_info
            name = env.names[nidx]
            type = env.exprs[eidx]
            env.add_constant(name, type)
        else:
            assert False, each

    print("NAMES:")
    for name, value in env.names.items():
        print(name, value)

    print("\nEXPRS:")
    for name, value in env.exprs.items():
        print(name, value)
