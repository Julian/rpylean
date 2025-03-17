from __future__ import print_function

from rpylean.parser import parse


class LevelZero:
    pass


class Expr:
    pass


class ExprSort(Expr):
    def __init__(self, level):
        self.level = level

    def __repr__(self):
        return "ExprSort(%s)" % (self.level,)


class ExprConst(Expr):
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


def interpret(source):
    environment = Environment()
    ast = parse(source)
    ast.compile(environment)

    print("NAMES:")
    for name, value in environment.names.items():
        print(name, value)

    print("\nEXPRS:")
    for name, value in environment.exprs.items():
        print(name, value)
