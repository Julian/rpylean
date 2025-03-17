from __future__ import print_function

from rpython.rlib.objectmodel import we_are_translated

from rpylean.objects import W_LEVEL_ZERO
from rpylean.parser import parse


class Environment:
    def __init__(self):
        self.levels = {"0": W_LEVEL_ZERO}
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

    def register_expr(self, eidx, w_expr):
        assert eidx not in self.exprs
        self.exprs[eidx] = w_expr

    def register_constant(self, name, type):
        assert name not in self.constants
        self.constants[name] = type

    def register_level(self, uidx, level):
        assert uidx not in self.levels
        self.levels[uidx] = level

    def register_rec_rule(self, ridx, w_recrule):
        assert ridx not in self.rec_rules
        self.rec_rules[ridx] = w_recrule

    def register_declaration(self, name_idx, decl):
        assert name_idx not in self.declarations
        self.declarations[name_idx] = decl


def interpret(source):
    environment = Environment()
    ast = parse(source)
    ast.compile(environment)

    if we_are_translated():
        print(environment)
    else:
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
