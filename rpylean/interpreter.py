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

    def dump(self):
        for attr, value in sorted(self.__dict__.items()):
            if not value:
                continue

            print(attr)
            print("-" * len(attr), end="\n\n")

            for k, v in value.items():
                print(k, ":", v)

            print("")

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
    ast = parse(source)

    environment = Environment()
    ast.compile(environment)

    if not we_are_translated():
        environment.dump()
