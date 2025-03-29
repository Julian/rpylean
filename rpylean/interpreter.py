from __future__ import print_function

from rpylean.objects import W_LEVEL_ZERO, W_Sort
from rpylean.parser import parse
from rpython.rlib.objectmodel import we_are_translated

import sys; sys.setrecursionlimit(10000)


def print_heading(s):
    print(s)
    print("-" * len(s), end="\n\n")


class Name:
    def __init__(self, components):
        self.components = components

    def __hash__(self):
        hash_val = 0
        for c in self.components:
            hash_val = hash_val ^ hash(c)
        return hash_val
    
    def __eq__(self, other):
        return self.components == other.components

    def __repr__(self):
        return "<Name %r>" % (self.components,)

    def pretty(self):
        return '.'.join(self.components)
    
class Environment:
    def __init__(self):
        self.levels = {"0": W_LEVEL_ZERO}
        self.exprs = {}
        self.names = {"0": Name([])}
        self.constants = {}
        self.rec_rules = {}
        self.declarations = {}

    def __repr__(self):
        return "Environment()"

    def dump(self):
        print_heading("declarations")
        for name, decl in self.declarations.items():
            print(name, "->", decl)

        print("")
        print_heading("exprs")
        for id, expr in self.exprs.items():
            print(id, "->", expr)

        print("")
        print_heading("constants")
        for id, constant in self.constants.items():
            print(id, "->", constant)

        print("")
        print_heading("levels")
        for id, level in self.levels.items():
            print(id, "->", level)

        print("")
        print_heading("rec_rules")
        for id, rule in self.rec_rules.items():
            print(id, "->", rule)

    def dump_pretty(self):
        print_heading("declarations")
        for name, decl in self.declarations.items():
            print(name.pretty(), "->", decl.pretty())

        print("")
        print_heading("exprs")
        for id, expr in self.exprs.items():
            print(id, "->", expr.pretty())

        print("")
        print_heading("constants")
        for id, constant in self.constants.items():
            print(id, "->", constant.pretty())

        print("")
        print_heading("levels")
        for id, level in self.levels.items():
            print(id, "->", level.pretty())

        print("")
        print_heading("rec_rules")
        for id, rule in self.rec_rules.items():
            print(id, "->", rule.pretty())

    def register_name(self, nidx, parent_nidx, name):
        assert nidx not in self.names, nidx
        parent = self.names[parent_nidx]
        self.names[nidx] = Name(parent.components + [name])

    def register_expr(self, eidx, w_expr):
        assert eidx not in self.exprs, eidx
        self.exprs[eidx] = w_expr

    def register_constant(self, name, type):
        assert name not in self.constants, name
        self.constants[name] = type

    def register_level(self, uidx, level):
        assert uidx not in self.levels, uidx
        self.levels[uidx] = level

    def register_rec_rule(self, ridx, w_recrule):
        assert ridx not in self.rec_rules, ridx
        self.rec_rules[ridx] = w_recrule

    def register_declaration(self, name_idx, decl):
        name = self.names[name_idx]
        # > the kernel requires that the declaration is not already
        # > declared in the environment
        #
        #  -- from https://ammkrn.github.io/type_checking_in_lean4/kernel_concepts/the_big_picture.html
        assert name not in self.declarations
        self.declarations[name] = decl


class InferenceContext:
    def __init__(self, env):
        self.env = env

    # Checks if two expressions are definitionally equal.
    def def_eq(self, expr1, expr2):
        if not we_are_translated():
            assert type(expr1) == type(expr2)
        try:
            return expr1.def_eq(expr2, self)
        except Exception as e:
            print("Error in def_eq for:")
            print("  %s" % expr1.pretty())
            print("  %s" % expr2.pretty())
            raise
    
    def infer_sort_of(self, expr):
        expr_type = expr.infer(self).whnf(self.env)
        if isinstance(expr_type, W_Sort):
            return expr_type.level
        raise RuntimeError("Expected Sort, got %s" % expr_type)


def interpret(source):
    ast = parse(source)

    environment = Environment()
    ast.compile(environment)

    ctx = InferenceContext(environment)
    environment.dump_pretty()

    for name, decl in environment.declarations.items():
        print("Checking declaration:", name)
        decl.w_kind.type_check(ctx)

