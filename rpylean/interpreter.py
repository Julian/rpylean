from __future__ import print_function

from rpylean.objects import W_LEVEL_ZERO, NotDefEq, W_App, W_BVar, W_Const, W_FVar, W_ForAll, W_Lambda, W_Sort
from rpylean.parser import parse
from rpython.rlib.objectmodel import we_are_translated


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
        assert name not in self.declarations, "Duplicate declaration: %s" % name
        self.declarations[name] = decl


class InferenceContext:
    def __init__(self, env):
        self.env = env

    # Checks if two expressions are definitionally equal.
    def def_eq(self, expr1, expr2):
        print("Considering: %s vs %s" % (expr1.pretty(), expr2.pretty()))

        # Simple cases - expressions are the same type, so we just recurse
        if isinstance(expr1, W_FVar) and isinstance(expr2, W_FVar):
            if expr1.id != expr2.id:
                raise NotDefEq(expr1, expr2)
            return True
        elif isinstance(expr1, W_Sort) and isinstance(expr2, W_Sort):
            if not expr1.level.antisymm_eq(expr2.level, self):
                raise NotDefEq(expr1, expr2)
            return True
        elif (isinstance(expr1, W_ForAll) and isinstance(expr2, W_ForAll)) or (isinstance(expr1, W_Lambda) and isinstance(expr2, W_Lambda)):
            if not self.def_eq(expr1.binder_type, expr2.binder_type):
                raise NotDefEq(expr1, expr2)
            
            fvar = W_FVar(expr1)
            body = expr1.body.instantiate(fvar, 0)
            other_body = expr2.body.instantiate(fvar, 0)
            return self.def_eq(body, other_body)

        
        # Fast path for constants - if the name and levels are all equal, then they are definitionally equal
        if isinstance(expr1, W_Const) and isinstance(expr2, W_Const) and expr1.name == expr2.name:
            # A given constant always has the same number of universe parameters
            assert len(expr1.levels) == len(expr2.levels)
            all_match = True
            for i in range(len(expr1.levels)):
                if not expr1.levels[i].antisymm_eq(expr2.levels[i], self):
                    all_match = False
                    break
            if all_match:
                return True
            
        # At this point, we've exhausted all of the simple cases, and we now need to perform some kind of reduction
        # For now, we don't handle all of the needed cases, so we'll sometimes raise a spurious `NotDefEq` exception.

        # Naive approach - try a single round of delta reduction on both expressions
        # If either reduction makes progress, then retry with the new expressions.
        # Otherwise, give up
        progress = False
        expr1_reduced = expr1.whnf(self.env)
        expr2_reduced = expr2.whnf(self.env)
        if expr1_reduced != expr1:
            expr1 = expr1_reduced
            progress = True
        if expr2_reduced != expr2:
            expr2 = expr2_reduced
            progress = True

        if progress:
            return self.def_eq(expr1, expr2)

        if isinstance(expr1, W_Const):
            expr1_reduced = expr1.try_delta_reduce(self.env)
            if expr1_reduced is not None:
                expr1 = expr1_reduced
                progress = True
        if isinstance(expr2, W_Const):
            expr2_reduced = expr2.try_delta_reduce(self.env)
            if expr2_reduced is not None:
                expr2 = expr2_reduced
                progress = True

        if progress:
            return self.def_eq(expr1, expr2)
        
        # Only perform this check after we've already tried reduction,
        # since this check can get fail in cases like '((fvar 1) x)' ((fun y => ((fvar 1) x)) z)
        if isinstance(expr1, W_App) and isinstance(expr2, W_App):
           fn_eq = self.def_eq(expr1.fn, expr2.fn)
           arg_eq = self.def_eq(expr1.arg, expr2.arg)
           return fn_eq and arg_eq

        raise NotDefEq(expr1, expr2)

    def infer_sort_of(self, expr):
        expr_type = expr.infer(self).whnf(self.env)
        if isinstance(expr_type, W_Sort):
            return expr_type.level
        raise RuntimeError("Expected Sort, got %s" % expr_type)


def interpret(lines):
    environment = Environment()
    for item in parse(lines):
        item.compile(environment)

    ctx = InferenceContext(environment)
    environment.dump_pretty()

    for name, decl in environment.declarations.items():
        print("Checking declaration:", name)
        decl.w_kind.type_check(ctx)
