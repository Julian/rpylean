from __future__ import print_function

from rpylean.objects import W_TypeError, W_LEVEL_ZERO, W_App, W_BVar, W_Const, W_FVar, W_ForAll, W_Lambda, W_LitNat, W_Proj, W_Sort, Name
from rpylean.parser import parse
from rpython.rlib.objectmodel import r_dict

import sys
sys.setrecursionlimit(5000)


class Environment:
    def __init__(self):
        self.levels = {"0": W_LEVEL_ZERO}
        self.exprs = {}
        self.names = {"0": Name.ANONYMOUS}
        self.rec_rules = {}
        self.declarations = r_dict(Name.eq, Name.__hash__)

    def __getitem__(self, name_or_list):
        if isinstance(name_or_list, str):
            name_or_list = [name_or_list]
        return self.declarations[Name(name_or_list)]

    def __repr__(self):
        return "<Environment with %s declarations>" % (len(self.declarations),)

    @staticmethod
    def from_lines(lines):
        """
        Load an environment out of some lean4export-formatted lines.
        """
        return Environment.from_items(parse(lines))

    @staticmethod
    def from_items(items):
        """
        Load an environment out of some parsed lean4export items.
        """
        env = Environment()
        for item in items:
            item.compile(env)
        return env

    def type_check(self):
        """
        Type check each declaration in the environment.
        """
        ctx = self.inference_context()

        invalid = []
        for name, each in self.declarations.items():
            try:
                each.type_check(ctx)
            except W_TypeError as error:
                invalid.append((name, each, error))

        return CheckResult(self, invalid)

    def dump_pretty(self, stdout):
        """
        Dump the contents of this environment to the given stream.
        """
        stdout.write(heading("declarations"))
        for name, decl in self.declarations.items():
            stdout.write("%s := %s\n" % (name.pretty(), decl.pretty()))

        stdout.write("\n")
        stdout.write(heading("exprs"))
        for id, expr in self.exprs.items():
            stdout.write("%s -> %s\n" % (id, expr.pretty()))

        stdout.write("\n")
        stdout.write(heading("levels"))
        for id, level in self.levels.items():
            stdout.write("%s -> %s\n" % (id, level.pretty()))

        stdout.write("\n")
        stdout.write(heading("rec_rules"))
        for id, rule in self.rec_rules.items():
            stdout.write("%s -> %s\n" % (id, rule.pretty()))

    def inference_context(self):
        return _InferenceContext(self)

    def register_name(self, nidx, parent_nidx, name):
        assert nidx not in self.names, nidx
        parent = self.names[parent_nidx]
        self.names[nidx] = parent.child(name)

    def register_expr(self, eidx, w_expr):
        assert eidx not in self.exprs, eidx
        self.exprs[eidx] = w_expr

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


class _InferenceContext:
    def __init__(self, env):
        self.env = env

    # Checks if two expressions are definitionally equal.
    def def_eq(self, expr1, expr2):
        #print("Checking:\n  %s\n  %s" % (expr1.pretty(), expr2.pretty()))
        # Simple cases - expressions are the same type, so we just recurse
        if isinstance(expr1, W_FVar) and isinstance(expr2, W_FVar):
            if expr1.id != expr2.id:
                return False
            return True
        elif isinstance(expr1, W_Sort) and isinstance(expr2, W_Sort):
            if not expr1.level.eq(expr2.level):
                return False
            return True
        elif (isinstance(expr1, W_ForAll) and isinstance(expr2, W_ForAll)) or (isinstance(expr1, W_Lambda) and isinstance(expr2, W_Lambda)):
            if not self.def_eq(expr1.binder_type, expr2.binder_type):
                return False

            fvar = W_FVar(expr1)
            body = expr1.body.instantiate(fvar, 0)
            other_body = expr2.body.instantiate(fvar, 0)

            return self.def_eq(body, other_body)
        # Fast path for nat lits to avoid unnecessary conversion into 'Nat.succ' form
        elif isinstance(expr1, W_LitNat) and isinstance(expr2, W_LitNat):
            if expr1.val != expr2.val:
                return False
            return True

        # Fast path for constants - if the name and levels are all equal, then they are definitionally equal
        if isinstance(expr1, W_Const) and isinstance(expr2, W_Const) and expr1.name.eq(expr2.name):
            # A given constant always has the same number of universe parameters
            assert len(expr1.levels) == len(expr2.levels)
            all_match = True
            for i in range(len(expr1.levels)):
                if not expr1.levels[i].eq(expr2.levels[i]):
                    all_match = False
                    break
            if all_match:
                return True

        if isinstance(expr1, W_App) and isinstance(expr2, W_App):
            if (
                    self.def_eq(expr1.fn, expr2.fn)
                and self.def_eq(expr1.arg, expr2.arg)
            ):
                return True

        # Try a reduction step
        progress1, expr1_reduced = expr1.strong_reduce_step(self)
        progress2, expr2_reduced = expr2.strong_reduce_step(self)
        if progress1 or progress2:
            # If expr2 made progress, retry with the new expr2
            return self.def_eq(expr1_reduced, expr2_reduced)
        expr1 = expr1_reduced
        expr2 = expr2_reduced

        # Proof irrelevance check: Get the types of our expressions
        expr1_ty = expr1.infer(self)
        expr2_ty = expr2.infer(self)
        # If these types are themselves Prop (Sort 0), and the types are equal, then our original expressions are proofs of the same `Prop`
        expr1_ty_kind = expr1_ty.infer(self)
        expr2_ty_kind = expr2_ty.infer(self)
        if expr1_ty_kind.syntactic_eq(W_LEVEL_ZERO.sort()) and expr2_ty_kind.syntactic_eq(W_LEVEL_ZERO.sort()):
            if self.def_eq(expr1_ty, expr2_ty):
                return True

        # Only perform this check after we've already tried reduction,
        # since this check can get fail in cases like '((fvar 1) x)' ((fun y => ((fvar 1) x)) z)

        expr2_eta = self.try_eta_expand(expr1, expr2)
        if expr2_eta is not None:
            return self.def_eq(expr1, expr2_eta)
        expr1_eta = self.try_eta_expand(expr2, expr1)
        if expr1_eta is not None:
            return self.def_eq(expr1_eta, expr2)


        # Perform this check late, as it can be very slow for large nested App expressiosn
        if expr1.syntactic_eq(expr2):
            return True

        # As the *very* last step, try converting NatLit exprs
        # In order to be able to type check things like 'UInt32.size',
        # we need to try everything else before actually calling 'build_nat_expr'
        # (so that checks like syntactic equality can succeed and prevent us from
        # building up ~4 billion `Nat` expressions)
        if isinstance(expr1, W_LitNat):
            return self.def_eq(expr1.build_nat_expr(), expr2)
        elif isinstance(expr2, W_LitNat):
            return self.def_eq(expr1, expr2.build_nat_expr())

        return False

    def try_eta_expand(self, expr1, expr2):
        if isinstance(expr1, W_Lambda):
            expr2_ty = expr2.infer(self).whnf(self)
            if isinstance(expr2_ty, W_ForAll):
                #print("Eta-expanding %s" % expr2.pretty())
                # Turn 'f' into 'fun x => f x'
                return W_Lambda(
                    binder_name=expr2_ty.binder_name,
                    binder_info=expr2_ty.binder_info,
                    binder_type=expr2_ty.binder_type,
                    body=W_App(expr2.incr_free_bvars(1, 0), W_BVar(0))
                )
        return None

    def infer_sort_of(self, expr):
        expr_type = expr.infer(self).whnf(self)
        if isinstance(expr_type, W_Sort):
            return expr_type.level
        raise RuntimeError("Expected Sort, got %s" % expr_type)


class CheckResult(object):
    """
    The result of type checking an environment.
    """

    def __init__(self, environment, invalid=None):
        self.environment = environment
        self.invalid = invalid

    def succeeded(self):
        return not self.invalid


def heading(s):
    return "%s\n%s\n\n" % (s, "-" * len(s))
