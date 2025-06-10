from __future__ import print_function

from rpython.rlib.objectmodel import r_dict

from rpylean import parser
from rpylean.objects import (
    W_TypeError,
    W_LEVEL_ZERO,
    Name,
    W_App,
    W_BVar,
    W_Const,
    W_FVar,
    W_ForAll,
    W_Lambda,
    W_LitNat,
    W_Sort,
)

import sys
sys.setrecursionlimit(5000)


class EnvironmentBuilder(object):
    """
    A mutable environment builder.

    Incrementally builds up an environment as we parse an export file.
    """

    def __init__(self, levels=None, exprs=None, names=[]):
        self.levels = [W_LEVEL_ZERO] if levels is None else levels
        self.exprs = [] if exprs is None else exprs
        self.names = [Name.ANONYMOUS] + names
        self.rec_rules = {}
        self.inductive_skeletons = {}
        self.declarations = r_dict(Name.eq, Name.hash)

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        # r_dict doesn't have sane __eq__
        if not all(
            v == getattr(other, k)
            for k, v in vars(self).iteritems()
            if k != "declarations"
        ):
            return False
        return r_dict_eq(self.declarations, other.declarations)

    def __ne__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return not self == other

    def __repr__(self):
        return "<EnvironmentBuilder with %s declarations>" % (
            len(self.declarations),
        )

    def consume(self, items):
        """
        Incrementally consume some items into this builder.

        Returns self, even though this mutates, so that chaining is possible.
        """
        for item in items:
            item.compile(self)
        return self

    def register_name(self, nidx, parent_nidx, name):
        assert nidx == len(self.names), nidx
        parent = self.names[parent_nidx]
        self.names.append(parent.child(name))

    def register_expr(self, eidx, w_expr):
        assert eidx == len(self.exprs), eidx
        self.exprs.append(w_expr)

    def register_level(self, uidx, level):
        # Are levels always dense? If not, we can presumably renumber them?
        assert uidx == len(self.levels), uidx
        self.levels.append(level)

    def register_rec_rule(self, rule_idx, w_recrule):
        assert rule_idx not in self.rec_rules, rule_idx
        self.rec_rules[rule_idx] = w_recrule

    def register_inductive_skeleton(self, skeleton):
        """
        Add the skeleton to our processing mapping.

        It will be finished when we see all of its constructors.
        """
        assert skeleton.name_idx not in self.inductive_skeletons
        self.inductive_skeletons[skeleton.name_idx] = skeleton

    def register_declaration(self, decl):
        seen = {}
        for level in decl.levels:
            assert level not in seen, "%s has duplicate level %s in all kind: %s" % (
                decl.name.pretty(),
                level,
                decl.levels,
            )
            seen[level] = True

        # > the kernel requires that the declaration is not already
        # > declared in the environment
        #
        #  -- from https://ammkrn.github.io/type_checking_in_lean4/kernel_concepts/the_big_picture.html
        assert decl.name not in self.declarations, "Duplicate declaration: %s" % (decl.name.pretty(),)
        self.declarations[decl.name] = decl

    def finish(self):
        """
        Finish building, generating the known-valid and immutable environment.
        """
        assert not self.inductive_skeletons, "Incomplete inductives: %s" % (
            ", ".join(
                [
                    self.names[nidx].pretty()
                    for nidx in self.inductive_skeletons
                ],
            ),
        )
        assert not self.rec_rules, "Incomplete recursors: %s" % (
            ", ".join(
                [
                    rule.ctor_name.pretty()
                    for rule in self.rec_rules.values()
                ],
            ),
        )
        return Environment(declarations=self.declarations)


def from_export(export):
    """
    Load an environment out of some lean4export-formatted export.
    """
    return from_items(parser.from_export(export)).finish()


def from_lines(lines):
    """
    Load an environment builder out of some partial lean4export lines.
    """
    return from_items(parser.to_items(lines))


def from_items(items):
    """
    Load an environment builder out of some parsed lean4export items.
    """
    return EnvironmentBuilder().consume(items)


class Environment(object):
    """
    A Lean environment with its declarations.
    """

    def __init__(self, declarations):
        self.declarations = declarations

    def __getitem__(self, name_or_list):
        if isinstance(name_or_list, str):
            name_or_list = [name_or_list]
        return self.declarations[Name(name_or_list)]

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return r_dict_eq(self.declarations, other.declarations)

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        return "<Environment with %s declarations>" % (len(self.declarations),)

    @staticmethod
    def having(declarations):
        """
        Construct an environment with the given declarations.
        """
        by_name = r_dict(Name.eq, Name.hash)
        for declaration in declarations:
            by_name[declaration.name] = declaration
        return Environment(declarations=by_name)

    def type_check(self):
        """
        Type check each declaration in the environment.
        """
        invalid = []
        for name, each in self.declarations.items():
            try:
                each.type_check(self)
            except W_TypeError as error:
                invalid.append((name, each, error))
            except Exception as error:
                print("Error checking %s: %s" % (name.pretty(), error))

        return CheckResult(self, invalid)

    def dump_pretty(self, stdout):
        """
        Dump the contents of this environment to the given stream.
        """
        for decl in self.declarations.values():
            stdout.write("%s\n" % (decl.pretty(),))

    def def_eq(self, expr1, expr2):
        """
        Check if two expressions are definitionally equal.
        """
        #print("Checking:\n  %s\n  %s" % (expr1.pretty(), expr2.pretty()))
        # Simple cases - expressions are the same type, so we just recurse
        if isinstance(expr1, W_FVar) and isinstance(expr2, W_FVar):
            return expr1.id == expr2.id
        elif isinstance(expr1, W_Sort) and isinstance(expr2, W_Sort):
            return expr1.level.eq(expr2.level)
        # Fast path for nat lits to avoid unnecessary conversion into 'Nat.succ' form
        elif isinstance(expr1, W_LitNat) and isinstance(expr2, W_LitNat):
            return expr1.val == expr2.val
        elif (isinstance(expr1, W_ForAll) and isinstance(expr2, W_ForAll)) or (isinstance(expr1, W_Lambda) and isinstance(expr2, W_Lambda)):
            if not self.def_eq(expr1.binder.type, expr2.binder.type):
                return False

            fvar = expr1.binder.fvar()
            body = expr1.body.instantiate(fvar, 0)
            other_body = expr2.body.instantiate(fvar, 0)

            return self.def_eq(body, other_body)

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
                return expr2_ty.binder.fun(
                    body=expr2.incr_free_bvars(1, 0).app(W_BVar(0)),
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


def r_dict_eq(left, right):
    # r_dict doesn't define sane __eq__
    return (
        len(left) == len(right)
        and all(k in right and right[k] == v for k, v in left.iteritems())
    )


def heading(s):
    return "%s\n%s\n\n" % (s, "-" * len(s))
