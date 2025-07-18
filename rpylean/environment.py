from __future__ import print_function
from sys import stderr
from traceback import print_exc
import pdb

from rpython.rlib.objectmodel import not_rpython, r_dict, we_are_translated

from rpylean import parser
from rpylean._rlib import r_dict_eq
from rpylean.exceptions import (
    AlreadyDeclared,
    DuplicateLevels,
    UnknownQuotient,
)
from rpylean.objects import (
    W_LEVEL_ZERO,
    PROP,
    Name,
    W_BVar,
    W_Const,
    W_ForAll,
    W_Lambda,
    W_LitNat,
    W_LitStr,
    W_Sort,
    fun,
    name_eq,
    syntactic_eq,
)


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
        self.quotient = []

        self.declarations = []

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return vars(self) == vars(other)

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

    # We assume nidx, eidx and uidx are always the next index to use.
    # This seems to hold for exports we've seen, but if it ever weren't the
    # case we could just have these methods renumber the indices so they're
    # still contiguous.
    def register_name(self, nidx, name):
        assert nidx == len(self.names), nidx
        self.names.append(name)

    def register_expr(self, eidx, w_expr):
        assert eidx == len(self.exprs), eidx
        self.exprs.append(w_expr)

    def register_level(self, uidx, level):
        assert uidx == len(self.levels), uidx
        self.levels.append(level)

    def register_rec_rule(self, rule_idx, w_recrule):
        """
        Store a rule until its recursor comes to grab it with its siblings.
        """
        assert rule_idx not in self.rec_rules, rule_idx
        self.rec_rules[rule_idx] = w_recrule

    def register_inductive_skeleton(self, skeleton):
        """
        Add the skeleton to our processing mapping.

        It will be finished when we see all of its constructors.
        """
        assert skeleton.nidx not in self.inductive_skeletons
        self.inductive_skeletons[skeleton.nidx] = skeleton

    def register_quotient(self, name, type):
        self.quotient.append((name, type))

    def register_declaration(self, decl):
        self.declarations.append(decl)

    def finish(self):
        """
        Finish building, generating the known-valid and immutable environment.
        """
        # TODO: Make these all proper exceptions.
        assert not self.inductive_skeletons, "Incomplete inductives: %s" % (
            ", ".join(
                [
                    self.names[nidx].str()
                    for nidx in self.inductive_skeletons
                ],
            ),
        )
        assert not self.rec_rules, "Incomplete recursors: %s" % (
            ", ".join(
                [
                    rule.ctor_name.str()
                    for rule in self.rec_rules.values()
                ],
            ),
        )

        if self.quotient:
            from rpylean.quot import QUOT, QUOT_MK, QUOT_IND, QUOT_LIFT

            for name, type in self.quotient:
                n = len(name.components)
                if (
                    n == 0
                    or n > 2
                    or name.components[0] != "Quot"
                ):
                    raise UnknownQuotient(name, type)

                if n == 1:
                    expected = QUOT
                elif name.components[1] == "mk":
                    expected = QUOT_MK
                elif name.components[1] == "ind":
                    expected = QUOT_IND
                elif name.components[1] == "lift":
                    expected = QUOT_LIFT
                else:
                    raise UnknownQuotient(name, type)

                print(name.str())
                print(type)
                print(expected)

        return Environment.having(self.declarations)


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

    @not_rpython
    def __getitem__(self, value):
        name = value if isinstance(value, Name) else Name.from_str(value)
        return self.declarations[name]

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
        by_name = r_dict(name_eq, Name.hash)
        for each in declarations:
            if each.name in by_name:
                raise AlreadyDeclared(each, by_name)

            levels = {}
            for level in each.levels:
                if level in levels:
                    raise DuplicateLevels(each, level)
                levels[level] = True

            by_name[each.name] = each
        return Environment(declarations=by_name)

    def pretty(self, declaration):
        """
        Pretty-print the given declaration.
        """
        return declaration.pretty(self.declarations)

    def print(self, declaration, file, end="\n"):
        """
        Pretty-print the declaration to the given file.
        """
        file.write(self.pretty(declaration))
        file.write(end)

    def type_check(self, declarations=None):
        """
        Type check each declaration in the environment.
        """
        if declarations is None:
            declarations = self.declarations.values()

        for each in declarations:
            try:
                error = each.type_check(self)
            except Exception as e:
                if not we_are_translated():
                    print_exc(None, stderr)
                    stderr.write("\nwhile checking:\n\n")
                    self.print(each, stderr)
                    pdb.post_mortem()
                raise
            if error is not None:
                yield error

    def dump_pretty(self, stdout):
        """
        Dump the contents of this environment to the given stream.
        """
        for decl in self.declarations.values():
            self.print(decl, stdout)

    def def_eq(self, expr1, expr2):
        """
        Check if two expressions are definitionally equal.
        """
        assert not isinstance(expr1, W_BVar), (
            "unexpectedly encountered BVar in def_eq: %s" % expr1
        )
        assert not isinstance(expr2, W_BVar), (
            "unexpectedly encountered BVar in def_eq: %s" % expr2
        )

        cls = expr1.__class__
        if cls is expr2.__class__ and (
            # returning NotImplemented (from W_Const.def_eq)
            # isn't valid RPython, and the point is these are not comparable
            # until they're reduced...
            # Still would love to think of a better way.
            cls is not W_Const
            or expr1.name == expr2.name
        ):
            return expr1.def_eq(expr2, self.def_eq)

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
        if syntactic_eq(expr1_ty_kind, PROP) and syntactic_eq(expr2_ty_kind, PROP):
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

        # As the *very* last step, try converting NatLit exprs
        # In order to be able to type check things like 'UInt32.size',
        # we need to try everything else before actually calling 'build_nat_expr'
        # (so that checks like syntactic equality can succeed and prevent us from
        # building up ~4 billion `Nat` expressions)
        if cls is W_LitNat:
            return self.def_eq(expr1.build_nat_expr(), expr2)
        elif isinstance(expr2, W_LitNat):
            return self.def_eq(expr1, expr2.build_nat_expr())

        if cls is W_LitStr:
            return self.def_eq(expr1.build_str_expr(self), expr2)
        elif isinstance(expr2, W_LitStr):
            return self.def_eq(expr1, expr2.build_str_expr(self))

        return False

    def try_eta_expand(self, expr1, expr2):
        if isinstance(expr1, W_Lambda):
            expr2_ty = expr2.infer(self).whnf(self)
            if isinstance(expr2_ty, W_ForAll):
                #print("Eta-expanding %s" % expr2.pretty())
                # Turn 'f' into 'fun x => f x'
                return fun(expr2_ty.binder)(
                    expr2.incr_free_bvars(1, 0).app(W_BVar(0)),
                )
        return None

    def infer_sort_of(self, expr):
        expr_type = expr.infer(self).whnf(self)
        if isinstance(expr_type, W_Sort):
            return expr_type.level
        raise RuntimeError("Expected Sort, got %s" % expr_type)


#: The empty environment.
Environment.EMPTY = Environment.having([])


def heading(s):
    return "%s\n%s\n\n" % (s, "-" * len(s))
