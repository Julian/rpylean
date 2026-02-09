from __future__ import print_function

from sys import stderr
from traceback import print_exc
import pdb

from rpython.rlib.jit import promote
from rpython.rlib.objectmodel import not_rpython, r_dict, we_are_translated

from rpylean import parser
from rpylean._rlib import r_dict_eq
from rpylean.exceptions import (
    AlreadyDeclared,
    DuplicateLevels,
    HeartbeatExceeded,
    UnknownQuotient,
)
from rpylean.objects import (
    W_LEVEL_ZERO,
    PROP,
    Name,
    W_App,
    W_BVar,
    W_Const,
    W_Constructor,
    W_ForAll,
    W_HeartbeatError,
    W_Inductive,
    W_Lambda,
    W_LitNat,
    W_LitStr,
    W_Proj,
    W_Sort,
    fun,
    get_decl,
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
        return "<EnvironmentBuilder with %s declarations>" % (len(self.declarations),)

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

    def register_quotient(self, name, type, levels):
        self.quotient.append((name, type, levels))

    def register_declaration(self, decl):
        self.declarations.append(decl)

    def finish(self):
        """
        Finish building, generating the known-valid and immutable environment.
        """
        # TODO: Make these all proper exceptions.
        assert not self.rec_rules, "Incomplete recursors: %s" % (
            ", ".join(
                [rule.ctor_name.str() for rule in self.rec_rules.values()],
            ),
        )

        if self.quotient:
            from rpylean.quot import QUOT, QUOT_MK, QUOT_IND, QUOT_LIFT

            for name, type, levels in self.quotient:
                n = len(name.components)
                if n == 0 or n > 2 or name.components[0] != "Quot":
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

                self.register_declaration(name.axiom(type=type, levels=levels))

        return Environment.having(self.declarations)


def from_export(export):
    """
    Load an environment out of some lean4export-formatted export.
    """
    return from_items(parser.from_export(export)).finish()


def from_items(items):
    """
    Load an environment builder out of some parsed lean4export items.
    """
    return EnvironmentBuilder().consume(items)


def from_str(text):
    """
    Load an environment out of a lean4export-formatted string.
    """
    return from_items(parser.from_str(text))


class Tracer(object):
    """
    No-op tracer.
    """

    def __init__(self, stream):
        self._stream = stream
        self._depth = 0

    def enter(self, expr1, expr2, declarations):
        """Called when entering a def_eq comparison."""

    def result(self, value):
        """Called when leaving a def_eq comparison. Returns the value."""
        return value


class StreamTracer(Tracer):
    """
    Tracer that writes indented def_eq comparisons to a stream.
    """

    def enter(self, expr1, expr2, declarations):
        pretty1 = expr1.pretty(declarations)
        pretty2 = expr2.pretty(declarations)
        indent = "  " * self._depth
        self._stream.write(
            "%sdef_eq %s =?= %s\n" % (indent, pretty1, pretty2),
        )
        self._depth += 1

    def result(self, value):
        self._depth -= 1
        indent = "  " * self._depth
        self._stream.write("%s=> %s\n" % (indent, value))
        return value


class Environment(object):
    """
    A Lean environment with its declarations.
    """

    def __init__(self, declarations, tracer=Tracer(None)):
        self.declarations = declarations
        self.tracer = tracer
        self.heartbeat = 0
        self.max_heartbeat = 0
        self._current_decl = None

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

    def type_check(self, declarations=None, verbose="", progress=None):
        """
        Type check each declaration in the environment.
        """
        if declarations is None:
            for each in self.declarations.itervalues():
                if verbose:
                    progress.write("  %s\n" % each.name.str())
                error = self._check_one(each)
                if error is not None:
                    yield error
        else:
            for each in declarations:
                if verbose:
                    progress.write("  %s\n" % each.name.str())
                error = self._check_one(each)
                if error is not None:
                    yield error

    def _check_one(self, each):
        self.heartbeat = 0
        self._current_decl = each
        try:
            return each.type_check(self)
        except HeartbeatExceeded as err:
            return W_HeartbeatError(
                each.name,
                err.heartbeats,
                err.max_heartbeat,
            )
        except Exception:
            if not we_are_translated():
                print_exc(None, stderr)
                stderr.write("\nwhile checking:\n\n")
                self.print(each, stderr)
                pdb.post_mortem()
            raise

    def filter_declarations(self, substring):
        """
        Yield declarations whose name contains the given substring.
        """
        for decl in self.declarations.itervalues():
            if substring in decl.name.str():
                yield decl

    def dump_pretty(self, stdout):
        """
        Dump the contents of this environment to the given stream.
        """
        for decl in self.declarations.itervalues():
            if not decl.is_private:
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

        max_heartbeat = self.max_heartbeat
        if max_heartbeat > 0:
            self.heartbeat += 1
            if self.heartbeat > max_heartbeat:
                raise HeartbeatExceeded(
                    self._current_decl,
                    self.heartbeat,
                    max_heartbeat,
                )

        tracer = self.tracer
        tracer.enter(expr1, expr2, self.declarations)

        # First reduce both to WHNF to ensure heads are in canonical form
        expr1 = expr1.whnf(self)
        expr2 = expr2.whnf(self)

        # Promote the classes so the JIT can specialize on expression types.
        # This is critical for the type dispatch below - it allows the JIT
        # to compile specialized traces for common type combinations.
        cls1 = promote(expr1.__class__)
        cls2 = promote(expr2.__class__)

        if cls1 is cls2 and (
            # returning NotImplemented (from W_Const.def_eq)
            # isn't valid RPython, and the point is these are not comparable
            # until they're reduced...
            # Still would love to think of a better way.
            cls1 is not W_Const or expr1.name.syntactic_eq(expr2.name)
        ):
            result = expr1.def_eq(expr2, self.def_eq)
            return tracer.result(result)

        # Proof irrelevance check: Get the types of our expressions
        expr1_ty = expr1.infer(self)
        expr2_ty = expr2.infer(self)
        # If these types are themselves Prop (Sort 0), and the types are equal, then our original expressions are proofs of the same `Prop`
        expr1_ty_kind = expr1_ty.infer(self)
        expr2_ty_kind = expr2_ty.infer(self)
        if syntactic_eq(expr1_ty_kind, PROP) and syntactic_eq(expr2_ty_kind, PROP):
            if self.def_eq(expr1_ty, expr2_ty):
                return tracer.result(True)

        # Only perform this check after we've already tried reduction,
        # since this check can get fail in cases like '((fvar 1) x)' ((fun y => ((fvar 1) x)) z)

        expr2_eta = self.try_eta_expand(expr1, expr2)
        if expr2_eta is not None:
            result = self.def_eq(expr1, expr2_eta)
            return tracer.result(result)
        expr1_eta = self.try_eta_expand(expr2, expr1)
        if expr1_eta is not None:
            result = self.def_eq(expr1_eta, expr2)
            return tracer.result(result)

        # Structure eta: S.mk (S.p₁ x) ... (S.pₙ x) =?= x
        if self.try_struct_eta(expr1, expr2):
            return tracer.result(True)
        if self.try_struct_eta(expr2, expr1):
            return tracer.result(True)

        # As the *very* last step, try converting NatLit exprs
        # In order to be able to type check things like 'UInt32.size',
        # we need to try everything else before actually calling 'build_nat_expr'
        # (so that checks like syntactic equality can succeed and prevent us from
        # building up ~4 billion `Nat` expressions)
        if cls1 is W_LitNat:
            result = self.def_eq(expr1.build_nat_expr(), expr2)
            return tracer.result(result)
        elif isinstance(expr2, W_LitNat):
            result = self.def_eq(expr1, expr2.build_nat_expr())
            return tracer.result(result)

        if cls1 is W_LitStr:
            result = self.def_eq(expr1.build_str_expr(self), expr2)
            return tracer.result(result)
        elif isinstance(expr2, W_LitStr):
            result = self.def_eq(expr1, expr2.build_str_expr(self))
            return tracer.result(result)

        return tracer.result(False)

    def try_eta_expand(self, expr1, expr2):
        if isinstance(expr1, W_Lambda):
            expr2_ty = expr2.infer(self).whnf(self)
            if isinstance(expr2_ty, W_ForAll):
                # print("Eta-expanding %s" % expr2.pretty())
                # Turn 'f' into 'fun x => f x'
                return fun(expr2_ty.binder)(
                    expr2.incr_free_bvars(1, 0).app(W_BVar(0)),
                )
        return None

    def try_struct_eta(self, ctor_side, other_side):
        """
        Structure eta: S.mk (S.p₁ x) ... (S.pₙ x) =?= x

        If ctor_side is a fully applied constructor of a structure type,
        and the types match, compare each field of the constructor
        application with the corresponding projection of other_side.
        """
        # Decompose ctor_side into head + args
        head = ctor_side
        args = []
        while isinstance(head, W_App):
            args.append(head.arg)
            head = head.fn

        if not isinstance(head, W_Const):
            return False

        # Check if head is a constructor
        ctor_decl = get_decl(self.declarations, head.name)
        if not isinstance(ctor_decl.w_kind, W_Constructor):
            return False

        num_params = ctor_decl.w_kind.num_params
        num_fields = ctor_decl.w_kind.num_fields

        # Must be fully applied
        if len(args) != num_params + num_fields:
            return False

        # Look up the inductive type to check it qualifies as a struct
        # The constructor's type should end in an application of the
        # inductive type, and the inductive must have exactly 1 constructor
        # and no indices.
        ctor_type = ctor_decl.type
        while isinstance(ctor_type, W_ForAll):
            ctor_type = ctor_type.body
        # ctor_type should now be the result type, e.g. "Wrap" or "ULift α"
        result_head = ctor_type
        while isinstance(result_head, W_App):
            result_head = result_head.fn
        if not isinstance(result_head, W_Const):
            return False

        struct_name = result_head.name
        inductive_decl = get_decl(self.declarations, struct_name)
        if not isinstance(inductive_decl.w_kind, W_Inductive):
            return False

        ind = inductive_decl.w_kind
        # Must be a struct: exactly 1 constructor, no indices,
        # and not recursive (matching Lean's is_structure_like).
        if len(ind.constructors) != 1:
            return False
        if ind.num_indices != 0:
            return False
        if ind.is_recursive:
            return False

        # Check that inferred types are def-eq
        ctor_ty = ctor_side.infer(self)
        other_ty = other_side.infer(self)
        if not self.def_eq(ctor_ty, other_ty):
            return False

        # Compare each field: Proj(i, other_side) =?= args[num_params + i]
        args.reverse()
        i = 0
        while i < num_fields:
            proj = W_Proj(struct_name, i, other_side)
            if not self.def_eq(proj, args[num_params + i]):
                return False
            i += 1

        return True

    def infer_sort_of(self, expr):
        expr_type = expr.infer(self).whnf(self)
        if isinstance(expr_type, W_Sort):
            return expr_type.level
        raise RuntimeError("Expected Sort, got %s" % expr_type)


#: The empty environment.
Environment.EMPTY = Environment.having([])
