from __future__ import print_function

from sys import stderr
from traceback import print_exc
import pdb

from rpython.rlib.jit import promote
from rpython.rlib.objectmodel import (
    compute_identity_hash,
    not_rpython,
    r_dict,
    we_are_translated,
)

from rpylean import parser
from rpylean._tokens import TRACE, TokenWriter
from rpylean._rlib import r_dict_eq
from rpylean.exceptions import (
    AlreadyDeclared,
    DuplicateLevels,
    HeartbeatExceeded,
    IndexGapError,
    UnknownQuotient,
    W_Error,
    W_InvalidDeclaration,
)
from rpylean.objects import (
    W_CheckError,
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
    W_Sort,
    _InferCacheEntry,
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
        self.declarations = []
        self.env = Environment(declarations=r_dict(name_eq, Name.hash))

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return (
            self.levels == other.levels
            and self.exprs == other.exprs
            and self.names == other.names
            and self.declarations == other.declarations
        )

    def __ne__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return not self == other

    def __repr__(self):
        return "<EnvironmentBuilder with %s declarations>" % (len(self.declarations),)

    def consume(self, items, hook=None):
        """
        Incrementally consume some items into this builder.

        If ``hook`` is given, its ``on_declaration`` is invoked for each
        declaration as it is registered, with the partially-built environment
        available at ``self.env`` for streaming type-checking. Returning a
        truthy value from ``on_declaration`` aborts the loop early.

        Returns self.
        """
        if hook is None:
            for item in items:
                item.compile(self)
            return self

        n = 0
        for item in items:
            item.compile(self)
            while n < len(self.declarations):
                if hook.on_declaration(self.declarations[n]):
                    return self
                n += 1
        return self

    # We assume nidx, eidx and uidx are always the next index to use.
    # This seems to hold for exports we've seen, but if it ever weren't the
    # case we could just have these methods renumber the indices so they're
    # still contiguous.
    def register_name(self, nidx, name):
        if nidx != len(self.names):
            raise IndexGapError("name", len(self.names), nidx)
        self.names.append(name)

    def register_expr(self, eidx, w_expr):
        if eidx != len(self.exprs):
            raise IndexGapError("expr", len(self.exprs), eidx)
        self.exprs.append(w_expr)

    def register_level(self, uidx, level):
        if uidx != len(self.levels):
            raise IndexGapError("level", len(self.levels), uidx)
        self.levels.append(level)

    def register_quotient(self, name, type, levels):
        n = len(name.components)
        if n == 0 or n > 2 or name.components[0] != "Quot":
            raise UnknownQuotient(name, type)
        if n == 2 and name.components[1] not in ("mk", "ind", "lift"):
            raise UnknownQuotient(name, type)
        self.register_declaration(name.axiom(type=type, levels=levels))

    def register_declaration(self, decl):
        env_decls = self.env.declarations
        if decl.name in env_decls:
            raise AlreadyDeclared(decl.name, env_decls)
        if len(decl.levels) > 1:
            seen = {}
            for level in decl.levels:
                if level in seen:
                    raise DuplicateLevels(decl.name, decl.levels, level)
                seen[level] = True
        self.declarations.append(decl)
        env_decls[decl.name] = decl

    def finish(self):
        """
        Finish building, returning the live environment.
        """
        return self.env


class DeclarationHook(object):
    """
    Base class for streaming hooks invoked on each newly-registered declaration.
    """

    def on_declaration(self, decl):
        """Return a truthy value to abort the consume loop early."""
        return False


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

    def __init__(self, writer):
        self._writer = writer
        self._depth = 0

    def enter(self, expr1, expr2, declarations):
        """Called when entering a def_eq comparison."""

    def result(self, value):
        """Called when leaving a def_eq comparison. Returns the value."""
        return value

    def whnf_step(self, expr, declarations):
        """Called for each form encountered during WHNF reduction.

        Invoked once per iteration of the reduction loop, including for the
        initial expression and the final form returned as the WHNF.
        """


class StreamTracer(Tracer):
    """
    Tracer that writes indented def_eq comparisons to a stream.
    """

    def __init__(self, writer):
        self._writer = writer
        self._depth = 0
        self._pending_newline = False

    def _flush_pending(self):
        if self._pending_newline:
            self._writer.write_plain("\n")
            self._pending_newline = False

    def enter(self, expr1, expr2, declarations):
        self._flush_pending()
        indent = "  " * self._depth
        self._writer.write_plain(indent)
        self._writer.write([TRACE.emit("def_eq")])
        self._writer.write_plain(" ")
        self._writer.write(expr1.tokens(declarations))
        self._writer.write_plain(" ≟ ")
        self._writer.write(expr2.tokens(declarations))
        self._pending_newline = True
        self._depth += 1

    def result(self, value):
        self._depth -= 1
        mark = " ✓" if value else " ✗"
        if self._pending_newline:
            self._writer.write_plain(mark + "\n")
            self._pending_newline = False
        else:
            indent = "  " * self._depth
            self._writer.write_plain("%s%s\n" % (indent, mark.lstrip()))
        return value

    def whnf_step(self, expr, declarations):
        self._flush_pending()
        indent = "  " * self._depth
        self._writer.write_plain(indent)
        self._writer.write([TRACE.emit("whnf")])
        self._writer.write_plain(" ")
        self._writer.write(expr.tokens(declarations))
        self._writer.write_plain("\n")


class _DefEqCacheEntry(object):
    """
    An entry in the def_eq cache, keyed by object identity.
    """

    def __init__(self, expr1, expr2, result):
        self.expr1 = expr1
        self.expr2 = expr2
        self.result = result


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
        self._def_eq_cache = {}
        self._infer_cache = {}

    def infer(self, expr):
        """
        Infer the type of ``expr``, caching the result by identity.

        Crucial for type-checking proof terms with DAG-shared subexpressions
        (e.g. ``app-lam.ndjson``): without caching, sharing turns into O(2ⁿ)
        re-inference of the same lambda.
        """
        # Recursive types use a per-instance inline cache slot. Avoids the
        # dict / hash / list-walk overhead of the generic cache below for the
        # most-frequently-cached classes.
        cls = expr.__class__
        if cls is W_App or cls is W_Lambda or cls is W_ForAll:
            cached = expr._infer_cache_result
            if cached is not None:
                return cached
            result = expr.infer(self)
            expr._infer_cache_result = result
            return result

        key = compute_identity_hash(expr)
        entries = self._infer_cache.get(key, None)
        if entries is not None:
            i = 0
            while i < len(entries):
                entry = entries[i]
                if entry.expr is expr:
                    return entry.result
                i += 1
        result = expr.infer(self)
        new_entry = _InferCacheEntry(expr, result)
        if entries is not None:
            entries.append(new_entry)
        else:
            self._infer_cache[key] = [new_entry]
        return result

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
                raise AlreadyDeclared(each.name, by_name)

            levels = {}
            for level in each.levels:
                if level in levels:
                    raise DuplicateLevels(each.name, each.levels, level)
                levels[level] = True

            by_name[each.name] = each
        return Environment(declarations=by_name)

    def type_check(self, declarations, pp=None):
        """
        Type check each declaration in the environment.
        """
        for each in declarations:
            for err in self.type_check_one(each, pp=pp):
                yield err

    def type_check_one(self, decl, pp=None):
        """
        Type check a single declaration, yielding zero or one errors.
        """
        if pp is not None:
            pp(self, decl)

        # FIXME: Better state encapsulation for heartbeats...
        self.heartbeat = 0
        self._current_decl = decl
        self._def_eq_cache = {}
        self._infer_cache = {}
        try:
            error = decl.type_check(self)
        except HeartbeatExceeded as err:
            yield W_HeartbeatError(
                decl.name,
                err.heartbeats,
                err.max_heartbeat,
            )
        except W_CheckError as err:
            if err.name is None:
                err.name = decl.name
            yield err
        except W_Error as err:
            yield W_InvalidDeclaration(decl, err, self.declarations)
        except Exception:
            if not we_are_translated():
                print_exc(None, stderr)
                stderr.write("\nwhile checking ")
                stderr.write(decl.name.str())
                stderr.write("\n\n")
                pdb.post_mortem()
            raise
        else:
            if error is not None:
                yield error

    def all(self):
        """
        All declarations in the environment.
        """
        return _AllDeclarations(self.declarations)

    def only(self, names):
        """
        Yield declarations whose name is in the given collection.
        """
        if not names:
            return self.all()
        return _NamedDeclarations(self.declarations, names)

    def match(self, substring):
        """
        Yield declarations whose name contains the given substring.
        """
        return _MatchingDeclarations(self.declarations, substring)

    def public(self):
        """
        All public declarations in the environment.
        """
        return self.all().public()

    def def_eq(self, expr1, expr2):
        """
        Check if two expressions are definitionally equal.
        """
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

        # Check the def_eq cache (keyed by object identity after WHNF)
        cache_key = compute_identity_hash(expr1) * 1000003 ^ compute_identity_hash(
            expr2
        )
        entries = self._def_eq_cache.get(cache_key, None)
        if entries is not None:
            i = 0
            while i < len(entries):
                entry = entries[i]
                if entry.expr1 is expr1 and entry.expr2 is expr2:
                    return tracer.result(entry.result)
                i += 1

        result = self._def_eq_core(expr1, expr2)

        # Store the result in the cache
        entry = _DefEqCacheEntry(expr1, expr2, result)
        if entries is not None:
            entries.append(entry)
        else:
            self._def_eq_cache[cache_key] = [entry]

        return tracer.result(result)

    def _def_eq_core(self, expr1, expr2):
        """
        Core definitional equality logic, called after WHNF reduction.
        """
        # Promote the classes so the JIT can specialize on expression types.
        # This is critical for the type dispatch below - it allows the JIT
        # to compile specialized traces for common type combinations.
        cls1 = promote(expr1.__class__)
        cls2 = promote(expr2.__class__)

        # Fast-path: syntactically identical expressions are def-eq without
        # needing to infer types or do proof-irrelevance work. Critical for
        # avoiding redundant type inference on every recursive def_eq call
        # over a large expression tree.
        if cls1 is cls2 and syntactic_eq(expr1, expr2):
            return True

        # Proof irrelevance: two proofs of the same Prop are equal.
        expr1_ty = expr1.infer(self)
        if syntactic_eq(expr1_ty.infer(self), PROP):
            expr2_ty = expr2.infer(self)
            if syntactic_eq(expr2_ty.infer(self), PROP):
                if self.def_eq(expr1_ty, expr2_ty):
                    return True

        if cls1 is cls2 and (
            # returning NotImplemented (from W_Const.def_eq)
            # isn't valid RPython, and the point is these are not comparable
            # until they're reduced...
            # Still would love to think of a better way.
            cls1 is not W_Const or expr1.name.syntactic_eq(expr2.name)
        ):
            if expr1.def_eq(expr2, self.def_eq):
                return True
            return self.try_struct_eta_fields(expr1, expr2)

        # Only perform this check after we've already tried reduction,
        # since this check can get fail in cases like '((fvar 1) x)' ((fun y => ((fvar 1) x)) z)

        expr2_eta = self.try_eta_expand(expr1, expr2)
        if expr2_eta is not None:
            return self.def_eq(expr1, expr2_eta)
        expr1_eta = self.try_eta_expand(expr2, expr1)
        if expr1_eta is not None:
            return self.def_eq(expr1_eta, expr2)

        # Structure eta: S.mk (S.p₁ x) ... (S.pₙ x) ≟ x
        if self.try_struct_eta(expr1, expr2):
            return True
        if self.try_struct_eta(expr2, expr1):
            return True

        # As the *very* last step, try converting NatLit exprs
        # In order to be able to type check things like 'UInt32.size',
        # we need to try everything else before actually calling 'build_nat_expr'
        # (so that checks like syntactic equality can succeed and prevent us from
        # building up ~4 billion `Nat` expressions)
        if cls1 is W_LitNat:
            return self.def_eq(expr1.build_nat_expr(), expr2)
        elif isinstance(expr2, W_LitNat):
            return self.def_eq(expr1, expr2.build_nat_expr())

        if cls1 is W_LitStr:
            return self.def_eq(expr1.build_str_expr(self), expr2)
        elif isinstance(expr2, W_LitStr):
            return self.def_eq(expr1, expr2.build_str_expr(self))

        return False

    def try_struct_eta_fields(self, expr1, expr2):
        """
        Structure eta when neither side is a constructor application.

        Compares field-by-field: S.proj i expr1 ≟ S.proj i expr2.

        Only called from the same-class fallback path where the
        projection comparisons cannot cycle back here (projections
        have the field type, not the structure type).
        """
        ty = expr1.infer(self).whnf(self)
        head = ty.head()
        if not isinstance(head, W_Const):
            return False
        decl = get_decl(self.declarations, head.name)
        if not isinstance(decl.w_kind, W_Inductive):
            return False
        ind = decl.w_kind
        if len(ind.constructors) != 1 or ind.num_indices != 0 or ind.is_recursive:
            return False
        struct_name = head.name
        num_fields = ind.constructors[0].w_kind.num_fields

        if not self.def_eq(ty, expr2.infer(self).whnf(self)):
            return False

        i = 0
        while i < num_fields:
            if not self.def_eq(
                struct_name.proj(i, expr1),
                struct_name.proj(i, expr2),
            ):
                return False
            i += 1
        return True

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
        Structure eta: S.mk (S.p₁ x) ... (S.pₙ x) ≟ x

        If ctor_side is a fully applied constructor of a structure type,
        and the types match, compare each field of the constructor
        application with the corresponding projection of other_side.
        """
        # Decompose ctor_side into head + args
        head, args = ctor_side.unapp()

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

        # Check that ctor_side's type is a structure-like inductive.
        ctor_ty = ctor_side.infer(self).whnf(self)
        result_head = ctor_ty.head()
        if not isinstance(result_head, W_Const):
            return False
        struct_name = result_head.name
        inductive_decl = get_decl(self.declarations, struct_name)
        if not isinstance(inductive_decl.w_kind, W_Inductive):
            return False
        ind = inductive_decl.w_kind
        if len(ind.constructors) != 1 or ind.num_indices != 0 or ind.is_recursive:
            return False

        # Check that inferred types are def-eq
        if not self.def_eq(ctor_ty, other_side.infer(self)):
            return False

        # Compare each field: Proj(i, other_side) ≟ args[num_params + i]
        args.reverse()
        i = 0
        while i < num_fields:
            proj = struct_name.proj(i, other_side)
            if not self.def_eq(proj, args[num_params + i]):
                return False
            i += 1

        return True


#: The empty environment.
Environment.EMPTY = Environment.having([])


class _Declarations(object):
    def __iter__(self):
        return self

    def public(self):
        return _PublicDeclarations(self)


class _AllDeclarations(_Declarations):
    def __init__(self, declarations):
        self.declarations = declarations
        self.iter = iter(self.declarations.itervalues())

    def next(self):
        return next(self.iter)


class _MatchingDeclarations(_Declarations):
    def __init__(self, declarations, substring):
        self.declarations = declarations
        self.substring = substring
        self.iter = iter(self.declarations.itervalues())

    def next(self):
        for decl in self.iter:
            if self.substring in decl.name.str():
                return decl


class _NamedDeclarations(_Declarations):
    def __init__(self, declarations, names):
        self.declarations = declarations
        self.names = names
        self.iter = iter(self.names)

    def next(self):
        name = next(self.iter)
        assert name in self.declarations, name.str()
        return self.declarations[name]


class _PublicDeclarations(_Declarations):
    def __init__(self, iterator):
        self.iter = iterator

    def next(self):
        for declaration in self.iter:
            if declaration.is_private:
                continue
            return declaration
