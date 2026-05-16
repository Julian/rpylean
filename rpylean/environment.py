from __future__ import print_function

from sys import stderr
from time import clock
from traceback import print_exc
import pdb

from rpython.rlib import rgc
from rpython.rlib.jit import promote
from rpython.rlib.objectmodel import (
    compute_identity_hash,
    not_rpython,
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
    HINT_ABBREV,
    W_CheckError,
    W_LEVEL_ZERO,
    PROP,
    Name,
    StrName,
    W_App,
    W_BVar,
    W_Closure,
    W_Const,
    W_Constructor,
    W_Definition,
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
    name_dict,
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
        self.env = Environment(declarations=name_dict())

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

    def consume(self, stream, hook=None):
        """
        Parse NDJSON lines from ``stream`` directly into this builder.

        If ``hook`` is given, its ``on_declaration`` is invoked for each
        declaration as it is registered, with the partially-built environment
        available at ``self.env`` for streaming type-checking. Returning a
        truthy value from ``on_declaration`` aborts the loop early.

        Returns self.
        """
        if hook is None:
            while True:
                line = stream.readline()
                if not line:
                    return self
                parser.parse_line(line, self)

        n = 0
        while True:
            line = stream.readline()
            if not line:
                return self
            parser.parse_line(line, self)
            while n < len(self.declarations):
                if hook.on_declaration(self.declarations[n]):
                    return self
                n += 1

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

    def register_quotient(self, name, type, levels, kind):
        # Allowed: Quot, Quot.mk, Quot.ind, Quot.lift (all `Name.str` chains
        # rooted at the anonymous name).
        if not isinstance(name, StrName):
            raise UnknownQuotient(name, type)
        parent = name.parent
        if parent.is_anonymous():
            if name.suffix != "Quot":
                raise UnknownQuotient(name, type)
        elif (
            isinstance(parent, StrName)
            and parent.parent.is_anonymous()
            and parent.suffix == "Quot"
            and name.suffix in ("mk", "ind", "lift")
        ):
            pass
        else:
            raise UnknownQuotient(name, type)
        self.register_declaration(
            name.quotient(type=type, kind=kind, levels=levels),
        )

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
    parser.validate_export_metadata(export)
    return EnvironmentBuilder().consume(export).finish()


def from_str(text):
    """
    Load an environment out of a lean4export-formatted string.
    """
    return parser.from_str(text)


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


class CheckResult(object):
    """
    The outcome of type-checking a single declaration.

    `elapsed` is wall/CPU clock; `gc_elapsed` is the time the runtime
    spent in GC during this check (subtract for "real work" time);
    `bytes_allocated` is the cumulative bytes allocated by the runtime
    during the check (most of which are short-lived and reclaimed by GC).
    `heartbeats` is meaningful only when the environment has heartbeat
    counting enabled (via `max_heartbeat` or `count_heartbeats`); it is
    `0` otherwise.
    """

    def __init__(self, elapsed, gc_elapsed, bytes_allocated, heartbeats,
                 error):
        self.elapsed = elapsed
        self.gc_elapsed = gc_elapsed
        self.bytes_allocated = bytes_allocated
        self.heartbeats = heartbeats
        self.error = error


def _gc_time_seconds():
    """
    Total GC time so far in seconds. Returns 0.0 in untranslated mode
    where `rgc.get_stats` is unavailable.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.TOTAL_GC_TIME) * 0.001
    return 0.0


def _bytes_allocated():
    """
    Cumulative bytes allocated so far. Returns 0 in untranslated mode.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.TOTAL_ALLOCATED_MEMORY)
    return 0


class Environment(object):
    """
    A Lean environment with its declarations.
    """

    def __init__(self, declarations, tracer=Tracer(None)):
        self.declarations = declarations
        self.tracer = tracer
        self.heartbeat = 0
        self.max_heartbeat = 0
        self.count_heartbeats = False
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
        # Recursive types and W_Const use a per-instance inline cache slot.
        # W_Const references are heavily DAG-shared (every use of e.g.
        # ``Nat.add`` resolves to the same instance) so caching on identity
        # acts as a per-name cache and avoids the dict / hash / list-walk
        # overhead of the generic cache below.
        cls = expr.__class__
        if (cls is W_App or cls is W_Lambda or cls is W_ForAll
                or cls is W_Const):
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
        by_name = name_dict()
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
        Type check each declaration, yielding only the errors.
        """
        for each in declarations:
            result = self.type_check_one(each, pp=pp)
            if result.error is not None:
                yield result.error

    def type_check_one(self, decl, pp=None):
        """
        Type check a single declaration, returning a `CheckResult`.
        """
        if pp is not None:
            pp(self, decl)

        # FIXME: Better state encapsulation for heartbeats...
        self.heartbeat = 0
        self._current_decl = decl
        self._def_eq_cache = {}
        self._infer_cache = {}
        error = None
        gc_start = _gc_time_seconds()
        bytes_start = _bytes_allocated()
        start = clock()
        try:
            error = decl.type_check(self)
        except HeartbeatExceeded as err:
            error = W_HeartbeatError(
                decl.name,
                err.heartbeats,
                err.max_heartbeat,
            )
        except W_CheckError as err:
            if err.name is None:
                err.name = decl.name
            error = err
        except W_Error as err:
            error = W_InvalidDeclaration(decl, err, self.declarations)
        except Exception:
            if not we_are_translated():
                print_exc(None, stderr)
                stderr.write("\nwhile checking ")
                stderr.write(decl.name.str())
                stderr.write("\n\n")
                pdb.post_mortem()
            raise
        elapsed = clock() - start
        gc_elapsed = _gc_time_seconds() - gc_start
        bytes_allocated = _bytes_allocated() - bytes_start
        return CheckResult(
            elapsed, gc_elapsed, bytes_allocated, self.heartbeat, error,
        )

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
        if max_heartbeat > 0 or self.count_heartbeats:
            self.heartbeat += 1
            if max_heartbeat > 0 and self.heartbeat > max_heartbeat:
                raise HeartbeatExceeded(
                    self._current_decl,
                    self.heartbeat,
                    max_heartbeat,
                )

        tracer = self.tracer
        tracer.enter(expr1, expr2, self.declarations)

        # Pointer-equality fast path before WHNF: shared subexpressions
        # are very common in proof terms (the DAG that lean4export
        # produces is heavily shared), and WHNFing the same instance
        # twice just to discover it's equal to itself wastes work and
        # — more importantly — bloats the def_eq cache with redundant
        # entries that slow down subsequent lookups.
        if expr1 is expr2:
            return tracer.result(True)

        # Structural-equality fast path before WHNF: catches DAG
        # fragments that are equal but live in distinct instances —
        # e.g. things produced by reduction rather than parsed. The
        # walk piggy-backs on identity at each level (see
        # `syntactic_eq`) so it remains cheap for shared subtrees.
        if syntactic_eq(expr1, expr2):
            return tracer.result(True)

        # Lazy delta reduction: when both sides are application spines
        # headed by the same delta-reducible constant, compare args
        # *before* unfolding either head. Mirrors lean4's
        # `isDefEqLazyDelta`. Crucial for proof terms in the
        # `String.Decode` / BitVec / UIntN family, whose bodies are
        # long `congr (congrArg f h) (ite_congr ...)` chains: the
        # spines line up structurally so we should never delta-reduce
        # through `instHMod → UInt32.mod → BitVec.umod → Fin.mod`
        # just to compare two identical arg subtrees.
        if self._try_lazy_delta(expr1, expr2):
            return tracer.result(True)

        # Pre-WHNF cache lookup. Same `_def_eq_cache` as the post-WHNF
        # path below; entries are keyed by identity of *whatever pair
        # of instances was passed to def_eq*, so a hit here lets us
        # skip both WHNFs and `_def_eq_core` for a pair we've already
        # decided on this decl.
        pre_key = compute_identity_hash(expr1) * 1000003 ^ compute_identity_hash(
            expr2
        )
        pre_entries = self._def_eq_cache.get(pre_key, None)
        if pre_entries is not None:
            i = 0
            while i < len(pre_entries):
                entry = pre_entries[i]
                if entry.expr1 is expr1 and entry.expr2 is expr2:
                    return tracer.result(entry.result)
                i += 1

        # First reduce both to WHNF to ensure heads are in canonical form
        pre_expr1 = expr1
        pre_expr2 = expr2
        expr1 = expr1.whnf(self)
        expr2 = expr2.whnf(self)

        # Same post-WHNF: pointer equality before hitting the cache or
        # invoking `_def_eq_core`'s structural dispatch.
        if expr1 is expr2:
            return tracer.result(True)

        # Check the def_eq cache (keyed by object identity after WHNF)
        post_key = compute_identity_hash(expr1) * 1000003 ^ compute_identity_hash(
            expr2
        )
        if post_key == pre_key:
            post_entries = pre_entries
        else:
            post_entries = self._def_eq_cache.get(post_key, None)
            if post_entries is not None:
                i = 0
                while i < len(post_entries):
                    entry = post_entries[i]
                    if entry.expr1 is expr1 and entry.expr2 is expr2:
                        return tracer.result(entry.result)
                    i += 1

        result = self._def_eq_core(expr1, expr2)

        # Store the result under the post-WHNF key.
        post_entry = _DefEqCacheEntry(expr1, expr2, result)
        if post_entries is not None:
            post_entries.append(post_entry)
        else:
            self._def_eq_cache[post_key] = [post_entry]

        # Also store under the pre-WHNF key when WHNF actually changed
        # at least one side (otherwise the keys / instances coincide
        # and we'd be storing the same entry twice).
        if pre_expr1 is not expr1 or pre_expr2 is not expr2:
            pre_entry = _DefEqCacheEntry(pre_expr1, pre_expr2, result)
            if pre_key == post_key:
                # Same bucket; `post_entries` is the live list we
                # just appended `post_entry` to.
                post_entries.append(pre_entry)
            elif pre_entries is not None:
                pre_entries.append(pre_entry)
            else:
                self._def_eq_cache[pre_key] = [pre_entry]

        return tracer.result(result)

    def _def_eq_core(self, expr1, expr2):
        """
        Core definitional equality logic, called after WHNF reduction.
        """
        # Closures are an internal representation of deferred substitution;
        # peel any that survive WHNF here so the rest of the dispatch
        # can compare canonical forms.
        if isinstance(expr1, W_Closure):
            expr1 = expr1.force()
        if isinstance(expr2, W_Closure):
            expr2 = expr2.force()

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
            return self.def_eq_unit(expr1, expr2)

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

        if self.def_eq_unit(expr1, expr2):
            return True

        # As the *very* last step, expose a single Nat constructor from
        # any remaining `W_LitNat`. We only peel one `Nat.succ` per
        # def-eq call: if the other side is `Nat.succ Y`, the recursive
        # def-eq descends into `(W_LitNat (val-1), Y)` and we loop only
        # as deep as the other side's actual `Nat.succ` nesting. If the
        # other side is anything else, def-eq bails immediately. This
        # keeps `UInt32.size`-sized literals (2^32) from materialising
        # ~4 billion `Nat.succ` nodes the way `build_nat_expr` did.
        if cls1 is W_LitNat:
            return self.def_eq(expr1.one_step_constructor(), expr2)
        elif isinstance(expr2, W_LitNat):
            return self.def_eq(expr1, expr2.one_step_constructor())

        if cls1 is W_LitStr:
            return self.def_eq(expr1.build_str_expr(self), expr2)
        elif isinstance(expr2, W_LitStr):
            return self.def_eq(expr1, expr2.build_str_expr(self))

        return False

    # Safety cap on the unfold-and-retry loop in `_try_lazy_delta`.
    # `expr.whnf` is idempotent (cached on the instance), so each
    # side makes at most one step of progress and the loop bottoms
    # out in a handful of iterations regardless; the cap is just to
    # rule out runaway behaviour on pathological inputs.
    _LAZY_DELTA_MAX_ITER = 32

    def _try_lazy_delta(self, expr1, expr2):
        """
        Iterative lazy delta reduction, mirroring lean4's
        ``isDefEqLazyDelta``: walk the heads of ``expr1`` and
        ``expr2`` in sync, unfolding one side at a time and
        short-circuiting whenever a same-head args check succeeds.

        Returns ``True`` iff a same-head args check passes; returns
        ``False`` to mean "can't decide here, fall through to the
        WHNF + ``_def_eq_core`` path". **Never** returns ``False``
        meaning "the expressions are unequal".

        Which side to unfold is decided by ``W_Definition.hint``:
        an abbrev (``HINT_ABBREV``) unfolds before a regular def,
        and among regulars the higher-height side unfolds first.
        Higher height means a definition layered on top of
        lower-height ones, so peeling it off pushes both sides
        toward a common lower-level form.
        """
        for _ in range(self._LAZY_DELTA_MAX_ITER):
            kind1 = self._delta_kind(expr1.head())
            kind2 = self._delta_kind(expr2.head())

            # Neither side is delta-reducible: lazy delta has nothing
            # more to offer; let the caller's WHNF + _def_eq_core
            # path handle it.
            if kind1 is None and kind2 is None:
                return False

            # Exactly one side reducible: unfold that one and retry.
            # WHNF is idempotent (cached on the instance) so a
            # second WHNF of the same instance signals "no further
            # progress possible on this side" and we bail.
            if kind1 is None:
                new_e2 = expr2.whnf(self)
                if new_e2 is expr2:
                    return False
                expr2 = new_e2
                continue
            if kind2 is None:
                new_e1 = expr1.whnf(self)
                if new_e1 is expr1:
                    return False
                expr1 = new_e1
                continue

            # Both delta-reducible. Pick which side to unfold.
            hint1 = kind1.hint
            hint2 = kind2.hint

            # Abbrevs unfold ahead of regular defs, regardless of
            # the numeric `hint` value (in our encoding abbrev is
            # -1, so straight height comparison would unfold the
            # *regular* side, which is the wrong way around).
            if hint1 == HINT_ABBREV and hint2 != HINT_ABBREV:
                new_e1 = expr1.whnf(self)
                if new_e1 is expr1:
                    return False
                expr1 = new_e1
                continue
            if hint2 == HINT_ABBREV and hint1 != HINT_ABBREV:
                new_e2 = expr2.whnf(self)
                if new_e2 is expr2:
                    return False
                expr2 = new_e2
                continue

            # Same-head args fast path. Two app spines headed by the
            # same `W_Const` (with matching levels) are def-equal iff
            # their args are pairwise def-equal — no need to unfold
            # the head at all. We only ``unapp`` here, after the
            # cheap head/hint checks have committed us to looking at
            # args, so the bail-out cases above avoid the spine-list
            # allocation.
            head1, args1 = expr1.unapp()
            head2, args2 = expr2.unapp()
            if syntactic_eq(head1, head2) and len(args1) == len(args2):
                all_eq = True
                for j in range(len(args1)):
                    if not self.def_eq(args1[j], args2[j]):
                        all_eq = False
                        break
                if all_eq:
                    return True

            # Heights differ: unfold the higher one.
            if hint1 > hint2:
                new_e1 = expr1.whnf(self)
                if new_e1 is expr1:
                    return False
                expr1 = new_e1
                continue
            if hint1 < hint2:
                new_e2 = expr2.whnf(self)
                if new_e2 is expr2:
                    return False
                expr2 = new_e2
                continue

            # Same height, and same-head args either failed or
            # arities/heads didn't match. Unfold both; if neither
            # made progress, bail.
            new_e1 = expr1.whnf(self)
            new_e2 = expr2.whnf(self)
            if new_e1 is expr1 and new_e2 is expr2:
                return False
            expr1 = new_e1
            expr2 = new_e2

        return False

    def _delta_kind(self, head):
        """Return ``head``'s ``W_Definition`` kind if ``head`` is a
        delta-reducible constant — i.e. a definition that's neither
        an opaque nor a constructor/inductive/recursor (those don't
        subclass ``W_Definition``). Returns ``None`` otherwise.
        """
        if not isinstance(head, W_Const):
            return None
        decl = self.declarations.get(head.name, None)
        if decl is None:
            return None
        kind = decl.w_kind
        if not isinstance(kind, W_Definition):
            return None
        # `W_Opaque` is a `W_Definition` subclass whose
        # `get_delta_reduce_target` returns ``None`` — rules it out.
        if kind.get_delta_reduce_target() is None:
            return None
        return kind

    def def_eq_unit(self, expr1, expr2):
        """
        Unit-like definitional equality: any two values of a
        non-recursive structure with zero indices and a zero-field
        constructor are def-eq — there are no fields to disagree on,
        so equality follows from the types matching.
        """
        expr1_ty = expr1.infer(self).whnf(self)
        head = expr1_ty.head()
        if not isinstance(head, W_Const):
            return False
        decl = get_decl(self.declarations, head.name)
        if not isinstance(decl.w_kind, W_Inductive):
            return False
        ind = decl.w_kind
        if not ind.is_non_recursive_structure():
            return False
        if ind.num_indices != 0:
            return False
        if ind.constructors[0].w_kind.num_fields != 0:
            return False
        expr2_ty = expr2.infer(self)
        return self.def_eq(expr1_ty, expr2_ty)

    def try_eta_expand(self, expr1, expr2):
        if isinstance(expr1, W_Lambda):
            expr2_ty = expr2.infer(self).whnf(self)
            # WHNF can leave a `W_Closure` at the head — force it so
            # the `isinstance(W_ForAll)` check below isn't dodged by
            # a deferred substitution. Funext's proof routes through
            # `congrArg` and stalls here without this; see
            # `arena/perf/grind-ring-5`.
            if isinstance(expr2_ty, W_Closure):
                expr2_ty = expr2_ty.force()
            if isinstance(expr2_ty, W_ForAll):
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
        if not ind.is_non_recursive_structure():
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
            if declaration.name.is_private:
                continue
            return declaration
