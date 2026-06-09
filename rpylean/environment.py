from __future__ import print_function

from sys import stderr
from time import clock
from traceback import print_exc
import pdb

from rpython.rlib import rgc
from rpython.rlib.jit import JitDriver, promote
from rpython.rlib.objectmodel import (
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
    WallTimeExceeded,
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
    W_FunBase,
    W_HeartbeatError,
    W_WallTimeError,
    W_Inductive,
    W_Lambda,
    W_LitNat,
    W_LitStr,
    W_Proj,
    W_Sort,
    _BOOL_TRUE,
    _is_nat_zero_const,
    _mk_w_bvar,
    _nat_succ_pred,
    fun,
    get_decl,
    name_dict,
    syntactic_eq,
)


_OFFSET_UNDEF = 0
_OFFSET_TRUE = 1
_OFFSET_FALSE = 2


def _def_eq_printable_location(expr1_class):
    """
    Label `def_eq` traces by the left head class. We don't include
    `expr2.__class__` because WHNF tends to canonicalise both heads
    into the same class on hot paths — adding it as a second green
    multiplied the specialisation space ~10× without proportionate
    payback on init-prelude (bridges went 90 → 133 vs the no-driver
    baseline).
    """
    return "def_eq: %s" % expr1_class.__name__


# JIT driver covering the structural-dispatch core of def_eq. Merge
# point lives at the top of `_def_eq_core` (after closure-peeling),
# so the green sees the post-WHNF post-force left head — the same
# class `_def_eq_core` dispatches on. `is_recursive=True` because the
# core recurses into `def_eq` for sub-checks, and each recursive entry
# hits this same merge point with its own green key.
def_eq_jitdriver = JitDriver(
    greens=["expr1_class"],
    reds=["expr1", "expr2", "env"],
    name="def_eq",
    get_printable_location=_def_eq_printable_location,
    is_recursive=True,
)


class EnvironmentBuilder(object):
    """
    A mutable environment builder.

    Incrementally builds up an environment as we parse an export file.
    """

    _attrs_ = ['levels', 'exprs', 'names', 'declarations', 'env']

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

    _attrs_ = []

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

    Override any hook to observe the reduction loop. The bodies here
    are intentionally empty so RPython inlines them away on the default
    path; hot call sites in `objects.py` invoke these unconditionally
    on `env.tracer` rather than gating on the tracer's identity.
    """

    _attrs_ = ['_writer', '_depth']

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

    def whnf_cache_hit(self):
        """Called when a `W_App.whnf` call returns its inline cache hit."""

    def whnf_cache_miss(self):
        """Called when a `W_App.whnf` call has to compute a fresh result."""

    def iota(self, recursor_name):
        """Called when a recursor's iota rule fires on a constructor.

        ``recursor_name`` is the recursor's ``Name`` (e.g. `Nat.rec`).
        """

    def beta(self):
        """Called when a beta-redex `(fun ... ↦ ...) arg` is reduced."""

    def delta(self, const_name):
        """Called when a constant `c` is delta-unfolded to its definition."""

    def nat_reduce(self, op_name):
        """Called when the native nat reducer fires on a binary op.

        ``op_name`` is the kernel-op ``Name`` (e.g. `Nat.add`).
        """

    def print_summary(self, writer):
        """Called by the progress signal handler (and end-of-run with
        ``--stats``) to dump whatever rolling counters the tracer holds.
        No-op by default; `StreamTracer` overrides to dump iota / beta /
        delta / whnf-cache counts.
        """


class StreamTracer(Tracer):
    """
    Tracer that counts everything and (when ``writer`` is non-None) writes
    indented def_eq comparisons to that stream.

    Pass ``writer=None`` to suppress stream output and just collect stats.
    The counters are always live so callers can read them out via
    `print_summary` at the end of a run.
    """

    _attrs_ = [
        '_pending_newline',
        'def_eq_count', 'whnf_step_count', 'beta_count',
        'whnf_cache_hit_count', 'whnf_cache_miss_count',
        'iota_by_name', 'delta_by_name', 'nat_reduce_by_name',
    ]

    def __init__(self, writer):
        self._writer = writer
        self._depth = 0
        self._pending_newline = False
        self.def_eq_count = 0
        self.whnf_step_count = 0
        self.beta_count = 0
        self.whnf_cache_hit_count = 0
        self.whnf_cache_miss_count = 0
        self.iota_by_name = name_dict()
        self.delta_by_name = name_dict()
        self.nat_reduce_by_name = name_dict()

    def _flush_pending(self):
        if self._pending_newline:
            self._writer.write_plain("\n")
            self._pending_newline = False

    def enter(self, expr1, expr2, declarations):
        self.def_eq_count += 1
        if self._writer is None:
            return
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
        if self._writer is None:
            return value
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
        self.whnf_step_count += 1
        if self._writer is None:
            return
        self._flush_pending()
        indent = "  " * self._depth
        self._writer.write_plain(indent)
        self._writer.write([TRACE.emit("whnf")])
        self._writer.write_plain(" ")
        self._writer.write(expr.tokens(declarations))
        self._writer.write_plain("\n")

    def whnf_cache_hit(self):
        self.whnf_cache_hit_count += 1

    def whnf_cache_miss(self):
        self.whnf_cache_miss_count += 1

    def iota(self, recursor_name):
        self.iota_by_name[recursor_name] = (
            self.iota_by_name.get(recursor_name, 0) + 1
        )

    def beta(self):
        self.beta_count += 1

    def delta(self, const_name):
        self.delta_by_name[const_name] = (
            self.delta_by_name.get(const_name, 0) + 1
        )

    def nat_reduce(self, op_name):
        self.nat_reduce_by_name[op_name] = (
            self.nat_reduce_by_name.get(op_name, 0) + 1
        )

    def print_summary(self, writer):
        """Write a human-readable summary of collected counts to ``writer``.

        ``writer`` is a `TokenWriter` (uses `write_plain`).
        """
        writer.write_plain("\n--- tracer stats ---\n")
        writer.write_plain("def_eq calls:   %d\n" % self.def_eq_count)
        writer.write_plain("whnf steps:     %d\n" % self.whnf_step_count)
        writer.write_plain("whnf calls (cache hit): %d\n"
                           % self.whnf_cache_hit_count)
        writer.write_plain("whnf calls (cache miss): %d\n"
                           % self.whnf_cache_miss_count)
        writer.write_plain("beta reductions: %d\n" % self.beta_count)
        _write_by_name(writer, "iota fires", self.iota_by_name)
        _write_by_name(writer, "delta unfolds", self.delta_by_name)
        _write_by_name(writer, "native nat reductions", self.nat_reduce_by_name)


def _write_by_name(writer, label, counts):
    # Dump unsorted (matching `--slower-than`'s output style) so callers
    # can pipe through `sort -k1 -rn` if they want a ranked summary —
    # avoids needing an RPython-friendly sort key here.
    if not counts:
        writer.write_plain("%s: 0\n" % label)
        return
    total = 0
    for name, count in counts.iteritems():
        total += count
    writer.write_plain("%s: %d total\n" % (label, total))
    for name, count in counts.iteritems():
        writer.write_plain("  %d\t%s\n" % (count, name.str()))


class TypeChecker(object):
    """
    Per-declaration type-checking context.

    Created by `Environment.type_check_one` at the start of each decl
    check and discarded when the check returns. Owns the per-decl
    mutable state — the heartbeat counter, and `def_eq` / `infer` /
    associated reduction helpers which all read it. Persistent
    run-config (declarations, tracer, max_heartbeat, count_heartbeats)
    is reached via `self.env`.
    """

    _attrs_ = [
        'env', 'decl', 'heartbeat',
        'declarations', 'tracer',
        'max_heartbeat', 'count_heartbeats',
        'max_wall_time', 'start_time', '_whnf_tick',
        '_intern_w_app', '_intern_w_proj',
    ]
    # `declarations` etc. are mirrored from the env at construction so
    # per-class methods (`W_*.infer` / `.whnf` / etc.) that read
    # `env.declarations` / `env.tracer` / `env.def_eq` / `env.infer`
    # continue to work when handed a `TypeChecker` — those fields are
    # quasi-immutable on `Environment`, so the snapshot is stable for
    # the lifetime of the TC.
    _immutable_fields_ = [
        'env', 'decl',
        'declarations',
        'tracer?', 'max_heartbeat?', 'count_heartbeats?',
        'max_wall_time?', 'start_time',
    ]

    # Safety cap on the unfold-and-retry loop in `_try_lazy_delta`.
    # `expr.whnf` is idempotent (cached on the instance), so each side
    # makes at most one step of progress and the loop bottoms out in a
    # handful of iterations regardless; the cap is just to rule out
    # runaway behaviour on pathological inputs.
    _LAZY_DELTA_MAX_ITER = 32

    # Mask for the wall-time sampling in `def_eq`. We only read `clock()`
    # every 1024th heartbeat to keep the per-call cost negligible —
    # `clock()` is ~20-50ns but a 5% throttle on def_eq matters.
    _WALL_TIME_SAMPLE_MASK = 1023

    def __init__(self, env, decl):
        self.env = env
        self.decl = decl
        self.heartbeat = 0
        self.declarations = env.declarations
        self.tracer = env.tracer
        self.max_heartbeat = env.max_heartbeat
        self.count_heartbeats = env.count_heartbeats
        self.max_wall_time = env.max_wall_time
        self.start_time = clock()
        self._whnf_tick = 0
        # Per-decl arenas for reduction-produced W_App / W_Proj —
        # mirrors nanoda_lib's fresh per-decl `LeanDag` dag created
        # in `with_tc_and_declar` (util.rs:239+). Stays bounded by
        # the *distinct* sub-expressions reduction visits within this
        # decl; dropped when the TC goes out of scope so reduction
        # output never pollutes the persistent parse-time intern.
        self._intern_w_app = {}
        self._intern_w_proj = {}

    def tick_wall_time(self):
        """
        Increment the wall-time tick counter; every 1024th call, check
        whether `max_wall_time` has been exceeded and raise if so. Called
        from the hot WHNF loop (`whnf_with_progress`) and from `def_eq`.

        No-op when `max_wall_time` is zero (the common case), so the JIT
        can fold the check away when the limit isn't set.
        """
        max_wall_time = self.max_wall_time
        if max_wall_time <= 0.0:
            return
        self._whnf_tick += 1
        if (self._whnf_tick & self._WALL_TIME_SAMPLE_MASK) != 0:
            return
        elapsed = clock() - self.start_time
        if elapsed > max_wall_time:
            raise WallTimeExceeded(
                self.decl, elapsed, max_wall_time,
            )

    # ---- public def_eq / infer entry points ----------------------------

    def def_eq(self, expr1, expr2):
        """
        Check if two expressions are definitionally equal.
        """
        env = self.env
        max_heartbeat = env.max_heartbeat
        if max_heartbeat > 0 or env.count_heartbeats:
            self.heartbeat += 1
            if max_heartbeat > 0 and self.heartbeat > max_heartbeat:
                raise HeartbeatExceeded(
                    self.decl,
                    self.heartbeat,
                    max_heartbeat,
                )
        self.tick_wall_time()

        tracer = env.tracer
        tracer.enter(expr1, expr2, env.declarations)

        # Pointer-equality fast path before WHNF: shared subexpressions
        # are very common in proof terms (the DAG that lean4export
        # produces is heavily shared), so WHNFing the same instance
        # twice just to discover it's equal to itself wastes work.
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

        # Nat-offset: short-circuit `Nat.zero =?= Nat.zero` and
        # `Nat.succ a =?= Nat.succ b` (and the `W_LitNat` analogues)
        # without WHNF. Mirrors lean4's `is_def_eq_offset`
        # (type_checker.cpp:961), called from `lazy_delta_reduction`
        # at line 975. Recurses on the predecessors; `_OFFSET_FALSE`
        # bypasses the fallthrough so a structurally-unequal Nat-succ
        # spine doesn't get re-explored via WHNF + `_def_eq_core`.
        offset = self._def_eq_offset(expr1, expr2)
        if offset == _OFFSET_TRUE:
            return tracer.result(True)
        if offset == _OFFSET_FALSE:
            return tracer.result(False)

        # `decide`-tactic shortcut: when one side is the constant
        # `Bool.true`, WHNF only the other and check it reduces there
        # too. Mirrors lean4's `is_def_eq_core` (type_checker.cpp:1062)
        # and nanoda_lib (tc.rs:935). Proofs from `decide` come out as
        # `of_eq_true (Eq.refl true) : decide p = true`, so the spot
        # we hit this is the `decide p =?= true` def_eq — short-circuits
        # away the full structural dispatch on the proof side.
        if expr2 is _BOOL_TRUE:
            if expr1.whnf(self) is _BOOL_TRUE:
                return tracer.result(True)
        elif expr1 is _BOOL_TRUE:
            if expr2.whnf(self) is _BOOL_TRUE:
                return tracer.result(True)

        # Reduce both to WHNF so heads are in canonical form.
        expr1 = expr1.whnf(self)
        expr2 = expr2.whnf(self)

        # Pointer equality after WHNF before invoking `_def_eq_core`'s
        # structural dispatch — heads collapsed by WHNF often share.
        if expr1 is expr2:
            return tracer.result(True)

        return tracer.result(self._def_eq_core(expr1, expr2))

    def infer(self, expr):
        """
        Infer the type of ``expr``.

        The hot classes (`W_App`, `W_Lambda`, `W_ForAll`, `W_Const`)
        hit a per-instance inline cache slot — DAG-shared
        subexpressions otherwise turn into O(2ⁿ) re-inference, so this
        matters even when the JIT is involved. Cold classes (`W_Let`,
        `W_Proj`, `W_Sort`, literals, vars) re-compute on each call;
        they're rare enough on hot paths that a dict-based fallback
        wasn't paying for the JIT-hostile lookups it added to the
        def_eq trace.
        """
        cls = expr.__class__
        if cls is W_App:
            assert isinstance(expr, W_App)
            if expr._infer_cache_env is self:
                return expr._infer_cache_result
            result = expr.infer(self)
            expr._infer_cache_env = self
            expr._infer_cache_result = result
            return result
        if cls is W_Lambda or cls is W_ForAll:
            assert isinstance(expr, W_FunBase)
            if expr._infer_cache_env is self:
                return expr._infer_cache_result
            result = expr.infer(self)
            expr._infer_cache_env = self
            expr._infer_cache_result = result
            return result
        if cls is W_Const:
            assert isinstance(expr, W_Const)
            if expr._infer_cache_env is self:
                return expr._infer_cache_result
            result = expr.infer(self)
            expr._infer_cache_env = self
            expr._infer_cache_result = result
            return result
        return expr.infer(self)

    # ---- inner helpers --------------------------------------------------

    def _def_eq_core(self, expr1, expr2):
        """
        Core definitional equality logic, called after WHNF reduction.
        """
        # Closures are an internal representation of deferred
        # substitution; peel any that survive WHNF here so the rest of
        # the dispatch — and the JIT driver's greens — see canonical
        # forms rather than closure wrappers.
        if isinstance(expr1, W_Closure):
            expr1 = expr1.force(self)
        if isinstance(expr2, W_Closure):
            expr2 = expr2.force(self)

        # Merge point sits at the structural-dispatch entry: heads are
        # post-WHNF and post-closure-force here, so the JIT specializes
        # on the left head's class — the same dispatch the code below
        # switches on.
        def_eq_jitdriver.jit_merge_point(
            expr1_class=expr1.__class__,
            expr1=expr1,
            expr2=expr2,
            env=self,
        )

        # The greens above already promote the classes for the JIT;
        # the explicit `promote` calls give the annotator the same
        # hint on the untranslated/non-JIT path.
        cls1 = promote(expr1.__class__)
        cls2 = promote(expr2.__class__)

        # Fast-path: syntactically identical expressions are def-eq
        # without needing to infer types or do proof-irrelevance work.
        # Critical for avoiding redundant type inference on every
        # recursive def_eq call over a large expression tree.
        if cls1 is cls2 and syntactic_eq(expr1, expr2):
            return True

        # Proof irrelevance: two proofs of the same Prop are equal.
        expr1_ty = expr1.infer(self)
        if syntactic_eq(expr1_ty.infer(self), PROP):
            expr2_ty = expr2.infer(self)
            if syntactic_eq(expr2_ty.infer(self), PROP):
                if self.def_eq(expr1_ty, expr2_ty):
                    return True

        if cls1 is cls2:
            if cls1 is W_Const:
                assert isinstance(expr1, W_Const)
                assert isinstance(expr2, W_Const)
                names_eq = expr1.name.syntactic_eq(expr2.name)
            else:
                names_eq = True
            if names_eq:
                if expr1.def_eq(expr2, self.def_eq):
                    return True
                return self.def_eq_unit(expr1, expr2)

        # Only perform this check after we've already tried reduction,
        # since this check can get fail in cases like
        # '((fvar 1) x)' ((fun y => ((fvar 1) x)) z)
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
            return self.def_eq(expr1.one_step_constructor(self), expr2)
        elif isinstance(expr2, W_LitNat):
            return self.def_eq(expr1, expr2.one_step_constructor(self))

        if cls1 is W_LitStr:
            return self.def_eq(expr1.build_str_expr(self), expr2)
        elif isinstance(expr2, W_LitStr):
            return self.def_eq(expr1, expr2.build_str_expr(self))

        return False

    def _def_eq_offset(self, expr1, expr2):
        """
        Mirrors lean4's ``is_def_eq_offset`` (type_checker.cpp:961).

        Returns:
          ``_OFFSET_TRUE``   both sides are ``Nat.zero``, or both are
                             ``Nat.succ x`` / ``Nat.succ y`` with
                             ``x``, ``y`` def-equal predecessors.
          ``_OFFSET_FALSE``  both sides are ``Nat.succ _`` but the
                             predecessors are not def-equal.
          ``_OFFSET_UNDEF``  Nat-shape doesn't apply; caller falls
                             through to its normal path.

        Two ``W_LitNat`` literals get compared by value rather than by
        peeling — peeling a 2³² literal one ``Nat.succ`` at a time
        would blow the stack, and lean4 sidesteps the same case via
        the ``Lit`` fast path in ``quick_is_def_eq``
        (type_checker.cpp:758).
        """
        if isinstance(expr1, W_LitNat) and isinstance(expr2, W_LitNat):
            if expr1.val.eq(expr2.val):
                return _OFFSET_TRUE
            return _OFFSET_FALSE
        if _is_nat_zero_const(expr1) and _is_nat_zero_const(expr2):
            return _OFFSET_TRUE
        pred1 = _nat_succ_pred(expr1)
        if pred1 is None:
            return _OFFSET_UNDEF
        pred2 = _nat_succ_pred(expr2)
        if pred2 is None:
            return _OFFSET_UNDEF
        if self.def_eq(pred1, pred2):
            return _OFFSET_TRUE
        return _OFFSET_FALSE

    def _try_lazy_delta(self, expr1, expr2):
        """
        Iterative lazy delta reduction, mirroring lean4's
        ``isDefEqLazyDelta``: walk the heads of ``expr1`` and ``expr2``
        in sync, unfolding one side at a time and short-circuiting
        whenever a same-head args check succeeds.

        Returns ``True`` iff a same-head args check passes; returns
        ``False`` to mean "can't decide here, fall through to the
        WHNF + ``_def_eq_core`` path". **Never** returns ``False``
        meaning "the expressions are unequal".

        Which side to unfold is decided by ``W_Definition.hint``:
        an abbrev (``HINT_ABBREV``) unfolds before a regular def, and
        among regulars the higher-height side unfolds first. Higher
        height means a definition layered on top of lower-height ones,
        so peeling it off pushes both sides toward a common lower-level
        form.
        """
        for _ in range(self._LAZY_DELTA_MAX_ITER):
            kind1 = self._delta_kind(expr1.head())
            kind2 = self._delta_kind(expr2.head())

            # Neither side is delta-reducible: lazy delta has nothing
            # more to offer; let the caller's WHNF + _def_eq_core path
            # handle it.
            if kind1 is None and kind2 is None:
                return False

            # Exactly one side reducible: unfold that one and retry.
            # First, if the non-delta side is a projection-headed app,
            # try WHNFing it instead — the proj may resolve cheaply via
            # struct-eta or constructor iota, avoiding an expensive
            # well-founded-recursion delta-unfold on the other side.
            # Mirrors lean4's `try_unfold_proj_app` (type_checker.cpp:868,
            # called from `lazy_delta_reduction_step` at lines 898/905).
            if kind1 is None:
                if isinstance(expr1.head(), W_Proj):
                    new_e1 = expr1.whnf(self)
                    if new_e1 is not expr1:
                        expr1 = new_e1
                        continue
                new_e2 = expr2.whnf(self)
                if new_e2 is expr2:
                    return False
                expr2 = new_e2
                continue
            if kind2 is None:
                if isinstance(expr2.head(), W_Proj):
                    new_e2 = expr2.whnf(self)
                    if new_e2 is not expr2:
                        expr2 = new_e2
                        continue
                new_e1 = expr1.whnf(self)
                if new_e1 is expr1:
                    return False
                expr1 = new_e1
                continue

            # Both delta-reducible. Pick which side to unfold.
            hint1 = kind1.hint
            hint2 = kind2.hint

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
            # the head at all.
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
            # arities/heads didn't match. Unfold both; if neither made
            # progress, bail.
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
        decl = self.env.declarations.get(head.name, None)
        if decl is None:
            return None
        kind = decl.w_kind
        if not isinstance(kind, W_Definition):
            return None
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
        decl = get_decl(self.env.declarations, head.name)
        ind = decl.w_kind
        if not isinstance(ind, W_Inductive):
            return False
        if not ind.is_non_recursive_structure():
            return False
        if ind.num_indices != 0:
            return False
        first_ctor_kind = ind.constructors[0].w_kind
        assert isinstance(first_ctor_kind, W_Constructor)
        if first_ctor_kind.num_fields != 0:
            return False
        expr2_ty = expr2.infer(self)
        return self.def_eq(expr1_ty, expr2_ty)

    def try_eta_expand(self, expr1, expr2):
        if isinstance(expr1, W_Lambda):
            expr2_ty = expr2.infer(self).whnf(self)
            if isinstance(expr2_ty, W_Closure):
                expr2_ty = expr2_ty.force(self)
            if isinstance(expr2_ty, W_ForAll):
                # Turn 'f' into 'fun x => f x'
                return fun(expr2_ty.binder)(
                    expr2.incr_free_bvars(self, 1, 0).app_in(self, _mk_w_bvar(0)),
                )
        return None

    def try_struct_eta(self, ctor_side, other_side):
        """
        Structure eta: S.mk (S.p₁ x) ... (S.pₙ x) ≟ x
        """
        head, args = ctor_side.unapp()

        if not isinstance(head, W_Const):
            return False

        ctor_decl = get_decl(self.env.declarations, head.name)
        ctor_kind = ctor_decl.w_kind
        if not isinstance(ctor_kind, W_Constructor):
            return False

        num_params = ctor_kind.num_params
        num_fields = ctor_kind.num_fields

        if len(args) != num_params + num_fields:
            return False

        ctor_ty = ctor_side.infer(self).whnf(self)
        result_head = ctor_ty.head()
        if not isinstance(result_head, W_Const):
            return False
        struct_name = result_head.name
        inductive_decl = get_decl(self.env.declarations, struct_name)
        if not isinstance(inductive_decl.w_kind, W_Inductive):
            return False
        ind = inductive_decl.w_kind
        if not ind.is_non_recursive_structure():
            return False

        if not self.def_eq(ctor_ty, other_side.infer(self)):
            return False

        args.reverse()
        i = 0
        while i < num_fields:
            proj = struct_name.proj_in(self, i, other_side)
            if not self.def_eq(proj, args[num_params + i]):
                return False
            i += 1
        return True


class CheckResult(object):
    """
    The outcome of type-checking a single declaration.

    `elapsed` is wall/CPU clock; `gc_elapsed` is the time the runtime
    spent in GC during this check (subtract for "real work" time);
    `bytes_allocated` is the cumulative bytes allocated by the runtime
    during the check (most of which are short-lived and reclaimed by GC);
    `live_memory` is the live heap size at the *end* of the check —
    a sequence of decls whose `live_memory` keeps climbing is
    permanently growing the working set, vs. churning through
    ephemeral allocations that the GC reclaims back to a stable
    plateau.
    `peak_growth` is how much this decl pushed the process-wide peak
    heap up: 0 means the decl fit within previously-seen high-water
    headroom; positive means the run needed *more* memory to clear it.
    `heartbeats` is meaningful only when the environment has heartbeat
    counting enabled (via `max_heartbeat` or `count_heartbeats`); it is
    `0` otherwise.
    """

    _attrs_ = [
        'elapsed', 'gc_elapsed', 'bytes_allocated', 'live_memory',
        'peak_growth', 'heartbeats', 'error',
    ]

    def __init__(self, elapsed, gc_elapsed, bytes_allocated, live_memory,
                 peak_growth, heartbeats, error):
        self.elapsed = elapsed
        self.gc_elapsed = gc_elapsed
        self.bytes_allocated = bytes_allocated
        self.live_memory = live_memory
        self.peak_growth = peak_growth
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


def _live_memory():
    """
    Current live heap size in bytes. Returns 0 in untranslated mode.

    Unlike `_bytes_allocated` (a monotonically-increasing cumulative
    counter), this reflects what the GC has not yet reclaimed — useful
    for spotting per-decl working-set growth.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.TOTAL_MEMORY)
    return 0


def _peak_memory():
    """
    Process-wide peak heap size so far in bytes. Returns 0 in
    untranslated mode. Monotonically non-decreasing across a run — a
    *delta* across one decl tells you how much that decl raised the
    high-water mark.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.PEAK_MEMORY)
    return 0


class Environment(object):
    """
    A Lean environment with its declarations.
    """

    _attrs_ = [
        'declarations', 'tracer',
        'max_heartbeat', 'count_heartbeats',
        'max_wall_time',
        '_intern_w_app', '_intern_w_proj',
    ]
    # `declarations` is fully immutable: the reference is set in
    # `__init__` and never reassigned (the dict's *contents* are
    # mutated as decls are parsed, but the reference isn't).
    # `tracer` / `max_heartbeat` / `count_heartbeats` / `max_wall_time`
    # change only at run-setup time (CLI options) or at REPL command
    # boundaries — never inside the check loop — so quasi-immutable
    # (`?`) lets the JIT compile assuming they're constant and
    # invalidate only on the rare reassignment.
    _immutable_fields_ = [
        'declarations',
        'tracer?',
        'max_heartbeat?',
        'count_heartbeats?',
        'max_wall_time?',
    ]

    def __init__(self, declarations, tracer=Tracer(None)):
        self.declarations = declarations
        self.tracer = tracer
        self.max_heartbeat = 0
        self.count_heartbeats = False
        self.max_wall_time = 0.0
        # `None` is the sentinel routing `_mk_app_in` / `_mk_w_proj_in`
        # back to the persistent intern. Same attribute name as on
        # `TypeChecker` so the duck-typed dispatch works without
        # isinstance checks.
        self._intern_w_app = None
        self._intern_w_proj = None

    def tick_wall_time(self):
        """No-op: wall-time tracking is a per-decl `TypeChecker` concern;
        bare `Environment` (REPL / tests / cold paths) never enforces it."""
        pass

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

    def type_check(self, declarations, printer=None):
        """
        Type check each declaration, yielding only the errors.
        """
        for each in declarations:
            result = self.type_check_one(each, printer=printer)
            if result.error is not None:
                yield result.error

    def check_decl(self, decl):
        """
        Type-check a single declaration without the `CheckResult`
        bookkeeping `type_check_one` does — returns the `W_Error` (or
        ``None`` on success) directly. Convenience for tests and
        scripts that want a one-shot check; production paths should
        use `type_check_one`.
        """
        return decl.type_check(TypeChecker(self, decl))

    def type_check_one(self, decl, printer=None):
        """
        Type check a single declaration, returning a `CheckResult`.
        """
        if printer is not None:
            printer.before(self, decl)

        tc = TypeChecker(self, decl)
        error = None
        gc_start = _gc_time_seconds()
        bytes_start = _bytes_allocated()
        peak_start = _peak_memory()
        start = clock()
        try:
            error = decl.type_check(tc)
        except HeartbeatExceeded as err:
            error = W_HeartbeatError(
                decl.name,
                err.heartbeats,
                err.max_heartbeat,
            )
        except WallTimeExceeded as err:
            error = W_WallTimeError(
                decl.name,
                err.elapsed,
                err.max_wall_time,
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
        live_memory = _live_memory()
        peak_growth = _peak_memory() - peak_start
        result = CheckResult(
            elapsed, gc_elapsed, bytes_allocated, live_memory,
            peak_growth, tc.heartbeat, error,
        )
        if printer is not None:
            printer.after(self, decl, result)
        return result

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
        Definitional equality, with a transient `TypeChecker`.

        Each call gets its own `TypeChecker(self, None)`; heartbeat
        counting won't accumulate across calls. Tests and REPL paths
        that just need a single comparison use this. Production paths
        (type_check_one) construct one TC and call `tc.def_eq` directly
        so heartbeat and any per-decl caches are properly scoped.
        """
        return TypeChecker(self, None).def_eq(expr1, expr2)

    def infer(self, expr):
        """
        Type inference, with a transient `TypeChecker`. See `def_eq`.
        """
        return TypeChecker(self, None).infer(expr)



#: The empty environment.
Environment.EMPTY = Environment.having([])


class _Declarations(object):
    _attrs_ = []

    def __iter__(self):
        return self

    def public(self):
        return _PublicDeclarations(self)


class _AllDeclarations(_Declarations):
    _attrs_ = ['declarations', 'iter']

    def __init__(self, declarations):
        self.declarations = declarations
        self.iter = iter(self.declarations.itervalues())

    def next(self):
        return next(self.iter)


class _MatchingDeclarations(_Declarations):
    _attrs_ = ['declarations', 'substring', 'iter']

    def __init__(self, declarations, substring):
        self.declarations = declarations
        self.substring = substring
        self.iter = iter(self.declarations.itervalues())

    def next(self):
        for decl in self.iter:
            if self.substring in decl.name.str():
                return decl


class _NamedDeclarations(_Declarations):
    _attrs_ = ['declarations', 'names', 'iter']

    def __init__(self, declarations, names):
        self.declarations = declarations
        self.names = names
        self.iter = iter(self.names)

    def next(self):
        name = next(self.iter)
        assert name in self.declarations, name.str()
        return self.declarations[name]


class _PublicDeclarations(_Declarations):
    _attrs_ = ['iter']

    def __init__(self, iterator):
        self.iter = iterator

    def next(self):
        for declaration in self.iter:
            if declaration.name.is_private:
                continue
            return declaration
