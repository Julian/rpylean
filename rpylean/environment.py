from __future__ import print_function

from sys import stderr
from time import clock
from traceback import print_exc
import pdb

from rpython.rlib import rgc
from rpython.rlib.jit import dont_look_inside
from rpython.rlib.objectmodel import (
    not_rpython,
    specialize,
    we_are_translated,
)

from rpylean import parser
from rpylean._tokens import TRACE, TokenWriter
from rpylean._rlib import r_dict_eq
from rpylean.exceptions import (
    AlreadyDeclared,
    DuplicateLevels,
    HeartbeatExceeded,
    MemoryExceeded,
    UnknownQuotient,
    W_Error,
    W_InvalidDeclaration,
    WallTimeExceeded,
)
from rpylean.machine import Machine
from rpylean.objects import (
    W_CheckError,
    Name,
    StrName,
    W_HeartbeatError,
    W_MemoryError,
    W_NotYetDeclared,
    W_UnsafeReference,
    W_WallTimeError,
    W_Inductive,
    W_LEVEL_ZERO,
    PROP,
    fun,
    _mk_w_bvar,
    find_decl,
    get_decl,
    name_dict,
)


_OFFSET_UNDEF = 0
_OFFSET_TRUE = 1
_OFFSET_FALSE = 2

#: Fed to the reused parser during the reference-counting pre-pass wherever
#: it would otherwise splice in a real sub-expression. That pass builds
#: exprs only to discard them (it keeps just the counts), so the operand it
#: hands to each `.app()` / binder / `.proj()` is pure write-only scaffolding
#: — never stored in the pool, never compared, never read as data. It must
#: still be *some* valid `W_Expr` (you cannot call `.app()` on `None`), so a
#: loose de Bruijn `#0` is used: syntactically incomplete on its own, so it
#: reads as filler rather than a meaningful value like `PROP` would.
#:
#: This is the opposite situation to the two "this slot is dead" markers —
#: a freed pool slot and a dropped theorem value — which ARE read back and
#: so must be `None`, the one value no real expr can take (see `ref_expr`
#: and `W_Theorem.drop_checked_value`).
_SCAN_SCAFFOLD = _mk_w_bvar(0)

#: `_try_lazy_delta` outcomes: proved equal, or undecided (with both
#: sides advanced to whnf_core'd, delta-exhausted forms).
_LD_TRUE = 1
_LD_UNDEF = 0


@specialize.call_location()
def _register_at(table, idx, value, placeholder):
    n = len(table)
    if idx == n:
        table.append(value)
    elif idx < n:
        table[idx] = value
    else:
        while len(table) < idx:
            table.append(placeholder)
        table.append(value)


class EnvironmentBuilder(object):
    """
    A mutable environment builder.

    Incrementally builds up an environment as we parse an export file.
    """

    _attrs_ = [
        'levels', 'exprs', 'names', 'declarations', 'env',
        '_refcount', '_scanning', '_groups', 'ordered',
    ]

    def __init__(self, levels=None, exprs=None, names=[]):
        self.levels = [W_LEVEL_ZERO] if levels is None else levels
        self.exprs = [] if exprs is None else exprs
        self.names = [Name.ANONYMOUS] + names
        self.declarations = []
        self.env = Environment(declarations=name_dict())
        # Whether registration order is declaration order. It is for an
        # export, which lists each declaration after everything it uses;
        # it is not for declarations pulled in on demand, which arrive in
        # the order the checker happens to need them.
        self.ordered = True
        # Block name (see `W_Declaration.group_key`) -> group id, so the
        # members of a mutual block registered as separate records still
        # end up in one group.
        self._groups = name_dict()
        # Expr-pool pruning (see `ref_expr`). `_refcount` is `None` on the
        # default path (no pruning — REPL, tests, stdin); a `list[int]`
        # of parse-time reference counts when a pre-scan has run. While
        # `_scanning` is True this builder IS that counting pre-pass:
        # `ref_expr` tallies references and hands back a dummy instead of
        # a real expr, so no deep expr DAG is retained.
        self._refcount = None
        self._scanning = False

    def start_scan(self):
        """Configure this builder as the reference-counting pre-pass."""
        self._scanning = True
        self._refcount = []

    def ref_expr(self, eidx):
        """
        Resolve one parse-time reference to expression index ``eidx``.

        Every ``builder.exprs[...]`` read in the parser goes through here,
        which is what makes expr-pool pruning possible in three modes:

        * No pruning (``_refcount is None`` — REPL, tests, streamed stdin):
          just return the pooled expr.
        * Counting pre-pass (``_scanning``): tally this reference and hand
          back scaffolding. Because it is the *same* parser walking the
          *same* file, its tallies are exactly the reference counts the
          real pass will make — no separate, drift-prone scanner.
        * Real pass (counts present, not scanning): return the expr and
          decrement its count; when the last reference is consumed, drop
          the pool's hold so the sub-tree can be reclaimed once the owning
          declaration lets go too.
        """
        counts = self._refcount
        if counts is None:
            e = self.exprs[eidx]
            assert e is not None
            return e
        if self._scanning:
            counts[eidx] += 1
            return _SCAN_SCAFFOLD
        # A slot the parser still references must have a positive count and
        # a live expr. Either assertion failing means the pre-pass under-
        # counted this index and its expr was freed too early: fail loudly
        # rather than splice a released slot into a later expression.
        c = counts[eidx]
        assert c > 0
        e = self.exprs[eidx]
        assert e is not None
        c -= 1
        counts[eidx] = c
        if c == 0:
            self.exprs[eidx] = None
        return e

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

    # The export format only requires `in`/`ie`/`il` references to be integers,
    # so an index may skip values or fill a previously-skipped one even though
    # lean4export emits them densely and in order. Skipped slots are padded
    # with a same-typed placeholder (never referenced by a valid export) so the
    # tables stay homogeneous lists rather than `Optional` ones.
    def register_name(self, nidx, name):
        _register_at(self.names, nidx, name, Name.ANONYMOUS)

    def register_expr(self, eidx, w_expr):
        if self._scanning:
            # The counting pre-pass keeps only the per-slot reference
            # tally; the scaffolding-built expr itself is discarded.
            _register_at(self._refcount, eidx, 0, 0)
            return
        _register_at(self.exprs, eidx, w_expr, PROP)

    def register_level(self, uidx, level):
        _register_at(self.levels, uidx, level, W_LEVEL_ZERO)

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

    def check_name(self, name):
        """
        Lean's ``environment.check_name``: nothing may already be
        declared under ``name``.
        """
        env_decls = self.env.declarations
        if name in env_decls:
            raise AlreadyDeclared(name, env_decls)

    def register_declaration(self, decl, group=-1):
        """
        Register ``decl`` as the next declaration.

        ``group`` names the block ``decl`` belongs to when the record
        being parsed is itself the block (an inductive record with its
        constructors and recursors); otherwise the block, if any, is
        derived from the declaration.
        """
        env_decls = self.env.declarations
        if decl.name in env_decls:
            raise AlreadyDeclared(decl.name, env_decls)
        if len(decl.levels) > 1:
            seen = {}
            for level in decl.levels:
                if level in seen:
                    raise DuplicateLevels(decl.name, decl.levels, level)
                seen[level] = True
        if self.ordered:
            self._place(decl, group)
        self.declarations.append(decl)
        env_decls[decl.name] = decl

    def _place(self, decl, group):
        index = len(self.declarations)
        decl.index = index
        key = decl.group_key()
        if group < 0:
            if key is None:
                return
            group = self._groups.get(key, -1)
            if group < 0:
                group = index
        if key is not None and key not in self._groups:
            self._groups[key] = group
        decl.group = group

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

    _attrs_ = ['_writer', '_depth', 'recording', 'writes']

    def __init__(self, writer):
        self._writer = writer
        self._depth = 0
        # Whether this tracer renders terms (a stream is attached).
        # A counting-only tracer must not be handed rendered terms: the
        # machine would have to export both sides of every comparison
        # just to be counted.
        self.writes = False
        # Whether this tracer records anything. The hottest call sites
        # (arena probes, whnf steps, the def_eq prologue) fire billions
        # of times per heavy declaration; a virtual call into an empty
        # method is not free at that volume, so they gate on this flag
        # instead of relying on the empty bodies being inlined away.
        self.recording = False


    def census(self, nrecs, nleaves, inst, shift, bind, eqv, neq, failed):
        """Called as a `Machine` is freed, with the sizes its tables
        reached for that declaration."""

    def phase(self, phase):
        """Called by the `Machine` as a phase of a declaration's check
        ends; a counting tracer attributes the def_eq calls since the
        previous phase to it."""

    def begin_argcheck(self):
        """Called before an argument check, to bracket its def_eq calls."""

    def end_argcheck(self, head, index):
        """Called after the check of argument ``index`` of an application
        of ``head``, closing the bracket `begin_argcheck` opened."""

    def counted_enter(self):
        """`enter` without the terms, for a tracer that only counts."""

    def counted_result(self, result):
        """`result` without rendering, for a tracer that only counts."""
        return result

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

    def eqv_hit(self):
        """Called when def_eq resolves via the equivalence union-find."""


    def pi_hit(self):
        """Called when def_eq resolves via proof irrelevance."""

    def identity_hit(self):
        """Called when def_eq resolves via `expr1 is expr2` at entry."""


    def klike_fired(self):
        """Called when K-like reduction replaces a stuck major."""

    def klike_bail_head(self):
        """Called when K-like bails: major's type head is not a const."""

    def klike_bail_mutual(self):
        """Called when K-like bails: recursor belongs to a mutual block."""

    def klike_bail_ctors(self):
        """Called when K-like bails: inductive is not single-ctor."""

    def klike_bail_defeq(self):
        """Called when K-like bails: ctor type is not def-eq to the
        major's type."""

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
        'iota_by_name', 'delta_by_name', 'nat_reduce_by_name',
        'eqv_hit_count', 'pi_hit_count', 'false_count',
        'identity_hit_count',
        'klike_fired_count', 'klike_bail_head_count',
        'klike_bail_mutual_count', 'klike_bail_ctors_count',
        'klike_bail_defeq_count',
        'table_max', 'phases', '_phase_mark',
        'argchecks', '_arg_mark',
    ]

    def __init__(self, writer):
        self._writer = writer
        self._depth = 0
        self.recording = True
        self.writes = writer is not None
        self._pending_newline = False
        # Largest per-declaration table sizes seen: records, leaves,
        # instantiate / shift / bind memos, eqv, neq, failed.
        self.table_max = [0] * 8
        self.phases = {}
        self._phase_mark = 0
        self.argchecks = {}
        self._arg_mark = 0
        self.def_eq_count = 0
        self.whnf_step_count = 0
        self.beta_count = 0
        self.iota_by_name = name_dict()
        self.delta_by_name = name_dict()
        self.nat_reduce_by_name = name_dict()
        self.eqv_hit_count = 0
        self.pi_hit_count = 0
        self.false_count = 0
        self.identity_hit_count = 0
        self.klike_fired_count = 0
        self.klike_bail_head_count = 0
        self.klike_bail_mutual_count = 0
        self.klike_bail_ctors_count = 0
        self.klike_bail_defeq_count = 0

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

    def counted_enter(self):
        self.def_eq_count += 1

    def counted_result(self, value):
        if not value:
            self.false_count += 1
        return value

    def result(self, value):
        if not value:
            self.false_count += 1
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

    def eqv_hit(self):
        self.eqv_hit_count += 1


    def pi_hit(self):
        self.pi_hit_count += 1

    def identity_hit(self):
        self.identity_hit_count += 1


    def klike_fired(self):
        self.klike_fired_count += 1

    def klike_bail_head(self):
        self.klike_bail_head_count += 1

    def klike_bail_mutual(self):
        self.klike_bail_mutual_count += 1

    def klike_bail_ctors(self):
        self.klike_bail_ctors_count += 1

    def klike_bail_defeq(self):
        self.klike_bail_defeq_count += 1


    def census(self, nrecs, nleaves, inst, shift, bind, eqv, neq, failed):
        sizes = [nrecs, nleaves, inst, shift, bind, eqv, neq, failed]
        for i in range(8):
            if sizes[i] > self.table_max[i]:
                self.table_max[i] = sizes[i]

    def begin_argcheck(self):
        self._arg_mark = self.def_eq_count

    def end_argcheck(self, head, index):
        key = "%s #%d" % (head, index)
        self.argchecks[key] = (
            self.argchecks.get(key, 0) + self.def_eq_count - self._arg_mark
        )

    def phase(self, phase):
        calls = self.def_eq_count - self._phase_mark
        self._phase_mark = self.def_eq_count
        self.phases[phase] = self.phases.get(phase, 0) + calls


    def print_summary(self, writer):
        """Write a human-readable summary of collected counts to ``writer``.

        ``writer`` is a `TokenWriter` (uses `write_plain`).
        """
        writer.write_plain("\n--- tracer stats ---\n")
        writer.write_plain("def_eq calls:   %d\n" % self.def_eq_count)
        writer.write_plain("def_eq false:   %d\n" % self.false_count)
        writer.write_plain("def_eq eqv hits: %d\n" % self.eqv_hit_count)
        writer.write_plain("def_eq proof-irrelevance hits: %d\n"
                           % self.pi_hit_count)
        writer.write_plain("def_eq identity hits: %d\n"
                           % self.identity_hit_count)
        m = self.table_max
        writer.write_plain(
            "max per decl: records %d, leaves %d, inst memo %d, "
            "shift memo %d, bind memo %d, eqv %d, neq %d, failed %d\n"
            % (m[0], m[1], m[2], m[3], m[4], m[5], m[6], m[7]),
        )
        for phase, count in self.phases.iteritems():
            writer.write_plain("def_eq calls in %s: %d\n" % (phase, count))
        writer.write_plain("def_eq calls by argument check:\n")
        for key, count in self.argchecks.iteritems():
            if count > 0:
                writer.write_plain("  %d\t%s\n" % (count, key))
        writer.write_plain(
            "k-like fired/bail head/mutual/ctors/defeq: %d/%d/%d/%d/%d\n" % (
                self.klike_fired_count,
                self.klike_bail_head_count,
                self.klike_bail_mutual_count,
                self.klike_bail_ctors_count,
                self.klike_bail_defeq_count,
            ),
        )
        writer.write_plain("whnf steps:     %d\n" % self.whnf_step_count)
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
    The checker for one declaration: the machine reducing, inferring
    and comparing that declaration's terms, plus the per-declaration
    limits (heartbeats, wall time, memory) and the reference rules its
    position and safety impose.
    """

    _attrs_ = [
        'env', 'decl', 'heartbeat', 'machine',
        'declarations', 'tracer',
        'max_heartbeat', 'count_heartbeats',
        'max_wall_time', 'max_memory', 'start_time', 'start_peak',
        '_whnf_tick',
    ]
    _immutable_fields_ = [
        'env', 'decl', 'machine', 'declarations', 'tracer',
        'max_heartbeat', 'count_heartbeats', 'max_wall_time', 'max_memory',
        'start_time', 'start_peak',
    ]

    # Mask for the wall-time sampling: `clock()` is read every 1024th
    # tick so the per-tick cost stays a counter bump and a mask test.
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
        self.max_memory = env.max_memory
        self.start_time = clock()
        self.start_peak = _peak_memory() if env.max_memory > 0 else 0
        self._whnf_tick = 0
        self.machine = Machine(self)

    def free(self):
        """Release the machine's memory once the check is over."""
        self.machine.free()

    def tick_wall_time(self):
        """
        Count a reduction step; every 1024th one, check whether
        `max_wall_time` or `max_memory` has been exceeded.
        """
        self._whnf_tick += 1
        if (self._whnf_tick & self._WALL_TIME_SAMPLE_MASK) != 0:
            return
        max_wall_time = self.max_wall_time
        max_memory = self.max_memory
        if max_wall_time <= 0.0 and max_memory <= 0:
            return
        if max_wall_time > 0.0:
            elapsed = clock() - self.start_time
            if elapsed > max_wall_time:
                raise WallTimeExceeded(
                    self.decl, elapsed, max_wall_time,
                )
        if max_memory > 0:
            # Two triggers: live heap above the cap (even a major
            # collection can't shrink below this), or this decl pushing
            # the process-wide footprint high-water mark up by more
            # than the cap (`TOTAL_MEMORY` oscillates with the major
            # collection cycle, so it alone misses footprint spikes —
            # the thing that actually drives the machine into swap).
            live = _live_memory()
            if live > max_memory:
                raise MemoryExceeded(
                    self.decl, live, max_memory,
                )
            growth = _peak_memory() - self.start_peak
            if growth > max_memory:
                raise MemoryExceeded(
                    self.decl, growth, max_memory,
                )

    def check_reference(self, const, target):
        """
        ``const``, occurring in the declaration under check, names the
        declaration ``target``: verify the declaration may use it.

        It may not use anything declared after it, nor itself, except
        within its own block; and it may not use anything less safe
        than it is.
        """
        current = self.decl
        if current is None:
            return
        if current.index >= 0 and target.index >= current.index:
            if current.group < 0 or target.group != current.group:
                raise W_NotYetDeclared(self, const)
        if target.safety > current.safety:
            raise W_UnsafeReference(self, const, target.safety)

    def whnf(self, expr):
        """The weak head normal form of ``expr``."""
        machine = self.machine
        h = machine.store.import_term(expr)
        result = machine.whnf(h)
        if result == h:
            return expr
        return machine.export(result)

    def whnf_core(self, expr):
        """``expr`` reduced without unfolding definitions."""
        machine = self.machine
        h = machine.store.import_term(expr)
        result = machine.whnf_core(h)
        if result == h:
            return expr
        return machine.export(result)

    def infer(self, expr):
        """The type of ``expr``, checking it along the way."""
        machine = self.machine
        return machine.export(
            machine.infer(machine.store.import_term(expr), True),
        )

    def def_eq(self, expr1, expr2):
        """Whether ``expr1`` and ``expr2`` are definitionally equal."""
        machine = self.machine
        store = machine.store
        return machine.def_eq(
            store.import_term(expr1), store.import_term(expr2),
        )


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


@dont_look_inside
def _live_memory():
    """
    Current live heap size in bytes. Returns 0 in untranslated mode.

    Unlike `_bytes_allocated` (a monotonically-increasing cumulative
    counter), this reflects what the GC has not yet reclaimed — useful
    for spotting per-decl working-set growth. `dont_look_inside`
    because `gc_get_stats` has no JIT equivalent and this is reached
    from traced code via `tick_wall_time`.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.TOTAL_MEMORY)
    return 0


@dont_look_inside
def _arena_memory():
    """
    Live GC-arena bytes (small objects). Returns 0 untranslated.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.TOTAL_ARENA_MEMORY)
    return 0


@dont_look_inside
def _rawmalloced_memory():
    """
    Live raw-malloced bytes (large objects: big lists/dicts/strings).
    Returns 0 untranslated.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.TOTAL_RAWMALLOCED_MEMORY)
    return 0


@dont_look_inside
def _peak_memory():
    """
    Process-wide peak heap size so far in bytes. Returns 0 in
    untranslated mode. Monotonically non-decreasing across a run — a
    *delta* across one decl tells you how much that decl raised the
    high-water mark. `dont_look_inside` because `gc_get_stats` has no
    JIT equivalent and this is reached from traced code via
    `tick_wall_time`.
    """
    if we_are_translated():
        return rgc.get_stats(rgc.PEAK_MEMORY)
    return 0


def _place_all(declarations):
    """
    Give ``declarations`` their positions in declaration order and their
    blocks, the way `EnvironmentBuilder` does one at a time. An
    inductive's constructors and recursors join its block.
    """
    groups = name_dict()
    index = 0
    for each in declarations:
        each.index = index
        key = each.group_key()
        if key is not None:
            group = groups.get(key, -1)
            if group < 0:
                group = index
                groups[key] = group
            each.group = group
        index += 1
    for each in declarations:
        kind = each.w_kind
        if isinstance(kind, W_Inductive):
            for member in kind.constructors:
                member.group = each.group
            for member in kind.recursors:
                member.group = each.group


class Environment(object):
    """
    A Lean environment with its declarations.
    """

    _attrs_ = [
        'declarations', 'tracer',
        'max_heartbeat', 'count_heartbeats',
        'max_wall_time', 'max_memory',
    ]
    # `declarations` is fully immutable: the reference is set in
    # `__init__` and never reassigned (the dict's *contents* are
    # mutated as decls are parsed, but the reference isn't). The
    # limits change only at run-setup time (CLI options) or at REPL
    # command boundaries — never inside the check loop.
    _immutable_fields_ = [
        'declarations',
        'tracer?',
        'max_heartbeat?',
        'count_heartbeats?',
        'max_wall_time?',
        'max_memory?',
    ]

    def __init__(self, declarations, tracer=Tracer(None)):
        self.declarations = declarations
        self.tracer = tracer
        self.max_heartbeat = 0
        self.count_heartbeats = False
        self.max_wall_time = 0.0
        self.max_memory = 0

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
        _place_all(declarations)
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
        tc = TypeChecker(self, decl)
        try:
            return decl.type_check(tc)
        finally:
            tc.free()

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
        except MemoryExceeded as err:
            error = W_MemoryError(
                decl.name,
                err.used,
                err.max_memory,
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
        tc.free()
        if isinstance(error, W_MemoryError):
            # The decl blew the memory cap: collect now so the next
            # decl starts from a shrunken heap instead of riding the
            # high-water mark into swap.
            rgc.collect()
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

        Each call gets its own checker, outside any declaration, so
        nothing accumulates across calls: for tests and REPL paths that
        need a single comparison. A declaration's check constructs one
        checker and uses it throughout, so its heartbeats and memos are
        scoped to the declaration.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.def_eq(expr1, expr2)
        finally:
            tc.free()

    def infer(self, expr):
        """
        Type inference, with a transient `TypeChecker`. See `def_eq`.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.infer(expr)
        finally:
            tc.free()

    def whnf(self, expr):
        """
        Weak head normal form, with a transient `TypeChecker`. See
        `def_eq`.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.whnf(expr)
        finally:
            tc.free()

    def whnf_core(self, expr):
        """
        Reduction without unfolding definitions, with a transient
        `TypeChecker`. See `def_eq`.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.whnf_core(expr)
        finally:
            tc.free()


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
