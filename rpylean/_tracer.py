"""
Reduction and def_eq tracing hooks for `Environment`.
"""

from rpylean._tokens import TRACE
from rpylean.objects import name_dict


class Tracer(object):
    """
    No-op tracer.

    Override any hook to observe the reduction loop. The bodies here
    are intentionally empty so RPython inlines them away on the default
    path; hot call sites invoke these unconditionally on `env.tracer`
    rather than gating on the tracer's identity.
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
