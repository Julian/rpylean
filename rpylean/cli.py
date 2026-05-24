"""
CLI for rpylean.
"""

from __future__ import print_function

from time import time
import errno

from rpython.rlib import debug
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.streamio import fdopen_as_stream, open_file_as_stream

from rpylean import _progress, parser
from rpylean._rcli import CLI, UsageError
from rpylean._tokens import (
    ERROR, FORMAT_PLAIN, HEAT_0, HEAT_1, HEAT_2, HEAT_3, HEAT_4,
    PLAIN, writer_from_arg,
)
from rpylean.exceptions import ExportError
from rpylean.ffi import (
    Exporter, FFI, detect_prefix, read_constant_info,
)
from rpylean.ffi import _lltypes as _lean
from rpylean.environment import (
    DeclarationHook,
    EnvironmentBuilder,
    StreamTracer,
    _bytes_allocated,
    _peak_memory,
    from_export,
)
from rpylean.objects import Name, name_dict


cli = CLI(
    tagline="A type checker for the Lean theorem prover.",
    default="check",
)
COLOR = (
    "color",
    "colorize output (yes|no|auto, default: auto)",
)


@cli.subcommand(
    ["*EXPORT_FILES"],
    help="Type check an exported Lean environment.",
    options=[
        (
            "max-fail",
            "the maximum number of type errors to report before giving up",
        ),
        (
            "filter",
            "only check the given declaration(s), separated by commas",
        ),
        (
            "filter-match",
            "only check declarations whose name contains this substring",
        ),
        (
            "max-heartbeat",
            "maximum number of def_eq calls per declaration before giving up",
        ),
        (
            "print",
            (
                "print something for each declaration (valid values are "
                "name|dots|timing|jsonl|decls|declarations|all)"
            ),
        ),
        (
            "slower-than",
            (
                "print each declaration that exceeded this threshold "
                "to check (bare numbers are heartbeats; suffixes: "
                "s/ms/m for time, h for heartbeats)"
            ),
        ),
        (
            "break-at",
            "drop into pdb before checking each declaration whose name "
            "contains this substring; requires running rpylean "
            "untranslated (`pypy -m rpylean check ...`)",
        ),
        COLOR,
    ],
    flags=[
        (
            "trace",
            "enable tracing some def eq and reduction steps",
            "",
            "yes",  # we can't use StreamTracer here, thanks static typing
        ),
        (
            "stats",
            "collect reduction counts (def_eq, whnf, iota, beta, delta, "
            "native nat) and print a summary after the check",
            "",
            "yes",
        ),
    ],
)
def check(self, args, stdin, stdout, stderr):
    stdoutw = writer_from_arg(args.options["color"], stdout)
    stderrw = writer_from_arg(args.options["color"], stderr)

    # Wire `kill -INFO <pid>` (macOS) / `kill -USR1 <pid>` (Linux) to
    # print a one-line progress dump from `_StreamingChecker`. Cheap
    # — one flag-test per declaration, zero work on the no-signal path.
    _progress.install()

    failures = 0

    max_fail = int(args.options["max-fail"] or "0")
    max_heartbeat = int(args.options["max-heartbeat"] or "0")
    printer = Printer.from_str(args.options["print"], stdoutw)
    slow_secs, slow_hb = _parse_threshold(args.options["slower-than"])

    filter_match = args.options["filter-match"]
    filter_names = None
    if filter_match is None and args.options["filter"] is not None:
        filter_names = name_dict()
        for each in args.options["filter"].split(","):
            filter_names[Name.from_str(each)] = True

    break_at = args.options["break-at"]
    if break_at is not None and we_are_translated():
        raise UsageError(
            "--break-at requires running rpylean untranslated "
            "(`pypy -m rpylean check ...`); pdb is unavailable in the "
            "translated binary."
        )

    trace = args.options["trace"]
    stats = args.options["stats"]

    for path in args.varargs:
        start = time()
        if max_fail > 0:
            # `max(1, ...)` preserves a quirk of the original: once we've hit
            # max_fail, subsequent files still parse and emit a single error
            # each before aborting.
            abort_at = max_fail - failures
            if abort_at < 1:
                abort_at = 1
        else:
            abort_at = 0
        new_failures = _check_one_file(
            path,
            stdin,
            stderr,
            stdoutw,
            stderrw,
            printer,
            slow_secs,
            slow_hb,
            filter_match,
            filter_names,
            abort_at,
            max_heartbeat,
            trace,
            break_at,
            stats,
        )
        failures += new_failures
        elapsed = time() - start
        stderr.write("checked in %fs\n" % (elapsed,))
    return 1 if failures else 0


class _StreamingChecker(DeclarationHook):
    """
    Per-declaration filter + type-check, accumulating errors and failure count.
    """

    _attrs_ = [
        'env', 'stdoutw', 'stderrw', 'printer',
        'slow_secs', 'slow_hb',
        'filter_match', 'filter_names',
        'abort_at', 'failures', 'break_at',
        'n_seen', 'n_checked', 'total_heartbeats',
    ]

    def __init__(
        self,
        env,
        stdoutw,
        stderrw,
        printer,
        slow_secs,
        slow_hb,
        filter_match,
        filter_names,
        abort_at,
        break_at,
    ):
        self.env = env
        self.stdoutw = stdoutw
        self.stderrw = stderrw
        self.printer = printer
        self.slow_secs = slow_secs
        self.slow_hb = slow_hb
        self.filter_match = filter_match
        self.filter_names = filter_names
        self.abort_at = abort_at
        self.failures = 0
        self.break_at = break_at
        self.n_seen = 0
        self.n_checked = 0
        self.total_heartbeats = 0

    def on_declaration(self, decl):
        self.n_seen += 1
        # Drain any pending SIGINFO/SIGUSR1 — see `rpylean/_progress.py`.
        # This is the only safe point in a streaming check: a signal
        # arriving mid-decl waits for the next boundary, at which the
        # `decl.name.str()` we print *is* what we were stuck on (the
        # decl that just blocked the loop on the prior iteration).
        if _progress.poll():
            self.stderrw.write_plain(
                "[progress] seen=%d checked=%d failures=%d cur=%s\n" % (
                    self.n_seen, self.n_checked, self.failures,
                    decl.name.str(),
                ),
            )
            # No-op on the default `Tracer`; `StreamTracer` (active
            # under `--stats`) dumps a running iota/beta/delta/whnf
            # snapshot up to *this point* rather than waiting for the
            # final summary (which never arrives if the run is stuck).
            self.env.tracer.print_summary(self.stderrw)
            # `stderr` is block-buffered when redirected to a file, so
            # without an explicit flush the user's `kill -INFO` probe
            # would set the flag and write the line but it'd stay in
            # the buffer until the run ended (or crashed) — defeating
            # the point of the signal.
            self.stderrw.flush()
        if self.filter_match is not None and self.filter_match not in decl.name.str():
            return False
        if self.filter_names is not None and decl.name not in self.filter_names:
            return False
        self.n_checked += 1
        if self.break_at is not None and self.break_at in decl.name.str():
            self._break_for(decl)
        # PYPYLOG section marker so JIT log output (jit-log-opt, etc.)
        # is interleaved with `[ts] {rpylean-decl ... }rpylean-decl`
        # markers naming the decl currently being checked. Translated
        # only — `debug_start` prints unconditionally to stderr in
        # untranslated mode, which would swamp the dev REPL.
        if we_are_translated():
            debug.debug_start("rpylean-decl")
            if debug.have_debug_prints():
                debug.debug_print(decl.name.str())
        result = self.env.type_check_one(decl, printer=self.printer)
        if we_are_translated():
            debug.debug_stop("rpylean-decl")
        self.total_heartbeats += result.heartbeats
        slow_by_time = self.slow_secs >= 0.0 and result.elapsed > self.slow_secs
        slow_by_hb = self.slow_hb >= 0 and result.heartbeats > self.slow_hb
        if slow_by_time or slow_by_hb:
            self.stdoutw.write_plain(
                "%f\t%f\t%d\t%d\t%d\t%d\t" % (
                    result.elapsed,
                    result.gc_elapsed,
                    result.bytes_allocated,
                    result.live_memory,
                    result.peak_growth,
                    result.heartbeats,
                ),
            )
            self.stdoutw.writeline(decl.name.tokens(self.env.declarations))
            # Flush per row so a `timeout`-killed run's tsv reflects what
            # the worker actually saw, not just what filled the 8 KB stdio
            # buffer before the SIGTERM dropped the tail.
            self.stdoutw.flush()
        if result.error is not None:
            result.error.write_to(self.stderrw)
            self.failures += 1
            if 0 < self.abort_at <= self.failures:
                return True
        return False

    def _break_for(self, decl):
        # Gated on `not we_are_translated()` because `pdb` is a CPython
        # module and isn't available in the translated binary. The
        # `--break-at` CLI handler already errors out when the user
        # passes the flag under translation, so reaching here under
        # translation is dead code.
        if not we_are_translated():
            import pdb
            print("[break-at] entering pdb before checking: %s"
                  % (decl.name.str(),))
            pdb.set_trace()


def _check_one_file(
    path,
    stdin,
    stderr,
    stdoutw,
    stderrw,
    printer,
    slow_secs,
    slow_hb,
    filter_match,
    filter_names,
    abort_at,
    max_heartbeat,
    trace,
    break_at,
    stats,
):
    """
    Stream-check a single export file, returning the number of new failures.

    ``abort_at`` is the failure count at which to stop (0 means unlimited).
    """
    file = _open_export(path, stdin)
    builder = EnvironmentBuilder()
    checker = _StreamingChecker(
        env=builder.env,
        stdoutw=stdoutw,
        stderrw=stderrw,
        printer=printer,
        slow_secs=slow_secs,
        slow_hb=slow_hb,
        filter_match=filter_match,
        filter_names=filter_names,
        abort_at=abort_at,
        break_at=break_at,
    )
    # When either --trace or --stats is set, install a `StreamTracer`.
    # The writer is None for --stats-only (no stream output, just count);
    # --trace points the writer at stderr. A single class covers both
    # because counting is cheap and harmless to keep on whenever the
    # stream tracer is active.
    tracer = None
    if trace or stats:
        tracer = StreamTracer(stderrw if trace else None)
        builder.env.tracer = tracer
    bytes_at_start = _bytes_allocated()
    try:
        try:
            if max_heartbeat > 0:
                builder.env.max_heartbeat = max_heartbeat
            if (
                slow_secs >= 0.0
                or slow_hb >= 0
                or (printer is not None and printer.wants_heartbeats)
            ):
                builder.env.count_heartbeats = True
            parser.validate_export_metadata(file)
            builder.consume(file, hook=checker)
        except ExportError as err:
            stderrw.writeline(err.tokens())
            stderrw.write_plain("\n")
            return checker.failures + 1
        except UsageError:
            raise
        except:
            stderr.write("Unexpected error during type checking\n")
            raise
    finally:
        if path != "-":
            file.close()
        if stats and tracer is not None:
            tracer.print_summary(stderrw)
        # One-line aggregate so two runs are comparable at a glance
        # without grepping `--slower-than` output. RPython's `%`
        # formatter doesn't accept `%.1f`, so the MB figures are
        # rounded to whole megabytes via integer division.
        # `_bytes_allocated()` and `_peak_memory()` are no-ops
        # untranslated (return 0), so we skip the memory fields in
        # that mode rather than emit three misleading zeros.
        if we_are_translated():
            _MB = 1024 * 1024
            stderrw.write_plain(
                "summary: %d/%d decls checked, peak %d MB, "
                "allocated %d MB, heartbeats %d\n" % (
                    checker.n_checked,
                    checker.n_seen,
                    _peak_memory() // _MB,
                    (_bytes_allocated() - bytes_at_start) // _MB,
                    checker.total_heartbeats,
                )
            )
        else:
            stderrw.write_plain(
                "summary: %d/%d decls checked, heartbeats %d\n" % (
                    checker.n_checked,
                    checker.n_seen,
                    checker.total_heartbeats,
                )
            )
    return checker.failures


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Dump an exported Lean environment or specific declarations from it.",
    options=[COLOR],
)
def dump(self, args, stdin, stdout, stderr):
    stdoutw = writer_from_arg(args.options["color"], stdout)
    stderrw = writer_from_arg(args.options["color"], stderr)

    (path,) = args.args
    try:
        env = environment_from(path=path, stdin=stdin)
    except ExportError as err:
        stderrw.writeline(err.tokens())
        stderrw.write_plain("\n")
        return 1
    declarations = env.only([Name.from_str(each) for each in args.varargs])
    for each in declarations:
        stdoutw.writeline(each.tokens(env.declarations))
    return 0


@cli.subcommand(
    ["EXPORT_FILE"],
    help="Open a REPL with the given export's environment loaded into it.",
    options=[
        (
            "command",
            "run a single REPL command and exit instead of starting an interactive session",
        ),
    ],
)
def repl(self, args, stdin, stdout, stderr):
    (path,) = args.args
    try:
        environment = environment_from(path=path, stdin=stdin)
    except ExportError as err:
        stderrw = writer_from_arg("auto", stderr)
        stderrw.writeline(err.tokens())
        stderrw.write_plain("\n")
        return 1
    from rpylean import repl

    command = args.options["command"]
    if command is not None:
        stdoutw = writer_from_arg("auto", stdout)
        stderrw = writer_from_arg("auto", stderr)
        ok = repl.dispatch(environment, command, stdin, stdoutw, stderrw)
        return 0 if ok else 1

    repl.interact(environment)
    return 0


ffi = cli.subcli(
    "ffi",
    help="Talk to a real Lean toolchain via FFI.",
    options=[
        (
            "prefix",
            "path to the Lean prefix to link against",
            # TODO: default to `lean --print-prefix` once we can spawn from RPython.
        ),
    ],
)


def _resolve_prefix(args, stderr):
    """Resolve the `--prefix` option, falling back to `$LEAN_PREFIX` /
    `lean --print-prefix`. Returns `None` (after writing a usage hint to
    `stderr`) if nothing turns up; otherwise returns the path."""
    prefix = args.options["prefix"]
    if prefix is None:
        prefix = detect_prefix()
    if prefix is None:
        stderr.write(
            "no --prefix, no $LEAN_PREFIX, and `lean` not on PATH\n"
        )
    return prefix


@ffi.subcommand(
    ["*MODULES"],
    help="Type-check declarations from a Lean toolchain via FFI.",
    options=[
        (
            "filter",
            "only check the given declaration(s), separated by commas",
        ),
        (
            "filter-match",
            "only check declarations whose name contains this substring",
        ),
        (
            "max-fail",
            "the maximum number of type errors to report before giving up",
        ),
        (
            "slower-than",
            (
                "print each declaration that exceeded this threshold "
                "to check (bare numbers are heartbeats; suffixes: "
                "s/ms/m for time, h for heartbeats)"
            ),
        ),
        COLOR,
    ],
)
def check(self, args, stdin, stdout, stderr):
    modules = args.varargs
    if not modules:
        return 1
    prefix = _resolve_prefix(args, stderr)
    if prefix is None:
        return 1

    stdoutw = writer_from_arg(args.options["color"], stdout)
    stderrw = writer_from_arg(args.options["color"], stderr)

    _progress.install()

    filter_match = args.options["filter-match"]
    filter_names = None
    if filter_match is None and args.options["filter"] is not None:
        filter_names = name_dict()
        for each in args.options["filter"].split(","):
            filter_names[Name.from_str(each)] = True

    max_fail = int(args.options["max-fail"] or "0")
    slow_secs, slow_hb = _parse_threshold(args.options["slower-than"])

    builder = EnvironmentBuilder()
    if slow_secs >= 0.0 or slow_hb >= 0:
        builder.env.count_heartbeats = True
    checker = _StreamingChecker(
        env=builder.env, stdoutw=stdoutw, stderrw=stderrw, printer=None,
        slow_secs=slow_secs, slow_hb=slow_hb,
        filter_match=filter_match, filter_names=filter_names,
        abort_at=max_fail if max_fail > 0 else 0,
        break_at=None,
    )
    collector = _FFICollector(builder, checker)
    with FFI.from_prefix(prefix) as ffi_obj:
        env_obj = ffi_obj.import_modules(modules)
        if filter_names is not None:
            # Fast path: look up each filtered name individually rather
            # than walking the entire SMap.
            for fname in filter_names:
                opt = ffi_obj.find_constant(env_obj, fname.str())
                if _lean.obj_tag(opt) == 0:
                    stderr.write("%s: not found\n" % fname.str())
                    continue
                aborted = collector.on_constant(_lean.box(0),
                                                _lean.ctor_get(opt, 0))
                ffi_obj.release(opt)
                if aborted:
                    break
        else:
            ffi_obj.each_constant(env_obj, collector)
        ffi_obj.release(env_obj)
    return 1 if checker.failures else 0


@ffi.subcommand(
    ["*MODULES"],
    help="Open a REPL with a Lean toolchain's environment loaded via FFI.",
    options=[
        (
            "command",
            "run a single REPL command and exit instead of starting an interactive session",
        ),
    ],
)
def repl(self, args, stdin, stdout, stderr):
    modules = args.varargs
    if not modules:
        return 1
    prefix = _resolve_prefix(args, stderr)
    if prefix is None:
        return 1

    builder = EnvironmentBuilder()
    collector = _FFILoader(builder)
    with FFI.from_prefix(prefix) as ffi_obj:
        env_obj = ffi_obj.import_modules(modules)
        ffi_obj.each_constant(env_obj, collector)
        ffi_obj.release(env_obj)

    from rpylean import repl

    command = args.options["command"]
    if command is not None:
        stdoutw = writer_from_arg("auto", stdout)
        stderrw = writer_from_arg("auto", stderr)
        ok = repl.dispatch(builder.env, command, stdin, stdoutw, stderrw)
        return 0 if ok else 1

    repl.interact(builder.env)
    return 0


@ffi.subcommand(
    ["*MODULES"],
    help="Emit lean4export-format NDJSON for a Lean toolchain via FFI.",
    options=[
        (
            "filter",
            "only emit the given declaration(s) (plus their transitive "
            "dependencies), separated by commas",
        ),
    ],
)
def export(self, args, stdin, stdout, stderr):
    modules = args.varargs
    if not modules:
        return 1
    prefix = _resolve_prefix(args, stderr)
    if prefix is None:
        return 1

    filter_names = None
    if args.options["filter"] is not None:
        filter_names = [Name.from_str(each)
                        for each in args.options["filter"].split(",")]

    exporter = Exporter(stdout)
    with FFI.from_prefix(prefix) as ffi_obj:
        exporter.set_lean_meta(ffi_obj.lean_version, ffi_obj.lean_githash)
        env_obj = ffi_obj.import_modules(modules)
        collector = _ExportCollector(exporter)
        ffi_obj.each_constant(env_obj, collector)
        ffi_obj.release(env_obj)
    exporter.emit_meta()
    if filter_names is None:
        exporter.dump_all()
    else:
        exporter.dump_named(filter_names)
    return 0


class _FFICollectorBase(object):
    """Common base for `FFI.each_constant` callbacks.

    Subclasses override `_handle` to do something with each walked
    declaration. Returning `True` signals an early-abort and ends the
    walk. Walker failures (unexpected ctor tags, layout drift) are left
    to propagate so they show up loudly instead of as silent "skipped"
    noise."""

    _attrs_ = []

    def on_constant(self, name_obj, ci_obj):
        return self._handle(read_constant_info(ci_obj))

    def _handle(self, decl):
        raise NotImplementedError


class _ExportCollector(_FFICollectorBase):
    """Register every walked constant with the Exporter; `dump_all`
    emits them all in dependency order afterwards."""

    _attrs_ = ['exporter']

    def __init__(self, exporter):
        self.exporter = exporter

    def _handle(self, decl):
        self.exporter.register(decl)
        return False


class _FFILoader(_FFICollectorBase):
    """Register every walked constant into a builder; used by `ffi
    repl` to populate the env before dropping into interactive mode."""

    _attrs_ = ['builder']

    def __init__(self, builder):
        self.builder = builder

    def _handle(self, decl):
        self.builder.register_declaration(decl)
        return False


class _FFICollector(_FFICollectorBase):
    """Register → stream-check, one declaration at a time. Returns
    `True` when the checker has signalled an early-abort (e.g.
    `--max-fail` reached)."""

    _attrs_ = ['builder', 'checker']

    def __init__(self, builder, checker):
        self.builder = builder
        self.checker = checker

    def _handle(self, decl):
        self.builder.register_declaration(decl)
        return self.checker.on_declaration(decl)


def _open_export(path, stdin):
    if path == "-":
        return fdopen_as_stream(stdin.fileno(), "r")
    try:
        return open_file_as_stream(path)
    except OSError as err:
        if err.errno != errno.ENOENT:
            raise
        raise UsageError("`%s` does not exist." % (path,))


def environment_from(path, stdin):
    file = _open_export(path, stdin)
    try:
        return from_export(file)
    finally:
        if path != "-":
            file.close()


def _parse_threshold(s):
    """Parse a ``--slower-than`` threshold into ``(seconds, heartbeats)``.

    The non-active value of the pair is ``-1``. Bare numbers are heartbeats;
    suffixes ``s``, ``ms``, ``m`` mean seconds; ``h`` means heartbeats.
    Returns ``(-1.0, -1)`` for ``None``.
    """
    if s is None:
        return -1.0, -1
    length = len(s)
    if s.endswith("ms"):
        end = length - 2
        assert end >= 0
        return _pos_int(s, s[:end]) * 0.001, -1
    if s.endswith("s"):
        end = length - 1
        assert end >= 0
        return float(_pos_int(s, s[:end])), -1
    if s.endswith("m"):
        end = length - 1
        assert end >= 0
        return _pos_int(s, s[:end]) * 60.0, -1
    if s.endswith("h"):
        end = length - 1
        assert end >= 0
        return -1.0, _pos_int(s, s[:end])
    return -1.0, _pos_int(s, s)


def _pos_int(orig, n):
    try:
        value = int(n)
    except ValueError:
        raise UsageError("Invalid threshold: %s" % (orig,))
    if value < 0:
        raise UsageError("Invalid threshold: %s" % (orig,))
    return value


class Printer(object):
    """
    A streaming pretty-printer for declarations being type-checked.

    Subclasses override `before` (called just before a decl is checked)
    and/or `after` (called with the `CheckResult` once the check returns).
    `wants_heartbeats` lets a subclass opt the env into heartbeat counting
    so `result.heartbeats` is populated when its output depends on it.
    """

    _attrs_ = ['writer']
    wants_heartbeats = False

    def __init__(self, writer):
        self.writer = writer

    def before(self, env, decl):
        """Run just before `decl` is type-checked."""

    def after(self, env, decl, result):
        """Run just after `decl` is type-checked, with its `CheckResult`."""

    @staticmethod
    def from_str(pp_str, writer):
        """Construct a Printer from a CLI string, or return None for 'none'."""
        if pp_str == "all" or pp_str == "decls" or pp_str == "declarations":
            return _DeclPrinter(writer)
        elif pp_str == "name" or pp_str == "names":
            return _NamePrinter(writer)
        elif pp_str == "dots":
            return _DotPrinter(writer)
        elif pp_str == "timing":
            return _TimingPrinter(writer)
        elif pp_str == "jsonl":
            return _JSONLPrinter(writer)
        elif pp_str is None or pp_str == "none":
            return None
        else:
            raise UsageError("Unknown pretty print choice: %s" % (pp_str,))


class _DeclPrinter(Printer):
    _attrs_ = []

    def before(self, env, decl):
        self.writer.writeline(decl.tokens(env.declarations))


class _NamePrinter(Printer):
    """Print `name ... ` before, then `OK` / `FAIL` after the check."""

    _attrs_ = []

    def before(self, env, decl):
        self.writer.write(decl.name.tokens(env.declarations))
        self.writer.write([PLAIN.emit(" ... ")])
        self.writer.flush()

    def after(self, env, decl, result):
        if result.error is None:
            self.writer.writeline([PLAIN.emit("OK")])
        else:
            self.writer.writeline([ERROR.emit("FAIL")])
        self.writer.flush()


#: Heat levels for streaming printers, ordered cool → hot. Each entry is
#: ``(token, glyph)``. Glyphs are 5 visually distinct ASCII chars so the
#: magnitude survives ``--color=no``; colors layer on top via the token
#: when the writer is in ANSI mode.
_HEAT_LEVELS = [
    (HEAT_0, "."),
    (HEAT_1, ":"),
    (HEAT_2, "o"),
    (HEAT_3, "O"),
    (HEAT_4, "#"),
]


def _heat_level(elapsed, heartbeats):
    """
    Pick an index into `_HEAT_LEVELS` from one decl's `CheckResult`.

    Prefers heartbeats (deterministic across machines and JIT warmup);
    falls back to wall-clock when heartbeats aren't being counted.
    """
    if heartbeats > 0:
        if heartbeats < 1000:
            return 0
        elif heartbeats < 10000:
            return 1
        elif heartbeats < 100000:
            return 2
        elif heartbeats < 1000000:
            return 3
        return 4
    if elapsed < 0.001:
        return 0
    elif elapsed < 0.01:
        return 1
    elif elapsed < 0.1:
        return 2
    elif elapsed < 1.0:
        return 3
    return 4


class _DotPrinter(Printer):
    """One glyph per decl, colored by heartbeats (or wall time)."""

    _attrs_ = []
    wants_heartbeats = True

    def after(self, env, decl, result):
        token, glyph = _HEAT_LEVELS[_heat_level(result.elapsed, result.heartbeats)]
        self.writer.write([token.emit(glyph)])
        self.writer.flush()


class _TimingPrinter(_NamePrinter):
    """Stream `name ... elapsed (N hb)` per decl (extends `_NamePrinter`)."""

    _attrs_ = []
    wants_heartbeats = True

    def after(self, env, decl, result):
        # Heartbeat counting is unconditionally enabled (`wants_heartbeats`),
        # so `0 hb` here means the decl genuinely needed no def_eq calls,
        # not that the counter was off.
        timing = "%fs (%d hb)" % (result.elapsed, result.heartbeats)
        if result.error is None:
            self.writer.writeline([PLAIN.emit(timing)])
        else:
            self.writer.writeline(
                [PLAIN.emit(timing + " "), ERROR.emit("FAIL")],
            )
        self.writer.flush()


_HEX = "0123456789abcdef"


def _json_escape(s):
    """Escape `s` for use inside a JSON string literal."""
    out = []
    for ch in s:
        c = ord(ch)
        if c == 0x22:
            out.append("\\\"")
        elif c == 0x5c:
            out.append("\\\\")
        elif c == 0x0a:
            out.append("\\n")
        elif c == 0x0d:
            out.append("\\r")
        elif c == 0x09:
            out.append("\\t")
        elif c < 0x20:
            # All control chars fit in two hex digits; the upper byte is 0.
            out.append("\\u00" + _HEX[c >> 4] + _HEX[c & 0xf])
        else:
            out.append(ch)
    return "".join(out)


class _JSONLPrinter(Printer):
    """One JSON object per checked decl, newline delimited."""

    _attrs_ = []
    wants_heartbeats = True

    def after(self, env, decl, result):
        if result.error is None:
            status = "\"ok\":true"
        else:
            status = "\"ok\":false,\"error\":\"%s\"" % (
                _json_escape(FORMAT_PLAIN(result.error.tokens())),
            )
        line = (
            "{\"name\":\"%s\",%s,"
            "\"elapsed\":%f,"
            "\"gc_elapsed\":%f,"
            "\"bytes_allocated\":%d,"
            "\"live_memory\":%d,"
            "\"peak_growth\":%d,"
            "\"heartbeats\":%d}\n"
        ) % (
            _json_escape(decl.name.str()),
            status,
            result.elapsed,
            result.gc_elapsed,
            result.bytes_allocated,
            result.live_memory,
            result.peak_growth,
            result.heartbeats,
        )
        self.writer.write([PLAIN.emit(line)])
        self.writer.flush()


if __name__ == "__main__":
    import sys

    sys.exit(cli.main(sys.argv))
