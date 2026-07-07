"""
CLI for rpylean.
"""

from __future__ import print_function

from time import time
import errno
import os

from rpython.rlib import debug, rgc
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.streamio import fdopen_as_stream, open_file_as_stream

from rpylean import _format, _progress, parser
from rpylean._rlib.rcli import CLI, UsageError
from rpylean._rlib.rterminal import terminal_width
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
    _arena_memory,
    _bytes_allocated,
    _live_memory,
    _peak_memory,
    _rawmalloced_memory,
    from_export,
)
from rpylean.objects import (
    Name, Resolver, intern_stats, name_dict, set_resolver,
)


cli = CLI(
    tagline="A type checker for the Lean theorem prover.",
    default="check",
)
COLOR = (
    "color",
    "colorize output (yes|no|auto, default: auto)",
)
WIDTH = (
    "width",
    "wrap pretty-printed output at this many columns "
    "(default: the terminal width, or 100 when not a terminal)",
)


def apply_width(width_arg, stdout):
    """
    Configure the pretty-printer's line width from ``--width``.

    An explicit ``--width`` wins; otherwise we use the terminal width when
    ``stdout`` is a terminal, falling back to the default width (which keeps
    piped/redirected output stable and reproducible).
    """
    if width_arg:
        try:
            width = int(width_arg)
        except ValueError:
            raise UsageError("Invalid --width: %s" % (width_arg,))
        if width <= 0:
            raise UsageError("Invalid --width: %s" % (width_arg,))
        _format.set_render_width(width)
        return
    if stdout.isatty():
        width = terminal_width(stdout.fileno())
        if width > 0:
            _format.set_render_width(width)
            return
    _format.set_render_width(_format.DEFAULT_WIDTH)

#: The options shared by `check` and `ffi check`, parsed by `_CheckRun`.
CHECK_OPTIONS = [
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
        "max-wall-time-per-decl",
        "maximum wall-clock seconds per declaration before giving up "
        "(suffixes: s/ms/m, default seconds; sampled every 1024 def_eq calls)",
    ),
    (
        "max-memory-per-decl",
        "give up on the declaration being checked when the process' "
        "live heap exceeds this size (suffixes: K/M/G, default bytes; "
        "sampled with the wall-time check)",
    ),
    (
        "flush-memory-per-decl",
        "drop the per-decl caches mid-decl whenever the live heap "
        "grows past the declaration's starting point by this much, "
        "trading recomputation for a bounded footprint (suffixes: "
        "K/M/G, default bytes; sampled with the wall-time check)",
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
    WIDTH,
]
CHECK_FLAGS = [
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
]


@cli.subcommand(
    ["*EXPORT_FILES"],
    help="Type check an exported Lean environment.",
    options=CHECK_OPTIONS,
    flags=CHECK_FLAGS,
)
def check(self, args, stdin, stdout, stderr):
    stdoutw = writer_from_arg(args.options["color"], stdout)
    stderrw = writer_from_arg(args.options["color"], stderr)
    apply_width(args.options["width"], stdout)

    # Wire `kill -INFO <pid>` (macOS) / `kill -USR1 <pid>` (Linux) to
    # print a one-line progress dump from `_StreamingChecker`. Cheap
    # — one flag-test per declaration, zero work on the no-signal path.
    _progress.install()

    run = _CheckRun(args, stdoutw, stderrw)
    failures = 0
    for path in args.varargs:
        start = time()
        if run.max_fail > 0:
            # `max(1, ...)` preserves a quirk of the original: once we've hit
            # max_fail, subsequent files still parse and emit a single error
            # each before aborting.
            abort_at = run.max_fail - failures
            if abort_at < 1:
                abort_at = 1
        else:
            abort_at = 0
        failures += _check_one_file(path, stdin, stderr, run, abort_at)
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
            apps, projs, consts, pending = intern_stats()
            _MB = 1024 * 1024
            self.stderrw.write_plain(
                "[progress] seen=%d checked=%d failures=%d "
                "live=%dMB arena=%dMB rawmalloc=%dMB "
                "interned(apps=%d projs=%d consts=%d) pending=%d "
                "cur=%s\n" % (
                    self.n_seen, self.n_checked, self.failures,
                    _live_memory() // _MB,
                    _arena_memory() // _MB,
                    _rawmalloced_memory() // _MB,
                    apps, projs, consts, pending,
                    decl.name.str(),
                ),
            )
            # No-op on the default `Tracer`; `StreamTracer` (active
            # under `--stats`) dumps a running iota/beta/delta/whnf
            # snapshot up to *this point* rather than waiting for the
            # final summary (which never arrives if the run is stuck).
            self.env.tracer.print_summary(self.stderrw)
            # Also dump the full heap graph for offline analysis with
            # pypy/tool/gcdump.py (decompress the typeids blob first:
            # `python3 -c "import zlib,sys;
            #   sys.stdout.write(zlib.decompress(
            #     open('/tmp/rpylean-typeids.z','rb').read()).decode())"
            #   > /tmp/rpylean-typeids.txt`). Translated only —
            # `dump_rpy_heap` is a GC hook with no untranslated
            # equivalent. Pauses the check for the dump's duration,
            # which is fine for a manual `kill -INFO` probe.
            if we_are_translated():
                fd = os.open(
                    "/tmp/rpylean-heap.dump",
                    os.O_WRONLY | os.O_CREAT | os.O_TRUNC,
                    0644,
                )
                rgc.dump_rpy_heap(fd)
                os.close(fd)
                fd = os.open(
                    "/tmp/rpylean-typeids.z",
                    os.O_WRONLY | os.O_CREAT | os.O_TRUNC,
                    0644,
                )
                # `get_typeids_z` hands back a low-level char array,
                # not a str — join it the way pypy's gc module does.
                array = rgc.get_typeids_z()
                blob = ''.join([array[i] for i in range(len(array))])
                os.write(fd, blob)
                os.close(fd)
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


class _CheckRun(object):
    """
    The option set shared by `check` and `ffi check`, parsed once, plus
    the builder/checker wiring derived from it.

    `check` calls `start` once per export file (each file is its own
    environment); `ffi check` calls it once per invocation.
    """

    _attrs_ = [
        'stdoutw', 'stderrw',
        'max_fail', 'max_heartbeat', 'max_wall_time', 'max_memory',
        'flush_memory', 'printer', 'slow_secs', 'slow_hb',
        'filter_match', 'filter_names', 'break_at', 'trace', 'stats',
    ]

    def __init__(self, args, stdoutw, stderrw):
        self.stdoutw = stdoutw
        self.stderrw = stderrw

        self.max_fail = int(args.options["max-fail"] or "0")
        self.max_heartbeat = int(args.options["max-heartbeat"] or "0")
        self.max_wall_time = _parse_seconds(
            args.options["max-wall-time-per-decl"],
        )
        self.max_memory = _parse_bytes(args.options["max-memory-per-decl"])
        self.flush_memory = _parse_bytes(
            args.options["flush-memory-per-decl"],
        )
        self.printer = Printer.from_str(args.options["print"], stdoutw)
        self.slow_secs, self.slow_hb = _parse_threshold(
            args.options["slower-than"],
        )

        self.filter_match = args.options["filter-match"]
        filter_names = None
        if self.filter_match is None and args.options["filter"] is not None:
            filter_names = name_dict()
            for each in args.options["filter"].split(","):
                filter_names[Name.from_str(each)] = True
        self.filter_names = filter_names

        self.break_at = args.options["break-at"]
        if self.break_at is not None and we_are_translated():
            raise UsageError(
                "--break-at requires running rpylean untranslated "
                "(`pypy -m rpylean check ...`); pdb is unavailable in the "
                "translated binary."
            )

        self.trace = args.options["trace"]
        self.stats = args.options["stats"]

    def start(self, abort_at):
        """
        A fresh ``(builder, checker, tracer)`` wired with the parsed
        limits.

        ``abort_at`` is the failure count at which to stop (0 means
        unlimited).
        """
        builder = EnvironmentBuilder()
        env = builder.env
        if self.max_heartbeat > 0:
            env.max_heartbeat = self.max_heartbeat
        if self.max_wall_time > 0.0:
            env.max_wall_time = self.max_wall_time
        if self.max_memory > 0:
            env.max_memory = self.max_memory
        if self.flush_memory > 0:
            env.flush_memory = self.flush_memory
        if (
            self.slow_secs >= 0.0
            or self.slow_hb >= 0
            or (self.printer is not None and self.printer.wants_heartbeats)
        ):
            env.count_heartbeats = True
        checker = _StreamingChecker(
            env=env,
            stdoutw=self.stdoutw,
            stderrw=self.stderrw,
            printer=self.printer,
            slow_secs=self.slow_secs,
            slow_hb=self.slow_hb,
            filter_match=self.filter_match,
            filter_names=self.filter_names,
            abort_at=abort_at,
            break_at=self.break_at,
        )
        # When either --trace or --stats is set, install a `StreamTracer`.
        # The writer is None for --stats-only (no stream output, just count);
        # --trace points the writer at stderr. A single class covers both
        # because counting is cheap and harmless to keep on whenever the
        # stream tracer is active.
        tracer = None
        if self.trace or self.stats:
            tracer = StreamTracer(self.stderrw if self.trace else None)
            env.tracer = tracer
        return builder, checker, tracer

    def summarize(self, checker, tracer, bytes_at_start):
        if self.stats and tracer is not None:
            tracer.print_summary(self.stderrw)
        # One-line aggregate so two runs are comparable at a glance
        # without grepping `--slower-than` output. RPython's `%`
        # formatter doesn't accept `%.1f`, so the MB figures are
        # rounded to whole megabytes via integer division.
        # `_bytes_allocated()` and `_peak_memory()` are no-ops
        # untranslated (return 0), so we skip the memory fields in
        # that mode rather than emit three misleading zeros.
        if we_are_translated():
            _MB = 1024 * 1024
            self.stderrw.write_plain(
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
            self.stderrw.write_plain(
                "summary: %d/%d decls checked, heartbeats %d\n" % (
                    checker.n_checked,
                    checker.n_seen,
                    checker.total_heartbeats,
                )
            )


def _check_one_file(path, stdin, stderr, run, abort_at):
    """
    Stream-check a single export file, returning the number of new failures.

    ``abort_at`` is the failure count at which to stop (0 means unlimited).
    """
    file = _open_export(path, stdin)
    builder, checker, tracer = run.start(abort_at)
    bytes_at_start = _bytes_allocated()
    try:
        try:
            parser.validate_export_metadata(file)
            builder.consume(file, hook=checker)
        except ExportError as err:
            run.stderrw.writeline(err.tokens())
            run.stderrw.write_plain("\n")
            return checker.failures + 1
        except UsageError:
            raise
        except:
            stderr.write("Unexpected error during type checking\n")
            raise
    finally:
        if path != "-":
            file.close()
        run.summarize(checker, tracer, bytes_at_start)
    return checker.failures


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Dump an exported Lean environment or specific declarations from it.",
    options=[COLOR, WIDTH],
    flags=[
        (
            "export",
            "emit lean4export-format NDJSON (with transitive "
            "dependencies) instead of pretty-printing",
            "",
            "yes",
        ),
    ],
)
def dump(self, args, stdin, stdout, stderr):
    stdoutw = writer_from_arg(args.options["color"], stdout)
    stderrw = writer_from_arg(args.options["color"], stderr)
    apply_width(args.options["width"], stdout)

    (path,) = args.args
    try:
        env = environment_from(path=path, stdin=stdin)
    except ExportError as err:
        stderrw.writeline(err.tokens())
        stderrw.write_plain("\n")
        return 1
    if args.options["export"]:
        exporter = Exporter(stdout)
        for each in env.declarations.values():
            exporter.register(each)
        exporter.emit_meta()
        if args.varargs:
            exporter.dump_named(
                [Name.from_str(each) for each in args.varargs],
            )
        else:
            exporter.dump_all()
        return 0
    declarations = env.only([Name.from_str(each) for each in args.varargs])
    for each in declarations:
        stdoutw.writeline(each.tokens(env.declarations))
    return 0


#: The options shared by `repl` and `ffi repl`.
REPL_OPTIONS = [
    (
        "command",
        "run a single REPL command and exit instead of starting an interactive session",
    ),
    WIDTH,
]


def _run_repl(environment, args, stdin, stdout, stderr):
    """
    Run a REPL `--command` (if given) or start an interactive session.
    """
    from rpylean import repl

    apply_width(args.options["width"], stdout)

    command = args.options["command"]
    if command is not None:
        stdoutw = writer_from_arg("auto", stdout)
        stderrw = writer_from_arg("auto", stderr)
        try:
            return repl.dispatch(environment, command, stdin, stdoutw, stderrw)
        except repl._Quit as quit:
            return quit.exit_code

    repl.interact(environment)
    return 0


@cli.subcommand(
    ["EXPORT_FILE"],
    help="Open a REPL with the given export's environment loaded into it.",
    options=REPL_OPTIONS,
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
    return _run_repl(environment, args, stdin, stdout, stderr)


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
    options=CHECK_OPTIONS,
    flags=CHECK_FLAGS,
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
    apply_width(args.options["width"], stdout)

    _progress.install()

    run = _CheckRun(args, stdoutw, stderrw)
    start = time()
    abort_at = run.max_fail if run.max_fail > 0 else 0
    builder, checker, tracer = run.start(abort_at)
    collector = _FFICollector(builder, checker)
    bytes_at_start = _bytes_allocated()
    try:
        with FFI.from_prefix(prefix) as ffi_obj:
            env_obj = ffi_obj.import_modules(modules)
            set_resolver(_FFIResolver(ffi_obj, env_obj, builder))
            try:
                if run.filter_names is not None:
                    # Fast path: look up each filtered name individually
                    # rather than walking the entire SMap.
                    for fname in run.filter_names:
                        opt = ffi_obj.find_constant_named(env_obj, fname)
                        if _lean.obj_tag(opt) == 0:
                            stderr.write("%s: not found\n" % fname.str())
                            continue
                        aborted = collector.on_constant(
                            _lean.box(0), _lean.ctor_get(opt, 0),
                        )
                        ffi_obj.release(opt)
                        if aborted:
                            break
                else:
                    ffi_obj.each_constant(env_obj, collector)
            finally:
                set_resolver(None)
                ffi_obj.release(env_obj)
    finally:
        run.summarize(checker, tracer, bytes_at_start)
    stderr.write("checked in %fs\n" % (time() - start,))
    return 1 if checker.failures else 0


@ffi.subcommand(
    ["*MODULES"],
    help="Open a REPL with a Lean toolchain's environment loaded via FFI.",
    options=REPL_OPTIONS,
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
    return _run_repl(builder.env, args, stdin, stdout, stderr)


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
        declarations = self.builder.env.declarations
        if decl.name in declarations:
            # Already demand-loaded by the `_FFIResolver` as a
            # dependency of an earlier-walked decl; check the registered
            # instance — it's the one other decls resolved against.
            decl = declarations[decl.name]
        else:
            self.builder.register_declaration(decl)
        return self.checker.on_declaration(decl)


class _FFIResolver(Resolver):
    """
    Demand-load missing declarations from the Lean environment.

    `each_constant` walks `Environment.constants` in hash-bucket order,
    so a streamed declaration may reference constants the walk hasn't
    reached yet; this resolver fetches each one by name the moment a
    lookup misses. It only registers — checking stays with the walk,
    which still visits every constant exactly once.
    """

    _attrs_ = ['ffi', 'env_obj', 'builder']

    def __init__(self, ffi, env_obj, builder):
        self.ffi = ffi
        self.env_obj = env_obj
        self.builder = builder

    def resolve(self, name):
        opt = self.ffi.find_constant_named(self.env_obj, name)
        if _lean.obj_tag(opt) != 0:
            self.builder.register_declaration(
                read_constant_info(_lean.ctor_get(opt, 0)),
            )
        self.ffi.release(opt)


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


def _parse_seconds(s):
    """Parse a wall-clock duration into seconds. Returns 0.0 for `None`.

    Bare numbers and `s` suffix are seconds; `ms` is milliseconds; `m` is
    minutes. `h` (heartbeats) is rejected — this option is time-only.
    """
    if s is None:
        return 0.0
    if s.endswith("h"):
        raise UsageError(
            "Invalid wall-time threshold (use s/ms/m suffix, not h): %s" % (s,)
        )
    length = len(s)
    if s.endswith("ms"):
        end = length - 2
        assert end >= 0
        return _pos_int(s, s[:end]) * 0.001
    if s.endswith("s"):
        end = length - 1
        assert end >= 0
        return float(_pos_int(s, s[:end]))
    if s.endswith("m"):
        end = length - 1
        assert end >= 0
        return _pos_int(s, s[:end]) * 60.0
    return float(_pos_int(s, s))


def _parse_bytes(s):
    """Parse a memory size into bytes. Returns 0 for `None`.

    Bare numbers are bytes; `K`/`M`/`G` (or `KB`/`MB`/`GB`) suffixes
    are binary multiples.
    """
    if s is None:
        return 0
    scaled = s
    if scaled.endswith("B"):
        end = len(scaled) - 1
        assert end >= 0
        scaled = scaled[:end]
    multiplier = 1
    if scaled.endswith("K"):
        multiplier = 1024
    elif scaled.endswith("M"):
        multiplier = 1024 * 1024
    elif scaled.endswith("G"):
        multiplier = 1024 * 1024 * 1024
    if multiplier > 1:
        end = len(scaled) - 1
        assert end >= 0
        scaled = scaled[:end]
    return _pos_int(s, scaled) * multiplier


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
