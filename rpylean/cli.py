"""
CLI for rpylean.
"""

from __future__ import print_function

from time import time
import errno

from rpython.rlib.objectmodel import r_dict
from rpython.rlib.streamio import fdopen_as_stream, open_file_as_stream

from rpylean import parser
from rpylean._rcli import CLI, UsageError
from rpylean._tokens import PLAIN, writer_from_arg
from rpylean.exceptions import ExportError
from rpylean import _lltypes as _lean
from rpylean._lean_runtime import read_expr, read_name
from rpylean.leanffi import FFI
from rpylean.environment import (
    DeclarationHook,
    EnvironmentBuilder,
    StreamTracer,
    from_export,
)
from rpylean.objects import Name, name_eq


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
                "name|dots|decls|declarations|all)"
            ),
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
    ],
)
def check(self, args, stdin, stdout, stderr):
    stdoutw = writer_from_arg(args.options["color"], stdout)
    stderrw = writer_from_arg(args.options["color"], stderr)

    failures = 0

    max_fail = int(args.options["max-fail"] or "0")
    max_heartbeat = int(args.options["max-heartbeat"] or "0")
    printer = Printer.from_str(args.options["print"], stdoutw)
    pp = printer.show if printer is not None else None

    filter_match = args.options["filter-match"]
    filter_names = None
    if filter_match is None and args.options["filter"] is not None:
        filter_names = r_dict(name_eq, Name.hash)
        for each in args.options["filter"].split(","):
            filter_names[Name.from_str(each)] = True

    trace = args.options["trace"]

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
            stderrw,
            pp,
            filter_match,
            filter_names,
            abort_at,
            max_heartbeat,
            trace,
        )
        failures += new_failures
        elapsed = time() - start
        stderr.write("checked in %fs\n" % (elapsed,))
    return 1 if failures else 0


class _StreamingChecker(DeclarationHook):
    """
    Per-declaration filter + type-check, accumulating errors and failure count.
    """

    def __init__(self, env, stderrw, pp, filter_match, filter_names, abort_at):
        self.env = env
        self.stderrw = stderrw
        self.pp = pp
        self.filter_match = filter_match
        self.filter_names = filter_names
        self.abort_at = abort_at
        self.failures = 0

    def on_declaration(self, decl):
        if self.filter_match is not None and self.filter_match not in decl.name.str():
            return False
        if self.filter_names is not None and decl.name not in self.filter_names:
            return False
        for w_error in self.env.type_check_one(decl, pp=self.pp):
            w_error.write_to(self.stderrw)
            self.failures += 1
            if 0 < self.abort_at <= self.failures:
                return True
        return False


def _check_one_file(
    path,
    stdin,
    stderr,
    stderrw,
    pp,
    filter_match,
    filter_names,
    abort_at,
    max_heartbeat,
    trace,
):
    """
    Stream-check a single export file, returning the number of new failures.

    ``abort_at`` is the failure count at which to stop (0 means unlimited).
    """
    file = _open_export(path, stdin)
    builder = EnvironmentBuilder()
    checker = _StreamingChecker(
        env=builder.env,
        stderrw=stderrw,
        pp=pp,
        filter_match=filter_match,
        filter_names=filter_names,
        abort_at=abort_at,
    )
    try:
        try:
            if trace:
                builder.env.tracer = StreamTracer(stderrw)
            if max_heartbeat > 0:
                builder.env.max_heartbeat = max_heartbeat
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


@cli.subcommand(
    ["*MODULES"],
    help="Directly extract an environment via FFI to a real Lean toolchain.",
    options=[
        (
            "prefix",
            "path to the Lean prefix to link against ",
            # TODO: "[default: `lean --print-prefix`]",
        ),
        (
            "lookup",
            "comma-separated declaration names to print the type of",
        ),
    ],
)
def ffi(self, args, stdin, stdout, stderr):
    modules = args.varargs
    if not modules:
        return 1  # TODO: some default, maybe Init

    prefix = args.options["prefix"]
    if prefix is None:
        return 1  # TODO: some default, lean --print-prefix but RPython spawn??

    lookup_arg = args.options["lookup"]
    lookups = lookup_arg.split(",") if lookup_arg else []

    with FFI.from_prefix(prefix) as ffi:
        env = ffi.import_modules(modules)
        for probe in lookups:
            opt = ffi.find_constant(env, probe)
            if _lean.obj_tag(opt) == 0:
                stdout.write("%s: not found\n" % probe)
                continue
            ci = _lean.ctor_get(opt, 0)
            cval = _lean.ctor_get(_lean.ctor_get(ci, 0), 0)
            name = read_name(_lean.ctor_get(cval, 0))
            # Walk the type Expr to verify the data is reachable; we don't
            # render it (rendering needs the full constants map for
            # name resolution).
            read_expr(_lean.ctor_get(cval, 2))
            stdout.write("%s : %s\n" % (name.str(), _ci_kind(_lean.ptr_tag(ci))))
    return 0


def _ci_kind(tag):
    if tag == 0: return "axiom"
    if tag == 1: return "defn"
    if tag == 2: return "thm"
    if tag == 3: return "opaque"
    if tag == 4: return "quot"
    if tag == 5: return "induct"
    if tag == 6: return "ctor"
    if tag == 7: return "recursor"
    return "?"


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


class Printer(object):
    """
    A pretty-printer for declarations.
    """

    def __init__(self, writer):
        self.writer = writer

    def show(self, env, decl):
        """Print a single declaration according to this printer's mode."""
        raise NotImplementedError

    @staticmethod
    def from_str(pp_str, writer):
        """Construct a Printer from a CLI string, or return None for 'none'."""
        if pp_str == "all" or pp_str == "decls" or pp_str == "declarations":
            return _DeclPrinter(writer)
        elif pp_str == "name" or pp_str == "names":
            return _NamePrinter(writer)
        elif pp_str == "dots":
            return _DotPrinter(writer)
        elif pp_str is None or pp_str == "none":
            return None
        else:
            raise UsageError("Unknown pretty print choice: %s" % (pp_str,))


class _DeclPrinter(Printer):
    def show(self, env, decl):
        self.writer.writeline(decl.tokens(env.declarations))


class _NamePrinter(Printer):
    def show(self, env, decl):
        self.writer.writeline(decl.name.tokens(env.declarations))


class _DotPrinter(Printer):
    def show(self, env, decl):
        self.writer.write([PLAIN.emit(".")])


if __name__ == "__main__":
    import sys

    sys.exit(cli.main(sys.argv))
