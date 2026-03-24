"""
CLI for rpylean.
"""

from __future__ import print_function

from time import time
import errno

from rpython.rlib.streamio import fdopen_as_stream, open_file_as_stream

from rpylean._rcli import CLI, UsageError
from rpylean._tokens import PLAIN, writer_from_arg
from rpylean.exceptions import ExportError
from rpylean.leanffi import FFI
from rpylean.environment import StreamTracer, from_export
from rpylean.objects import Name


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

    for path in args.varargs:
        start = time()
        try:
            env = environment_from(path=path, stdin=stdin)
        except ExportError as err:
            stderrw.writeline(err.tokens())
            stderrw.write_plain("\n")
            failures += 1
            continue
        parse_elapsed = time() - start

        if args.options["trace"]:
            env.tracer = StreamTracer(stderrw)

        max_heartbeat = int(args.options["max-heartbeat"] or "0")
        if max_heartbeat > 0:
            env.max_heartbeat = max_heartbeat

        if args.options["filter-match"] is not None:
            match = args.options["filter-match"]
            declarations = env.match(match)
        elif args.options["filter"] is not None:
            names = [Name.from_str(each) for each in args.options["filter"].split(",")]
            declarations = env.only(names)
        else:
            declarations = env.all()

        max_fail = int(args.options["max-fail"] or "0")
        printer = Printer.from_str(args.options["print"], stdoutw)
        pp = printer.show if printer is not None else None

        check_start = time()
        try:
            for w_error in env.type_check(declarations, pp=pp):
                w_error.write_to(stderrw)
                failures += 1
                if 0 < max_fail <= failures:
                    break
        except:
            stderr.write("Unexpected error during type checking\n")
            raise
        check_elapsed = time() - check_start

        stderr.write(
            "parsed in %fs, checked in %fs\n"
            % (
                parse_elapsed,
                check_elapsed,
            ),
        )
    return 1 if failures else 0


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
)
def repl(self, args, stdin, stdout, stderr):
    stderrw = writer_from_arg(args.options["color"], stderr)

    (path,) = args.args
    try:
        environment = environment_from(path=path, stdin=stdin)
    except ExportError as err:
        stderrw.writeline(err.tokens())
        stderrw.write_plain("\n")
        return 1
    from rpylean import repl

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
    ],
)
def ffi(self, args, stdin, stdout, stderr):
    modules = args.varargs
    if not modules:
        return 1  # TODO: some default, maybe Init

    prefix = args.options["prefix"]
    if prefix is None:
        return 1  # TODO: some default, lean --print-prefix but RPython spawn??
    with FFI.from_prefix(prefix) as ffi:
        for name in modules:
            module = ffi.initialize_module(name)
            stdout.write("%s: %s\n" % (name, module))
    return 0


def environment_from(path, stdin):
    if path == "-":
        return from_export(fdopen_as_stream(stdin.fileno(), "r"))

    try:
        file = open_file_as_stream(path)
    except OSError as err:
        if err.errno != errno.ENOENT:
            raise
        raise UsageError("`%s` does not exist." % (path,))

    environment = from_export(file)
    file.close()
    return environment


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
