"""
CLI for rpylean.
"""

from __future__ import print_function
from rpylean.parser import ExportVersionError

import errno

from rpython.rlib.streamio import fdopen_as_stream, open_file_as_stream

from rpylean._rcli import CLI, UsageError
from rpylean.leanffi import FFI
from rpylean.environment import StreamTracer, from_export
from rpylean.objects import Name


cli = CLI(
    tagline="A type checker for the Lean theorem prover.",
    default="check",
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
            "only check declarations whose name contains this substring",
        ),
        (
            "max-heartbeat",
            "maximum number of def_eq calls per declaration before giving up",
        ),
    ],
    flags=[
        (
            "trace",
            "enable tracing some def eq and reduction steps",
            "",
            "yes",  # we can't use StreamTracer here, thanks static typing
        ),
        (
            "verbose",
            "print each declaration name to stderr as it is checked",
            "",
            "yes",
        ),
    ],
)
def check(self, args, stdin, stdout, stderr):
    for path in args.varargs:
        try:
            environment = environment_from(path=path, stdin=stdin)
        except ExportVersionError as err:
            stderr.write(err.__str__())
            stderr.write("\n")
            return 1

        if args.options["trace"]:
            environment.tracer = StreamTracer(stderr)

        max_heartbeat = int(args.options["max-heartbeat"] or "0")
        if max_heartbeat > 0:
            environment.max_heartbeat = max_heartbeat

        name_filter = args.options["filter"]
        if name_filter is not None:
            declarations = environment.filter_declarations(name_filter)
        else:
            declarations = None

        suffix = "" if len(args.varargs) == 1 else " from %s" % (path,)
        if declarations is None:
            n = len(environment.declarations)
            stdout.write(
                "Checking %s declaration%s%s…\n" % (n, "s" if n != 1 else "", suffix),
            )
        else:
            stdout.write(
                "Checking declarations matching '%s'%s…\n" % (name_filter, suffix),
            )

        failures, max_fail = 0, int(args.options["max-fail"] or "0")
        verbose = args.options["verbose"]

        try:
            for w_error in environment.type_check(
                declarations,
                verbose=verbose,
                progress=stderr,
            ):
                stderr.write(w_error.str())
                stderr.write("\n")

                failures += 1
                if 0 < max_fail <= failures:
                    break
        except Exception:
            stderr.write("Unexpected error during type checking\n")
            raise

        if failures:
            return 1

    stdout.write("All declarations are type-correct.\n")
    return 0


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Dump an exported Lean environment or specific declarations from it.",
)
def dump(self, args, stdin, stdout, stderr):
    (path,) = args.args
    environment = environment_from(path=path, stdin=stdin)
    if args.varargs:
        for each in args.varargs:
            declaration = environment.declarations[Name.from_str(each)]
            environment.print(declaration, stdout)
    else:
        environment.dump_pretty(stdout)
    return 0


@cli.subcommand(
    ["EXPORT_FILE"],
    help="Open a REPL with the given export's environment loaded into it.",
)
def repl(self, args, stdin, stdout, stderr):
    (path,) = args.args
    environment = environment_from(path=path, stdin=stdin)
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


if __name__ == "__main__":
    import sys

    sys.exit(cli.main(sys.argv))
