"""
CLI for rpylean.
"""
from __future__ import print_function

import errno

from rpython.rlib.streamio import open_file_as_stream

from rpylean._rcli import CLI, UsageError
from rpylean.leanffi import FFI
from rpylean.environment import from_export
from rpylean.objects import Name


cli = CLI(
    tagline="A type checker for the Lean theorem prover.",
    default="check",
)


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Type check an exported Lean environment.",
    options=[
        (
            "max-fail",
            "the maximum number of type errors to report before giving up",
        ),
    ],
)
def check(self, args, stdin, stdout, stderr):
    path, = args.args
    environment = environment_from(path=path, stdin=stdin)
    ncheck = len(args.varargs) or len(environment.declarations)
    stdout.write(
        "Checking %s declaration%s...\n" % (
            ncheck,
            "s" if ncheck != 1 else "",
        ),
    )

    failures, max_fail = 0, int(args.options["max-fail"])
    if args.varargs:
        declarations = [
            environment.declarations[Name.from_str(each)]
            for each in args.varargs
        ]
        errors = environment.type_check(declarations)
    else:
        errors = environment.type_check()

    try:
        for w_error in errors:
            stderr.write(w_error.str())
            stderr.write("\n")

            failures += 1
            if failures >= max_fail:
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
    path, = args.args
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
    path, = args.args
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
            "path to the Lean prefix to link against "
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
    # FIXME: lazify me!

    if path == "-":
        source = stdin.read()
        stdin.close()
    else:
        try:
            file = open_file_as_stream(path)
        except OSError as err:
            if err.errno != errno.ENOENT:
                raise
            raise UsageError("`%s` does not exist." % (path,))
        source = file.readall()
        file.close()

    return from_export(source.splitlines())


if __name__ == '__main__':
    import sys
    sys.exit(cli.main(sys.argv))
