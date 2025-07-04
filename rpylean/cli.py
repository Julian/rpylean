"""
CLI for rpylean.
"""
from __future__ import print_function

import errno

from rpython.rlib.streamio import open_file_as_stream

from rpylean._rcli import CLI, UsageError
from rpylean import leanffi
from rpylean.environment import from_export
from rpylean.objects import Name


cli = CLI(
    tagline="A type checker for the Lean theorem prover.",
    default="check",
)


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Type check an exported Lean environment.",
)
def check(self, args, varargs, stdin, stdout, stderr):
    path, = args
    environment = environment_from(path=path, stdin=stdin)
    ncheck = len(varargs) or len(environment.declarations)
    stdout.write(
        "Checking %s declaration%s...\n" % (
            ncheck,
            "s" if ncheck != 1 else "",
        ),
    )

    succeeded = True
    if varargs:
        declarations = [
            environment.declarations[Name.from_str(each)]
            for each in varargs
        ]
        errors = environment.type_check(declarations)
    else:
        errors = environment.type_check()

    try:
        for w_error in errors:
            succeeded = False
            stderr.write(w_error.str())
            stderr.write("\n")
    except Exception as e:
        stderr.write("Unexpected error during type checking: %s\n" % (str(e),))
        return 2

    if not succeeded:
        return 1

    stdout.write("All declarations are type-correct.\n")
    return 0


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Dump an exported Lean environment or specific declarations from it.",
)
def dump(self, args, varargs, stdin, stdout, stderr):
    path, = args
    environment = environment_from(path=path, stdin=stdin)
    if varargs:
        for each in varargs:
            declaration = environment.declarations[Name.from_str(each)]
            stdout.write(environment.pretty(declaration))
            stdout.write("\n")
    else:
        environment.dump_pretty(stdout)
    return 0


@cli.subcommand(
    ["EXPORT_FILE"],
    help="Open a REPL with the given export's environment loaded into it.",
)
def repl(self, args, _, stdin, stdout, stderr):
    path, = args
    environment = environment_from(path=path, stdin=stdin)
    from rpylean import repl
    repl.interact(environment)
    return 0


@cli.subcommand(
    ["*MODULES"],
    help="Directly extract an environment via FFI to a real Lean toolchain.",
)
def ffi(self, _, varargs, stdin, stdout, stderr):
    modules = varargs
    if not modules:
        return 1  # TODO: some default, maybe Init
    with leanffi.initialize():
        for name in modules:
            result = leanffi.initialize_module(name)
            stdout.write("Module %s initialized (raw result: %s)\n" % (name, result))
        stdout.write("Would import modules via FFI: %s\n" % ", ".join(modules))
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
