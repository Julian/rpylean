"""
CLI for rpylean.
"""
from __future__ import print_function

import errno
import sys

from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.rfile import create_stdio

from rpylean import environment
from rpylean.objects import Name


TAGLINE = "A type checker for the Lean theorem prover."
SUBCOMMANDS = {}  # { name: short_help }


class UsageError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message

    @staticmethod
    def with_tagline(executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m rpylean"
        return UsageError(TAGLINE + "\n\n" + USAGE % (executable,))


def main(argv):
    stdin, stdout, stderr = create_stdio()

    try:
        command, args = subcommand_from(argv)
        return command.run(args, stdin, stdout, stderr)
    except UsageError as error:
        stderr.write(error.__str__())
        stderr.write("\n")
        return 1
    return 0


class Command(object):

    ALL = {}

    def __init__(self, name, help, metavars, run):
        assert name not in Command.ALL, name
        self.ALL[name] = self
        self.name = name
        self._help = help
        self._metavars = metavars
        self._run = run

    def run(self, args, stdin, stdout, stderr):
        expected, varargs = len(self._metavars), []

        if self._metavars and self._metavars[-1].startswith("*"):
            nfixed = expected = expected - 1
            assert nfixed >= 0

            if len(args) > nfixed:
                args, varargs = args[:nfixed], args[nfixed:]
        elif len(args) > expected:
            self.usage_error("Unknown arguments: %s" % (args[expected:]))

        if len(args) < expected:
            self.usage_error("Expected an %s" % (self._metavars[len(args)],))

        return self._run(self, args, varargs, stdin, stdout, stderr)

    def help(self, executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m rpylean"
        message = COMMAND_USAGE % (
            self._help,
            executable,
            self.name,
            " ".join(self._metavars),
        )
        raise UsageError(message)

    def usage_error(self, message):
        message = USAGE_ERROR % (
            message,
            self._help,
            self.name,
            " ".join(self._metavars),
        )
        raise UsageError(message)


def subcommand(metavars, help):
    short_help = help.strip().split("\n", 1)[0]

    def _subcommand(fn):
        name = fn.__name__
        SUBCOMMANDS[name] = short_help
        return Command(name, help.strip("\n"), metavars, fn)
    return _subcommand


@subcommand(
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

    if varargs:
        declarations = []
        for each in varargs:
            name = Name.from_str(each)
            declarations.append((name, environment.declarations[name]))
        result = environment.type_check(declarations)
    else:
        result = environment.type_check()

    for name, decl, w_error in result.invalid:
        stderr.write(
            "%s is not type-correct: %s\n" % (decl.pretty(), w_error.str())
        )

    if not result.succeeded():
        return 1

    stdout.write("All declarations are type-correct.\n")
    return 0


@subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Dump an exported Lean environment or specific declarations from it.",
)
def dump(self, args, varargs, stdin, stdout, stderr):
    path, = args
    environment = environment_from(path=path, stdin=stdin)
    if varargs:
        for each in varargs:
            declaration = environment.declarations[Name.from_str(each)]
            stdout.write(declaration.pretty())
            stdout.write("\n")
    else:
        environment.dump_pretty(stdout)
    return 0


@subcommand(
    ["EXPORT_FILE"],
    help="Open a REPL with the given export's environment loaded into it.",
)
def repl(self, args, _, stdin, stdout, stderr):
    path, = args
    environment = environment_from(path=path, stdin=stdin)
    from rpylean import repl
    repl.interact(environment)
    return 0


def subcommand_from(argv):
    if len(argv) == 1 or argv[1] == "--help":
        raise UsageError.with_tagline(argv[0])

    command = Command.ALL.get(argv[1])
    if command is None:
        command, args = Command.ALL["check"], argv[1:]
    else:
        args = argv[2:]

    if "--help" in args:
        raise command.help(argv[0])

    return command, args


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

    return environment.from_export(source.splitlines())


USAGE = """\
USAGE

  %s <subcommand> [<args>]

COMMANDS

""" + "\n".join("  %s: %s" % each for each in SUBCOMMANDS.items())
COMMAND_USAGE = """\
%s

USAGE

    %s %s %s
"""
USAGE_ERROR = """\
%s

%s

USAGE

  rpylean %s %s
"""


if __name__ == '__main__':
    sys.exit(main(sys.argv))
