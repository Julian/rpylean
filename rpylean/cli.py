"""
CLI for rpylean.
"""
from __future__ import print_function

import errno
import sys

from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.rfile import RFile, c_stderr, c_stdout

from rpylean.environment import Environment


TAGLINE = "A type checker for the Lean theorem prover."
USAGE = """\
USAGE

  %s <subcommand> [<args>]

COMMANDS

  check: type check a given file
  dump: parse an export file and simply dump its contents
  repl: load an export file into an interactive REPL
""".rstrip("\n")


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
    stdout = RFile(c_stdout(), close2=(None, None))
    stderr = RFile(c_stderr(), close2=(None, None))

    try:
        command, args = subcommand_from(argv)
        return command.run(args, stdout, stderr)
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

    def run(self, args, stdout, stderr):
        expected = len(self._metavars)
        if len(args) > expected:
            self.usage_error("Unknown arguments: %s" % (args[expected:]))
        elif len(args) < expected:
            self.usage_error("Expected an %s" % (self._metavars[len(args)],))

        return self._run(self, args, stdout, stderr)

    def help(self, executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m rpylean"
        message = """\
        %s

        USAGE

          %s %s %s
        """ % (self._help, executable, self.name, " ".join(self._metavars))
        raise UsageError(message)

    def usage_error(self, message):
        message = """\
        %s

        %s

        USAGE

          rpylean %s %s
        """ % (message, self._help, self.name, " ".join(self._metavars))
        raise UsageError(message)


def subcommand(metavars):
    def _subcommand(fn):
        name = fn.__name__
        help = fn.__doc__.strip("\n")
        return Command(name, help, metavars, fn)
    return _subcommand


@subcommand(["EXPORT_FILE"])
def check(self, args, stdout, stderr):
    """
    Type check an exported Lean environment.
    """
    path, = args
    environment = Environment.from_lines(lines_from_path(path))
    stdout.write("Checking %s declarations...\n" % (len(environment.declarations)))

    result = environment.type_check()

    for name, decl, w_error in result.invalid:
        stderr.write("%s is not type-correct: %s\n" % (
            name.pretty(),
            w_error.__str__()),
        )

    if not result.succeeded():
        return 1

    stdout.write("All declarations are type-correct.\n")
    return 0


@subcommand(["EXPORT_FILE"])
def dump(self, args, stdout, stderr):
    """
    Dump an exported Lean environment.
    """
    path, = args
    environment = Environment.from_lines(lines_from_path(path))
    environment.dump_pretty(stdout)
    return 0


@subcommand(["EXPORT_FILE"])
def repl(self, args, stdout, stderr):
    """
    Open a REPL with the environment loaded from the given export.
    """
    path, = args
    environment = Environment.from_lines(lines_from_path(path))
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


def lines_from_path(path):
    try:
        file = open_file_as_stream(path)
    except OSError as err:
        if err.errno != errno.ENOENT:
            raise
        raise UsageError("`%s` does not exist." % (path,))

    lines = file.readall().splitlines()
    file.close()
    return lines


if __name__ == '__main__':
    import sys
    sys.exit(main(sys.argv))
