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
        return UsageError(TAGLINE + "\n" + USAGE % (executable,))


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
    def help(self, executable):
        raise UsageError(self.__doc__.strip("\n"))

    def usage_error(self, message):
        raise UsageError("%s\n\n%s" % (message, self.__doc__.strip("\n")))


class Check(Command):
    """
    Type check an exported Lean environment.

    USAGE:

        rpylean check EXPORT_FILE
    """

    name = "check"

    def run(self, args, stdout, stderr):
        if len(args) > 1:
            self.usage_error("unknown arguments: %s" % (args[1:]))

        lines = lines_from_path(args[0])
        environment = Environment.from_lines(lines)
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


class Dump(Command):
    """
    Dump an exported Lean environment.

    USAGE:

        rpylean dump EXPORT_FILE
    """

    name = "dump"

    def run(self, args, stdout, stderr):
        if len(args) > 1:
            self.usage_error("unknown arguments: %s" % (args[1:]))

        lines = lines_from_path(args[0])
        environment = Environment.from_lines(lines)
        environment.dump_pretty(stdout)
        return 0


COMMANDS = {Command.name: Command() for Command in [Check, Dump]}


def subcommand_from(argv):
    if len(argv) == 1 or argv[1] == "--help":
        raise UsageError.with_tagline(argv[0])

    command = COMMANDS.get(argv[1])
    if command is None:
        command, args = COMMANDS["check"], argv[1:]
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
