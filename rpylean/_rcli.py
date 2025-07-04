"""
A mini-framework for CLIs in RPython.
"""
from rpython.rlib.rfile import create_stdio


class UsageError(Exception):
    def __init__(self, message, exit_code=1):
        self.message = message
        self.exit_code = exit_code

    def __str__(self):
        return self.message


class Command(object):
    def __init__(self, name, help, metavars, run):
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
        raise UsageError(message, exit_code=0)

    def usage_error(self, message):
        message = USAGE_ERROR % (
            message,
            self._help,
            self.name,
            " ".join(self._metavars),
        )
        raise UsageError(message)


class CLI(object):
    def __init__(self, tagline="", default=None, executable="rpylean"):
        self.executable = executable
        self.tagline = tagline
        self._default = default
        self._subcommands = {}

    def subcommand(self, metavars, help):
        short_help = help.strip().split("\n", 1)[0]

        def _subcommand(fn):
            name = fn.__name__
            assert name not in self._subcommands, name
            command = Command(name, help.strip("\n"), metavars, fn)
            self._subcommands[name] = (command, short_help)
            return command
        return _subcommand

    def parse(self, argv):
        if len(argv) == 1 or argv[1] == "--help":
            raise self.with_tagline(argv[0])

        command, _ = self._subcommands.get(argv[1], (None, None))
        if command is None:
            command, args = self._subcommands[self._default][0], argv[1:]
        else:
            args = argv[2:]

        if "--help" in args:
            raise command.help(argv[0])

        return command, args

    def main(self, argv, stdio=None):
        if stdio is None:
            stdio = create_stdio()
        stdin, stdout, stderr = stdio

        try:
            command, args = self.parse(argv)
            return command.run(args, stdin, stdout, stderr)
        except UsageError as error:
            stderr.write(error.__str__())
            stderr.write("\n")
            return error.exit_code
        return 0

    def usage(self, executable):
        return _USAGE % (executable,) + "\n".join(
            [
                "  %s: %s" % (k, v)
                for k, (_, v) in self._subcommands.items()
            ],
        )

    def with_tagline(self, executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m %s" % (self.executable,)
        return UsageError(
            self.tagline + "\n\n" + self.usage(executable),
            exit_code=0,
        )


_USAGE = """\
USAGE

  %s <subcommand> [<args>]

COMMANDS

"""
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
