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


_USAGE = """\
USAGE

  %s <subcommand> [<args>]

OPTIONS

  --help: Show this help message

COMMANDS

"""
COMMAND_USAGE = """\
%s

USAGE

  %s %s %s%s
"""
USAGE_ERROR = """\
%s

%s

USAGE

  rpylean %s %s
"""


class Command(object):
    def __init__(self, name, help, metavars, options, run, short_help=None):
        if short_help is None:
            short_help = help.strip().split("\n", 1)[0]

        self.name = name
        self.short_help = short_help
        self._help = help
        self._metavars = metavars
        self._options = dict(options)
        self._run = run

    def run(self, executable, args, stdin, stdout, stderr):
        expected, parsed_args, varargs = len(self._metavars), [], []
        options = {}
        for k in self._options:
            options[k] = None

        positional = []
        i = 0
        while i < len(args):
            arg = args[i]
            if arg.startswith("--"):
                opt = arg[2:]
                if opt == "help":
                    raise self.help(executable)
                if opt not in self._options:
                    self.usage_error("Unknown option: --%s" % opt)
                if i + 1 >= len(args) or args[i + 1].startswith("--"):
                    self.usage_error("Option --%s requires an argument" % opt)
                options[opt] = args[i + 1]
                i += 2
            else:
                positional.append(arg)
                i += 1

        if self._metavars and self._metavars[-1].startswith("*"):
            nfixed = expected = expected - 1
            assert nfixed >= 0

            if len(positional) > nfixed:
                parsed_args, varargs = positional[:nfixed], positional[nfixed:]
            else:
                parsed_args = positional
        else:
            if len(positional) > expected:
                self.usage_error("Unknown arguments: %s" % (positional[expected:],))
            parsed_args = positional

        if len(parsed_args) < expected:
            self.usage_error("Expected an %s" % (self._metavars[len(parsed_args)],))

        combined = Args(args=parsed_args, varargs=varargs, options=options)
        return self._run(self, combined, stdin, stdout, stderr)

    def help(self, executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m rpylean"
        options = [
            "  --%s: %s" % (opt, desc) for opt, desc in self._options.items()
        ]
        options.append("  --help: Show this help message")
        message = COMMAND_USAGE % (
            self._help,
            executable,
            self.name,
            " ".join(self._metavars),
            "\n\nOPTIONS\n\n%s" % "\n".join(options),
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
        self._commands = {}

    def subcommand(self, metavars, help, options=None):
        def _subcommand(fn):
            name = fn.__name__
            assert name not in self._commands, name
            command = self._commands[name] = Command(
                name=name,
                help=help.strip("\n"),
                metavars=metavars,
                options=options or [],
                run=fn,
            )
            return command
        return _subcommand

    def parse(self, argv):
        if len(argv) == 1 or argv[1] == "--help":
            raise self.with_tagline(argv[0])

        command = self._commands.get(argv[1])
        if command is None:
            command, args = self._commands[self._default], argv[1:]
        else:
            args = argv[2:]

        return command, args

    def main(self, argv, stdio=None):
        if stdio is None:
            stdio = create_stdio()
        stdin, stdout, stderr = stdio

        try:
            command, args = self.parse(argv)
            return command.run(argv[0], args, stdin, stdout, stderr)
        except UsageError as error:
            stderr.write(error.__str__())
            stderr.write("\n")
            return error.exit_code
        return 0

    def usage(self, executable):
        return _USAGE % (executable,) + "\n".join(
            [
                "  %s: %s" % (k, cmd.short_help)
                for k, cmd in self._commands.items()
            ],
        )

    def with_tagline(self, executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m %s" % (self.executable,)
        return UsageError(
            self.tagline + "\n\n" + self.usage(executable),
            exit_code=0,
        )


class Args(object):
    def __init__(self, args=None, varargs=None, options=None):
        self.args = args if args is not None else []
        self.varargs = varargs if varargs is not None else []
        self.options = options if options is not None else {}

    def __repr__(self):
        return "<Args {} varargs={} options={}>".format(
            self.args,
            self.varargs,
            self.options,
        )

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return vars(self) == vars(other)
