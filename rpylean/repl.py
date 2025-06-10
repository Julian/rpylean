"""
Interactive REPL for rpylean.
"""
from rpython.rlib.rfile import create_stdio
import os

from rpylean.objects import W_TypeError, Name


COMMANDS, HELP = {}, {}

#: Either 0 or 1 arguments.
OPTIONAL = -2

def command(names, nargs=0, help=None):
    assert help is not None, "No help given for command %r" % names

    def _command(fn):
        assert names, "No names given for command %r" % fn.__name__
        HELP[names[0]] = help

        def wrapper(env, args, stdin, stdout, stderr):
            """
            Run the command after checking the number of arguments.
            """
            if nargs == OPTIONAL:
                if len(args) > 1:
                    stderr.write(
                        "%s takes 0 or 1 arguments, got %d.\n" % (
                            names[0],
                            len(args),
                        ),
                    )
                    return
            elif len(args) != nargs:
                stderr.write(
                    "%s takes %s arguments, got %d.\n" % (
                        names[0],
                        nargs if nargs else "no",
                        len(args),
                    ),
                )
                return

            return fn(env, args, stdin, stdout, stderr)

        for name in names:
            assert name not in COMMANDS, "Duplicate command name: %r" % name
            COMMANDS[name] = wrapper

        return wrapper
    return _command


@command(["dump", "d"], help="Dump the current environment.")
def dump(env, _, __, stdout, ___):
    env.dump_pretty(stdout)


@command(
    ["check", "c"],
    nargs=OPTIONAL,
    help=(
        "Type check a declaration by name, "
        "or all declarations if no name is given."
    ),
)
def check(env, args, _, stdout, __):
    if not args:  # ok, all of them!
        env.type_check()
        stdout.write(
            "Checked %d declarations.\n" % len(env.declarations),
        )
        return

    name = Name.from_str(args[0])
    declaration = env.declarations[name]
    try:
        declaration.type_check(env)
    except W_TypeError as error:
        stdout.write("Type error: %s\n" % error)
    else:
        stdout.write("%s correctly type checks.\n" % name.pretty())


@command(["print", "p"], nargs=1, help="Pretty print a declaration by name.")
def print_decl(env, args, _, stdout, __):
    name, = args
    stdout.write(env[name].pretty())
    stdout.write("\n")


@command(
    ["names", "n"],
    nargs=OPTIONAL,
    help=(
        "Show all names in the environment, "
        "or those matching a prefix or length."
    ),
)
def names(env, args, stdin, stdout, stderr):
    names = env.declarations.keys()
    if len(args) == 1:  # ok, all of them!
        arg = args[0].strip()
        if arg.isdigit():  # all names with at most `n` components
            n = int(arg)
            names = [
                name for name in names if len(name.components) <= n
            ]
        else:              # all names starting with the given prefix
            names = [
                name for name in names if name.pretty().startswith(arg)
            ]

    for name in names:
        stdout.write(name.pretty())
        stdout.write("\n")


@command(["help", "commands", "?"], help="Show the available REPL commands.")
def help(_, __, ___, stdout, ____):
    for command, doc in HELP.items():
        stdout.write(command)
        stdout.write(": ")
        stdout.write(doc)
        stdout.write("\n")


def interact(env):
    stdin, stdout, stderr = create_stdio()

    last = "help"

    while True:
        stdout.write("L∃∀N> ")
        input = stdin.readline()
        if not input:
            return

        input = input.strip()
        if not input:
            input = last

        last = input

        split = input.split(" ", 1)
        command = split[0]

        fn = COMMANDS.get(command, None)
        if fn is None:
            stderr.write("Unknown command: %s\n" % command)
            continue
        fn(env, split[1:], stdin, stdout, stderr)
