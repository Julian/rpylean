"""
Interactive REPL for rpylean.
"""
from rpython.rlib.rfile import create_stdio

from rpylean.objects import W_TypeError, Name


COMMANDS, HELP = {}, {}

def command(names, help=None):
    assert help is not None, names

    def _command(func):
        for name in names:
            assert name not in COMMANDS, "Duplicate command name: %r" % name
            COMMANDS[name] = func
        HELP[names[0]] = help
        return func
    return _command


@command(["dump", "d"], help="Dump the current environment.")
def dump(env, _, __, stdout, ___):
    env.dump_pretty(stdout)


@command(
    ["check", "c"],
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


@command(["print", "p"], help="Pretty print a declaration by name.")
def print_decl(env, args, _, stdout, __):
    name, = args
    stdout.write(env[name].pretty())
    stdout.write("\n")


@command(
    ["names", "n"],
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
