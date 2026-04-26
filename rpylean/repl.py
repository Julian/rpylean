"""
Interactive REPL for rpylean.
"""

from __future__ import print_function
from rpython.rlib.rfile import create_stdio
import os

from rpylean._tokens import ERROR, FORMAT_COLOR, PROMPT, TokenWriter
from rpylean.environment import StreamTracer
from rpylean.objects import Name


COMMANDS, HELP = {}, {}

#: Either 0 or 1 arguments.
OPTIONAL = -2


def command(names, nargs=0, help=None):
    assert help is not None, "No help given for command %r" % names

    def _command(fn):
        assert names, "No names given for command %r" % fn.__name__
        HELP[names[0]] = help

        def wrapper(env, args, stdin, stdoutw, stderrw):
            """
            Run the command after checking the number of arguments.
            """
            if nargs == OPTIONAL:
                if len(args) > 1:
                    stderrw.write(
                        [
                            ERROR.emit(
                                "%s takes 0 or 1 arguments, got %d.\n"
                                % (
                                    names[0],
                                    len(args),
                                ),
                            ),
                        ],
                    )
                    return
            elif len(args) != nargs:
                stderrw.write(
                    [
                        ERROR.emit(
                            "%s takes %s arguments, got %d.\n"
                            % (
                                names[0],
                                nargs if nargs else "no",
                                len(args),
                            ),
                        ),
                    ],
                )
                return

            return fn(env, args, stdin, stdoutw, stderrw)

        for name in names:
            assert name not in COMMANDS, "Duplicate command name: %r" % name
            COMMANDS[name] = wrapper

        return wrapper

    return _command


@command(["dump", "d"], help="Dump the current environment.")
def dump(env, _, __, stdoutw, ___):
    for each in env.public():
        stdoutw.writeline(each.tokens(env.declarations))


@command(
    ["check", "c"],
    nargs=OPTIONAL,
    help=("Type check a declaration by name, or all declarations if no name is given."),
)
def check(env, args, _, stdoutw, stderrw):
    if not args:
        succeeded, result = True, env.type_check(env.all())
        for w_error in result:
            succeeded = False
            w_error.write_to(stderrw)
        if succeeded:
            stdoutw.write_plain(
                "Checked %d declarations.\n" % len(env.declarations),
            )
        return

    name = Name.from_str(args[0])
    declaration = env.declarations.get(name, None)
    if declaration is None:
        stderrw.write_plain("%s does not exist in the environment.\n" % name.str())
        return

    error = declaration.type_check(env)
    if error is None:
        stdoutw.write_plain("%s correctly type checks.\n" % name.str())
    else:
        error.write_to(stdoutw)


@command(
    ["first", "f"],
    help="Find the first declaration which does not type check.",
)
def first(env, _, __, stdoutw, stderrw):
    for each in env.declarations.values():
        try:
            error = each.type_check(env)
        except Exception as error:
            stderrw.write_plain(
                "Unexpected error when checking %s: %s\n"
                % (
                    each.name.str(),
                    error,
                ),
            )
            return
        if error is not None:
            error.write_to(stdoutw)
            return
    stdoutw.write_plain("All declarations type check.\n")


@command(["print", "p"], nargs=1, help="Pretty print a declaration by name.")
def print_decl(env, args, _, stdoutw, stderrw):
    name = Name.from_str(args[0])
    declaration = env.declarations.get(name, None)
    if declaration is None:
        stderrw.write_plain("%s does not exist in the environment.\n" % name.str())
        return
    stdoutw.writeline(declaration.tokens(env.declarations))


@command(
    ["reduce", "r"],
    nargs=1,
    help="Step through WHNF reduction of a declaration's value.",
)
def reduce_decl(env, args, _, stdoutw, stderrw):
    name = Name.from_str(args[0])
    declaration = env.declarations.get(name, None)
    if declaration is None:
        stderrw.write_plain("%s does not exist in the environment.\n" % name.str())
        return
    target = declaration.w_kind.get_delta_reduce_target()
    if target is None:
        stderrw.write_plain("%s has no reducible value.\n" % name.str())
        return

    prev_tracer = env.tracer
    env.tracer = StreamTracer(stdoutw)
    try:
        target.whnf(env)
    finally:
        env.tracer = prev_tracer


@command(
    ["names", "n"],
    nargs=OPTIONAL,
    help=(
        "Show all non-private names in the environment, "
        "or those matching a prefix or length."
    ),
)
def names(env, args, stdin, stdoutw, stderrw):
    names = env.declarations.keys()
    if not args:
        names = [name for name in names if not name.is_private]
    elif len(args) == 1:
        arg = args[0].strip()
        if arg.isdigit():  # all names with at most `n` components
            n = int(arg)
            names = [name for name in names if len(name.components) <= n]
        else:  # all names starting with the given prefix
            names = [name for name in names if name.str().startswith(arg)]

    for name in names:
        stdoutw.writeline(name.tokens(env.declarations))


@command(["help", "commands", "?"], help="Show the available REPL commands.")
def help(_, __, ___, stdoutw, ____):
    for command, doc in HELP.items():
        stdoutw.write_plain(command)
        stdoutw.write_plain(": ")
        stdoutw.write_plain(doc)
        stdoutw.write_plain("\n")


@command(["exit", "quit"], help="Quit the REPL.")
def quit(*args):
    os._exit(0)


def interact(env):
    stdin, stdout, stderr = create_stdio()
    stdoutw = TokenWriter(stdout, FORMAT_COLOR)
    stderrw = TokenWriter(stderr, FORMAT_COLOR)

    last = "help"

    while True:
        stdoutw.write([PROMPT.emit("L∃∀N> ")])
        try:
            input = stdin.readline()
        except KeyboardInterrupt:
            continue

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
        fn(env, split[1:], stdin, stdoutw, stderrw)
