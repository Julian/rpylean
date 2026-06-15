"""
Interactive REPL for rpylean.
"""

from __future__ import print_function
from rpython.rlib.rfile import create_stdio

from rpylean._rlib import rlineedit
from rpylean._tokens import (
    DEFAULT_THEME,
    ERROR,
    FORMAT_COLOR,
    PROMPT,
    TokenWriter,
    _ANSI_RESET,
)
from rpylean.environment import StreamTracer, TypeChecker
from rpylean.objects import Name


COMMANDS, HELP = {}, {}


class _Quit(Exception):
    """Raised by a command to unwind out of the REPL loop with an exit code."""

    _attrs_ = ['exit_code']

    def __init__(self, exit_code=0):
        self.exit_code = exit_code

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

    error = env.check_decl(declaration)
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
            error = env.check_decl(each)
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
    if declaration.w_kind.get_delta_reduce_target() is None:
        stderrw.write_plain("%s has no reducible value.\n" % name.str())
        return

    const = declaration.const_with_level_params()

    prev_tracer = env.tracer
    env.tracer = StreamTracer(stdoutw)
    try:
        const.whnf(TypeChecker(env, declaration))
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
            names = [name for name in names if name.depth() <= n]
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
    raise _Quit()


def dispatch(env, input, stdin, stdoutw, stderrw):
    """
    Run a single REPL command line, returning its exit code.

    The exit code is ``0`` if the command ran (regardless of what it did) or
    ``1`` if the command name was unknown. A ``quit``/``exit`` command instead
    raises ``_Quit``, whose ``exit_code`` carries the status to leave with.
    """
    split = input.split(" ", 1)
    command = split[0]
    fn = COMMANDS.get(command, None)
    if fn is None:
        stderrw.write_plain("Unknown command: %s\n" % command)
        return 1
    fn(env, split[1:], stdin, stdoutw, stderrw)
    return 0


PROMPT_TEXT = "L∃∀N> "


def _editor_prompt(editor):
    """
    Build the REPL prompt string for the line editor.

    Coloured the way the editor's library renders correctly: the editor
    injects the assembler (markers for GNU readline, inline escapes for libedit).
    """
    return editor.format_prompt(
        DEFAULT_THEME.get("prompt", ""), PROMPT_TEXT, _ANSI_RESET,
    )


class _ReplState(object):
    """Holds the active environment for the completion matcher.

    The matcher runs inside readline's C callback, which is a bare function,
    so the environment it completes against lives on this prebuilt singleton.
    """

    _attrs_ = ['env']

    def __init__(self):
        self.env = None


_state = _ReplState()


def _matching_completions(env, prefix):
    """Command names and public declaration names that start with ``prefix``.

    Computed lazily per TAB rather than materialised up front, so opening a
    REPL on a large environment (e.g. Mathlib) stays cheap.
    """
    result = []
    for name in COMMANDS:
        if name.startswith(prefix):
            result.append(name)
    for decl_name in env.declarations:
        if not decl_name.is_private:
            name_str = decl_name.str()
            if name_str.startswith(prefix):
                result.append(name_str)
    return result


def _complete(prefix):
    """The matcher injected into the line editor; reads the active env."""
    env = _state.env
    if env is None:
        return []
    return _matching_completions(env, prefix)


def interact(env):
    stdin, stdout, stderr = create_stdio()
    stdoutw = TokenWriter(stdout, FORMAT_COLOR)
    stderrw = TokenWriter(stderr, FORMAT_COLOR)

    editor = rlineedit.try_open()
    prompt = ""
    if editor is not None:
        prompt = _editor_prompt(editor)
        _state.env = env
        editor.enable_completion(_complete)
        editor.load_history()

    last = "help"

    while True:
        if editor is None:
            stdoutw.write([PROMPT.emit(PROMPT_TEXT)])
            stdoutw.flush()
            try:
                line = stdin.readline()
            except KeyboardInterrupt:
                continue
            if not line:
                return
        else:
            stdoutw.flush()
            stderrw.flush()
            try:
                maybe = editor.readline(prompt)
            except KeyboardInterrupt:
                continue
            if maybe is None:
                stdoutw.write_plain("\n")
                stdoutw.flush()
                editor.save_history()
                return
            line = maybe
            if line.strip():
                editor.add_history(line)

        input = line.strip()
        if not input:
            input = last

        last = input
        try:
            dispatch(env, input, stdin, stdoutw, stderrw)
        except _Quit:
            if editor is not None:
                editor.save_history()
            return
