"""
CLI for rpylean.
"""

from __future__ import print_function

from time import time
import errno

from rpython.rlib.objectmodel import specialize
from rpython.rlib.streamio import fdopen_as_stream, open_file_as_stream

from rpylean._rcli import CLI, UsageError
from rpylean.leanffi import FFI
from rpylean.environment import StreamTracer, from_export
from rpylean.objects import Name
from rpylean.parser import ExportVersionError


cli = CLI(
    tagline="A type checker for the Lean theorem prover.",
    default="check",
)


@cli.subcommand(
    ["*EXPORT_FILES"],
    help="Type check an exported Lean environment.",
    options=[
        (
            "max-fail",
            "the maximum number of type errors to report before giving up",
        ),
        (
            "filter",
            "only check the given declaration(s), separated by commas",
        ),
        (
            "filter-match",
            "only check declarations whose name contains this substring",
        ),
        (
            "max-heartbeat",
            "maximum number of def_eq calls per declaration before giving up",
        ),
        (
            "print", (
                "print something for each declaration (valid values are "
                "name|dots|decls|declarations|all)"
            ),
        ),
    ],
    flags=[
        (
            "trace",
            "enable tracing some def eq and reduction steps",
            "",
            "yes",  # we can't use StreamTracer here, thanks static typing
        ),
    ],
)
def check(self, args, stdin, stdout, stderr):
    failures = 0
    for path in args.varargs:
        start = time()
        try:
            env = environment_from(path=path, stdin=stdin)
        except ExportVersionError as err:
            stderr.write(err.__str__())
            stderr.write("\n")
            return 1
        parse_elapsed = time() - start

        if args.options["trace"]:
            env.tracer = StreamTracer(stderr)

        max_heartbeat = int(args.options["max-heartbeat"] or "0")
        if max_heartbeat > 0:
            env.max_heartbeat = max_heartbeat

        if args.options["filter-match"] is not None:
            match = args.options["filter-match"]
            suffix = "declarations matching %s" % (match,)
            declarations = env.match(match)
        elif args.options["filter"] is not None:
            names = [
                Name.from_str(each)
                for each in args.options["filter"].split(",")
            ]
            suffix = "%s declaration%s" % s(names)
            declarations = env.only(names)
        else:
            suffix = "%s declaration%s" % s(env.declarations)
            declarations = None

        stdout.write(
            "Checking %s%s…\n" % (
                suffix,
                "" if len(args.varargs) == 1 else " from %s" % (path,),
            ),
        )

        max_fail = int(args.options["max-fail"] or "0")
        pp = Printer.from_str(args.options["print"], stderr)

        check_start = time()
        try:
            for w_error in env.type_check(declarations, pp=pp):
                stderr.write(w_error.str())
                stderr.write("\n")

                failures += 1
                if 0 < max_fail <= failures:
                    break
        except:
            stderr.write("Unexpected error during type checking\n")
            raise
        check_elapsed = time() - check_start

        stderr.write(
            "parsed in %fs, checked in %fs\n" % (
                parse_elapsed,
                check_elapsed,
            ),
        )

    if args.varargs:
        stdout.write("All declarations are type-correct.\n")
    return 1 if failures else 0


@cli.subcommand(
    ["EXPORT_FILE", "*DECLS"],
    help="Dump an exported Lean environment or specific declarations from it.",
)
def dump(self, args, stdin, stdout, stderr):
    (path,) = args.args
    environment = environment_from(path=path, stdin=stdin)
    if args.varargs:
        for each in args.varargs:
            declaration = environment.declarations[Name.from_str(each)]
            environment.print(declaration, stdout)
    else:
        environment.dump_pretty(stdout)
    return 0


@cli.subcommand(
    ["EXPORT_FILE"],
    help="Open a REPL with the given export's environment loaded into it.",
)
def repl(self, args, stdin, stdout, stderr):
    (path,) = args.args
    environment = environment_from(path=path, stdin=stdin)
    from rpylean import repl

    repl.interact(environment)
    return 0


@cli.subcommand(
    ["*MODULES"],
    help="Directly extract an environment via FFI to a real Lean toolchain.",
    options=[
        (
            "prefix",
            "path to the Lean prefix to link against ",
            # TODO: "[default: `lean --print-prefix`]",
        ),
    ],
)
def ffi(self, args, stdin, stdout, stderr):
    modules = args.varargs
    if not modules:
        return 1  # TODO: some default, maybe Init

    prefix = args.options["prefix"]
    if prefix is None:
        return 1  # TODO: some default, lean --print-prefix but RPython spawn??
    with FFI.from_prefix(prefix) as ffi:
        for name in modules:
            module = ffi.initialize_module(name)
            stdout.write("%s: %s\n" % (name, module))
    return 0


def environment_from(path, stdin):
    if path == "-":
        return from_export(fdopen_as_stream(stdin.fileno(), "r"))

    try:
        file = open_file_as_stream(path)
    except OSError as err:
        if err.errno != errno.ENOENT:
            raise
        raise UsageError("`%s` does not exist." % (path,))

    environment = from_export(file)
    file.close()
    return environment


class Printer(object):
    def __init__(self, format, stream):
        self.format = format
        self.stream = stream

    def print(self, env, decl):
        output = self.format(env, decl)
        if output:
            self.stream.write(output)

    @staticmethod
    def from_str(pp_str, stream):
        if pp_str == "all" or pp_str == "decls" or pp_str == "declarations":
            def pp(env, decl):
                return "%s\n" % (env.pretty(decl),)
        elif pp_str == "name" or pp_str == "names":
            def pp(env, decl):
                return "%s\n" % (env.pretty(decl.name),)
        elif pp_str == "dots":
            def pp(env, decl):
                return "." # FIXME: if error is None else "E"
        elif pp_str is None or pp_str == "none":
            return None
        else:
            raise UsageError("Unknown pretty print choice: %s" % (pp_str,))
        return Printer(format=pp, stream=stream).print


@specialize.call_location()
def s(collection):
    """
    Dumb pluralization based on the length of the collection.
    """
    length = len(collection)
    return (length, "s" if length != 1 else "")


if __name__ == "__main__":
    import sys

    sys.exit(cli.main(sys.argv))
