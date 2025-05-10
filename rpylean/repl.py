"""
Interactive REPL for rpylean.
"""
from rpython.rlib.rfile import create_stdio
import re

from rpylean.objects import W_TypeError, Name


def interact(env):
    stdin, stdout, stderr = create_stdio()

    while True:
        stdout.write("L∃∀N> ")
        input = stdin.readline()
        if not input:
            return

        input = input.strip()
        if not input:
            continue

        split = input.split(" ", 1)
        command = split[0]

        if command in ["d", "dump"]:
            env.dump_pretty(stdout)
        elif command in ["c", "check"]:
            if len(split) == 1:  # ok, all of them!
                env.type_check()
                stdout.write(
                    "Checked %d declarations.\n" % len(env.declarations),
                )
                continue

            name = Name.from_str(split[1])
            try:
                env.declarations[name].type_check(env.inference_context())
            except W_TypeError as error:
                stdout.write("Type error: %s\n" % error)
            else:
                stdout.write("%s correctly type checks.\n" % name.pretty())
        elif command in ["p", "print"]:
            name = split[1]
            stdout.write(env[name].pretty())
            stdout.write("\n")
        elif command in ["n", "names"]:
            names = env.names.values()
            if len(split) == 2:  # ok, all of them!
                arg = split[1].strip()
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
        else:
            stdout.write("Unknown command: %s\n" % command)
