"""
Interactive REPL for rpylean.
"""
from rpython.rlib.rfile import create_stdio


def interact(environment):
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
            environment.dump_pretty(stdout)
        elif command in ["p", "print"]:
            name = split[1]
            stdout.write(environment[name].pretty())
            stdout.write("\n")
        elif command in ["n", "names"]:
            for name in environment.names.values():
                stdout.write(name.pretty())
                stdout.write("\n")
        else:
            stdout.write("Unknown command: %s\n" % command)
