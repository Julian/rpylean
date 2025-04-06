"""
CLI for rpylean.
"""
from __future__ import print_function

import errno

from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.rfile import RFile, c_stderr

from rpylean.interpreter import interpret


USAGE = """
%s EXPORT_FILE
""".rstrip("\n")


class UsageError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message

    @staticmethod
    def with_message(message, executable):
        if executable.endswith("__main__.py"):
            executable = "pypy -m rpylean"
        usage = USAGE % (executable,)
        return UsageError("%s, run:\n%s" % (message, usage))


def main(argv):
    try:
        lines = parse_args(argv)
    except UsageError as error:
        stderr = RFile(c_stderr(), close2=(None, None))
        stderr.write(error.__str__())
        stderr.write("\n")
        return 1

    interpret(lines)
    return 0


def parse_args(argv):
    if len(argv) != 2:
        raise UsageError.with_message("Wrong number of arguments", argv[0])

    path = argv[1]
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
