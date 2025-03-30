from __future__ import print_function
import errno

from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.rfile import RFile, c_stderr

from rpylean.interpreter import interpret


def main(argv):
    if len(argv) != 2:
        print("Run %s <export-file>." % (argv[0],))
        return 1

    path = argv[1]
    try:
        f = open_file_as_stream(path)
    except OSError as err:
        if err.errno != errno.ENOENT:
            raise
        stderr = RFile(c_stderr(), close2=(None, None))
        stderr.write("%s does not exist.\n" % (path,))
        return 1

    try:
        interpret(f.readall().splitlines())
    finally:
        f.close()
    return 0
