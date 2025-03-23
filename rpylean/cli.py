"""
Execute ./rpylean-c <filename>
"""
from __future__ import print_function
import errno
import sys

from rpython.rlib.streamio import open_file_as_stream
from rpython.rlib.rfile import RFile, c_stderr

from rpylean.interpreter import interpret


def main(argv):
    if len(argv) != 2:
        print(__doc__)
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

    data = f.readall()
    f.close()
    interpret(data)
    return 0
