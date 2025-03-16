"""
Execute ./rpylean-c <filename>
"""

from rpython.rlib.streamio import open_file_as_stream

from rpylean.interpreter import interpret


def entry_point(argv):
    if not len(argv) == 2:
        print __doc__
        return 1
    f = open_file_as_stream(argv[1])
    data = f.readall()
    f.close()
    interpret(data)
    return 0


def target(*args):
    return entry_point


if __name__ == "__main__":
    import sys
    entry_point(sys.argv)
