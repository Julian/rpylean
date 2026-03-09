"""
Extra RPython standard library.

Could in theory move upstream if desired.
"""
from rpython.rlib.objectmodel import specialize


class count(object):
    """
    An equivalent of `itertools.count`.

    Especially useful because RPython does not support mutating
    global variables.
    """

    def __init__(self):
        self.count = 0

    def next(self):
        count, self.count = self.count, self.count + 1
        return count


def r_dict_eq(left, right):
    # r_dict doesn't define sane __eq__
    return (
        len(left) == len(right)
        and all(k in right and right[k] == v for k, v in left.iteritems())
    )


@specialize.call_location()
def plural(collection):
    """
    Dumb pluralization based on the length of the collection.
    """
    length = len(collection)
    return (length, "s" if length != 1 else "")


def warn(message):
    print("WARNING: %s" % (message,))
