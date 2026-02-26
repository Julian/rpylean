"""
Extra RPython standard library.

Could in theory move upstream if desired.
"""


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


def indent(text, prefix):
    """
    Indent lines in the text with the given prefix.
    """
    sep = "\n" + prefix
    return prefix + sep.join(text.splitlines())


def r_dict_eq(left, right):
    # r_dict doesn't define sane __eq__
    return (
        len(left) == len(right)
        and all(k in right and right[k] == v for k, v in left.iteritems())
    )


def warn(message):
    print("WARNING: %s" % (message,))
