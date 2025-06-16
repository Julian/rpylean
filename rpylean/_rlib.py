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
