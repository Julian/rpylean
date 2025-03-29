from __future__ import print_function

import py

PATH = py.path.local(__file__).dirpath()


def export(name):
    """
    The lean4export for the example with the given name.
    """

    return PATH.join(name, "export").readlines()


def all_examples():
    examples = (
        each.basename
        for each in PATH.listdir()
        if each.join("export").isfile()
    )
    return sorted(export(name) for name in examples)
