from __future__ import print_function

import py

PATH = py.path.local(__file__).dirpath()


def export(name):
    """
    The lean4export for the example with the given name.
    """

    return PATH.join(name, "export").readlines()


def all_examples_from_dir(example_dir):

    examples = (
        each.join("export")
        for each in PATH.join(example_dir).listdir()
        if each.join("export").isfile()
    )

    return sorted(examples)


def all_valid_examples():
    return all_examples_from_dir("valid")

def all_invalid_examples():
    return all_examples_from_dir("invalid")
