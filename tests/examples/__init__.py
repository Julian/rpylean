from __future__ import print_function

import py


EXAMPLES = py.path.local(__file__).dirpath()


def all_examples_from(example_dir):
    for each in example_dir.listdir():
        export = each.join("export")
        if export.isfile():
            yield export


VALID = sorted(all_examples_from(EXAMPLES.join("valid")))
# INVALID = sorted(all_examples_from(EXAMPLES.join("invalid")))


def name_of(example_path):
    """
    tests/valid/Foo/export -> Foo
    """
    return example_path.dirpath().basename
