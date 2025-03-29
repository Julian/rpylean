import py

PATH = py.path.local(__file__).dirpath()


def export(name):
    """
    The lean4export for the example with the given name.
    """

    return PATH.join(name, "export").read("rt")
