import os.path

PATH = os.path.dirname(os.path.abspath(__file__))


def export(name):
    """
    The lean4export for the example with the given name.
    """

    path = os.path.join(os.path.join(PATH, name), "export")
    with open(path) as file:
        return file.read()
