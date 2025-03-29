import os

PATH = os.path.dirname(os.path.abspath(__file__))


examples_dirs = [
    d
    for d in os.listdir(PATH)
    if os.path.isdir(os.path.join(PATH, d)) and not d.startswith("__")
]


def export(name):
    """
    The lean4export for the example with the given name.
    """

    path = os.path.join(os.path.join(PATH, name), "export")
    with open(path) as file:
        return file.read()
