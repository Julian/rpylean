"""
Load a bunch of useful stuff for poking at an environment at a PyPy REPL.

Expected to be used via `pypy -i`.
"""
from __future__ import print_function

import os

from rpylean.environment import Environment
from rpylean import objects as o
import rpylean

__example__ = os.environ.get("RPYLEAN_EXAMPLE", "")
if __example__:
    with open(__example__) as f:
        e = env = environment = Environment.from_lines(f)

    msg = "Loaded `e = env = {!r}` from {!r}."
    print(msg.format(e, __example__))
