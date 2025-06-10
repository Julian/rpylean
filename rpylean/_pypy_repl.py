"""
Load a bunch of useful stuff for poking at an environment at a PyPy REPL.

Expected to be used via `pypy -i`.
"""
from __future__ import print_function

import os

from rpylean.environment import from_export
from rpylean import objects as o  # noqa: F401

Name = o.Name
n = Name.simple

__example__ = os.environ.get("RPYLEAN_EXAMPLE", "")
if __example__:
    with open(__example__) as f:
        e = env = environment = from_export(f)
    del f
    print("Loaded `e = env = {!r}` from {!r}.".format(e, __example__))
else:
    Prop = o.W_LEVEL_ZERO.sort()
    Type = o.W_LEVEL_ZERO.succ().sort()

for k, v in sorted(locals().items()):
    if k.startswith("_") or k in {"os", "print", "print_function"}:
        continue
    print("{} = {!r}".format(k, v))
