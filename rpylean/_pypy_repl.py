"""
Load a bunch of useful stuff for poking at an environment at a PyPy REPL.

Expected to be used via `pypy -i`.
"""
from __future__ import print_function

from pprint import pprint as pp  # noqa: F401
import os

from rpylean import objects as o  # noqa: F401
from rpylean.environment import from_export
from rpylean.leanffi import FFI  # noqa: F401

Name = o.Name
n = names = o.names


__example__ = os.environ.get("RPYLEAN_EXAMPLE", "")
if __example__:
    with open(__example__) as f:
        e = env = environment = from_export(f)
    del f
    print("Loaded `e = env = {!r}` from {!r}.".format(e, __example__))
else:
    Prop, Type = o.PROP, o.TYPE


def ffi():
    from subprocess import check_output
    prefix = check_output(["lean", "--print-prefix"]).strip()
    return FFI.from_prefix(prefix)


for k, v in sorted(locals().items()):
    if k.startswith("_") or k in {"os", "print", "pp", "print_function"}:
        continue
    print("{} = {!r}".format(k, v))
