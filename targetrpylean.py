#!/usr/bin/env python
"""RPython translation target for rpylean."""

from __future__ import print_function

import subprocess
import sys

import py

from rpylean.cli import cli
import rpylean


# Floor the GC nursery to 32 MB.
#
# Type-checking allocates aggressively (intermediate W_App / W_Lambda from
# WHNF, dict resizes in the def_eq cache); on cache-fit-tuned defaults
# minor GCs dominate measured time. A 32 MB nursery cuts wall time ~29% on
# our benchmarks vs the 4 MB auto-estimate, and plateaus from there.
#
# We patch `estimate_best_nursery_size` rather than disabling auto-sizing
# entirely so that:
#   - Machines where the estimate already exceeds 32 MB are unaffected
#     (Intel servers with big L3 caches still get their L3/2 nursery).
#   - `PYPY_GC_NURSERY` still overrides everything (env var path is
#     consulted before estimate is called).
#   - The estimate-failure fallback (TRANSLATION_PARAMS["nursery_size"])
#     is untouched.
#
# `incminimark.py` imports `env` as a module and looks up
# `env.estimate_best_nursery_size` dynamically at call time, so replacing
# the module attribute here (before translation) takes effect in the
# translated binary.
from rpython.memory.gc import env as _gc_env

_RPYLEAN_NURSERY_FLOOR = 32 * 1024 * 1024
_unfloored_estimate = _gc_env.estimate_best_nursery_size


def _floored_estimate_best_nursery_size():
    n = _unfloored_estimate()
    if n > 0 and n < _RPYLEAN_NURSERY_FLOOR:
        return _RPYLEAN_NURSERY_FLOOR
    return n


_gc_env.estimate_best_nursery_size = _floored_estimate_best_nursery_size


def git(*argv):
    cmd = ["git"]
    cmd.extend(argv)
    return subprocess.check_output(cmd, stderr=subprocess.PIPE)


try:
    result = git("describe", "--always", "HEAD")
except (subprocess.CalledProcessError, OSError):
    git_version = "unknown"
else:
    git_version = result.decode("utf-8").strip()
    if git("status", "--porcelain"):
        git_version += "+dirty"


VERSION_TEMPLATE = """\
# Auto-generated during translation - do not edit manually
__version__ = "%s"
"""
VERSION_FILE = py.path.local(rpylean.__file__).dirpath().join("_version.py")
VERSION_FILE.write_binary(VERSION_TEMPLATE % (git_version,))
print(
    "Updated %s with version: %s" % (VERSION_FILE, git_version,),
    file=sys.stderr,
)


def main(argv):
    return cli.main(argv)


def target(driver, args):
    driver.exe_name = "rpylean-%(backend)s"
    return main
