"""
Regression tests against the hand-crafted Lean Kernel Arena fixtures
(``constlevels.ndjson``, ``nat-rec-rules.ndjson``, etc.).

The arena's tutorial archive is fetched by ``test_lka_tutorial``; the
focused regression tests live only in the arena's git tree. Set
``LKA_TESTS_DIR`` to a checkout of ``lean-kernel-arena/tests`` to run
these, or fall back to the conventional sibling location.

A test ships either as an export next to its description, or as Lean
source the arena builds into an export under ``_build/tests`` (``lka.py
build-test NAME``); a built export is picked up from there when present.
"""

from __future__ import print_function

import os

import pytest

import py

from rpylean.environment import from_export
from rpylean.exceptions import ExportError


_DEFAULT_PATH = py.path.local(__file__).dirpath().dirpath().dirpath().join(
    "lean-kernel-arena", "tests",
)
_ARENA = py.path.local(
    os.environ.get("LKA_TESTS_DIR", str(_DEFAULT_PATH)),
)


_BUILT = _ARENA.dirpath().join("_build", "tests")

#: The corpora, which take minutes and have their own harness.
_CORPORA = ["init-prelude", "init", "cedar", "std", "cslib", "mathlib"]


def _arena_cases():
    """Pairs of (ndjson path, expected outcome) from the arena ``tests/``."""
    if not _ARENA.isdir():
        return []
    cases = []
    for yaml in sorted(_ARENA.listdir("*.yaml")):
        if yaml.purebasename in _CORPORA:
            continue
        ndjson = yaml.new(ext=".ndjson")
        if not ndjson.isfile():
            ndjson = _BUILT.join(ndjson.basename)
            if not ndjson.isfile():
                continue
        outcome = None
        for line in yaml.readlines():
            line = line.strip()
            if line.startswith("outcome:"):
                outcome = line.split(":", 1)[1].strip()
                break
        if outcome in ("accept", "reject"):
            cases.append((ndjson, outcome))
    return cases


_CASES = _arena_cases()


# Tests known to fail today — see commit message / arena yaml description.
# Removing an entry here means the bug is fixed.
_XFAIL = {}


def _id(case):
    path, outcome = case
    return "%s[%s]" % (path.purebasename, outcome)


@pytest.mark.skipif(not _CASES,
                    reason="lean-kernel-arena tests/ not available "
                           "(set LKA_TESTS_DIR or check it out alongside)")
@pytest.mark.parametrize("case", _CASES, ids=_id)
def test_arena_outcome(case):
    path, outcome = case
    if path.purebasename in _XFAIL:
        pytest.xfail(_XFAIL[path.purebasename])
    try:
        environment = from_export(path.open())
    except ExportError:
        # Loading itself failed — that's also a reject.
        assert outcome == "reject"
        return
    errors = list(environment.type_check(environment.all()))
    if outcome == "accept":
        assert not errors, "expected accept but got %d errors" % len(errors)
    else:
        assert errors, "expected reject but checker accepted clean"
