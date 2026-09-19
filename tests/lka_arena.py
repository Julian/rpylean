"""
The hand-crafted Lean Kernel Arena fixtures, wherever they are.

Set ``LKA_TESTS_DIR`` to a checkout of ``lean-kernel-arena/tests``, or
fall back to the conventional sibling location.

A test ships either as an export next to its description, or as Lean
source the arena builds into an export under ``_build/tests`` (``lka.py
build-test NAME``); a built export is picked up from there when present.
"""

import os

import py


_DEFAULT_PATH = py.path.local(__file__).dirpath().dirpath().dirpath().join(
    "lean-kernel-arena", "tests",
)
_ARENA = py.path.local(
    os.environ.get("LKA_TESTS_DIR", str(_DEFAULT_PATH)),
)


_BUILT = _ARENA.dirpath().join("_build", "tests")

#: The corpora, which take minutes and have their own harness.
_CORPORA = ["init-prelude", "init", "cedar", "std", "cslib", "mathlib"]


def cases():
    """
    Triples of (name, ndjson path, expected outcome) from the arena
    ``tests/``, whose subdirectories group tests (``perf/app-lam``).
    """
    if not _ARENA.isdir():
        return []
    cases = []
    for yaml in sorted(_ARENA.visit("*.yaml")):
        name = yaml.relto(_ARENA)[:-len(".yaml")]
        if name in _CORPORA:
            continue
        ndjson = yaml.new(ext=".ndjson")
        if not ndjson.isfile():
            ndjson = _BUILT.join(name + ".ndjson")
            if not ndjson.isfile():
                continue
        outcome = None
        for line in yaml.readlines():
            line = line.strip()
            if line.startswith("outcome:"):
                outcome = line.split(":", 1)[1].strip()
                break
        if outcome in ("accept", "reject", "either"):
            cases.append((name, ndjson, outcome))
    return cases
