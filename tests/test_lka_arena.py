"""
Regression tests against the hand-crafted Lean Kernel Arena fixtures
(``constlevels.ndjson``, ``nat-rec-rules.ndjson``, etc.).

The arena's tutorial archive is fetched by ``test_lka_tutorial``; the
focused regression tests live only in the arena's git tree (see
``tests.lka_arena`` for where they are looked for).

A test whose outcome is ``either`` may be accepted or rejected, but
must be decided.

The ``perf/`` tests nest terms deeper than an untranslated run's host
stack goes, and are run against the translated binary instead.
"""

from __future__ import print_function

import pytest

from rpylean.environment import from_export
from rpylean.exceptions import ExportError
from tests import lka_arena


_CASES = [
    each for each in lka_arena.cases() if not each[0].startswith("perf/")
]


# Tests known to fail today — see commit message / arena yaml description.
# Removing an entry here means the bug is fixed.
_XFAIL = {}


def _id(case):
    name, _, outcome = case
    return "%s[%s]" % (name, outcome)


@pytest.mark.skipif(not _CASES,
                    reason="lean-kernel-arena tests/ not available "
                           "(set LKA_TESTS_DIR or check it out alongside)")
@pytest.mark.parametrize("case", _CASES, ids=_id)
def test_arena_outcome(case):
    name, path, outcome = case
    if name in _XFAIL:
        pytest.xfail(_XFAIL[name])
    try:
        environment = from_export(path.open())
    except ExportError:
        # Loading itself failed — that's also a reject.
        assert outcome != "accept"
        return
    errors = list(environment.type_check(environment.all()))
    if outcome == "accept":
        assert not errors, "expected accept but got %d errors" % len(errors)
    elif outcome == "reject":
        assert errors, "expected reject but checker accepted clean"
