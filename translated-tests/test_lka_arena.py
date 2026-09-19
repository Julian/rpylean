"""
The Lean Kernel Arena's fixtures, against the translated binary.
"""

import os
import subprocess
import threading

import pytest

from tests import lka_arena


_CASES = lka_arena.cases()

#: Seconds a test may take; the arena allows far longer, but none of
#: these should need it.
_TIMEOUT = 300


def _id(case):
    name, _, outcome = case
    return "%s[%s]" % (name, outcome)


@pytest.mark.skipif(not _CASES,
                    reason="lean-kernel-arena tests/ not available "
                           "(set LKA_TESTS_DIR or check it out alongside)")
@pytest.mark.parametrize("case", _CASES, ids=_id)
def test_arena_outcome(case):
    _, path, outcome = case
    process = subprocess.Popen(
        ["rpylean-c", "check", str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=dict(os.environ, PATH=".:" + os.environ.get("PATH", "")),
    )
    watchdog = threading.Timer(_TIMEOUT, process.kill)
    watchdog.start()
    try:
        stdout, stderr = process.communicate()
    finally:
        watchdog.cancel()
    code = process.returncode
    if outcome == "accept":
        assert code == 0, (stdout, stderr)
    elif outcome == "reject":
        assert code == 1, (stdout, stderr)
    else:
        assert code in (0, 1), (stdout, stderr)
