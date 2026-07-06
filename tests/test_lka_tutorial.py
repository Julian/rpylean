"""
Tests from the Lean Kernel Arena tutorial suite.
"""

from __future__ import print_function

import pytest

from rpylean.environment import from_export
from rpylean.exceptions import ExportError
from tests.cache_lka_tutorial import ensure_downloaded


_cache_dir = ensure_downloaded()

GOOD = sorted(_cache_dir.join("good").listdir("*.ndjson"))
BAD = sorted(_cache_dir.join("bad").listdir("*.ndjson"))


def _name_of(path):
    """Return the stem of a tutorial NDJSON path, e.g. ``'001_basicDef'``."""
    return path.purebasename


@pytest.mark.parametrize("path", GOOD, ids=_name_of)
def test_tutorial_good(path):
    environment = from_export(path.open())
    errors = list(environment.type_check(environment.all()))
    assert not errors


@pytest.mark.parametrize("path", BAD, ids=_name_of)
def test_tutorial_bad(path):
    try:
        environment = from_export(path.open())
    except ExportError:
        return
    errors = list(environment.type_check(environment.all()))
    assert errors
