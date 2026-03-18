"""
Tests from the Lean Kernel Arena tutorial suite.
"""

from __future__ import print_function

import pytest

from rpylean.environment import from_export
from rpylean.parser import ParseError
from tests.cache_lka_tutorial import ensure_downloaded


_cache_dir = ensure_downloaded()

GOOD = sorted(_cache_dir.join("good").listdir("*.ndjson"))
BAD = sorted(_cache_dir.join("bad").listdir("*.ndjson"))


def _name_of(path):
    """Return the stem of a tutorial NDJSON path, e.g. ``'001_basicDef'``."""
    return path.purebasename


XFAILS = frozenset(
    [
        "095_proofIrrelevance",
        "096_unitEta1",
        "097_unitEta2",
        "098_unitEta3",
        "118_quotLiftReduction",
        "119_quotIndReduction",
        "016_tut06_bad01",
        "040_inductBadNonSort2",
        "041_inductLevelParam",
        "042_inductTooFewParams",
        "043_inductWrongCtorParams",
        "044_inductWrongCtorResParams",
        "045_inductWrongCtorResLevel",
        "046_inductInIndex",
        "047_indNeg",
        "049_reduceCtorType.mk",
        "050_indNegReducible",
        "054_typeWithTooHighTypeField.mk",
        "078_projOutOfRange",
        "079_projNotStruct",
        "081_projProp2",
        "083_projProp4",
        "084_projProp5",
        "085_projProp6",
        "087_projIndexData",
        "088_projIndexData2",
        "105_reflOccLeft",
        "106_reflOccInIndex",
        "120_dup_defs",
    ]
)


@pytest.mark.parametrize("path", GOOD, ids=_name_of)
def test_tutorial_good(path):
    if _name_of(path) in XFAILS:
        pytest.xfail("not yet implemented")
    environment = from_export(path.open())
    assert not list(environment.type_check(environment.all()))


@pytest.mark.parametrize("path", BAD, ids=_name_of)
def test_tutorial_bad(path):
    if _name_of(path) in XFAILS:
        pytest.xfail("not yet implemented")
    try:
        environment = from_export(path.open())
    except ParseError:
        return
    assert list(environment.type_check(environment.all()))
