"""
Pretty printing of Lean objects.
"""

import pytest

from rpylean.objects import Name


@pytest.mark.parametrize(
    "parts, expected",
    [
        (["foo"], "foo"),
        (["Lean", "Meta", "whnf"], "Lean.Meta.whnf"),
        (["Foo", "bar.baz"], "Foo.«bar.baz»"),
        (["_uniq", 231], "_uniq.231"),
        ([], "[anonymous]"),
    ],
    ids=[
        "simple",
        "multipart_hierarchical",
        "with_atomic_part",
        "with_number",
        "anonymous",
    ]
)
def test_name(parts, expected):
    assert Name(parts).pretty() == expected
