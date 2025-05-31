"""
Pretty printing of Lean objects.
"""

import pytest

from rpylean.objects import Name, W_LEVEL_ZERO


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


u = Name.simple("u").level()
v = Name.simple("v").level()


@pytest.mark.parametrize(
    "level, expected",
    [
        (W_LEVEL_ZERO, "Prop"),
        (W_LEVEL_ZERO.succ(), "Type"),
        (W_LEVEL_ZERO.succ().succ(), "Type 1"),
        (u, "Sort u"),
        (u.succ(), "Type u"),
        (u.succ().succ().succ(), "Type (u + 2)"),
        (u.max(v), "Sort (max u v)"),
        (u.max(u), "Sort u"),
        (u.max(u.succ()), "Type u"),
        (u.succ().succ().max(u.succ()), "Type (u + 1)"),
        (u.succ().max(u), "Type u"),
        (u.succ().max(v.succ()), "Type (max u v)"),
        (u.imax(v), "Sort (imax u v)"),
        (u.imax(W_LEVEL_ZERO), "Prop"),
        (W_LEVEL_ZERO.succ().imax(u), "Sort u"),
    ],
    ids=[
        "prop",
        "type",
        "type1",
        "param_u",
        "param_u_succ",
        "param_u+3",
        "max_u_v",
        "max_u_u",
        "max_u_u+1",
        "max_u+1_u",
        "max_u+2_u+1",
        "max_u+1_v+1",
        "imax",
        "imax_0",
        "imax_1_u",
    ]
)
def test_sort(level, expected):
    assert level.sort().pretty() == expected
