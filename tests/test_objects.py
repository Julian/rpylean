import pytest

from rpylean.objects import (
    W_LEVEL_ZERO,
    Name,
    W_Const,
    W_LevelIMax,
    W_LevelMax,
    W_LevelParam,
    W_LevelSucc,
    W_Sort,
)


class TestName:
    def test_simple(self):
        assert Name.simple("foo") == Name(["foo"])

    def test_simple_hierarchical(self):
        assert Name.simple("foo.bar") == Name(["foo.bar"])

    def test_from_str(self):
        assert Name.from_str("foo") == Name(["foo"])

    def test_from_str_multipart(self):
        assert Name.from_str("foo.bar") == Name(["foo", "bar"])

    def test_child(self):
        assert Name.simple("foo").child("bar") == Name(["foo", "bar"])

    def test_child_anonymous(self):
        assert Name.ANONYMOUS.child("foo") == Name.simple("foo")

    def test_const_no_levels(self):
        bar = Name(["foo", "bar"])
        assert bar.const() == W_Const(bar, [])

    def test_const_with_levels(self):
        bar = Name(["foo", "bar"])
        u = Name.simple("u").level()
        v = Name.simple("v").level()
        assert bar.const([u, v]) == W_Const(bar, [u, v])

    def test_level(self):
        assert Name.simple("foo").level() == W_LevelParam(Name(["foo"]))


u = Name.simple("u").level()
v = Name.simple("v").level()


class TestLevel(object):

    @pytest.mark.parametrize(
        "lhs, rhs, expected",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (
                W_LEVEL_ZERO.succ(),
                W_LEVEL_ZERO.succ().succ().succ(),
                W_LEVEL_ZERO.succ().succ().succ(),
            ),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ().succ(), W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u, u),
            (u, v, W_LevelMax(u, v)),
            (u.succ(), v, W_LevelMax(u.succ(), v)),
            (u, v.succ(), W_LevelMax(u, v.succ())),
            (u.succ(), v.succ(), u.max(v).succ()),
            (u.succ(), u, u.succ()),
            (u, u.succ(), u.succ()),
        ],
        ids=[
            "0_0",
            "0_1",
            "1_3",
            "1_0",
            "2_1",
            "u_u",
            "u_v",
            "u+1_v",
            "u_v+1",
            "u+1_v+1",
            "u+1_u",
            "u_u+1",
        ]
    )
    def test_max(self, lhs, rhs, expected):
        assert lhs.max(rhs) == expected

    @pytest.mark.parametrize(
        "lhs, rhs, expected",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO, W_LEVEL_ZERO),

            # imax 1 0 = 0
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO, W_LEVEL_ZERO),

            # in fact imax u 0 = 0 for any u
            (u, W_LEVEL_ZERO, W_LEVEL_ZERO),

            # but imax 0 1 = 1
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),

            # in fact imax 0 u = u for any u
            (W_LEVEL_ZERO, u, u),

            # and in fact imax 1 u = u for any u as well
            (W_LEVEL_ZERO.succ(), u, u),

            (u, u, u),
            (u, v, W_LevelIMax(u, v)),
        ],
        ids=[
            "0_0",
            "1_0",
            "u_0",
            "0_1",
            "0_u",
            "1_u",
            "u_u",
            "u_v",
        ]
    )
    def test_imax(self, lhs, rhs, expected):
        assert lhs.imax(rhs) == expected

    @pytest.mark.parametrize(
        "lhs, rhs",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u.succ()),
            (u, u.succ().succ()),
        ],
        ids=[
            "0_1",
            "1_2",
            "u_u+1",
            "u_u+2",
        ]
    )
    def test_leq_lt(self, lhs, rhs):
        assert lhs.leq(rhs)
        assert not rhs.leq(lhs)

    @pytest.mark.parametrize(
        "lhs, rhs",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ().succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u),
            (u.succ(), u.succ()),
            (u.succ().succ(), u.succ().succ()),
            (u.max(v), u.max(v)),
            (u.max(v).succ(), u.max(v).succ()),
        ],
        ids=[
            "0_0",
            "1_1",
            "2_2",
            "u_u",
            "u+1_u+1",
            "u+2_u+2",
            "max_uv",
            "max_uv+1",
        ]
    )
    def test_leq_eq(self, lhs, rhs):
        assert lhs.leq(rhs)
        assert rhs.leq(lhs)
        assert lhs.eq(rhs)
        assert rhs.eq(lhs)

    def test_succ(self):
        assert u.succ() == W_LevelSucc(W_LevelParam(Name(["u"])))

    def test_succ_level_zero(self):
        assert W_LEVEL_ZERO.succ() == W_LevelSucc(W_LEVEL_ZERO)

    def test_sort(self):
        assert W_LEVEL_ZERO.sort() == W_Sort(W_LEVEL_ZERO)
