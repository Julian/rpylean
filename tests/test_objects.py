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


class TestLevel:
    def test_max(self):
        u = Name.simple("u").level()
        v = Name.simple("v").level()
        assert u.max(v) == W_LevelMax(u, v)

    def test_imax(self):
        u = Name.simple("u").level()
        v = Name.simple("v").level()
        assert u.imax(v) == W_LevelIMax(u, v)


class TestSort:
    def test_succ(self):
        u = Name(["u"]).level()
        assert u.succ() == W_LevelSucc(W_LevelParam(Name(["u"])))

    def test_succ_level_zero(self):
        assert W_LEVEL_ZERO.succ() == W_LevelSucc(W_LEVEL_ZERO)

    def test_sort(self):
        assert W_LEVEL_ZERO.sort() == W_Sort(W_LEVEL_ZERO)
