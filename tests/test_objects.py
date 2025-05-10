from rpylean.objects import Name, W_Const, W_LevelParam


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
        u = W_LevelParam("u")
        v = W_LevelParam("v")
        assert bar.const([u, v]) == W_Const(bar, [u, v])
