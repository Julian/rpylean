from rpylean.objects import Name


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
