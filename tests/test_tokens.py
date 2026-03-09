from __future__ import print_function

from StringIO import StringIO

from rpylean._tokens import (
    DEFAULT_THEME,
    FORMAT_COLOR,
    FORMAT_PLAIN,
    KEYWORD,
    LITERAL,
    PLAIN,
    SORT,
    TokenWriter,
)


class TestPlain(object):
    def test_basic(self):
        assert (
            FORMAT_PLAIN([KEYWORD.emit("def"), PLAIN.emit(" foo")])
            == "def foo"
        )


    def test_ignores_color(self):
        assert SORT.name in DEFAULT_THEME
        got = FORMAT_PLAIN(
            [SORT.emit("Prop"), PLAIN.emit(" "), LITERAL.emit("37")],
        )
        assert got == "Prop 37"


class TestColor(object):
    def test_plain(self):
        assert FORMAT_COLOR([PLAIN.emit("x")]) == "x"

    def test_keyword(self):
        result = FORMAT_COLOR([KEYWORD.emit("def")])
        assert result == "\033[1;38;2;86;156;214mdef\033[0m"

    def test_render_ansi_unknown_tag_unchanged(self):
        assert FORMAT_COLOR([("unknown-tag", "x")]) == "x"

    def test_default_theme_excludes_plain(self):
        assert PLAIN.name not in DEFAULT_THEME


class TestWriter(object):
    def test_write(self):
        out = StringIO()
        writer = TokenWriter(out, FORMAT_PLAIN)
        writer.write([KEYWORD.emit("def"), PLAIN.emit(" foo")])
        assert out.getvalue() == "def foo"


    def test_writeline(self):
        out = StringIO()
        writer = TokenWriter(out, FORMAT_PLAIN)
        writer.writeline([PLAIN.emit("hello")])
        assert out.getvalue() == "hello\n"

    def test_color(self):
        out = StringIO()
        writer = TokenWriter(out, FORMAT_COLOR)
        writer.write([KEYWORD.emit("def")])
        assert out.getvalue() == "\033[1;38;2;86;156;214mdef\033[0m"
