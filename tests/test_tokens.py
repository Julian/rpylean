from __future__ import print_function

from StringIO import StringIO

from rpylean._tokens import (
    DEFAULT_THEME,
    Diagnostic,
    FORMAT_COLOR,
    FORMAT_PLAIN,
    KEYWORD,
    LITERAL,
    NO_SPAN,
    PLAIN,
    SORT,
    TokenWriter,
)


class TestPlain(object):
    def test_basic(self):
        assert FORMAT_PLAIN([KEYWORD.emit("def"), PLAIN.emit(" foo")]) == "def foo"

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

    def test_writeline_diagnostic(self):
        out = StringIO()
        writer = TokenWriter(out, FORMAT_PLAIN)
        d = Diagnostic([PLAIN.emit("expr")], NO_SPAN, [PLAIN.emit("\noops")])
        writer.writeline_diagnostic(d)
        assert out.getvalue() == "expr\noops\n"

    def test_writeline_diagnostic_color_applies_ansi(self):
        """writeline_diagnostic with FORMAT_COLOR applies ANSI codes."""
        out = StringIO()
        writer = TokenWriter(out, FORMAT_COLOR)
        d = Diagnostic([SORT.emit("Prop")], NO_SPAN, [PLAIN.emit("\nerror")])
        writer.writeline_diagnostic(d)
        assert "\033[" in out.getvalue()


class TestFormatWith(object):
    def test_no_span_passthrough(self):
        d = Diagnostic([PLAIN.emit("abc")], NO_SPAN, [PLAIN.emit("\nmsg")])
        assert d.format_with(FORMAT_PLAIN) == "abc\nmsg"

    def test_span_carets_under_spanned_token(self):
        tokens = [PLAIN.emit("xx "), SORT.emit("Type"), PLAIN.emit(" yy")]
        d = Diagnostic(tokens, (1, 2), [PLAIN.emit("\nbad")])
        assert d.format_with(FORMAT_PLAIN) == "xx Type yy\n   ^^^^\n   bad"

    def test_multiline_span(self):
        tokens = [PLAIN.emit("line1\n  "), PLAIN.emit("marked"), PLAIN.emit(" end")]
        d = Diagnostic(tokens, (1, 2), [PLAIN.emit("\nerr")])
        assert d.format_with(FORMAT_PLAIN) == "line1\n  marked end\n  ^^^^^^\n  err"

    def test_message_with_multiple_lines(self):
        tokens = [PLAIN.emit("x "), PLAIN.emit("y")]
        d = Diagnostic(tokens, (1, 2), [PLAIN.emit("\nline1\nline2")])
        assert d.format_with(FORMAT_PLAIN) == "x y\n  ^\n  line1\n  line2"

    def test_span_across_multiple_tokens(self):
        tokens = [PLAIN.emit("a"), PLAIN.emit("b"), PLAIN.emit("c"), PLAIN.emit("d")]
        d = Diagnostic(tokens, (1, 3), [PLAIN.emit("\nerr")])
        assert d.format_with(FORMAT_PLAIN) == "abcd\n ^^\n err"

    def test_color_applies_ansi(self):
        d = Diagnostic([SORT.emit("Prop")], NO_SPAN, [PLAIN.emit("\nerror")])
        assert "\033[" in d.format_with(FORMAT_COLOR)

    def test_color_span_has_carets(self):
        tokens = [PLAIN.emit("x "), SORT.emit("Type")]
        d = Diagnostic(tokens, (1, 2), [PLAIN.emit("\nbad")])
        assert "^" in d.format_with(FORMAT_COLOR)
