"""
The Wadler-style ``Format`` document algebra and its renderer.
"""

from rpylean import _format
from rpylean._tokens import FORMAT_PLAIN, NO_SPAN, PLAIN, KEYWORD, PUNCT


def pretty(f, width=_format.DEFAULT_WIDTH):
    tokens, _span = _format.render(f, width)
    return FORMAT_PLAIN(tokens)


def t(s, token=PLAIN):
    return _format.text(token, s)


class TestBasics(object):
    def test_nil(self):
        assert pretty(_format.NIL) == ""

    def test_text(self):
        assert pretty(t("hello")) == "hello"

    def test_append(self):
        assert pretty(_format.append(t("a"), t("b"))) == "ab"

    def test_concat(self):
        assert pretty(_format.concat([t("a"), t("b"), t("c")])) == "abc"

    def test_concat_drops_nil(self):
        f = _format.concat([_format.NIL, t("a"), _format.NIL, t("b")])
        assert pretty(f) == "ab"

    def test_tags_preserved(self):
        tokens, _ = _format.render(
            _format.concat([t("def", KEYWORD), t(" "), t("(", PUNCT)]),
        )
        assert tokens == [
            KEYWORD.emit("def"), PLAIN.emit(" "), PUNCT.emit("("),
        ]


class TestSoftLine(object):
    def test_flat_when_it_fits(self):
        f = _format.group(_format.concat([t("a"), _format.LINE, t("b")]))
        assert pretty(f, width=80) == "a b"

    def test_breaks_when_too_wide(self):
        f = _format.group(_format.concat([t("aaa"), _format.LINE, t("bbb")]))
        assert pretty(f, width=4) == "aaa\nbbb"

    def test_nest_indents_broken_lines(self):
        f = _format.group(
            _format.nest(2, _format.concat([t("a"), _format.LINE, t("b")])),
        )
        assert pretty(f, width=1) == "a\n  b"

    def test_all_or_none_breaks_together(self):
        inner = _format.concat(
            [t("a"), _format.LINE, t("b"), _format.LINE, t("c")],
        )
        f = _format.group(inner)
        # Too narrow for "a b c" -> every soft line breaks.
        assert pretty(f, width=3) == "a\nb\nc"

    def test_fits_keeps_all_flat(self):
        inner = _format.concat(
            [t("a"), _format.LINE, t("b"), _format.LINE, t("c")],
        )
        assert pretty(_format.group(inner), width=80) == "a b c"


class TestFill(object):
    def test_fill_packs_as_many_as_fit(self):
        items = [t("aa"), t("bb"), t("cc"), t("dd")]
        parts = []
        for n, item in enumerate(items):
            if n > 0:
                parts.append(_format.LINE)
            parts.append(item)
        f = _format.fill(_format.concat(parts))
        # width 6 fits "aa bb" (5) but not "aa bb cc" (8): break, then pack.
        assert pretty(f, width=6) == "aa bb\ncc dd"


class TestHardLine(object):
    def test_hard_newline_always_breaks(self):
        f = t("a\nb")
        assert pretty(f, width=80) == "a\nb"

    def test_hard_newline_reindents(self):
        f = _format.nest(2, t("a\nb"))
        assert pretty(f, width=80) == "a\n  b"

    def test_hard_break_forces_enclosing_group_open(self):
        # Matching Lean's `foundFlattenedHardLine`: a mandatory newline in a
        # group's contents forces the group's soft lines to break too, even
        # when the first line would have fit.
        inner = t("x\ny")
        outer = _format.group(_format.concat([t("fun"), _format.LINE, inner]))
        assert pretty(outer, width=80) == "fun\nx\ny"


class TestNestedGroups(object):
    def test_inner_breaks_outer_flat(self):
        inner = _format.group(
            _format.nest(2, _format.concat([t("g"), _format.LINE, t("xxxx")])),
        )
        outer = _format.group(_format.concat([t("f"), t(" "), inner]))
        # Outer fits on its own; inner is forced to break.
        assert pretty(outer, width=5) == "f g\n  xxxx"


class TestTagSpans(object):
    def test_span_reports_token_range(self):
        f = _format.concat([
            t("a "),
            _format.tag(_format.MARK_TAG, t("MARKED")),
            t(" b"),
        ])
        tokens, span = _format.render(f, width=80)
        assert FORMAT_PLAIN(tokens) == "a MARKED b"
        start, end = span
        assert FORMAT_PLAIN(tokens[start:end]) == "MARKED"

    def test_span_over_multiple_tokens(self):
        marked = _format.concat([t("x", KEYWORD), t("y", PUNCT)])
        f = _format.concat([t("("), _format.tag(_format.MARK_TAG, marked), t(")")])
        tokens, span = _format.render(f, width=80)
        start, end = span
        assert FORMAT_PLAIN(tokens[start:end]) == "xy"

    def test_no_span_when_untagged(self):
        _tokens, span = _format.render(t("plain"), width=80)
        assert span == NO_SPAN
