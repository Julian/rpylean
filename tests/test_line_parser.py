"""
Tests for the direct byte-level NDJSON line parser.
"""

import pytest

from rpylean._line_parser import LineCursor


def test_read_int_simple():
    c = LineCursor("123")
    assert c.read_int() == 123
    assert c.pos == 3


def test_read_int_zero():
    c = LineCursor("0")
    assert c.read_int() == 0
    assert c.pos == 1


def test_read_int_negative():
    c = LineCursor("-42")
    assert c.read_int() == -42
    assert c.pos == 3


def test_read_int_then_more():
    c = LineCursor("123,456")
    assert c.read_int() == 123
    assert c.line[c.pos] == ","


def test_read_int_skips_whitespace():
    c = LineCursor("  42")
    assert c.read_int() == 42


def test_read_int_no_digits():
    c = LineCursor("abc")
    with pytest.raises(ValueError):
        c.read_int()


def test_read_string_simple():
    c = LineCursor('"hello"')
    assert c.read_string() == "hello"
    assert c.pos == 7


def test_read_string_empty():
    c = LineCursor('""')
    assert c.read_string() == ""
    assert c.pos == 2


def test_read_string_with_unescaped_unicode_bytes():
    s = '"\xce\xb1"'  # alpha as raw UTF-8
    c = LineCursor(s)
    assert c.read_string() == "\xce\xb1"


def test_read_string_with_escapes():
    c = LineCursor(r'"a\nb\tc\"d\\e"')
    assert c.read_string() == "a\nb\tc\"d\\e"


def test_read_string_with_unicode_escape():
    c = LineCursor(r'"é"')  # é
    assert c.read_string() == "\xc3\xa9"


def test_read_string_unterminated():
    c = LineCursor('"oops')
    with pytest.raises(ValueError):
        c.read_string()


def test_read_key():
    c = LineCursor('"name":')
    assert c.read_key() == "name"
    assert c.pos == 7


def test_read_key_with_whitespace():
    c = LineCursor('  "name"  :  ')
    assert c.read_key() == "name"


def test_expect_key_matches():
    c = LineCursor('"name":')
    c.expect_key("name")


def test_expect_key_mismatch():
    c = LineCursor('"other":')
    with pytest.raises(ValueError):
        c.expect_key("name")


def test_read_int_array_empty():
    c = LineCursor("[]")
    assert c.read_int_array() == []


def test_read_int_array_single():
    c = LineCursor("[42]")
    assert c.read_int_array() == [42]


def test_read_int_array_multiple():
    c = LineCursor("[1,2,3,4,5]")
    assert c.read_int_array() == [1, 2, 3, 4, 5]


def test_read_int_array_with_whitespace():
    c = LineCursor("[ 1 , 2 , 3 ]")
    assert c.read_int_array() == [1, 2, 3]


def test_expect_consumes():
    c = LineCursor("{abc}")
    c.expect("{")
    assert c.pos == 1


def test_expect_mismatch():
    c = LineCursor("{abc}")
    with pytest.raises(ValueError):
        c.expect("[")


def test_maybe_present():
    c = LineCursor("[]")
    c.expect("[")
    assert c.maybe("]") is True
    assert c.pos == 2


def test_maybe_absent():
    c = LineCursor("[1]")
    c.expect("[")
    assert c.maybe("]") is False
    assert c.pos == 1


def test_read_bool_true():
    c = LineCursor("true")
    assert c.read_bool() is True
    assert c.pos == 4


def test_read_bool_false():
    c = LineCursor("false")
    assert c.read_bool() is False
    assert c.pos == 5


def test_read_bool_with_whitespace():
    c = LineCursor("  true ")
    assert c.read_bool() is True
    assert c.pos == 6


def test_read_bool_neither():
    c = LineCursor("null")
    with pytest.raises(ValueError):
        c.read_bool()
