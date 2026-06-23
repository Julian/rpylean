"""
The ``--width`` option and terminal-width fallback (``cli.apply_width``).
"""

import pytest

from rpylean import _format, cli
from rpylean._rlib.rcli import UsageError


class _FakeStream(object):
    """A minimal stand-in for an output stream."""

    def __init__(self, isatty):
        self._isatty = isatty

    def isatty(self):
        return self._isatty

    def fileno(self):
        return 1


def teardown_function(function):
    # Keep the process-wide width from leaking between tests.
    _format.set_render_width(_format.DEFAULT_WIDTH)


def test_explicit_width_wins():
    cli.apply_width("42", _FakeStream(isatty=True))
    assert _format.RENDER_WIDTH.width == 42


def test_non_tty_falls_back_to_default():
    _format.set_render_width(7)
    cli.apply_width(None, _FakeStream(isatty=False))
    assert _format.RENDER_WIDTH.width == _format.DEFAULT_WIDTH


def test_invalid_width_is_rejected():
    with pytest.raises(UsageError):
        cli.apply_width("not-a-number", _FakeStream(isatty=False))


def test_nonpositive_width_is_rejected():
    with pytest.raises(UsageError):
        cli.apply_width("0", _FakeStream(isatty=False))
    with pytest.raises(UsageError):
        cli.apply_width("-5", _FakeStream(isatty=False))
