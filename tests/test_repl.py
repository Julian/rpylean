"""
Tests for the rpylean REPL.
"""

from io import BytesIO
from textwrap import dedent

import pytest

from rpylean._rlib.rlineedit import _bare_prompt, _marked_prompt
from rpylean._tokens import FORMAT_PLAIN, TokenWriter
from rpylean.environment import Environment
from rpylean.objects import NAT, Name
from rpylean.repl import _Quit, dispatch


def _writers():
    out, err = BytesIO(), BytesIO()
    return out, err, TokenWriter(out, FORMAT_PLAIN), TokenWriter(err, FORMAT_PLAIN)


class TestPrompt(object):
    PREFIX = "\033[1m"
    RESET = "\033[0m"

    def test_marked_brackets_escapes(self):
        """GNU readline gets its colour escapes wrapped in \001/\002."""
        assert _marked_prompt(self.PREFIX, "> ", self.RESET) == (
            "\001\033[1m\002> \001\033[0m\002"
        )

    def test_bare_leaves_escapes_inline(self):
        """libedit gets the escapes inline (it mishandles the markers)."""
        assert _bare_prompt(self.PREFIX, "> ", self.RESET) == "\033[1m> \033[0m"

    def test_no_prefix_is_just_text(self):
        """With no colour, both assemblers yield the bare prompt text."""
        assert _marked_prompt("", "> ", self.RESET) == "> "
        assert _bare_prompt("", "> ", self.RESET) == "> "


class TestDispatch(object):
    def test_unknown_command_exits_nonzero(self):
        """An unknown command writes a diagnostic and returns exit code 1."""
        out, err, stdoutw, stderrw = _writers()
        assert dispatch(Environment.EMPTY, "frobnicate", BytesIO(), stdoutw, stderrw) == 1
        assert err.getvalue() == "Unknown command: frobnicate\n"
        assert out.getvalue() == ""

    def test_quit_raises_quit_with_success(self):
        """``exit``/``quit`` unwinds the loop via ``_Quit`` with exit code 0."""
        out, err, stdoutw, stderrw = _writers()
        with pytest.raises(_Quit) as exc:
            dispatch(Environment.EMPTY, "exit", BytesIO(), stdoutw, stderrw)
        assert exc.value.exit_code == 0

    def test_known_command_exits_zero(self):
        """A known command is dispatched (exit code 0); arguments pass through."""
        a_decl = Name.simple("a").axiom(type=NAT)
        env = Environment.having([a_decl])

        out, err, stdoutw, stderrw = _writers()
        assert dispatch(env, "print a", BytesIO(), stdoutw, stderrw) == 0
        assert out.getvalue().decode("utf-8") == "axiom a : Nat\n"
        assert err.getvalue() == ""

    def test_reduce_traces_each_step(self):
        """Dispatching ``reduce`` runs the command's WHNF tracing."""
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").definition(type=NAT, value=a_decl.const())
        env = Environment.having([a_decl, b_decl])

        out, err, stdoutw, stderrw = _writers()
        assert dispatch(env, "reduce b", BytesIO(), stdoutw, stderrw) == 0
        assert out.getvalue().decode("utf-8") == dedent(
            u"""\
            whnf b
            whnf a
            """,
        )
