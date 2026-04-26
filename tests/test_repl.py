"""
Tests for the rpylean REPL.
"""

from io import BytesIO
from textwrap import dedent

from rpylean._tokens import FORMAT_PLAIN, TokenWriter
from rpylean.environment import Environment
from rpylean.objects import NAT, Name
from rpylean.repl import dispatch


def _writers():
    out, err = BytesIO(), BytesIO()
    return out, err, TokenWriter(out, FORMAT_PLAIN), TokenWriter(err, FORMAT_PLAIN)


class TestDispatch(object):
    def test_unknown_command_returns_false(self):
        """An unknown command writes a diagnostic and returns False."""
        out, err, stdoutw, stderrw = _writers()
        assert dispatch(Environment.EMPTY, "frobnicate", BytesIO(), stdoutw, stderrw) is False
        assert err.getvalue() == "Unknown command: frobnicate\n"
        assert out.getvalue() == ""

    def test_known_command_runs_and_returns_true(self):
        """A known command is dispatched; arguments are passed through."""
        a_decl = Name.simple("a").axiom(type=NAT)
        env = Environment.having([a_decl])

        out, err, stdoutw, stderrw = _writers()
        assert dispatch(env, "print a", BytesIO(), stdoutw, stderrw) is True
        assert out.getvalue().decode("utf-8") == "axiom a : Nat\n"
        assert err.getvalue() == ""

    def test_reduce_traces_each_step(self):
        """Dispatching ``reduce`` runs the command's WHNF tracing."""
        a_decl = Name.simple("a").axiom(type=NAT)
        b_decl = Name.simple("b").definition(type=NAT, value=a_decl.const())
        env = Environment.having([a_decl, b_decl])

        out, err, stdoutw, stderrw = _writers()
        assert dispatch(env, "reduce b", BytesIO(), stdoutw, stderrw) is True
        assert out.getvalue().decode("utf-8") == dedent(
            u"""\
            whnf b
            whnf a
            """,
        )
