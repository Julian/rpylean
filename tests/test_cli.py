from io import BytesIO
from StringIO import StringIO
import os
import threading

from rpylean._rlib.rcli import CLI, Args, UsageError
from rpylean._tokens import FORMAT_COLOR, FORMAT_PLAIN, TokenWriter
from rpylean.cli import (
    Printer, _HEAT_LEVELS, _heat_level, _json_escape, _parse_bytes,
    _parse_seconds, _write_progress_heap_dump, cli as rpylean_cli,
)
from rpylean.environment import CheckResult, Environment
from rpylean.objects import TYPE, Name


def run(cli, argv, exit=0):
    stdin = BytesIO()
    stdout, stderr = BytesIO(), BytesIO()
    got = cli.main(argv, (stdin, stdout, stderr))
    assert got == exit, stderr.getvalue()
    return stdout.getvalue(), stderr.getvalue()


def test_usage_error_on_no_args():
    cli = CLI()

    @cli.subcommand(["ARG"], help="Test command help.")
    def test(self, args, stdin, stdout, stderr):
        return 0

    out, err = run(cli, ["prog"])
    assert "USAGE" in err


def test_known_command_runs():
    cli = CLI()

    @cli.subcommand(["ARG"], help="Test command help.")
    def test(self, args, stdin, stdout, stderr):
        stdout.write("ran test with %s\n" % args.args[0])
        return 0

    out, err = run(cli, ["prog", "test", "foo"])
    assert "ran test with foo" in out


def test_underscored_command_name_dispatches_via_hyphen():
    cli = CLI()

    @cli.subcommand([], help="Multi-word command.")
    def my_command(self, args, stdin, stdout, stderr):
        stdout.write("ok\n")
        return 0

    out, _ = run(cli, ["prog", "my-command"])
    assert "ok" in out


def test_subcli_dispatches_to_named_child():
    cli = CLI()
    grp = cli.subcli("grp", help="A group.")

    @grp.subcommand([], help="Alpha leaf.")
    def alpha(self, args, stdin, stdout, stderr):
        stdout.write("alpha\n")
        return 0

    @grp.subcommand([], help="Beta leaf.")
    def beta(self, args, stdin, stdout, stderr):
        stdout.write("beta\n")
        return 0

    out, _ = run(cli, ["prog", "grp", "alpha"])
    assert "alpha" in out
    out, _ = run(cli, ["prog", "grp", "beta"])
    assert "beta" in out


def test_subcommand_explicit_name_and_custom_executable():
    cli = CLI(executable="mytool")
    grp = cli.subcli("grp", help="A group.")

    @cli.subcommand([], name="top-cmd", help="Top command.")
    def impl_top(self, args, stdin, stdout, stderr):
        stdout.write("top\n")
        return 0

    @grp.subcommand(["ARG"], name="sub-cmd", help="Sub command.")
    def impl_sub(self, args, stdin, stdout, stderr):
        stdout.write("sub=%s\n" % args.args[0])
        return 0

    out, _ = run(cli, ["mytool", "top-cmd"])
    assert out == "top\n"
    out, _ = run(cli, ["mytool", "grp", "sub-cmd", "x"])
    assert out == "sub=x\n"
    _, err = run(cli, ["mytool", "grp", "sub-cmd"], exit=1)
    assert "mytool grp sub-cmd ARG" in err
    _, err = run(cli, ["mytool", "--version"], exit=0)
    assert err.startswith("mytool ")


def test_subcli_shared_options_flow_to_child():
    cli = CLI()
    grp = cli.subcli("grp", help="A group.", options=[("shared", "shared opt")])

    @grp.subcommand([], help="Leaf.", options=[("local", "local opt")])
    def leaf(self, args, stdin, stdout, stderr):
        stdout.write("shared=%s local=%s\n"
                     % (args.options["shared"], args.options["local"]))
        return 0

    # Shared option before the leaf name.
    out, _ = run(
        cli, ["prog", "grp", "--shared", "S", "leaf", "--local", "L"],
    )
    assert "shared=S local=L" in out

    # Shared option after the leaf name still works.
    out, _ = run(
        cli, ["prog", "grp", "leaf", "--shared", "S", "--local", "L"],
    )
    assert "shared=S local=L" in out


def test_subcli_unknown_child_raises_usage():
    cli = CLI()
    grp = cli.subcli("grp", help="A group.")

    @grp.subcommand([], help="Only leaf.")
    def only(self, args, stdin, stdout, stderr):
        return 0

    _, err = run(cli, ["prog", "grp", "nope"], exit=1)
    assert "Unknown subcommand: nope" in err


def test_unknown_command_falls_back_to_default():
    cli = CLI(default="foo")

    @cli.subcommand(["ARG"], help="Fallback here.")
    def foo(self, args, stdin, stdout, stderr):
        assert args == Args(args=["unknown"])
        stdout.write("ran foo\n")
        return 0

    out, err = run(cli, ["prog", "unknown"])
    assert "ran foo" in out


def test_help_no_command():
    cli = CLI()
    out, err = run(cli, ["prog", "--help"])
    assert "USAGE" in err


def test_varargs_command():
    cli = CLI()

    @cli.subcommand(["A", "*REST"], help="Command with varargs.")
    def vargs(self, args, stdin, stdout, stderr):
        stdout.write("args=%r varargs=%r\n" % (args.args, args.varargs))
        return 0

    out, err = run(cli, ["prog", "vargs", "foo", "bar", "baz"])
    assert "args=['foo'] varargs=['bar', 'baz']" in out


def test_too_few_args():
    cli = CLI()

    @cli.subcommand(["A", "B"], help="Needs two args.")
    def tworeq(self, args, stdin, stdout, stderr):
        stdout.write("should not get here\n")
        return 0

    out, err = run(cli, ["prog", "tworeq", "onlyone"], exit=1)
    assert "Expected an B" in err
    assert out == ""


def test_too_many_args():
    cli = CLI()

    @cli.subcommand(["A"], help="Only one arg.")
    def onearg(self, args, stdin, stdout, stderr):
        stdout.write("should not get here\n")
        return 0

    out, err = run(cli, ["prog", "onearg", "a", "b"], exit=1)
    assert "Unknown arguments: ['b']" in err
    assert out == ""


def test_help_for_command():
    cli = CLI()

    @cli.subcommand(["A"], help="Help for foo command.")
    def foo(self, args, stdin, stdout, stderr):
        stdout.write("should not get here\n")
        return 0

    out, err = run(cli, ["prog", "foo", "--help"])
    assert "Help for foo command." in err
    assert "USAGE" in err


def test_short_help():
    cli = CLI()

    @cli.subcommand(["A"], help="Help for bar command.\n\nLonger description.")
    def bar(self, args, stdin, stdout, stderr):
        return 0

    out, err = run(cli, ["prog", "--help"])
    assert "bar: Help for bar command.\n" in err


class TestOption(object):
    cli = CLI()

    @cli.subcommand(
        ["A"],
        options=[("opt", "Option with argument.")],
        help="Command with option.",
    )
    def foo(self, args, stdin, stdout, stderr):
        stdout.write("args=%r options=%r\n" % (args.args, args.options))
        return 0

    def test_option_before_argument(self):
        out, err = run(self.cli, ["prog", "foo", "--opt", "val", "arg"])
        assert "args=['arg']" in out
        assert "options={'opt': 'val'}" in out
        assert err == ""

    def test_option_after_argument(self):
        out, err = run(self.cli, ["prog", "foo", "arg", "--opt", "val"])
        assert "args=['arg']" in out
        assert "options={'opt': 'val'}" in out
        assert err == ""

    def test_option_equal(self):
        out, err = run(self.cli, ["prog", "foo", "--opt=val", "arg"])
        assert "args=['arg']" in out
        assert "options={'opt': 'val'}" in out
        assert err == ""

    def test_missing_argument(self):
        out, err = run(self.cli, ["prog", "foo", "--opt"], exit=1)
        assert "Option --opt requires an argument" in err
        assert out == ""

    def test_help(self):
        out, err = run(self.cli, ["prog", "foo", "--help"])
        assert "--opt" in err
        assert "Option with argument." in err

    def test_unknown_option(self):
        out, err = run(self.cli, ["prog", "foo", "--bar", "1", "2"], exit=1)
        assert "Unknown option: --bar" in err
        assert out == ""


class TestFlag(object):
    cli = CLI()

    @cli.subcommand(
        ["A"],
        flags=[("flag", "A test flag.", "default", "enabled")],
        help="Command with flag.",
    )
    def bar(self, args, stdin, stdout, stderr):
        stdout.write("flag=%r\n" % args.options["flag"])
        return 0

    def test_flag_not_present(self):
        out, err = run(self.cli, ["prog", "bar", "arg"])
        assert "flag='default'" in out
        assert err == ""

    def test_flag_present(self):
        out, err = run(self.cli, ["prog", "bar", "arg", "--flag"])
        assert "flag='enabled'" in out
        assert err == ""

    def test_flag_before_argument(self):
        out, err = run(self.cli, ["prog", "bar", "--flag", "arg"])
        assert "flag='enabled'" in out
        assert err == ""

    def test_flag_does_not_consume_argument(self):
        out, err = run(self.cli, ["prog", "bar", "--flag", "arg1", "arg2"], exit=1)
        assert "Unknown arguments: ['arg2']" in err
        assert out == ""

    def test_flag_help(self):
        out, err = run(self.cli, ["prog", "bar", "--help"])
        assert "--flag" in err
        assert "A test flag." in err


class TestJitOption(object):
    cli = CLI()

    @cli.subcommand(["A"], help="Echoing command.")
    def echo(self, args, stdin, stdout, stderr):
        stdout.write("ran with %s\n" % args.args[0])
        return 0

    def test_strips_jit_space_form(self):
        out, _ = run(self.cli, ["prog", "--jit", "off", "echo", "x"])
        assert "ran with x" in out

    def test_strips_jit_equals_form(self):
        out, _ = run(self.cli, ["prog", "--jit=off", "echo", "x"])
        assert "ran with x" in out

    def test_jit_help_exits_zero(self):
        _, err = run(self.cli, ["prog", "--jit", "help"], exit=0)
        assert "PARAMETERS" in err
        assert "threshold" in err

    def test_jit_missing_argument(self):
        _, err = run(self.cli, ["prog", "--jit"], exit=1)
        assert "--jit requires an argument" in err

    def test_jit_invalid_optstring(self):
        _, err = run(self.cli, ["prog", "--jit", "nopesuchparam=1", "echo", "x"], exit=1)
        assert "Invalid --jit options" in err

    def test_jit_ignored_after_double_dash(self):
        out, _ = run(self.cli, ["prog", "echo", "--", "--jit=off"])
        assert "ran with --jit=off" in out

    def test_jit_before_double_dash_still_applies(self):
        out, _ = run(self.cli, ["prog", "--jit=off", "echo", "--", "--jit"])
        assert "ran with --jit" in out


class TestEndOfOptions(object):
    cli = CLI(default="echo")

    @cli.subcommand(
        ["*ARGS"],
        options=[("opt", "Option with argument.")],
        flags=[("flag", "A flag.", "", "yes")],
        help="Echo positional args.",
    )
    def echo(self, args, stdin, stdout, stderr):
        stdout.write("varargs=%r opt=%r flag=%r\n" % (
            args.varargs, args.options["opt"], args.options["flag"],
        ))
        return 0

    @cli.subcommand([], help="Another subcommand.")
    def other(self, args, stdin, stdout, stderr):
        stdout.write("ran other\n")
        return 0

    def test_option_like_args_after_double_dash(self):
        out, err = run(
            self.cli,
            ["prog", "echo", "--opt", "v", "--", "--help", "--flag", "--", "--opt"],
        )
        assert "varargs=['--help', '--flag', '--', '--opt']" in out
        assert "opt='v'" in out
        assert "flag=''" in out
        assert err == ""

    def test_option_still_requires_value_before_double_dash(self):
        out, err = run(self.cli, ["prog", "echo", "--opt", "--", "x"], exit=1)
        assert "Option --opt requires an argument" in err
        assert out == ""

    def test_double_dash_with_default_command_and_subcommand_name(self):
        out, err = run(self.cli, ["prog", "--", "other", "--help"])
        assert "varargs=['other', '--help']" in out
        assert err == ""

    def test_subcli_double_dash_passes_to_child(self):
        cli = CLI()
        grp = cli.subcli("grp", help="A group.", options=[("shared", "shared")])

        @grp.subcommand(["*ARGS"], help="Leaf.")
        def leaf(self, args, stdin, stdout, stderr):
            stdout.write("shared=%r varargs=%r\n" % (
                args.options["shared"], args.varargs,
            ))
            return 0

        out, _ = run(cli, ["prog", "grp", "--shared", "S", "leaf", "--", "--help"])
        assert "shared='S' varargs=['--help']" in out

        _, err = run(cli, ["prog", "grp", "--", "leaf"], exit=1)
        assert "Missing subcommand for grp" in err


class TestCheckCLI(object):
    def test_check_no_files_exits_nonzero(self):
        out, err = run(rpylean_cli, ["rpylean", "check"], exit=1)
        assert "Expected an EXPORT_FILE" in err
        assert out == ""

    def test_check_only_options_no_files_exits_nonzero(self):
        out, err = run(rpylean_cli, ["rpylean", "check", "--color=no"], exit=1)
        assert "Expected an EXPORT_FILE" in err
        assert out == ""

    def test_check_bare_double_dash_exits_nonzero(self):
        out, err = run(rpylean_cli, ["rpylean", "check", "--"], exit=1)
        assert "Expected an EXPORT_FILE" in err
        assert out == ""

    def test_default_bare_double_dash_exits_nonzero(self):
        out, err = run(rpylean_cli, ["rpylean", "--"], exit=1)
        assert "Expected an EXPORT_FILE" in err
        assert out == ""

    def test_check_option_like_filename_after_double_dash(self):
        out, err = run(
            rpylean_cli,
            ["rpylean", "check", "--", "--no-such-export.ndjson"],
            exit=1,
        )
        assert "`--no-such-export.ndjson` does not exist." in err
        assert "Unknown option" not in err
        assert out == ""

    def test_default_check_filename_matching_subcommand_after_double_dash(self):
        out, err = run(rpylean_cli, ["rpylean", "--", "dump"], exit=1)
        assert "`dump` does not exist." in err
        assert out == ""

    def test_check_regular_file_single_open_prescan_and_rewind(self, tmpdir):
        export = tmpdir.join("ok.ndjson")
        export.write(
            '{"meta":{"format":{"version":"3.1.0"},"exporter":{"name":"leanexport","version":"4.35.0"}}}\n'
            '{"in":1,"str":{"pre":0,"str":"P"}}\n'
            '{"il":1,"succ":0}\n'
            '{"ie":0,"sort":1}\n'
            '{"ie":1,"sort":0}\n'
            '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
        )
        out, err = run(rpylean_cli, ["rpylean", "check", "--", str(export)], exit=0)
        assert out == ""
        assert "1/1 decls checked" in err

    def test_check_regular_file_bad_metadata_rewinds_and_reports(self, tmpdir):
        export = tmpdir.join("bad-meta.ndjson")
        export.write('{"meta":{"format":{"version":"9.9.9"}}}\n')
        out, err = run(rpylean_cli, ["rpylean", "check", str(export)], exit=1)
        assert out == ""
        assert "9.9.9" in err

    def test_check_non_seekable_fifo_works_in_single_pass(self, tmpdir):
        fifo_path = str(tmpdir.join("export.fifo"))
        os.mkfifo(fifo_path)
        payload = (
            '{"meta":{"format":{"version":"3.1.0"}}}\n'
            '{"in":1,"str":{"pre":0,"str":"P"}}\n'
            '{"il":1,"succ":0}\n'
            '{"ie":0,"sort":1}\n'
            '{"ie":1,"sort":0}\n'
            '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
        )

        def write_once():
            fd = os.open(fifo_path, os.O_WRONLY)
            try:
                os.write(fd, payload)
            finally:
                os.close(fd)

        writer = threading.Thread(target=write_once)
        writer.start()
        try:
            out, err = run(rpylean_cli, ["rpylean", "check", "--", fifo_path], exit=0)
        finally:
            writer.join(timeout=5)
        assert not writer.is_alive()
        assert out == ""
        assert "1/1 decls checked" in err

    def test_check_directory_exits_nonzero_cleanly(self, tmpdir):
        out, err = run(rpylean_cli, ["rpylean", "check", str(tmpdir)], exit=1)
        assert out == ""
        assert "Could not read" in err

    def test_progress_heap_dump_swallows_oserror(self, tmpdir):
        out = StringIO()
        stderrw = TokenWriter(out, FORMAT_PLAIN)
        missing_dir = str(tmpdir.join("no-such-dir"))
        _write_progress_heap_dump(stderrw, directory=missing_dir)
        assert "[progress] skipped heap dump:" in out.getvalue()

    def test_dump_export_emits_declarations(self, tmpdir):
        export = tmpdir.join("ok.ndjson")
        export.write(
            '{"meta":{"format":{"version":"3.1.0"}}}\n'
            '{"in":1,"str":{"pre":0,"str":"P"}}\n'
            '{"il":1,"succ":0}\n'
            '{"ie":0,"sort":1}\n'
            '{"ie":1,"sort":0}\n'
            '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
        )
        out, err = run(rpylean_cli, ["rpylean", "dump", "--export", str(export)], exit=0)
        assert err == ""
        assert '{"def":' in out
        assert '"str":"P"' in out

    def test_ffi_subcommands_require_module(self):
        for sub in ["check", "repl", "export"]:
            out, err = run(rpylean_cli, ["rpylean", "ffi", sub], exit=1)
            assert out == ""
            assert "Expected a MODULE" in err


class TestPrinter(object):
    decl = Name.simple("Foo").axiom(type=TYPE)
    env = Environment.having([decl])

    def _ok(self, elapsed=0.0):
        return CheckResult(
            elapsed=elapsed, gc_elapsed=0.0, bytes_allocated=0,
            live_memory=0, peak_growth=0, error=None,
        )

    def _run(self, mode, formatter, result=None):
        out = StringIO()
        printer = Printer.from_str(mode, TokenWriter(out, formatter))
        printer.before(self.env, self.decl)
        printer.after(self.env, self.decl, result or self._ok())
        return out.getvalue()

    def test_name_color(self):
        assert "\033[" in self._run("name", FORMAT_COLOR)

    def test_name_plain(self):
        assert self._run("name", FORMAT_PLAIN) == "Foo ... OK\n"

    def test_name_fail(self):
        result = CheckResult(
            elapsed=0.0, gc_elapsed=0.0, bytes_allocated=0,
            live_memory=0, peak_growth=0,
            error=object(),  # truthy non-None; printer only branches on `is None`
        )
        assert self._run("name", FORMAT_PLAIN, result=result) == "Foo ... FAIL\n"

    def test_dots_plain_distinct_glyphs(self):
        # All 5 heat levels must use distinct ASCII glyphs so --color=no
        # still conveys magnitude.
        glyphs = set(glyph for _token, glyph in _HEAT_LEVELS)
        assert len(glyphs) == len(_HEAT_LEVELS)

    def test_dots_all_heat_levels_distinguishable(self):
        # End-to-end: one elapsed value per bucket goes in, 5 distinct
        # plain-text glyphs come out. Catches regressions where someone
        # accidentally collapses two heat levels in `_HEAT_LEVELS` or
        # `_heat_level`.
        per_bucket = [0.0005, 0.005, 0.05, 0.5, 5.0]
        outs = [
            self._run("dots", FORMAT_PLAIN, result=self._ok(elapsed=secs))
            for secs in per_bucket
        ]
        assert len(set(outs)) == 5

    def test_dots_plain(self):
        assert self._run("dots", FORMAT_PLAIN) == "."

    def test_dots_color_hot(self):
        out = self._run("dots", FORMAT_COLOR, result=self._ok(elapsed=5.0))
        assert "\033[" in out and "#" in out

    def test_timing(self):
        out = self._run("timing", FORMAT_PLAIN, result=self._ok(elapsed=0.5))
        assert out.startswith("Foo ... ") and "0.5" in out and out.endswith("s\n")

    def test_jsonl(self):
        out = self._run("jsonl", FORMAT_PLAIN, result=self._ok(elapsed=0.5))
        # Only `after` writes; `before` is a no-op, so output is exactly one line.
        # `ok` is positioned right after `name` so previews / `head -c` snippets
        # show success status first.
        assert out.startswith('{"name":"Foo","ok":true,')
        assert '"elapsed":0.5' in out
        assert '"heartbeats"' not in out
        assert out.endswith("}\n")

    def test_jsonl_failure_status_before_metrics(self):
        # `ok` and `error` are status fields and belong adjacent at the
        # top of each record so a parser can short-circuit on failure.
        class FakeError(object):
            def tokens(self):
                from rpylean._tokens import PLAIN
                return [PLAIN.emit("oops")]

        result = CheckResult(
            elapsed=0.0, gc_elapsed=0.0, bytes_allocated=0,
            live_memory=0, peak_growth=0, error=FakeError(),
        )
        out = self._run("jsonl", FORMAT_PLAIN, result=result)
        assert out.startswith('{"name":"Foo","ok":false,"error":"oops",')

    def test_jsonl_failure_includes_error(self):
        class FakeError(object):
            def tokens(self):
                from rpylean._tokens import PLAIN
                return [PLAIN.emit("boom\nline2")]

        result = CheckResult(
            elapsed=0.0, gc_elapsed=0.0, bytes_allocated=0,
            live_memory=0, peak_growth=0, error=FakeError(),
        )
        out = self._run("jsonl", FORMAT_PLAIN, result=result)
        # `\n` in the error must be JSON-escaped (`\\n`), not raw, so the line stays parseable.
        assert '"ok":false' in out
        assert '"error":"boom\\nline2"' in out

    def test_decls_plain(self):
        out = self._run("all", FORMAT_PLAIN)
        # Full declaration prints in `before`; `after` is a no-op.
        assert "Foo" in out and out.endswith("\n")

    def test_unknown(self):
        try:
            Printer.from_str("nope", TokenWriter(StringIO(), FORMAT_PLAIN))
        except UsageError as err:
            assert "nope" in err.message
        else:
            assert False, "expected UsageError"

    def test_none(self):
        assert Printer.from_str(None, TokenWriter(StringIO(), FORMAT_PLAIN)) is None
        assert Printer.from_str("none", TokenWriter(StringIO(), FORMAT_PLAIN)) is None


class TestHeatLevel(object):
    def test_buckets(self):
        assert _heat_level(0.0005) == 0
        assert _heat_level(0.005) == 1
        assert _heat_level(0.05) == 2
        assert _heat_level(0.5) == 3
        assert _heat_level(5.0) == 4

    def test_boundaries_are_strict_less(self):
        # `< 0.001` so exactly 0.001 falls into the next bucket; lets us
        # change boundaries later without subtle off-by-one regressions.
        assert _heat_level(0.0009) == 0
        assert _heat_level(0.001) == 1
        assert _heat_level(0.009) == 1
        assert _heat_level(0.01) == 2
        assert _heat_level(0.09) == 2
        assert _heat_level(0.1) == 3
        assert _heat_level(0.9) == 3
        assert _heat_level(1.0) == 4


class TestJSONEscape(object):
    def test_plain_passthrough(self):
        assert _json_escape("hello") == "hello"

    def test_quote_and_backslash(self):
        assert _json_escape('a"b\\c') == 'a\\"b\\\\c'

    def test_control_chars(self):
        assert _json_escape("a\nb\tc\rd") == "a\\nb\\tc\\rd"
        assert _json_escape("\x01") == "\\u0001"

    def test_high_bytes_pass_through(self):
        # Lean identifiers can contain unicode (e.g. `≤`); UTF-8 bytes
        # should pass through as-is — JSON parsers accept raw UTF-8.
        assert _json_escape("\xe2\x89\xa4") == "\xe2\x89\xa4"


class TestParseSeconds(object):
    def test_none(self):
        assert _parse_seconds(None) == 0.0

    def test_bare_number_is_seconds(self):
        assert _parse_seconds("100") == 100.0

    def test_seconds_suffix(self):
        assert _parse_seconds("3s") == 3.0

    def test_milliseconds(self):
        assert _parse_seconds("500ms") == 0.5

    def test_minutes(self):
        assert _parse_seconds("2m") == 120.0

    def test_zero(self):
        assert _parse_seconds("0") == 0.0
        assert _parse_seconds("0s") == 0.0

    def test_invalid(self):
        try:
            _parse_seconds("nope")
        except UsageError as err:
            assert "Invalid threshold" in err.message
        else:
            assert False, "expected UsageError"

    def test_invalid_unit_value(self):
        try:
            _parse_seconds("xms")
        except UsageError as err:
            assert "Invalid threshold" in err.message
        else:
            assert False, "expected UsageError"

    def test_negative(self):
        try:
            _parse_seconds("-1")
        except UsageError as err:
            assert "Invalid threshold" in err.message
        else:
            assert False, "expected UsageError"


class TestParseBytes(object):
    def test_none(self):
        assert _parse_bytes(None) == 0

    def test_bare_number_is_bytes(self):
        assert _parse_bytes("4096") == 4096

    def test_kilobytes(self):
        assert _parse_bytes("4K") == 4096
        assert _parse_bytes("4KB") == 4096

    def test_megabytes(self):
        assert _parse_bytes("2M") == 2 * 1024 * 1024
        assert _parse_bytes("2MB") == 2 * 1024 * 1024

    def test_gigabytes(self):
        assert _parse_bytes("8G") == 8 * 1024 * 1024 * 1024
        assert _parse_bytes("8GB") == 8 * 1024 * 1024 * 1024

    def test_invalid(self):
        try:
            _parse_bytes("nope")
        except UsageError as err:
            assert "Invalid threshold" in err.message
        else:
            assert False, "expected UsageError"

    def test_negative(self):
        try:
            _parse_bytes("-1")
        except UsageError as err:
            assert "Invalid threshold" in err.message
        else:
            assert False, "expected UsageError"


class TestFFICollector(object):
    def test_already_registered_decl_is_checked_not_reregistered(self):
        """
        The walk reaching a constant the resolver already demand-loaded
        must not raise `AlreadyDeclared`, and must check the registered
        instance — the one other declarations resolved against.
        """
        from rpylean.cli import _FFICollector
        from rpylean.objects import name_dict
        from rpylean.parser import DeclarationHook

        class Record(DeclarationHook):
            seen = ()

            def on_declaration(self, decl):
                self.seen += (decl,)
                return False

        A = Name.simple("A")
        env = Environment(declarations=name_dict())
        registered = A.axiom(type=TYPE)
        env.register_declaration(registered, ordered=False)

        hook = Record()
        aborted = _FFICollector(env, hook)._handle(A.axiom(type=TYPE))

        assert not aborted
        assert hook.seen == (registered,)
        assert env.declarations[A] is registered


class TestShortOptionsAndJobs(object):
    def test_short_option_forms_and_help(self):
        cli = CLI()

        @cli.subcommand(
            ["*ARGS"],
            options=[("jobs", "Worker count.")],
            short_options=[("j", "jobs")],
            help="Test short opts.",
        )
        def work(self, args, stdin, stdout, stderr):
            stdout.write("jobs=%r varargs=%r\n" % (
                args.options["jobs"], args.varargs,
            ))
            return 0

        out, err = run(cli, ["prog", "work", "-j", "4", "a.ndjson"])
        assert out == "jobs='4' varargs=['a.ndjson']\n" and err == ""
        out, err = run(cli, ["prog", "work", "-j4", "a.ndjson"])
        assert out == "jobs='4' varargs=['a.ndjson']\n" and err == ""
        out, err = run(cli, ["prog", "work", "-j=4", "-"])
        assert out == "jobs='4' varargs=['-']\n" and err == ""
        _, err = run(cli, ["prog", "work", "-j"], exit=1)
        assert "Option -j requires an argument" in err
        _, err = run(cli, ["prog", "work", "-z", "x"], exit=1)
        assert "Unknown option: -z" in err
        _, err = run(cli, ["prog", "work", "--help"], exit=0)
        assert "-j, --jobs:" in err

    def test_parse_jobs_values(self):
        from rpylean._parallel import detect_cpus, parse_jobs

        assert parse_jobs(None) == detect_cpus()
        assert parse_jobs("1") == 1
        assert parse_jobs("4") == 4
        assert parse_jobs("auto") == detect_cpus()
        assert parse_jobs("0") == detect_cpus()
        for bad in ["-1", "nope", ""]:
            try:
                parse_jobs(bad)
            except UsageError as err:
                assert "Invalid --jobs" in err.message
            else:
                assert False, "expected UsageError for %r" % (bad,)

    def test_break_at_falls_back_on_default_jobs_and_rejects_explicit_parallel(self, tmpdir):
        export = tmpdir.join("ok.ndjson")
        export.write('{"meta":{"format":{"version":"3.1.0"}}}\n')
        # Without explicit -j, --break-at falls back to single-process checking.
        out, err = run(
            rpylean_cli,
            ["rpylean", "check", "--break-at", "Foo", str(export)],
            exit=0,
        )
        assert out == ""
        assert "0/0 decls checked" in err
        # Explicit -j > 1 with --break-at is still rejected.
        _, err = run(
            rpylean_cli,
            ["rpylean", "check", "-j", "2", "--break-at", "Foo", str(export)],
            exit=1,
        )
        assert "--break-at cannot be combined with --jobs > 1" in err

    def test_auto_default_skips_fork_for_tiny_batches(self, tmpdir):
        from rpylean._parallel import MIN_FORK_DECLS, start_parallel_batch, finish_parallel_batch
        from rpylean.cli import _DeclChunkRunner
        from rpylean.objects import name_dict

        path = self._write_multi_export(tmpdir)
        # Default (no -j) runs cleanly on tiny exports (< MIN_FORK_DECLS) without forking.
        out_def, err_def = run(rpylean_cli, ["rpylean", "check", "--color=no", path])
        out1, err1 = run(rpylean_cli, ["rpylean", "check", "--color=no", "-j", "1", path])
        assert out_def == out1 == ""
        assert "8/8 decls checked" in err_def
        assert "8/8 decls checked" in err1
        # Verify start_parallel_batch skips fork below MIN_FORK_DECLS even for non-empty batches.
        from rpylean.objects import W_Axiom, W_Declaration, W_LEVEL_ZERO
        env = Environment(declarations=name_dict())
        tiny = [
            W_Declaration(Name.simple("A"), W_LEVEL_ZERO.sort(), W_Axiom(), []),
            W_Declaration(Name.simple("B"), W_LEVEL_ZERO.sort(), W_Axiom(), []),
        ]
        for d in tiny:
            env.register_declaration(d)
        runner = _DeclChunkRunner(env, tiny, FORMAT_PLAIN, FORMAT_PLAIN, None, -1.0)
        inflight = start_parallel_batch(tiny, 4, runner, min_fork_decls=MIN_FORK_DECLS)
        assert inflight.work_r == -1
        res = finish_parallel_batch(inflight)
        assert res.total_checked == 2
        assert res.errors is None

    def _write_multi_export(self, tmpdir, bad_indices=()):
        """Build an export with 8 declarations (theorems + defs); indices in
        ``bad_indices`` have ill-typed values."""
        lines = [
            '{"meta":{"format":{"version":"3.1.0"}}}',
            '{"il":1,"succ":0}',
            '{"in":100,"str":{"pre":0,"str":"p"}}',
            '{"in":101,"str":{"pre":0,"str":"h"}}',
            '{"ie":0,"sort":1}',  # Type 0 (Sort 1)
            '{"ie":1,"sort":0}',  # Prop   (Sort 0)
            '{"ie":2,"bvar":0}',
            '{"ie":3,"bvar":1}',
            # ie 4: ∀ (h : p), p  (under binder p : Prop)
            '{"ie":4,"forallE":{"binderInfo":"default","body":3,"name":101,"type":2}}',
            # ie 5: ∀ (p : Prop) (h : p), p  (: Prop)
            '{"ie":5,"forallE":{"binderInfo":"default","body":4,"name":100,"type":1}}',
            # ie 6: fun (h : p) => h
            '{"ie":6,"lam":{"binderInfo":"default","body":2,"name":101,"type":2}}',
            # ie 7: fun (p : Prop) (h : p) => h  (: ∀ (p : Prop) (h : p), p)
            '{"ie":7,"lam":{"binderInfo":"default","body":6,"name":100,"type":1}}',
        ]
        for i in range(1, 9):
            lines.append('{"in":%d,"str":{"pre":0,"str":"D%d"}}' % (i, i))
            if i % 2 == 0:
                # Valid theorem: type=ie 5 (∀ p, p → p), value=ie 7; invalid: value=ie 1 (Prop)
                v_idx = 1 if i in bad_indices else 7
                lines.append(
                    '{"thm":{"all":[%d],"levelParams":[],"name":%d,'
                    '"type":5,"value":%d}}' % (i, i, v_idx)
                )
            else:
                # Valid def: type=Sort 1, value=Sort 0; invalid: type=Sort 0, value=Sort 0
                t_idx = 1 if i in bad_indices else 0
                lines.append(
                    '{"def":{"all":[%d],"hints":"opaque","levelParams":[],'
                    '"name":%d,"safety":"safe","type":%d,"value":1}}'
                    % (i, i, t_idx)
                )
        export = tmpdir.join("multi.ndjson")
        export.write("\n".join(lines) + "\n")
        return str(export)

    def test_parallel_check_passing_matches_sequential(self, tmpdir):
        path = self._write_multi_export(tmpdir)
        out1, err1 = run(rpylean_cli, ["rpylean", "check", "--color=no", "-j", "1", path])
        out4, err4 = run(
            rpylean_cli, ["rpylean", "check", "--color=no", "-j", "4", path],
        )
        assert out1 == out4 == ""
        assert "8/8 decls checked" in err1
        assert "8/8 decls checked" in err4

    def test_parallel_check_errors_deterministic_and_max_fail(self, tmpdir):
        path = self._write_multi_export(tmpdir, bad_indices=(2, 5, 7))
        _, err1 = run(
            rpylean_cli, ["rpylean", "check", "--color=no", "-j", "1", path], exit=1,
        )
        _, err4 = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "4", path],
            exit=1,
        )
        # Strip the trailing timing line ("checked in ...s") for exact compare.
        lines1 = [l for l in err1.splitlines() if not l.startswith("checked in ")]
        lines4 = [l for l in err4.splitlines() if not l.startswith("checked in ")]
        assert lines1 == lines4
        assert err4.index("D2") < err4.index("D5") < err4.index("D7")

        # --max-fail 1 must report ONLY the first failing decl (D2).
        _, err_mf = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "4", "--max-fail", "1", path],
            exit=1,
        )
        assert "D2" in err_mf
        assert "D5" not in err_mf
        assert "D7" not in err_mf

    def test_parallel_print_and_filter_match_sequential(self, tmpdir):
        path = self._write_multi_export(tmpdir, bad_indices=(4,))
        out1, _ = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "1", "--print", "name", path],
            exit=1,
        )
        out4, _ = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "4", "--print", "name", path],
            exit=1,
        )
        assert out1 == out4

        out_f, err_f = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "4", "--filter", "D1,D3,D6", path],
            exit=0,
        )
        assert out_f == ""
        assert "3/8 decls checked" in err_f

    def test_parallel_rejects_forward_reference_within_batch(self, tmpdir):
        # D1 references D2 which is declared AFTER D1 in the same batch.
        # Parallel batching must still reject D1 identically to -j 1.
        export = tmpdir.join("fwd.ndjson")
        export.write(
            '{"meta":{"format":{"version":"3.1.0"}}}\n'
            '{"il":1,"succ":0}\n'
            '{"in":1,"str":{"pre":0,"str":"D1"}}\n'
            '{"in":2,"str":{"pre":0,"str":"D2"}}\n'
            '{"ie":0,"sort":1}\n'
            '{"ie":1,"sort":0}\n'
            '{"ie":2,"const":{"name":2,"us":[]}}\n'
            '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":2}}\n'
            '{"def":{"all":[2],"hints":"opaque","levelParams":[],"name":2,"safety":"safe","type":0,"value":1}}\n'
        )
        _, err1 = run(rpylean_cli, ["rpylean", "check", "--color=no", "-j", "1", str(export)], exit=1)
        _, err4 = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "4", str(export)],
            exit=1,
        )
        # Both -j 1 (UnknownDeclaration) and -j 4 (W_NotYetDeclared) reject D1.
        assert "D1" in err1 and "D2" in err1
        assert "D1" in err4 and "D2" in err4
        assert "2/2 decls checked" in err1 and "2/2 decls checked" in err4

    def test_parallel_inductive_block_and_multi_batch_drop(self, tmpdir):
        # Valid inductive `Unit` + 6 theorems checked with tiny batch_size=2
        # to exercise multiple fork waves and proof dropping.
        from rpylean.cli import _ParallelChecker
        from rpylean.parser import EnvironmentBuilder, validate_export_metadata
        from rpylean.objects import W_Theorem, name_dict
        from rpython.rlib.streamio import open_file_as_stream

        export = tmpdir.join("ind.ndjson")
        export.write(
            '{"meta":{"format":{"version":"3.1.0"}}}\n'
            '{"il":1,"succ":0}\n'
            '{"in":1,"str":{"pre":0,"str":"U"}}\n'
            '{"in":2,"str":{"pre":1,"str":"mk"}}\n'
            '{"in":3,"str":{"pre":1,"str":"rec"}}\n'
            '{"in":4,"str":{"pre":0,"str":"motive"}}\n'
            '{"in":5,"str":{"pre":0,"str":"t"}}\n'
            '{"in":6,"str":{"pre":0,"str":"u"}}\n'
            '{"il":2,"param":6}\n'
            '{"ie":0,"sort":1}\n'
            '{"ie":1,"sort":0}\n'
            '{"ie":2,"const":{"name":1,"us":[]}}\n'
            '{"ie":3,"sort":2}\n'
            '{"ie":4,"forallE":{"binderInfo":"default","body":3,"name":5,"type":2}}\n'
            '{"ie":5,"bvar":0}\n'
            '{"ie":6,"bvar":1}\n'
            '{"ie":7,"bvar":2}\n'
            '{"ie":8,"const":{"name":2,"us":[]}}\n'
            '{"ie":9,"app":{"arg":8,"fn":5}}\n'
            '{"ie":10,"app":{"arg":5,"fn":7}}\n'
            '{"ie":11,"forallE":{"binderInfo":"default","body":10,"name":5,"type":2}}\n'
            '{"ie":12,"forallE":{"binderInfo":"default","body":11,"name":2,"type":9}}\n'
            '{"ie":13,"forallE":{"binderInfo":"implicit","body":12,"name":4,"type":4}}\n'
            '{"ie":14,"lam":{"binderInfo":"default","body":5,"name":2,"type":9}}\n'
            '{"ie":15,"lam":{"binderInfo":"implicit","body":14,"name":4,"type":4}}\n'
            '{"ie":16,"forallE":{"binderInfo":"default","body":6,"name":5,"type":5}}\n'
            '{"ie":17,"forallE":{"binderInfo":"default","body":16,"name":4,"type":1}}\n'
            '{"ie":18,"lam":{"binderInfo":"default","body":5,"name":5,"type":5}}\n'
            '{"ie":19,"lam":{"binderInfo":"default","body":18,"name":4,"type":1}}\n'
            '{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":2}],'
            '"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[6],"name":3,"numIndices":0,"numMinors":1,"numMotives":1,"numParams":0,'
            '"rules":[{"ctor":2,"nfields":0,"rhs":15}],"type":13}],'
            '"types":[{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}\n'
            '{"in":10,"str":{"pre":0,"str":"T1"}}\n'
            '{"in":11,"str":{"pre":0,"str":"T2"}}\n'
            '{"in":12,"str":{"pre":0,"str":"T3"}}\n'
            '{"in":13,"str":{"pre":0,"str":"T4"}}\n'
            '{"thm":{"all":[10],"levelParams":[],"name":10,"type":17,"value":19}}\n'
            '{"thm":{"all":[11],"levelParams":[],"name":11,"type":17,"value":19}}\n'
            '{"thm":{"all":[12],"levelParams":[],"name":12,"type":17,"value":19}}\n'
            '{"thm":{"all":[13],"levelParams":[],"name":13,"type":17,"value":19}}\n'
        )
        env = Environment(declarations=name_dict())
        out_s, err_s = StringIO(), StringIO()
        checker = _ParallelChecker(
            env=env,
            stdoutw=TokenWriter(out_s, FORMAT_PLAIN),
            stderrw=TokenWriter(err_s, FORMAT_PLAIN),
            printer=None,
            slow_secs=-1.0,
            filter_match=None,
            filter_names=None,
            abort_at=0,
            break_at=None,
            jobs=2,
            print_mode=None,
            batch_size=2,
        )
        stream = open_file_as_stream(str(export), "r", 0)
        try:
            validate_export_metadata(stream)
            EnvironmentBuilder(env=env).consume(stream, hook=checker)
            checker.finish()
        finally:
            stream.close()
        assert checker.failures == 0, err_s.getvalue()
        assert checker.n_checked == 7
        for tname in ["T1", "T2", "T3", "T4"]:
            wk = env.declarations[Name.simple(tname)].w_kind
            assert isinstance(wk, W_Theorem)
            assert wk.value is None

    def test_parallel_flushes_buffered_decls_before_export_error(self, tmpdir):
        # D1 fails type-checking; D2 duplicates D1 (ExportError during parse).
        # With --jobs 4, D1 must still be checked before reporting ExportError.
        export = tmpdir.join("dup.ndjson")
        export.write(
            '{"meta":{"format":{"version":"3.1.0"}}}\n'
            '{"il":1,"succ":0}\n'
            '{"in":1,"str":{"pre":0,"str":"D1"}}\n'
            '{"ie":0,"sort":0}\n'
            '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":0}}\n'
            '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":0}}\n'
        )
        _, err1 = run(rpylean_cli, ["rpylean", "check", "--color=no", "-j", "1", str(export)], exit=1)
        _, err4 = run(
            rpylean_cli, ["rpylean", "check", "--color=no", "-j", "4", str(export)], exit=1,
        )
        assert "already declared" in err1 and "already declared" in err4
        lines1 = [l for l in err1.splitlines() if not l.startswith("checked in ")]
        lines4 = [l for l in err4.splitlines() if not l.startswith("checked in ")]
        assert lines1 == lines4

        # With --max-fail 1, D1 hits max-fail so AlreadyDeclared is suppressed.
        _, err_mf1 = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "1", "--max-fail", "1", str(export)],
            exit=1,
        )
        _, err_mf4 = run(
            rpylean_cli,
            ["rpylean", "check", "--color=no", "-j", "4", "--max-fail", "1", str(export)],
            exit=1,
        )
        assert "already declared" not in err_mf1
        assert "already declared" not in err_mf4

    def test_cow_mode_never_mutates_expr_cache(self):
        from rpylean.objects import (
            Binder, HINT_ABBREV, W_App, W_BVar, W_ForAll, W_Lambda, W_Let,
            W_LEVEL_ZERO, W_Declaration, W_Definition, name_dict,
        )
        from rpylean.machine import reset_spare

        reset_spare()
        u = Name.simple("u")
        u_lvl = u.level()
        sort_u = u_lvl.sort()
        # Polymorphic identity: id.{u} : (A : Sort u) -> (a : A) -> A := fun A a => a
        id_name = Name.simple("id")
        id_type = W_ForAll(
            Binder(Name.simple("A"), sort_u),
            W_ForAll(Binder(Name.simple("a"), W_BVar(0)), W_BVar(1)),
        )
        id_val = W_Lambda(
            Binder(Name.simple("A"), sort_u),
            W_Lambda(Binder(Name.simple("a"), W_BVar(0)), W_BVar(0)),
        )
        id_decl = W_Declaration(
            name=id_name,
            levels=[u],
            type=id_type,
            w_kind=W_Definition(value=id_val, hint=HINT_ABBREV),
        )
        # Consumer with shared DAG subterms, let, and polymorphic constant app
        id_prop = id_name.const([W_LEVEL_ZERO.succ()])
        prop = W_LEVEL_ZERO.sort()
        shared = id_prop.app(prop)
        body = W_Let(
            Name.simple("z"),
            W_ForAll(Binder(Name.simple("x"), prop), prop),
            shared,
            W_App(W_BVar(0), W_App(shared, W_BVar(1))),
        )
        use_type = W_ForAll(Binder(Name.simple("p"), prop), prop)
        use_val = W_Lambda(Binder(Name.simple("p"), prop), body)
        use_decl = W_Declaration(
            name=Name.simple("use"),
            levels=[],
            type=use_type,
            w_kind=W_Definition(value=use_val, hint=HINT_ABBREV),
        )
        env = Environment(declarations=name_dict())
        env.cow_mode = True
        env.register_declaration(id_decl)
        env.register_declaration(use_decl)

        # Ensure every W_Expr starts with _cache == 0
        all_exprs = [
            sort_u, id_type, id_type.body, id_val, id_val.body,
            id_prop, prop, shared, body, body.type, body.body,
            use_type, use_val,
        ]
        for e in all_exprs:
            e._cache = 0

        res1 = env.type_check_one(id_decl)
        res2 = env.type_check_one(use_decl)
        assert res1.error is None
        assert res2.error is None
        for e in all_exprs:
            assert e._cache == 0, "cow_mode wrote _cache on %r" % (e,)
        reset_spare()
