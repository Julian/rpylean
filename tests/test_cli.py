from io import BytesIO

from rpylean._rcli import CLI, Args


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
