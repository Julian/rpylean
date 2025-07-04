from io import BytesIO

from rpylean._rcli import CLI


def run(cli, argv, exit=0):
    stdin = BytesIO()
    stdout, stderr = BytesIO(), BytesIO()
    got = cli.main(argv, (stdin, stdout, stderr))
    assert got == exit, stderr.getvalue()
    return stdout.getvalue(), stderr.getvalue()


def test_usage_error_on_no_args():
    cli = CLI()
    @cli.subcommand(["ARG"], help="Test command help.")
    def test(self, args, varargs, stdin, stdout, stderr):
        stdout.write("ran test with %s\n" % args[0])
        return 0
    out, err = run(cli, ["prog"])
    assert "USAGE" in err


def test_known_command_runs():
    cli = CLI()
    @cli.subcommand(["ARG"], help="Test command help.")
    def test(self, args, varargs, stdin, stdout, stderr):
        stdout.write("ran test with %s\n" % args[0])
        return 0
    out, err = run(cli, ["prog", "test", "foo"])
    assert "ran test with foo" in out


def test_unknown_command_falls_back_to_default():
    cli = CLI(default="foo")
    @cli.subcommand(["ARG"], help="Fallback here.")
    def foo(self, args, varargs, stdin, stdout, stderr):
        assert args == ["unknown"]
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
    def vargs(self, args, varargs, stdin, stdout, stderr):
        stdout.write("args=%r varargs=%r\n" % (args, varargs))
        return 0
    out, err = run(cli, ["prog", "vargs", "foo", "bar", "baz"])
    assert "args=['foo'] varargs=['bar', 'baz']" in out


def test_too_few_args():
    cli = CLI()
    @cli.subcommand(["A", "B"], help="Needs two args.")
    def tworeq(self, args, varargs, stdin, stdout, stderr):
        stdout.write("should not get here\n")
        return 0
    out, err = run(cli, ["prog", "tworeq", "onlyone"], exit=1)
    assert "Expected an B" in err
    assert out == ""


def test_too_many_args():
    cli = CLI()
    @cli.subcommand(["A"], help="Only one arg.")
    def onearg(self, args, varargs, stdin, stdout, stderr):
        stdout.write("should not get here\n")
        return 0
    out, err = run(cli, ["prog", "onearg", "a", "b"], exit=1)
    assert "Unknown arguments: ['b']" in err
    assert out == ""


def test_help_for_command():
    cli = CLI()
    @cli.subcommand(["A"], help="Help for foo command.")
    def foo(self, args, varargs, stdin, stdout, stderr):
        stdout.write("should not get here\n")
        return 0
    out, err = run(cli, ["prog", "foo", "--help"])
    assert "Help for foo command." in err
    assert "USAGE" in err
