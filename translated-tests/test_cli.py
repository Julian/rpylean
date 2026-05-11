"""
Tests of the translated binary.
"""

from __future__ import print_function

import os
import subprocess
from textwrap import dedent

from rpylean.parser import EXPORT_VERSION

META = '{"meta":{"format":{"version":"%s"}}}\n' % (EXPORT_VERSION,)

#: A valid export defining ``def basicDef : Type := Prop``.
VALID_EXPORT = META + dedent("""\
    {"in":1,"str":{"pre":0,"str":"basicDef"}}
    {"il":1,"succ":0}
    {"ie":0,"sort":1}
    {"ie":1,"sort":0}
    {"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}
""")

#: An invalid export with duplicate level parameter ``u``.
INVALID_EXPORT = META + dedent("""\
    {"in":1,"str":{"pre":0,"str":"bad"}}
    {"in":2,"str":{"pre":0,"str":"u"}}
    {"il":1,"param":2}
    {"il":2,"succ":0}
    {"ie":0,"sort":2}
    {"ie":1,"sort":0}
    {"def":{"all":[1],"hints":"opaque","levelParams":[2,2],"name":1,"safety":"safe","type":0,"value":1}}
""")


def rpylean(*args, **kwargs):
    return subprocess.Popen(
        ["rpylean-c"] + list(args),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=dict(os.environ, PATH=".:" + os.environ.get("PATH", "")),
    )


def test_stdin():
    process = rpylean("-")
    stdout, stderr = process.communicate(META)

    assert stdout == "", (stdout, stderr)


def test_no_such_file():
    process = rpylean("nonexistent/path")
    stdout, stderr = process.communicate()

    assert stdout == "", stdout
    assert stderr.strip().startswith("`nonexistent/path` does not exist.")


def test_invalid_def_exits_nonzero():
    process = rpylean("-")
    stdout, stderr = process.communicate(
        META + dedent("""\
            {"in":1,"str":{"pre":0,"str":"Anon"}}
            {"il":1,"succ":0}
            {"ie":0,"sort":0}
            {"ie":1,"sort":1}
            {"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}
        """),
    )

    assert process.returncode != 0, (stdout, stderr)


def _lean_on_path():
    try:
        subprocess.check_output(["lean", "--print-prefix"],
                                stderr=subprocess.PIPE)
    except (OSError, subprocess.CalledProcessError):
        return False
    return True


def test_ffi_check_against_pinned_toolchain():
    """End-to-end smoke against whatever `lean` resolves to.

    In CI that's the toolchain pinned by `lean-toolchain` (picked up by
    `Julian/setup-lean`). Locally it's whatever the user has installed.
    Either way: exercises FFI startup, the deep self-test, the prefix
    auto-detection path, and find_constant + walk on a handful of
    stable Init declarations.
    """
    if not _lean_on_path():
        import pytest
        pytest.skip("`lean` not on PATH")

    process = rpylean(
        "ffi", "check", "--filter", "Nat,Eq.refl,Nat.succ", "Init",
    )
    stdout, stderr = process.communicate()
    assert process.returncode == 0, (stdout, stderr)


def test_ffi_export_emits_valid_meta_and_decls():
    """`ffi export --filter ... Init` writes a valid lean4export-format
    NDJSON header, contains the requested constants, and round-trips
    through the parser side (`check --print=names`) without errors."""
    if not _lean_on_path():
        import pytest
        pytest.skip("`lean` not on PATH")

    process = rpylean(
        "ffi", "export", "--filter", "Nat.succ", "Init",
    )
    stdout, stderr = process.communicate()
    assert process.returncode == 0, (stdout, stderr)
    lines = stdout.splitlines()
    assert lines, stdout
    assert lines[0].startswith('{"meta"'), lines[0]
    assert any('"inductive"' in line for line in lines), stdout
    assert any('"str":"succ"' in line for line in lines), stdout


def test_ffi_export_roundtrips_through_check(tmpdir):
    """The two halves of rpylean agree: the names the FFI walker emits
    are the names the NDJSON parser reads back. Pulls a tiny, stable
    slice of Init so this stays fast and not coupled to iota gaps."""
    if not _lean_on_path():
        import pytest
        pytest.skip("`lean` not on PATH")

    process = rpylean(
        "ffi", "export", "--filter", "Nat.succ,Eq.refl", "Init",
    )
    stdout, stderr = process.communicate()
    assert process.returncode == 0, (stdout, stderr)

    exported = tmpdir.join("nat-eq.ndjson")
    # `tmpdir.write` is text-mode and chokes on non-ASCII bytes from
    # Init names like `α`; write raw bytes through.
    with open(str(exported), "wb") as f:
        f.write(stdout)

    check = rpylean("check", "--print=names", str(exported))
    out, err = check.communicate()
    assert check.returncode == 0, (out, err)
    names = out.splitlines()
    assert "Nat.succ" in names, names
    assert "Eq.refl" in names, names


def test_ffi_repl_loads_env_via_command():
    """`ffi repl --command "print Nat.succ" Init` starts the REPL with
    Init imported, runs the one command, and exits. Smoke-tests that
    the FFI-loaded env behaves like the export-loaded one for the
    existing REPL commands."""
    if not _lean_on_path():
        import pytest
        pytest.skip("`lean` not on PATH")

    process = rpylean(
        "ffi", "repl", "--command", "print Nat.succ", "Init",
    )
    stdout, stderr = process.communicate()
    assert process.returncode == 0, (stdout, stderr)
    assert "constructor Nat.succ" in stdout, stdout


def test_export_error_does_not_skip_remaining_files(tmpdir):
    invalid = tmpdir.join("invalid.ndjson")
    invalid.write(INVALID_EXPORT)

    valid = tmpdir.join("valid.ndjson")
    valid.write(VALID_EXPORT)

    process = rpylean("check", "--print=names", str(invalid), str(valid))
    stdout, stderr = process.communicate()

    assert stdout == "basicDef\n", (stdout, stderr)
