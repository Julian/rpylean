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
    assert "Nat.succ ... OK" in names, names
    assert "Eq.refl ... OK" in names, names


def test_ffi_export_decodes_big_nat_literals():
    """`UInt64.size = 2^64` — a literal that overflows a 63-bit word
    and lives in Lean's runtime as a `LeanMPZ` heap object. Exercises
    the GMP-limb decode path in `_read_mpz`."""
    if not _lean_on_path():
        import pytest
        pytest.skip("`lean` not on PATH")

    process = rpylean(
        "ffi", "export", "--filter", "UInt64.size", "Init",
    )
    stdout, stderr = process.communicate()
    assert process.returncode == 0, (stdout, stderr)
    assert '"natVal":"18446744073709551616"' in stdout, stdout


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

    assert stdout == "basicDef ... OK\n", (stdout, stderr)


def test_level_dependent_prop_mask_distinct_plans_and_parallel(tmpdir):
    """Regression test for RPython flowspace constant-folding `len()` on a
    prebuilt module-level `_PROP_MASK_PLANS` list:
      1. Checking a 2-level decl before a 1-level decl must not read past
         the 1-level `W_Const.levels` array (previously SIGSEGV).
      2. Checking a 1-level decl (`G.{u} : Sort u -> Type -> u -> Prop`)
         before a 2-level decl (`H.{u,v} : Sort u -> Sort v -> v -> Prop`)
         must NOT let `H.{0, 1}` inherit `G`'s plan (which checked `levels[0]`,
         falsely treating `H`'s `Sort 1` argument as Prop!).
      3. Both `-j 1` and `-j 4` must agree.
    """
    # Part 1: 2-level F checked BEFORE 1-level G (both valid).
    valid_two_before_one = META + dedent("""\
        {"in":1,"str":{"pre":0,"str":"P"}}
        {"in":2,"str":{"pre":0,"str":"A"}}
        {"in":3,"str":{"pre":0,"str":"F"}}
        {"in":4,"str":{"pre":0,"str":"G"}}
        {"in":5,"str":{"pre":0,"str":"u"}}
        {"in":6,"str":{"pre":0,"str":"v"}}
        {"in":7,"str":{"pre":0,"str":"x"}}
        {"in":8,"str":{"pre":0,"str":"h1"}}
        {"in":9,"str":{"pre":0,"str":"h2"}}
        {"in":10,"str":{"pre":0,"str":"okF"}}
        {"in":11,"str":{"pre":0,"str":"okG"}}
        {"il":1,"succ":0}
        {"il":2,"param":5}
        {"il":3,"param":6}
        {"ie":0,"sort":0}
        {"ie":1,"sort":1}
        {"ie":2,"sort":2}
        {"ie":3,"sort":3}
        {"ie":4,"bvar":0}
        {"ie":5,"bvar":1}
        {"ie":6,"bvar":2}
        {"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}
        {"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":1}}
        {"ie":7,"forallE":{"binderInfo":"default","body":0,"name":7,"type":4}}
        {"ie":8,"forallE":{"binderInfo":"default","body":7,"name":7,"type":3}}
        {"ie":9,"forallE":{"binderInfo":"default","body":8,"name":7,"type":2}}
        {"axiom":{"isUnsafe":false,"levelParams":[5,6],"name":3,"type":9}}
        {"ie":10,"forallE":{"binderInfo":"default","body":7,"name":7,"type":2}}
        {"axiom":{"isUnsafe":false,"levelParams":[5],"name":4,"type":10}}
        {"ie":11,"const":{"name":1,"us":[]}}
        {"ie":12,"const":{"name":2,"us":[]}}
        {"ie":13,"const":{"name":3,"us":[1,0]}}
        {"ie":14,"const":{"name":4,"us":[0]}}
        {"ie":15,"app":{"arg":12,"fn":13}}
        {"ie":16,"app":{"arg":11,"fn":15}}
        {"ie":17,"app":{"arg":5,"fn":16}}
        {"ie":18,"app":{"arg":4,"fn":16}}
        {"ie":19,"app":{"arg":5,"fn":16}}
        {"ie":20,"forallE":{"binderInfo":"default","body":19,"name":7,"type":17}}
        {"ie":21,"forallE":{"binderInfo":"default","body":20,"name":9,"type":11}}
        {"ie":22,"forallE":{"binderInfo":"default","body":21,"name":8,"type":11}}
        {"ie":23,"lam":{"binderInfo":"default","body":4,"name":7,"type":17}}
        {"ie":24,"lam":{"binderInfo":"default","body":23,"name":9,"type":11}}
        {"ie":25,"lam":{"binderInfo":"default","body":24,"name":8,"type":11}}
        {"def":{"all":[10],"hints":"opaque","levelParams":[],"name":10,"safety":"safe","type":22,"value":25}}
        {"ie":26,"app":{"arg":11,"fn":14}}
        {"ie":27,"app":{"arg":5,"fn":26}}
        {"ie":28,"app":{"arg":4,"fn":26}}
        {"ie":29,"forallE":{"binderInfo":"default","body":27,"name":7,"type":27}}
        {"ie":30,"forallE":{"binderInfo":"default","body":29,"name":9,"type":11}}
        {"ie":31,"forallE":{"binderInfo":"default","body":30,"name":8,"type":11}}
        {"ie":32,"lam":{"binderInfo":"default","body":4,"name":7,"type":27}}
        {"ie":33,"lam":{"binderInfo":"default","body":32,"name":9,"type":11}}
        {"ie":34,"lam":{"binderInfo":"default","body":33,"name":8,"type":11}}
        {"ie":35,"app":{"arg":6,"fn":16}}
        {"ie":36,"app":{"arg":5,"fn":16}}
        {"ie":37,"forallE":{"binderInfo":"default","body":36,"name":7,"type":17}}
        {"ie":38,"forallE":{"binderInfo":"default","body":37,"name":9,"type":11}}
        {"ie":39,"forallE":{"binderInfo":"default","body":38,"name":8,"type":11}}
        {"ie":40,"app":{"arg":6,"fn":26}}
        {"ie":41,"app":{"arg":5,"fn":26}}
        {"ie":42,"forallE":{"binderInfo":"default","body":41,"name":7,"type":27}}
        {"ie":43,"forallE":{"binderInfo":"default","body":42,"name":9,"type":11}}
        {"ie":44,"forallE":{"binderInfo":"default","body":43,"name":8,"type":11}}
        {"def":{"all":[11],"hints":"opaque","levelParams":[],"name":11,"safety":"safe","type":44,"value":34}}
    """)
    p_valid = tmpdir.join("pm_valid.ndjson")
    p_valid.write(valid_two_before_one)
    for jobs in ["1", "4"]:
        proc = rpylean("check", "-j", jobs, str(p_valid))
        out, err = proc.communicate()
        assert proc.returncode == 0, (jobs, out, err)

    # Part 2: Soundness — 1-level G.{u} : (α : Sort u) → (β : Type) → α → Prop
    # checked first, then 2-level H.{u, v} : (α : Sort u) → (β : Sort v) → β → Prop
    # must REJECT equating `H.{0, 1} P A a1` with `H.{0, 1} P A a2`.
    unsound_mix = META + dedent("""\
        {"in":1,"str":{"pre":0,"str":"P"}}
        {"in":2,"str":{"pre":0,"str":"A"}}
        {"in":3,"str":{"pre":0,"str":"a1"}}
        {"in":4,"str":{"pre":0,"str":"a2"}}
        {"in":5,"str":{"pre":0,"str":"G"}}
        {"in":6,"str":{"pre":0,"str":"H"}}
        {"in":7,"str":{"pre":0,"str":"u"}}
        {"in":8,"str":{"pre":0,"str":"v"}}
        {"in":9,"str":{"pre":0,"str":"x"}}
        {"in":10,"str":{"pre":0,"str":"h1"}}
        {"in":11,"str":{"pre":0,"str":"h2"}}
        {"in":12,"str":{"pre":0,"str":"okG"}}
        {"in":13,"str":{"pre":0,"str":"badH"}}
        {"il":1,"succ":0}
        {"il":2,"param":7}
        {"il":3,"param":8}
        {"ie":0,"sort":0}
        {"ie":1,"sort":1}
        {"ie":2,"sort":2}
        {"ie":3,"sort":3}
        {"ie":4,"bvar":0}
        {"ie":5,"bvar":1}
        {"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}
        {"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":1}}
        {"ie":6,"const":{"name":1,"us":[]}}
        {"ie":7,"const":{"name":2,"us":[]}}
        {"axiom":{"isUnsafe":false,"levelParams":[],"name":3,"type":7}}
        {"axiom":{"isUnsafe":false,"levelParams":[],"name":4,"type":7}}
        {"ie":8,"const":{"name":3,"us":[]}}
        {"ie":9,"const":{"name":4,"us":[]}}
        {"ie":10,"forallE":{"binderInfo":"default","body":0,"name":9,"type":5}}
        {"ie":11,"forallE":{"binderInfo":"default","body":10,"name":9,"type":1}}
        {"ie":12,"forallE":{"binderInfo":"default","body":11,"name":9,"type":2}}
        {"axiom":{"isUnsafe":false,"levelParams":[7],"name":5,"type":12}}
        {"ie":13,"forallE":{"binderInfo":"default","body":0,"name":9,"type":4}}
        {"ie":14,"forallE":{"binderInfo":"default","body":13,"name":9,"type":3}}
        {"ie":15,"forallE":{"binderInfo":"default","body":14,"name":9,"type":2}}
        {"axiom":{"isUnsafe":false,"levelParams":[7,8],"name":6,"type":15}}
        {"ie":16,"const":{"name":5,"us":[0]}}
        {"ie":17,"app":{"arg":6,"fn":16}}
        {"ie":18,"app":{"arg":7,"fn":17}}
        {"ie":19,"app":{"arg":5,"fn":18}}
        {"ie":20,"app":{"arg":4,"fn":18}}
        {"ie":21,"forallE":{"binderInfo":"default","body":19,"name":9,"type":19}}
        {"ie":22,"forallE":{"binderInfo":"default","body":21,"name":11,"type":6}}
        {"ie":23,"forallE":{"binderInfo":"default","body":22,"name":10,"type":6}}
        {"ie":24,"lam":{"binderInfo":"default","body":4,"name":9,"type":19}}
        {"ie":25,"lam":{"binderInfo":"default","body":24,"name":11,"type":6}}
        {"ie":26,"lam":{"binderInfo":"default","body":25,"name":10,"type":6}}
        {"ie":27,"app":{"arg":5,"fn":18}}
        {"ie":28,"forallE":{"binderInfo":"default","body":27,"name":9,"type":19}}
        {"ie":29,"forallE":{"binderInfo":"default","body":28,"name":11,"type":6}}
        {"ie":30,"forallE":{"binderInfo":"default","body":29,"name":10,"type":6}}
        {"ie":31,"lam":{"binderInfo":"default","body":4,"name":9,"type":19}}
        {"ie":32,"lam":{"binderInfo":"default","body":31,"name":11,"type":6}}
        {"ie":33,"lam":{"binderInfo":"default","body":32,"name":10,"type":6}}
        {"def":{"all":[12],"hints":"opaque","levelParams":[],"name":12,"safety":"safe","type":30,"value":33}}
        {"ie":34,"const":{"name":6,"us":[0,1]}}
        {"ie":35,"app":{"arg":6,"fn":34}}
        {"ie":36,"app":{"arg":7,"fn":35}}
        {"ie":37,"app":{"arg":8,"fn":36}}
        {"ie":38,"app":{"arg":9,"fn":36}}
        {"ie":39,"forallE":{"binderInfo":"default","body":38,"name":9,"type":37}}
        {"ie":40,"lam":{"binderInfo":"default","body":4,"name":9,"type":37}}
        {"def":{"all":[13],"hints":"opaque","levelParams":[],"name":13,"safety":"safe","type":39,"value":40}}
    """)
    p_bad = tmpdir.join("pm_bad.ndjson")
    p_bad.write(unsound_mix)
    for jobs in ["1", "4"]:
        proc = rpylean("check", "-j", jobs, str(p_bad))
        out, err = proc.communicate()
        assert proc.returncode != 0, (jobs, out, err)
        assert "badH" in err, (jobs, err)
