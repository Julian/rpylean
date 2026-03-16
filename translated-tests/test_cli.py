"""
Tests of the translated binary.
"""

from __future__ import print_function

import os
import subprocess
from textwrap import dedent

from rpylean.parser import EXPORT_VERSION


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
    stdout, stderr = process.communicate(
        '{"meta":{"format":{"version":"%s"}}}\n' % (EXPORT_VERSION,),
    )

    assert stdout == "", (stdout, stderr)


def test_no_such_file():
    process = rpylean("nonexistent/path")
    stdout, stderr = process.communicate()

    assert stdout == "", stdout
    assert stderr.strip().startswith("`nonexistent/path` does not exist.")


def test_invalid_def_exits_nonzero():
    process = rpylean("-")
    stdout, stderr = process.communicate(
        dedent("""\
            {"meta":{"format":{"version":"%s"}}}
            {"in":1,"str":{"pre":0,"str":"Anon"}}
            {"il":1,"succ":0}
            {"ie":0,"sort":0}
            {"ie":1,"sort":1}
            {"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}
        """)
        % (EXPORT_VERSION,),
    )

    assert process.returncode != 0, (stdout, stderr)
