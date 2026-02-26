"""
Tests of the translated binary.
"""
from __future__ import print_function

import os
import subprocess

from rpylean.parser import EXPORT_VERSION


def rpylean(*args, **kwargs):
    return subprocess.Popen(
        ["rpylean-c"] + list(args),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=dict(os.environ, PATH=".:" + os.environ.get("PATH", ""))
    )


def test_stdin():
    process = rpylean("-")
    stdout, stderr = process.communicate(
        '{"meta":{"format":{"version":"%s"}}}\n' % (EXPORT_VERSION,),
    )

    assert stdout == "", (stdout, stderr)
    assert "All declarations are type-correct." in stderr,  (stdout, stderr)


def test_no_such_file():
    process = rpylean("nonexistent/path")
    stdout, stderr = process.communicate()

    assert stdout == "", stdout
    assert stderr.strip().startswith("`nonexistent/path` does not exist.")
