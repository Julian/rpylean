"""
Tests of the translated binary.
"""
from __future__ import print_function

import os
import subprocess


def test_no_such_file():
    process = subprocess.Popen(
        ["rpylean-c", "nonexistent/path"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=dict(os.environ, PATH=".:" + os.environ.get("PATH", ""))
    )
    stdout, stderr = process.communicate()

    assert stdout == "", stdout
    assert stderr.strip().startswith("`nonexistent/path` does not exist.\n")
