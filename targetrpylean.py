#!/usr/bin/env python
"""RPython translation target for rpylean."""

from __future__ import print_function

import subprocess
import sys

import py

from rpylean.cli import cli
import rpylean


def git(*argv):
    cmd = ["git"]
    cmd.extend(argv)
    return subprocess.check_output(cmd, stderr=subprocess.PIPE)


try:
    result = git("describe", "--always", "HEAD")
except (subprocess.CalledProcessError, OSError):
    git_version = "unknown"
else:
    git_version = result.decode("utf-8").strip()
    if git("status", "--porcelain"):
        git_version += "+dirty"


VERSION_TEMPLATE = """\
# Auto-generated during translation - do not edit manually
__version__ = "%s"
"""
VERSION_FILE = py.path.local(rpylean.__file__).dirpath().join("_version.py")
VERSION_FILE.write_binary(VERSION_TEMPLATE % (git_version,))
print(
    "Updated %s with version: %s" % (VERSION_FILE, git_version,),
    file=sys.stderr,
)


def main(argv):
    return cli.main(argv)


def target(driver, args):
    driver.exe_name = "rpylean-%(backend)s"
    return main
