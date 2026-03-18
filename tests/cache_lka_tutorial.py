"""
Download and cache the Lean Kernel Arena tutorial NDJSON test files.

On first run, fetches the archive from the arena and extracts the tutorial
tests into <repo>/.cache/tutorial/good/ and <repo>/.cache/tutorial/bad/.
Subsequent runs send a conditional GET (If-None-Match) and skip extraction
when the server returns 304 Not Modified.

Run as a script to ensure the cache is populated and print the cache directory:

    pypy tests/cache_lka_tutorial.py
"""

from __future__ import print_function

import tarfile
import urllib2

import py


_ARENA_URL = "https://arena.lean-lang.org/lean-arena-tests.tar.gz"
_CACHE_DIR = py.path.local(__file__).dirpath().dirpath().join(".cache", "tutorial")
_ETAG_FILE = _CACHE_DIR.join("etag")


def ensure_downloaded():
    """
    Ensure tutorial NDJSON files are cached locally, downloading if needed.

    Returns the cache directory as a ``py.path.local``.
    """
    good_dir = _CACHE_DIR.join("good")
    bad_dir = _CACHE_DIR.join("bad")
    cached = good_dir.isdir() and bad_dir.isdir()

    headers = {}
    if cached and _ETAG_FILE.isfile():
        headers["If-None-Match"] = _ETAG_FILE.read().strip()

    request = urllib2.Request(_ARENA_URL, headers=headers)
    try:
        response = urllib2.urlopen(request)
    except urllib2.HTTPError as e:
        if e.code == 304:
            return _CACHE_DIR  # Not Modified -- cache is current
        raise RuntimeError(
            "Failed to download lean-kernel-arena test archive: HTTP %d" % e.code
        )
    except Exception as e:
        raise RuntimeError("Failed to download lean-kernel-arena test archive: %s" % e)

    # 200 OK -- extract tutorial files from the streaming response
    _CACHE_DIR.ensure(dir=True)
    good_dir.ensure(dir=True)
    bad_dir.ensure(dir=True)

    with tarfile.open(fileobj=response, mode="r|gz") as tar:
        for member in tar:
            if member.name.startswith("good/tutorial/") and member.name.endswith(
                ".ndjson"
            ):
                dest = good_dir.join(py.path.local(member.name).basename)
                dest.write(tar.extractfile(member).read(), mode="wb")
            elif member.name.startswith("bad/tutorial/") and member.name.endswith(
                ".ndjson"
            ):
                dest = bad_dir.join(py.path.local(member.name).basename)
                dest.write(tar.extractfile(member).read(), mode="wb")

    etag = response.info().getheader("ETag") or response.info().getheader(
        "Last-Modified"
    )
    if etag:
        _ETAG_FILE.write(etag)

    return _CACHE_DIR


if __name__ == "__main__":
    print(ensure_downloaded())
