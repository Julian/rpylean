"""
Optional line editing for the REPL via libedit or GNU readline.

We dlopen the platform's native line-editing library at runtime and use
its ``readline``/``add_history`` to give the REPL history navigation and
cursor editing. GNU readline and BSD libedit export the same symbols, so
a single binding covers either one; the caller falls back to a plain
``stdin.readline()`` when neither library is present.
"""
from __future__ import print_function

import os
import sys

from rpython.rlib import rlocale
from rpython.rlib.rdynload import (
    DLOpenError,
    RTLD_NOW,
    dlclose,
    dlopen,
    dlsym,
)
from rpython.rtyper.lltypesystem import lltype, rffi
from rpython.rtyper.lltypesystem.lltype import FuncType, Ptr, Void


#: ``char *readline(const char *prompt)``
RL_READLINE = Ptr(FuncType([rffi.CCHARP], rffi.CCHARP))
#: ``void add_history(const char *line)``
RL_ADD_HISTORY = Ptr(FuncType([rffi.CCHARP], Void))
#: ``int read_history(const char *)`` / ``int write_history(const char *)``
RL_HISTORY_FILE = Ptr(FuncType([rffi.CCHARP], rffi.INT))
#: ``int history_truncate_file(const char *, int nlines)``
RL_TRUNCATE_FILE = Ptr(FuncType([rffi.CCHARP, rffi.INT], rffi.INT))

#: Cap on the saved history file, so it doesn't grow without bound.
HISTORY_MAX = 1000

#: ``readline`` hands back a ``malloc``'d buffer the caller must ``free``.
c_free = rffi.llexternal("free", [rffi.VOIDP], lltype.Void, _nowrapper=True)

#: GNU readline's markers bracketing non-printing characters in a prompt.
RL_IGNORE_START = "\001"
RL_IGNORE_END = "\002"


def _marked_prompt(prefix, text, reset):
    """
    Assemble a coloured prompt for GNU readline.

    Brackets the colour escapes with ``\001``/``\002`` so readline measures
    the prompt's visible width correctly across edits and line wraps.
    """
    if not prefix:
        return text
    return (
        RL_IGNORE_START + prefix + RL_IGNORE_END
        + text
        + RL_IGNORE_START + reset + RL_IGNORE_END
    )


def _bare_prompt(prefix, text, reset):
    """
    Assemble a coloured prompt for libedit.

    libedit hoists bracketed escapes to the front of the prompt (cancelling
    the colour), so the escapes are left inline and unmarked instead.
    """
    if not prefix:
        return text
    return prefix + text + reset

#: Candidate shared libraries, in per-platform preference order. Names for
#: the wrong platform simply fail to ``dlopen`` and are skipped.
_CANDIDATES = [
    "libedit.dylib", "libedit.3.dylib",     # macOS / BSD: native
    "libreadline.dylib",                     # macOS: Homebrew readline
    "libreadline.so", "libreadline.so.8",    # Linux: native
    "libreadline.so.7", "libreadline.so.6",
    "libedit.so.2", "libedit.so.0", "libedit.so",  # Linux: libedit fallback
]


if sys.platform == "darwin":
    def _cache_dir():
        """The per-user cache directory: ``~/Library/Caches``."""
        home = os.environ.get("HOME")
        if not home:
            return ""
        return home + "/Library/Caches"
else:
    def _cache_dir():
        """The per-user cache directory: ``$XDG_CACHE_HOME`` or ``~/.cache``."""
        xdg = os.environ.get("XDG_CACHE_HOME")
        if xdg:
            return xdg
        home = os.environ.get("HOME")
        if not home:
            return ""
        return home + "/.cache"


def _ensure_dir(path):
    try:
        os.mkdir(path, 0o755)
    except OSError:
        pass  # already exists, or the parent is missing; history just won't persist


def _history_path():
    cache = _cache_dir()
    if not cache:
        return ""
    _ensure_dir(cache)
    app = cache + "/rpylean"
    _ensure_dir(app)
    return app + "/history"


def _set_ctype_locale():
    """
    Apply the environment's character encoding for the line editor.

    ``readline`` needs ``LC_CTYPE`` set to measure the width of the multi-byte
    ``∃∀`` prompt glyphs correctly.
    """
    category = rlocale.cConfig.LC_CTYPE
    if category is None:
        return
    try:
        rlocale.setlocale(category, "")
    except rlocale.LocaleError:
        pass


class LineEditor(object):
    """A thin wrapper over a dlopen'd ``readline``-compatible library."""

    _attrs_ = [
        "_handle",
        "_readline",
        "_add_history",
        "_read_history",
        "_write_history",
        "_truncate_history",
        "_history_path",
        "format_prompt",
        "_last_history",
    ]
    _immutable_fields_ = [
        "_handle",
        "_readline",
        "_add_history",
        "_read_history",
        "_write_history",
        "_truncate_history",
        "_history_path",
        "format_prompt",
    ]

    def __init__(
        self,
        handle,
        readline,
        add_history,
        read_history,
        write_history,
        truncate_history,
        history_path,
        format_prompt,
    ):
        self._handle = handle
        self._readline = readline
        self._add_history = add_history
        self._read_history = read_history
        self._write_history = write_history
        self._truncate_history = truncate_history
        self._history_path = history_path
        #: ``(prefix, text, reset) -> str``: assembles a coloured prompt the
        #: loaded library renders correctly. See ``_marked_prompt`` (GNU
        #: readline) and ``_bare_prompt`` (libedit).
        self.format_prompt = format_prompt
        #: The last line added to history, to collapse adjacent duplicates.
        self._last_history = ""

    def readline(self, prompt):
        """
        Read a line without its trailing newline, or ``None`` at end of input.

        End of input is Ctrl-D on an empty line.
        """
        with rffi.scoped_str2charp(prompt) as ll_prompt:
            ll_line = self._readline(ll_prompt)
        if not ll_line:
            return None
        line = rffi.charp2str(ll_line)
        c_free(rffi.cast(rffi.VOIDP, ll_line))
        return line

    def add_history(self, line):
        if line == self._last_history:
            return
        self._last_history = line
        with rffi.scoped_str2charp(line) as ll_line:
            self._add_history(ll_line)

    def load_history(self):
        if not self._read_history or not self._history_path:
            return
        with rffi.scoped_str2charp(self._history_path) as ll_path:
            self._read_history(ll_path)

    def save_history(self):
        if not self._write_history or not self._history_path:
            return
        with rffi.scoped_str2charp(self._history_path) as ll_path:
            self._write_history(ll_path)
            if self._truncate_history:
                self._truncate_history(ll_path, rffi.cast(rffi.INT, HISTORY_MAX))


def try_open():
    """
    Open the first available line-editing library, or ``None`` if none load.
    """
    null_history = lltype.nullptr(RL_HISTORY_FILE.TO)
    null_truncate = lltype.nullptr(RL_TRUNCATE_FILE.TO)
    for name in _CANDIDATES:
        try:
            handle = dlopen(name, RTLD_NOW)
        except DLOpenError:
            continue

        try:
            readline = rffi.cast(RL_READLINE, dlsym(handle, "readline"))
            add_history = rffi.cast(RL_ADD_HISTORY, dlsym(handle, "add_history"))
        except KeyError:
            dlclose(handle)
            continue

        read_history = null_history
        write_history = null_history
        truncate_history = null_truncate
        try:
            read_history = rffi.cast(
                RL_HISTORY_FILE, dlsym(handle, "read_history"),
            )
            write_history = rffi.cast(
                RL_HISTORY_FILE, dlsym(handle, "write_history"),
            )
        except KeyError:
            read_history = null_history
            write_history = null_history
        try:
            truncate_history = rffi.cast(
                RL_TRUNCATE_FILE, dlsym(handle, "history_truncate_file"),
            )
        except KeyError:
            truncate_history = null_truncate

        # libedit emulates the readline API but provides the native editline
        # entry points too; GNU readline does not. The two disagree on prompt
        # escape handling, so pick the matching prompt assembler here.
        try:
            dlsym(handle, "el_init")
            format_prompt = _bare_prompt
        except KeyError:
            format_prompt = _marked_prompt

        _set_ctype_locale()
        return LineEditor(
            handle,
            readline,
            add_history,
            read_history,
            write_history,
            truncate_history,
            _history_path(),
            format_prompt,
        )
    return None
