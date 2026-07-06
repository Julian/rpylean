"""
Terminal size detection via ``ioctl(TIOCGWINSZ)``, RPython-translatable.

The single public entry point, :func:`terminal_width`, returns the width in
columns of the terminal backing a file descriptor, or ``-1`` when it cannot
be determined (the descriptor is a pipe or file, the platform lacks
``TIOCGWINSZ``, or the ``ioctl`` fails).
"""

import sys

from rpython.rtyper.lltypesystem import lltype, rffi
from rpython.rtyper.tool import rffi_platform
from rpython.translator.tool.cbuild import ExternalCompilationInfo

_eci = ExternalCompilationInfo(includes=["sys/ioctl.h", "unistd.h"])


class _CConfig(object):
    _compilation_info_ = _eci
    TIOCGWINSZ = rffi_platform.DefinedConstantInteger("TIOCGWINSZ")


# `DefinedConstantInteger` resolves to the platform's value at translation
# time, or `None` where the macro is absent (e.g. Windows). Fall back to 0
# so the `ioctl` argument stays a plain int; `terminal_width` guards on it.
_TIOCGWINSZ = rffi_platform.configure(_CConfig)["TIOCGWINSZ"] or 0

# `struct winsize` from <sys/ioctl.h>; only `ws_col` interests us.
_WINSIZE = rffi.CStruct(
    "winsize",
    ("ws_row", rffi.USHORT),
    ("ws_col", rffi.USHORT),
    ("ws_xpixel", rffi.USHORT),
    ("ws_ypixel", rffi.USHORT),
)

if sys.platform == "darwin":
    # `ioctl` is variadic; darwin needs the natural (non-variadic) arity.
    _c_ioctl = rffi.llexternal(
        "ioctl", [rffi.INT, rffi.UINT, rffi.VOIDP], rffi.INT,
        compilation_info=_eci, save_err=rffi.RFFI_SAVE_ERRNO, natural_arity=2,
    )
else:
    _c_ioctl = rffi.llexternal(
        "ioctl", [rffi.INT, rffi.UINT, rffi.VOIDP], rffi.INT,
        compilation_info=_eci, save_err=rffi.RFFI_SAVE_ERRNO,
    )


def terminal_width(fd):
    """
    The width in columns of the terminal on file descriptor ``fd``, or
    ``-1`` if it cannot be determined.
    """
    if _TIOCGWINSZ == 0:
        return -1
    ws = lltype.malloc(_WINSIZE, flavor="raw")
    try:
        rc = _c_ioctl(fd, rffi.cast(rffi.UINT, _TIOCGWINSZ),
                      rffi.cast(rffi.VOIDP, ws))
        if rc != 0:
            return -1
        col = rffi.getintfield(ws, "c_ws_col")
        if col <= 0:
            return -1
        return col
    finally:
        lltype.free(ws, flavor="raw")
