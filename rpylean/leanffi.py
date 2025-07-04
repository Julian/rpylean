"""
An FFI to Real Lean.
"""
from __future__ import print_function

from subprocess import check_output

from rpython.rlib import rdynload
from rpython.rtyper.lltypesystem import lltype, rffi
from rpython.translator.tool.cbuild import ExternalCompilationInfo
import py


LEAN_SYSROOT = py.path.local(check_output(["lean", "--print-prefix"]).strip())
LEAN_INCLUDE = LEAN_SYSROOT.join("include")
LEAN_LIBDIR = LEAN_SYSROOT.join("lib/lean")

LeanObjectP = lltype.Ptr(lltype.Struct('lean_object'))

info = ExternalCompilationInfo(
    includes=["lean/lean.h"],
    include_dirs=[LEAN_INCLUDE],
    libraries=["Init_shared", "leanshared_1", "leanshared"],
    library_dirs=[LEAN_LIBDIR],
    post_include_bits=["void lean_initialize(void);"],
)

lean_initialize_runtime_module = rffi.llexternal(
    "lean_initialize_runtime_module",
    (),
    lltype.Void,
    compilation_info=info,
)
lean_initialize = rffi.llexternal(
    "lean_initialize",
    (),
    lltype.Void,
    compilation_info=info,
)
lean_io_mark_end_initialization = rffi.llexternal(
    "lean_io_mark_end_initialization",
    (),
    lltype.Void,
    compilation_info=info,
)

lean_io_result_show_error = rffi.llexternal(
    "lean_io_result_show_error",
    (LeanObjectP,),
    lltype.Void,
    compilation_info=info,
)

lean_mk_string = rffi.llexternal(
    "lean_mk_string",
    (rffi.CCHARP,),
    LeanObjectP,
    compilation_info=info,
)
lean_utf8_strlen = rffi.llexternal(
    "lean_utf8_strlen",
    (rffi.CONST_CCHARP,),
    rffi.SIZE_T,
    compilation_info=info,
)

# -- inlined in lean.h --

def lean_box(n):
    return rffi.cast(LeanObjectP, (n << 1) | 1)

def lean_io_mk_world():
    return lean_box(0)

# -- our own helpers --

LeanModuleInitFunc = lltype.Ptr(
    lltype.FuncType([rffi.UINT, LeanObjectP], LeanObjectP),
)

def initialize_module(name, builtin=True):
    """
    Initialize a Lean module by name.
    """
    handle = rdynload.dlopen(None)
    func_ptr = rdynload.dlsym(handle, "initialize_" + name)
    initialize = rffi.cast(LeanModuleInitFunc, func_ptr)
    return initialize(rffi.cast(rffi.UINT, builtin), lean_io_mk_world())


class initialize(object):
    """
    Initialize the Lean runtime environment.
    """
    def __enter__(self):
        lean_initialize()

    def __exit__(self, *args):
        lean_io_mark_end_initialization()


if __name__ == "__main__":
    with initialize():
        print("Lean runtime initialized.")

    hello = "hello"
    string = lean_mk_string(hello)
    print(string)
    print("String length:", lean_utf8_strlen(rffi.str2constcharp(hello)))
