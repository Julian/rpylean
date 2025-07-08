"""
Low-level types for FFI with Lean.
"""
from __future__ import print_function

from rpython.rtyper.lltypesystem.lltype import FuncType, Ptr, Struct, Void
from rpython.rtyper.lltypesystem import rffi


Object = Ptr(Struct('lean_object'))

initialize = Ptr(FuncType([], Void))
initialize_runtime_module = Ptr(FuncType([], Void))
io_mark_end_initialization = Ptr(FuncType([], Void))

io_result_show_error = Ptr(FuncType([Object], Void))
mk_string = Ptr(FuncType([rffi.CCHARP], Object))
utf8_strlen = Ptr(FuncType([rffi.CONST_CCHARP], rffi.SIZE_T))

initialize_module = Ptr(FuncType([rffi.UINT, Object], Object))

is_private_name = Ptr(FuncType([Object], rffi.INT))


# -- inlined in lean.h --

def box(n):
    return rffi.cast(Object, (n << 1) | 1)


def io_mk_world():
    return box(0)
