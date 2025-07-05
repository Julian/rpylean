"""
Low-level types for FFI with Lean.
"""
from __future__ import print_function

from rpython.rtyper.lltypesystem.lltype import FuncType, Ptr, Struct, Void
from rpython.rtyper.lltypesystem import rffi


Object = Ptr(Struct('lean_object'))
Initialize = Ptr(FuncType([], Void))
IoMarkEndInitialization = Ptr(FuncType([], Void))

InitializeRuntimeModuleFunc = Ptr(FuncType([], Void))
IoResultShowErrorFunc = Ptr(FuncType([Object], Void))
MkStringFunc = Ptr(FuncType([rffi.CCHARP], Object))
Utf8StrlenFunc = Ptr(FuncType([rffi.CONST_CCHARP], rffi.SIZE_T))

InitializeModule = Ptr(FuncType([rffi.UINT, Object], Object))


# -- inlined in lean.h --

def box(n):
    return rffi.cast(Object, (n << 1) | 1)

def io_mk_world():
    return box(0)
