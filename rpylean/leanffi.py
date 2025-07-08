"""
An FFI to Real Lean.
"""
from __future__ import print_function
from os.path import join
import sys

from rpython.rlib.rdynload import RTLD_LAZY, dlclose, dlopen, dlsym
from rpython.rtyper.lltypesystem import rffi

from rpylean import _lltypes as _lean


if sys.platform == "win32":
    def library(name):
        return "lib%s.dll" % name
elif sys.platform == "darwin":
    def library(name):
        return "lib%s.dylib" % name
else:
    def library(name):
        return "lib%s.so" % name


class FFI(object):
    """
    Dynamic loader for Lean libraries and functions.
    """
    @staticmethod
    def from_prefix(prefix):
        """
        Talk to a Lean interpreter via FFI.
        """
        lib = join(prefix, "lib/lean")
        return FFI(
            Init_shared=dlopen(join(lib, library("Init_shared")), RTLD_LAZY),
            leanshared=dlopen(join(lib, library("leanshared")), RTLD_LAZY),
            leanshared_1=dlopen(join(lib, library("leanshared_1")), RTLD_LAZY),
            close=True,
        )

    def __init__(self, Init_shared, leanshared_1, leanshared, close=False):
        self.Init_shared = Init_shared
        self.leanshared = leanshared
        self.leanshared_1 = leanshared_1
        self._close = close

    def __enter__(self):
        """
        Initialize the Lean runtime environment.
        """
        sym = dlsym(self.leanshared, "lean_initialize_runtime_module")
        rffi.cast(_lean.initialize_runtime_module, sym)()
        return self

    def __exit__(self, *args):
        sym = dlsym(self.leanshared, "lean_io_mark_end_initialization")
        rffi.cast(_lean.io_mark_end_initialization, sym)()

        if self._close:
            dlclose(self.Init_shared)
            dlclose(self.leanshared)
            dlclose(self.leanshared_1)

    def initialize_module(self, name, builtin=True):
        """
        Initialize a Lean module by name.
        """
        handle = dlopen(None, RTLD_LAZY)
        sym = dlsym(handle, "initialize_" + name.replace(".", "_"))
        initialize = rffi.cast(_lean.initialize_module, sym)
        return initialize(rffi.cast(rffi.UINT, builtin), _lean.io_mk_world())

    def is_private_name(self, name):
        sym = dlsym(self.leanshared, "lean_is_private_name")
        func = rffi.cast(_lean.is_private_name, sym)
        return func(name)
