"""
An FFI to Real Lean.

The basic flow:

    with FFI.from_prefix(prefix) as ffi:
        env = ffi.import_modules(["Init"])
        ci = ffi.find_constant(env, "Nat")
        ...

`__enter__` initialises Lean's runtime, the Init/Lean modules, and the
search path (rooted at `prefix` so we are not coupled to `$PATH`'s `lean`).
"""
from __future__ import print_function
from os.path import join
import sys

from rpython.rlib.rdynload import RTLD_LAZY, dlclose, dlopen, dlsym
from rpython.rtyper.lltypesystem import lltype, rffi

from rpylean.ffi import _lltypes as _lean


# Magic numbers used when calling into Lean's compiled APIs. Named here
# so the grep target is in one place and the rationale is captured.

#: Above this trust level, the kernel skips re-checking declarations.
#: We're going to re-check everything in rpylean, so we want Lean's
#: importer to load decls without its own kernel pass — saving time
#: at the cost of relying on rpylean for soundness, which is the
#: whole point.
TRUST_LEVEL_BELIEVER = 1024

#: `Lean.OLeanLevel.private` ctor tag — load every visibility (exported,
#: server, private). See `Lean.OLeanLevel` in Lean's source.
OLEAN_LEVEL_PRIVATE = 2

#: Empty `NameMap ImportArtifacts` is just `box(1)` at runtime: the
#: empty `Std.TreeMap` is the second nullary ctor of its leaf node.
#: Confirmed against Lean's compiled C output for `Lean.importModules`.
EMPTY_NAME_MAP = _lean.box(1)

#: `IO.Error.userError` is constructor tag 18 (the last constructor of
#: `Lean.IO.Error`, after every OS-error variant). When `importModules`
#: returns `Except.error e` and `e` has this tag, field 0 is the
#: error-message `String`.
IO_ERROR_USER = 18


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
            prefix=prefix,
            Init_shared=dlopen(join(lib, library("Init_shared")), RTLD_LAZY),
            leanshared=dlopen(join(lib, library("leanshared")), RTLD_LAZY),
            leanshared_1=dlopen(join(lib, library("leanshared_1")), RTLD_LAZY),
            close=True,
        )

    def __init__(self, Init_shared, leanshared_1, leanshared, prefix=None,
                 close=False):
        self.prefix = prefix
        self.Init_shared = Init_shared
        self.leanshared = leanshared
        self.leanshared_1 = leanshared_1
        self._close = close

    def __enter__(self):
        """
        Initialise the Lean runtime, load Init+Lean, and set the search path.

        After this returns, `import_modules` is callable.
        """
        rffi.cast(_lean.initialize_runtime_module,
                  dlsym(self.leanshared, "lean_initialize_runtime_module"))()

        # Module init: Init and Lean must be initialised before importModules.
        # Each `initialize_<M>(builtin, world)` returns Except IO.Error Unit.
        self._init_module("initialize_Init")
        self._init_module("initialize_Lean")

        rffi.cast(_lean.io_mark_end_initialization,
                  dlsym(self.leanshared, "lean_io_mark_end_initialization"))()

        # Resolve and cache every function pointer we'll call repeatedly,
        # so per-call methods avoid re-dlsym'ing on hot paths like
        # `find_constant` and `each_constant`'s inner loop.
        S = self.leanshared
        self._alloc_object = rffi.cast(_lean.alloc_object,
                                       dlsym(S, "lean_alloc_object"))
        self._mk_string = rffi.cast(_lean.mk_string,
                                    dlsym(S, "lean_mk_string"))
        self._name_mk_string = rffi.cast(_lean.name_mk_string,
                                         dlsym(S, "lean_name_mk_string"))
        self._array_empty = rffi.cast(_lean.array_empty_fn,
                                      dlsym(S, "l_Array_empty"))
        self._array_push = rffi.cast(_lean.array_push,
                                     dlsym(S, "lean_array_push"))
        self._init_sp = rffi.cast(_lean.init_search_path,
                                  dlsym(S, "l_Lean_initSearchPath"))
        self._import_modules = rffi.cast(_lean.import_modules_fn,
                                         dlsym(S, "l_Lean_importModules"))
        self._env_find = rffi.cast(_lean.environment_find,
                                   dlsym(S, "l_Lean_Environment_find_x3f"))
        self._env_constants = rffi.cast(_lean.environment_constants,
                                        dlsym(S, "l_Lean_Environment_constants"))
        self._options_empty = rffi.cast(rffi.CArrayPtr(_lean.Object),
                                        dlsym(S, "l_Lean_Options_empty"))[0]
        self._dec_ref_cold = rffi.cast(_lean.dec_ref_cold,
                                       dlsym(S, "lean_dec_ref_cold"))

        if self.prefix is not None:
            self._init_search_path(self.prefix)
        self._layout_self_test()
        return self

    def __exit__(self, *args):
        if self._close:
            dlclose(self.Init_shared)
            dlclose(self.leanshared)
            dlclose(self.leanshared_1)

    # ---- helpers --------------------------------------------------------

    def _layout_self_test(self):
        """
        Probe a known-shape Lean object to confirm `lean.h`'s layout still
        matches what `_lltypes` assumes. Cheap (a handful of FFI calls,
        runs once per process) and fails loudly the day Lean shifts
        something underneath us.

        Verifies, via `Name.mkStr Name.anonymous "rpylean"`:
        - ctor tag byte at header offset 7
        - object slots starting at header offset 8
        - string bytes starting at string-header offset 32
        """
        probe = self._build_name("rpylean")
        if _lean.is_scalar(probe):
            raise FFIError("layout self-test: Name unexpectedly scalar")
        if _lean.ptr_tag(probe) != 1:
            raise FFIError("layout self-test: Name.str tag should be 1")
        parent = _lean.ctor_get(probe, 0)
        if not _lean.is_scalar(parent) or _lean.unbox(parent) != 0:
            raise FFIError("layout self-test: Name parent should be anonymous")
        suffix = _lean.string_cstr(_lean.ctor_get(probe, 1))
        if suffix != "rpylean":
            raise FFIError("layout self-test: string roundtrip got " + suffix)

    def _init_module(self, sym_name):
        sym = dlsym(self.leanshared, sym_name)
        init = rffi.cast(_lean.initialize_module, sym)
        res = init(rffi.cast(rffi.UINT, 1), _lean.io_mk_world())
        if _lean.obj_tag(res) != 0:
            raise FFIError("Lean module init failed: %s" % sym_name)

    def _init_search_path(self, prefix):
        """
        Set Lean's `searchPathRef` so importModules can find olean files.

        We pass `prefix` directly rather than calling `findSysroot`, which
        would shell out via $PATH and pick up a different toolchain than
        the one we dlopen'd.
        """
        sysroot = self._mk_string(rffi.str2charp(prefix))
        res = self._init_sp(sysroot, _lean.io_mk_world())
        if _lean.obj_tag(res) != 0:
            raise FFIError("initSearchPath failed for prefix " + prefix)

    def _alloc_ctor(self, tag, num_objs, scalar_sz):
        """
        Allocate a fresh ctor object. m_rc=1; m_objs[] is uninitialised.
        """
        sz = _lean.OBJ_HDR_SIZE + 8 * num_objs + scalar_sz
        o = self._alloc_object(rffi.cast(rffi.SIZE_T, sz))
        rffi.cast(rffi.INTP, o)[0] = rffi.cast(rffi.INT, 1)
        b = rffi.cast(rffi.UCHARP, o)
        b[4] = rffi.cast(rffi.UCHAR, 0)
        b[5] = rffi.cast(rffi.UCHAR, 0)
        b[6] = rffi.cast(rffi.UCHAR, num_objs & 0xff)
        b[7] = rffi.cast(rffi.UCHAR, tag & 0xff)
        return o

    def _build_name(self, dotted):
        """Build a Lean.Name from a dotted string like 'Lean.Expr'."""
        n = _lean.box(0)  # Name.anonymous
        for piece in dotted.split("."):
            n = self._name_mk_string(n, self._mk_string(rffi.str2charp(piece)))
        return n

    def _build_import(self, module_name):
        """
        Build a `Lean.Import { module := <name>, isExported := true }`.

        The Import struct is ctor-tag 0 with 1 obj field (module) and 8
        scalar bytes (importAll, isExported, isMeta + padding).
        """
        imp = self._alloc_ctor(tag=0, num_objs=1, scalar_sz=8)
        _lean.ctor_set_obj(imp, 0, self._build_name(module_name))
        _lean.ctor_set_byte(imp, 1, 0, 0)  # importAll  = false
        _lean.ctor_set_byte(imp, 1, 1, 1)  # isExported = true
        _lean.ctor_set_byte(imp, 1, 2, 0)  # isMeta     = false
        return imp

    # ---- public API -----------------------------------------------------

    def initialize_module(self, name, builtin=True):
        """
        Initialise a Lean module by name (legacy: dlopen + initialize_<M>).

        Mostly superseded by `import_modules`, which loads .olean files
        from disk via Lean's importer rather than requiring the module's
        compiled shared library to be on dyld's path.
        """
        handle = dlopen(None, RTLD_LAZY)
        sym = dlsym(handle, "initialize_" + name.replace(".", "_"))
        initialize = rffi.cast(_lean.initialize_module, sym)
        return initialize(rffi.cast(rffi.UINT, builtin), _lean.io_mk_world())

    def is_private_name(self, name):
        sym = dlsym(self.leanshared, "lean_is_private_name")
        func = rffi.cast(_lean.is_private_name, sym)
        return func(name)

    def import_modules(self, modules):
        """
        Load `modules` (list of dotted module names) into a fresh
        Lean.Environment via `Lean.importModules`. Returns the environment
        as an opaque `lean_object *`.

        Caller owns the returned reference. Pass it to `find_constant` to
        look up declarations.
        """
        arr = self._array_empty()
        for m in modules:
            arr = self._array_push(arr, self._build_import(m))

        # `self._options_empty` is dlsym'd once in __enter__.
        result = self._import_modules(
            arr, self._options_empty,
            rffi.cast(rffi.UINT, TRUST_LEVEL_BELIEVER),
            self._array_empty(),
            rffi.cast(rffi.UCHAR, 0),  # leakEnv
            rffi.cast(rffi.UCHAR, 0),  # loadExts
            rffi.cast(rffi.UCHAR, OLEAN_LEVEL_PRIVATE),
            EMPTY_NAME_MAP,
        )
        if _lean.obj_tag(result) != 0:
            err = _lean.ctor_get(result, 0)
            if not _lean.is_scalar(err) and _lean.ptr_tag(err) == IO_ERROR_USER:
                raise FFIError("import failed: " + _lean.string_cstr(_lean.ctor_get(err, 0)))
            raise FFIError("import failed (IO.Error tag=%d)" %
                           _lean.ptr_tag(err))
        return _lean.ctor_get(result, 0)

    def find_constant(self, env, dotted_name):
        """
        Look up a constant by name. Returns the `Option ConstantInfo` Lean
        object: tag 0 means `none`, tag 1 means `some`, with the
        ConstantInfo at field 0.

        `find?` consumes its env argument; this method `inc`s env so the
        caller can continue using it.
        """
        _lean.inc(env)
        return self._env_find(env, self._build_name(dotted_name),
                              rffi.cast(rffi.UCHAR, 0))

    def release(self, o):
        """Drop one strong reference to a Lean object.

        Mirrors the inline `lean_dec_ref` from lean.h: skip scalars,
        decrement m_rc, hand off to `lean_dec_ref_cold` when rc reaches 0.
        """
        if _lean.is_scalar(o):
            return
        p = rffi.cast(rffi.INTP, o)
        rc = rffi.cast(lltype.Signed, p[0])
        if rc > 1:
            p[0] = rffi.cast(rffi.INT, rc - 1)
        elif rc != 0:
            # rc == 1: object becomes unreachable; let Lean's runtime
            # free it (and any non-shared children) via the cold path.
            self._dec_ref_cold(o)

    def each_constant(self, env, callback):
        """
        Walk every imported (Name, ConstantInfo) pair, calling
        ``callback.on_constant(name_obj, ci_obj)`` per entry. A truthy
        return from the callback ends the walk early.

        Reads `Lean.Environment.constants : SMap Name ConstantInfo`
        directly. The SMap's `map1 : Std.HashMap` holds imported
        constants (everything we want after `importModules`); `map2 :
        PHashMap` is for locally-added constants and is empty post-import.
        """
        _lean.inc(env)
        smap = self._env_constants(env)
        # SMap: ctor_get(0) = map₁ (Std.HashMap) — Lean inlines the
        # HashMap → DHashMap → Raw chain so this single ctor has both
        # `size` (field 0, ignored) and `buckets` (field 1) directly.
        hashmap = _lean.ctor_get(smap, 0)
        buckets = _lean.ctor_get(hashmap, 1)
        n = _lean.array_size(buckets)
        for i in range(n):
            cur = _lean.array_get(buckets, i)
            # AssocList: tag 0 = nil (scalar); tag 1 = cons(key, value, tail).
            while not _lean.is_scalar(cur) and _lean.ptr_tag(cur) == 1:
                if callback.on_constant(_lean.ctor_get(cur, 0),
                                        _lean.ctor_get(cur, 1)):
                    return
                cur = _lean.ctor_get(cur, 2)


class FFIError(Exception):
    """An error raised by the FFI when Lean returns a failure."""
