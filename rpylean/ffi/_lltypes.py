"""
Low-level types for FFI with Lean.

Mirrors the static-inline primitives from `lean.h` so we can read and
construct Lean runtime objects directly from RPython, without needing a
shim library.

# Object header

    typedef struct {
        int      m_rc;          // bytes 0-3
        unsigned m_cs_sz : 16;  // bytes 4-5
        unsigned m_other : 8;   // byte  6
        unsigned m_tag   : 8;   // byte  7
    } lean_object;

A constructor object follows the header with `lean_object * m_objs[]`
(`m_other` is the count), then trailing scalar bytes. `ctor_get(o, i)`
reads slot `i` at header+8+8*i; `ctor_set_byte(o, num_objs, k, v)`
writes one scalar byte at header+8+8*num_objs+k.

A string object has header + `m_size:size_t` + `m_capacity:size_t` +
`m_length:size_t` + UTF-8 bytes; `string_cstr` reads at offset 32.

An array object has header + `m_size:size_t` + `m_capacity:size_t` +
`m_data[]:lean_object*`; `array_size` reads offset 8 and `array_get`
reads each pointer starting at offset 24.

Scalar (small-immediate) values are pointer-encoded with bit 0 set:
`box(n) = (n << 1) | 1`, `unbox(o) = (uintptr_t)o >> 1`, and
`is_scalar(o) = ((uintptr_t)o & 1) == 1`.

# ABI

Every Lean function consumes its `lean_object *` arguments unless they
are marked `@&` in the signature. Callers that want to keep using the
borrowed reference must `inc()` it before each consume-call; conversely
`FFI.release(o)` drops one ref (mirroring inline `lean_dec_ref`).

# Where to look when this drifts

Each layout constant here is verified at startup by `FFI`:
`_layout_self_test` exercises the synthetic shapes (Name, ctor header,
string body), and `_deep_self_test` covers the loaded-env shapes
(ConstantInfo's `toConstantVal` indirection, forallE's slot order).
`rpylean.ffi._runtime`'s module docstring catalogues every ctor we
walk and points at its Lean source.
"""
from __future__ import print_function

from rpython.rtyper.lltypesystem.lltype import FuncType, Ptr, Struct, Void
from rpython.rtyper.lltypesystem import rffi, lltype


Object = Ptr(Struct('lean_object'))

initialize = Ptr(FuncType([], Void))
initialize_runtime_module = Ptr(FuncType([], Void))
io_mark_end_initialization = Ptr(FuncType([], Void))

io_result_show_error = Ptr(FuncType([Object], Void))
mk_string = Ptr(FuncType([rffi.CCHARP], Object))
utf8_strlen = Ptr(FuncType([rffi.CONST_CCHARP], rffi.SIZE_T))

initialize_module = Ptr(FuncType([rffi.UINT, Object], Object))

is_private_name = Ptr(FuncType([Object], rffi.INT))

# Allocator and helpers we resolve inside leanffi.
alloc_object = Ptr(FuncType([rffi.SIZE_T], Object))
name_mk_string = Ptr(FuncType([Object, Object], Object))
array_empty_fn = Ptr(FuncType([], Object))
array_push = Ptr(FuncType([Object, Object], Object))
init_search_path = Ptr(FuncType([Object, Object], Object))
# `Lean.Environment.find?  (env : Environment) (n : Name) (skipRealize := false)`
environment_find = Ptr(FuncType([Object, Object, rffi.UCHAR], Object))
environment_constants = Ptr(FuncType([Object], Object))
import_modules_fn = Ptr(FuncType(
    # imports, opts, trustLevel, plugins, leakEnv, loadExts, level, arts
    [Object, Object, rffi.UINT, Object, rffi.UCHAR, rffi.UCHAR, rffi.UCHAR, Object],
    Object,
))


# -- inlined helpers from lean.h --

OBJ_HDR_SIZE = 8
STRING_HDR_SIZE = 8 + 8 + 8 + 8  # header + size + capacity + length
ARRAY_HDR_SIZE = 8 + 8 + 8       # header + m_size + m_capacity


def box(n):
    return rffi.cast(Object, (n << 1) | 1)


def io_mk_world():
    return box(0)


def is_scalar(o):
    return (rffi.cast(lltype.Unsigned, o) & 1) == 1


def unbox(o):
    return rffi.cast(lltype.Unsigned, o) >> 1


def ptr_tag(o):
    """The constructor tag of a heap object (byte 7 of the header)."""
    return rffi.cast(lltype.Signed, rffi.cast(rffi.UCHARP, o)[7])


def obj_tag(o):
    """Tag-or-scalar: like `lean_obj_tag` from lean.h."""
    if is_scalar(o):
        return rffi.cast(lltype.Signed, unbox(o))
    return ptr_tag(o)


def ctor_get(o, i):
    """Borrow the i-th object pointer in a constructor's m_objs array."""
    base = rffi.cast(rffi.CArrayPtr(Object),
                     rffi.ptradd(rffi.cast(rffi.CCHARP, o), OBJ_HDR_SIZE))
    return base[i]


def ctor_set_obj(o, i, v):
    """Store v into the i-th object slot. Transfers ownership of v."""
    base = rffi.cast(rffi.CArrayPtr(Object),
                     rffi.ptradd(rffi.cast(rffi.CCHARP, o), OBJ_HDR_SIZE))
    base[i] = v


def ctor_set_byte(o, num_objs, byte_offset, value):
    """Store one scalar byte in the trailing scalar area of a ctor."""
    p = rffi.cast(rffi.UCHARP,
                  rffi.ptradd(rffi.cast(rffi.CCHARP, o),
                              OBJ_HDR_SIZE + 8 * num_objs))
    p[byte_offset] = rffi.cast(rffi.UCHAR, value)


def array_size(o):
    """The number of elements in a `lean_array_object`."""
    p = rffi.cast(rffi.CArrayPtr(rffi.SIZE_T),
                  rffi.ptradd(rffi.cast(rffi.CCHARP, o), OBJ_HDR_SIZE))
    return rffi.cast(lltype.Signed, p[0])


def array_get(o, i):
    """The i-th element of a `lean_array_object`'s `m_data[]`."""
    base = rffi.cast(rffi.CArrayPtr(Object),
                     rffi.ptradd(rffi.cast(rffi.CCHARP, o), ARRAY_HDR_SIZE))
    return base[i]


def string_cstr(o):
    """Read a Lean string's UTF-8 bytes as a Python str."""
    return rffi.charp2str(rffi.cast(
        rffi.CCHARP,
        rffi.ptradd(rffi.cast(rffi.CCHARP, o), STRING_HDR_SIZE),
    ))


def inc(o):
    """Increment a heap object's refcount (lean.h's `lean_inc_ref` for st-refs).

    Lean's @[export]'d functions consume their arguments by default. When
    we want to keep a borrowed reference alive across such a call, we must
    bump m_rc before passing it.
    """
    p = rffi.cast(rffi.INTP, o)
    p[0] = rffi.cast(rffi.INT, rffi.cast(lltype.Signed, p[0]) + 1)


# Function pointer type for `lean_dec_ref_cold`, the cold-path runtime
# entry called by inline `lean_dec_ref` when an object's rc reaches 0.
dec_ref_cold = Ptr(FuncType([Object], Void))
