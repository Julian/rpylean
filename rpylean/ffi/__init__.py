"""
FFI to a real Lean toolchain.

Public surface:

    from rpylean.ffi import FFI, FFIError, read_constant_info

`FFI.from_prefix(path)` dlopens a Lean install and exposes
`import_modules`, `find_constant`, `each_constant`. The walker in
`_runtime` converts the returned `lean_object *` instances into
`rpylean.objects` declarations.
"""
from rpylean.ffi._loader import FFI, FFIError
from rpylean.ffi._runtime import read_constant_info

__all__ = ["FFI", "FFIError", "read_constant_info"]
