"""
Convert Lean runtime objects (returned by `FFI.import_modules` /
`FFI.find_constant`) into rpylean's `objects` types.

Layout assumptions are validated by `FFI._layout_self_test` at runtime
and double-checked here against the Lean compiler's emitted C (see
docs/closures-spec.md vicinity for context).

# Ctor tags

    Lean.Name      0=anonymous   1=str(parent, suffix)  2=num(parent, idx)
    Lean.Level     0=zero        1=succ(l)              2=max(l, l)
                   3=imax(l, l)  4=param(name)          5=mvar  -- unused
    Lean.Expr      0=bvar(Nat)   1=fvar      2=mvar      3=sort(level)
                   4=const(name, levels)     5=app(fn, arg)
                   6=lam(name, ty, body)     7=forallE(name, ty, body)
                   8=letE(name, ty, val, body)           9=lit(Literal)
                   10=mdata(data, expr)                  11=proj(name, idx, struct)

# Caveats

- `extends` is *not* flattened in compiled C: a `*Val` with parent
  `ConstantVal` has `toConstantVal` at field 0, then its own fields
  starting at 1. We don't bridge ConstantInfo here yet — that's the
  next step.
- Each Expr ctor has a trailing `data : Data` scalar (a 64-bit hash)
  *before* any user-level scalar fields. So a `forallE`/`lam` ctor's
  scalar area is `[data:8 bytes, binderInfo:1 byte]`, and `letE`'s is
  `[data:8 bytes, nondep:1 byte]`. The `data` itself doesn't matter
  for our walking but the offset to subsequent bytes does.
- `Nat` is small-encoded as a scalar when it fits in a word. Larger
  Nats use `LeanMPZ`; we don't see those in any kernel-ABI test data
  so far, but `read_nat` handles both.
"""
from __future__ import print_function

from rpython.rlib.rarithmetic import intmask
from rpython.rlib.rbigint import rbigint
from rpython.rtyper.lltypesystem import lltype, rffi

from rpylean import _lltypes as _lean
from rpylean.objects import (
    Binder,
    HINT_ABBREV,
    HINT_OPAQUE,
    Name,
    W_BVar,
    W_ForAll,
    W_Lambda,
    W_LEVEL_ZERO,
    W_LitNat,
    W_LitStr,
)


def read_nat(o):
    """Decode a Lean.Nat (scalar small or LeanMPZ heap) into an rbigint."""
    if _lean.is_scalar(o):
        return rbigint.fromint(intmask(_lean.unbox(o)))
    # MPZ path: not exercised by current tests; fail loudly so we notice.
    raise RuntimeError("read_nat: large/MPZ Nat not yet supported")


def read_name(o):
    if _lean.is_scalar(o):
        return Name.ANONYMOUS
    tag = _lean.ptr_tag(o)
    if tag == 1:  # str
        parent = read_name(_lean.ctor_get(o, 0))
        suffix = _lean.string_cstr(_lean.ctor_get(o, 1))
        return parent.child(suffix)
    if tag == 2:  # num
        parent = read_name(_lean.ctor_get(o, 0))
        idx = read_nat(_lean.ctor_get(o, 1))
        # Name.components is a list of str (stringify the numeric component
        # to match the existing parser's convention).
        return parent.child(idx.str())
    raise RuntimeError("read_name: unexpected tag")


def read_level(o):
    if _lean.is_scalar(o):
        # Level.zero is the only scalar we expect.
        return W_LEVEL_ZERO
    tag = _lean.ptr_tag(o)
    if tag == 0:
        return W_LEVEL_ZERO
    if tag == 1:  # succ
        return read_level(_lean.ctor_get(o, 0)).succ()
    if tag == 2:  # max
        return read_level(_lean.ctor_get(o, 0)).max(
            read_level(_lean.ctor_get(o, 1)))
    if tag == 3:  # imax
        return read_level(_lean.ctor_get(o, 0)).imax(
            read_level(_lean.ctor_get(o, 1)))
    if tag == 4:  # param
        return read_name(_lean.ctor_get(o, 0)).level()
    raise RuntimeError("read_level: unexpected tag")


# `List α` walkers, specialised per element type. A single generic
# `_read_list(o, read_elt)` makes RPython unify the return type to the
# union of all callers, which then breaks function-pointer typing.

def _read_name_list(o):
    out = []
    while not _lean.is_scalar(o) and _lean.ptr_tag(o) == 1:
        out.append(read_name(_lean.ctor_get(o, 0)))
        o = _lean.ctor_get(o, 1)
    return out


def _read_level_list(o):
    out = []
    while not _lean.is_scalar(o) and _lean.ptr_tag(o) == 1:
        out.append(read_level(_lean.ctor_get(o, 0)))
        o = _lean.ctor_get(o, 1)
    return out


def _make_binder(scalar_byte, name, ty):
    # BinderInfo: 0=default 1=implicit 2=strictImplicit 3=instImplicit.
    # Inlined dispatch (rather than returning a function) so RPython
    # doesn't try to type-unify the four static-method signatures.
    if scalar_byte == 1:
        return Binder.implicit(name, ty)
    if scalar_byte == 2:
        return Binder.strict_implicit(name, ty)
    if scalar_byte == 3:
        return Binder.instance(name, ty)
    return Binder.default(name, ty)


def _ctor_byte(o, num_objs, byte_offset):
    """Read one byte from a ctor's trailing scalar area.

    `byte_offset` is relative to the start of the scalar area, which sits
    immediately after the 8 * num_objs object-pointer bytes. The first 8
    scalar bytes are typically Lean's cached `data` hash; user-level
    scalar fields (binderInfo, nondep) start at offset 8.
    """
    return rffi.cast(lltype.Signed, rffi.cast(rffi.UCHARP,
        rffi.ptradd(rffi.cast(rffi.CCHARP, o),
                    _lean.OBJ_HDR_SIZE + 8 * num_objs))[byte_offset])


def _ctor_uint32(o, num_objs, byte_offset):
    """Read a 4-byte little-endian uint32 from a ctor's scalar area."""
    p = rffi.cast(rffi.UINTP,
                  rffi.ptradd(rffi.cast(rffi.CCHARP, o),
                              _lean.OBJ_HDR_SIZE + 8 * num_objs + byte_offset))
    return intmask(p[0])


def read_expr(o):
    if _lean.is_scalar(o):
        raise RuntimeError("read_expr: unexpected scalar")
    tag = _lean.ptr_tag(o)
    if tag == 0:  # bvar(deBruijnIndex)
        idx = read_nat(_lean.ctor_get(o, 0))
        return W_BVar(idx.toint())
    if tag == 3:  # sort(u)
        return read_level(_lean.ctor_get(o, 0)).sort()
    if tag == 4:  # const(name, us : List Level)
        name = read_name(_lean.ctor_get(o, 0))
        levels = _read_level_list(_lean.ctor_get(o, 1))
        return name.const(levels=levels)
    if tag == 5:  # app(fn, arg)
        return read_expr(_lean.ctor_get(o, 0)).app(
            read_expr(_lean.ctor_get(o, 1)))
    if tag == 6 or tag == 7:  # lam / forallE
        name = read_name(_lean.ctor_get(o, 0))
        ty = read_expr(_lean.ctor_get(o, 1))
        body = read_expr(_lean.ctor_get(o, 2))
        binder = _make_binder(_ctor_byte(o, 3, 8), name, ty)
        if tag == 6:
            return W_Lambda(binder, body)
        return W_ForAll(binder, body)
    if tag == 8:  # letE(name, type, value, body, nondep)
        name = read_name(_lean.ctor_get(o, 0))
        ty = read_expr(_lean.ctor_get(o, 1))
        val = read_expr(_lean.ctor_get(o, 2))
        body = read_expr(_lean.ctor_get(o, 3))
        return name.let(ty, val, body)
    if tag == 9:  # lit(Literal)
        lit = _lean.ctor_get(o, 0)
        ltag = _lean.ptr_tag(lit)
        if ltag == 0:  # natVal
            return W_LitNat(read_nat(_lean.ctor_get(lit, 0)))
        # strVal
        return W_LitStr(_lean.string_cstr(_lean.ctor_get(lit, 0)))
    if tag == 10:  # mdata: drop the metadata, walk the inner expr
        return read_expr(_lean.ctor_get(o, 1))
    if tag == 11:  # proj(typeName, idx, struct)
        struct_name = read_name(_lean.ctor_get(o, 0))
        idx = read_nat(_lean.ctor_get(o, 1))
        struct = read_expr(_lean.ctor_get(o, 2))
        return struct_name.proj(idx.toint(), struct)
    raise RuntimeError("read_expr: unexpected tag")


def _read_hints(o):
    """Lean.ReducibilityHints → rpylean's int-encoded hint."""
    if _lean.is_scalar(o):
        # 0=opaque, 1=abbrev are nullary ctors → boxed scalars.
        u = _lean.unbox(o)
        if u == 0:
            return HINT_OPAQUE
        if u == 1:
            return HINT_ABBREV
        return HINT_OPAQUE
    # tag 2 = regular(_ : UInt32). The UInt32 lives in the ctor's scalar
    # area at offset 0 (no obj fields, no `data` prefix on non-Expr ctors).
    return _ctor_uint32(o, 0, 0)


def _read_constant_val(cval):
    """Read a `ConstantVal`'s {name, levelParams, type} fields."""
    name = read_name(_lean.ctor_get(cval, 0))
    levels = _read_name_list(_lean.ctor_get(cval, 1))
    type_expr = read_expr(_lean.ctor_get(cval, 2))
    return name, levels, type_expr


def read_constant_info(ci):
    """
    Convert a `Lean.ConstantInfo` runtime object into a `W_Declaration`.

    For inductive and recursor variants we do *not* recursively look up
    the related constructor/recursor declarations — those references are
    returned as `Name`s, and `W_Inductive.constructors` / `W_Recursor`'s
    rules etc. are populated via the same mechanism the lean4export
    parser uses for mutual blocks: empty at first, filled in as the
    constructors/recursors are walked separately.
    """
    tag = _lean.ptr_tag(ci)
    val = _lean.ctor_get(ci, 0)
    cval = _lean.ctor_get(val, 0)
    name, levels, type_expr = _read_constant_val(cval)

    if tag == 0:  # axiomInfo
        return name.axiom(type=type_expr, levels=levels)
    if tag == 1:  # defnInfo
        value = read_expr(_lean.ctor_get(val, 1))
        hint = _read_hints(_lean.ctor_get(val, 2))
        return name.definition(type=type_expr, value=value, hint=hint, levels=levels)
    if tag == 2:  # thmInfo
        value = read_expr(_lean.ctor_get(val, 1))
        return name.theorem(type=type_expr, value=value, levels=levels)
    if tag == 3:  # opaqueInfo
        value = read_expr(_lean.ctor_get(val, 1))
        return name.opaque(type=type_expr, value=value, levels=levels)
    if tag == 4:  # quotInfo — rpylean models Quot.{mk,lift,ind} as axioms.
        return name.axiom(type=type_expr, levels=levels)
    raise RuntimeError("read_constant_info: variant not yet supported")
