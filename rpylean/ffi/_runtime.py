"""
Convert Lean runtime objects (returned by `FFI.import_modules` /
`FFI.find_constant`) into rpylean's `objects` types.

Layout assumptions are validated at startup: `FFI._layout_self_test`
probes runtime-object shapes (header, ctor, string, array) and
`FFI._deep_self_test` probes loaded-env shapes (ConstantInfo,
forallE). Anything inconsistent there fails loudly; everything below
relies on those invariants holding.

# Ctor tags

    Lean.Name      0=anonymous   1=str(parent, suffix)  2=num(parent, idx)
                   See `Init.Prelude` (`inductive Name`).

    Lean.Level     0=zero        1=succ(l)              2=max(l, l)
                   3=imax(l, l)  4=param(name)          5=mvar -- unused
                   See `Lean/Level.lean`.

    Lean.Expr      0=bvar(Nat)   1=fvar      2=mvar      3=sort(level)
                   4=const(name, levels)     5=app(fn, arg)
                   6=lam(name, ty, body)     7=forallE(name, ty, body)
                   8=letE(name, ty, val, body)           9=lit(Literal)
                   10=mdata(data, expr)     11=proj(name, idx, struct)
                   See `Lean/Expr.lean` (`inductive Expr`). fvar/mvar
                   don't occur in declaration bodies and are treated
                   as walker errors.

    Lean.ConstantInfo
                   0=axiomInfo   1=defnInfo  2=thmInfo   3=opaqueInfo
                   4=quotInfo    5=inductInfo 6=ctorInfo 7=recInfo
                   See `Lean/Declaration.lean`. Each variant wraps a
                   single `*Val` at field 0.

    Lean.ReducibilityHints
                   0=opaque      1=abbrev    2=regular(_: UInt32)
                   The regular's UInt32 lives at *scalar* offset 0
                   (no `data` prefix on non-Expr ctors); see
                   `_read_hints`.

# Field positions

Every `*Val` has `toConstantVal` at field 0 — Lean's `extends` is
*not* flattened in compiled C. `ConstantVal`'s field order is
`[name, levelParams, type]`. Per-variant additional fields:

    AxiomVal       [toConstantVal] + scalar byte isUnsafe
    DefinitionVal  [toConstantVal, value, hints, all] + scalar byte safety
    TheoremVal     [toConstantVal, value, all]
    OpaqueVal      [toConstantVal, value, all] + scalar byte isUnsafe
    QuotVal        [toConstantVal] + scalar byte kind
    InductiveVal   [toConstantVal, numParams, numIndices, all, ctors,
                    numNested] + scalar bytes isRec/isUnsafe/isReflexive
    ConstructorVal [toConstantVal, induct, cidx, numParams, numFields]
                   + scalar byte isUnsafe
    RecursorVal    [toConstantVal, all, numParams, numIndices, numMotives,
                    numMinors, rules] + scalar bytes k/isUnsafe

`Lean.Expr` ctors with binder info / nondep flags interleave a
`data : Data` 64-bit hash *before* any user-level scalar fields. So
forallE/lam's scalar area is `[data:8 bytes, binderInfo:1 byte]`
and letE's is `[data:8 bytes, nondep:1 byte]`. The `data` doesn't
matter for walking but it shifts the offset to the byte we do read.

`Nat` is small-encoded as a scalar when it fits in a word; larger
Nats use `LeanMPZ`, which we decode by reading the GMP `mpz_t`
limbs directly out of the heap object — see `_read_mpz`.
"""
from __future__ import print_function

from rpython.rlib.objectmodel import specialize
from rpython.rlib.rarithmetic import intmask
from rpython.rlib.rbigint import rbigint
from rpython.rtyper.lltypesystem import lltype, rffi

from rpylean.ffi import _lltypes as _lean
from rpylean.objects import (
    Binder,
    HINT_ABBREV,
    HINT_OPAQUE,
    Name,
    W_BVar,
    W_Constructor,
    W_Declaration,
    W_ForAll,
    W_Inductive,
    W_Lambda,
    W_LEVEL_ZERO,
    W_LitNat,
    W_LitStr,
    W_RecRule,
    W_Recursor,
)


# Pointer-keyed hash-cons caches for the Lean `lean_object *`
# Expr/Level subtrees. Lean's runtime shares Expr/Level structure
# across occurrences via pointer equality, but the recursive walkers
# below build a fresh rpylean object at every visit; without dedup,
# every downstream consumer's output is exponential in the source
# tree's sharing factor.
#
# The cache is valid for as long as the underlying lean_object pointers
# are: from `FFI.import_modules` through `FFI.release(env_obj)`. The
# CLI is expected to call `reset_walk_caches()` at session entry. Held
# on a small singleton because RPython forbids rebinding module
# globals at runtime — `.clear()` on dict attributes is fine.

class _WalkState(object):
    def __init__(self):
        self.exprs = {}    # int (ptr addr) → W_Expr
        self.levels = {}   # int (ptr addr) → W_Level
        self.names = {}    # int (ptr addr) → Name

    def reset(self):
        self.exprs.clear()
        self.levels.clear()
        self.names.clear()


_WALK = _WalkState()


def reset_walk_caches():
    """Clear the pointer-keyed Expr/Level dedup caches.

    Call this when a new FFI session begins (the previous env's
    pointers are no longer valid and their addresses may be reused)
    or to bound memory growth between independent walks."""
    _WALK.reset()


def _ptr_key(o):
    return rffi.cast(lltype.Signed, o)


def read_nat(o):
    """Decode a Lean.Nat (scalar small or LeanMPZ heap) into an rbigint."""
    if _lean.is_scalar(o):
        return rbigint.fromint(intmask(_lean.unbox(o)))
    # Big nat: decode the GMP `mpz_t` payload directly. We can't go
    # through Lean's `Nat.reprFast` because it dereferences the
    # statically-allocated `Nat.reprArray`, which isn't reliably
    # set up when we call into the runtime from FFI (the access
    # SIGBUSes on macOS arm64 even with `lean_io_mark_end_initialization`
    # done).
    return _read_mpz(o)


def _read_mpz(o):
    # `mpz_object`: lean_object header (8 bytes), then `mpz` wrapping
    # `mpz_t` = `__mpz_struct[1]`:
    #   int _mp_alloc;   // 4 bytes
    #   int _mp_size;    // 4 bytes, signed: |size| = #limbs, sign = sign
    #   mp_limb_t *_mp_d;  // 8 bytes pointer; each limb is 8 bytes on
    #                         a 64-bit target
    base = rffi.cast(rffi.CCHARP, o)
    size_p = rffi.cast(rffi.INTP,
                       rffi.ptradd(base, _lean.OBJ_HDR_SIZE + 4))
    n_limbs = intmask(size_p[0])
    if n_limbs == 0:
        return rbigint.fromint(0)
    if n_limbs < 0:
        # `Nat` is non-negative; a negative mpz would be a kernel bug.
        raise RuntimeError("read_nat: negative LeanMPZ")
    limbs_pp = rffi.cast(rffi.CArrayPtr(rffi.ULONGP),
                         rffi.ptradd(base, _lean.OBJ_HDR_SIZE + 8))
    limbs = limbs_pp[0]
    # Accumulate most-significant first: result = sum(limb[i] << 64*i).
    # We split each 64-bit limb into two 32-bit halves so rbigint
    # stays on its native 31-bit digit machinery without unsigned
    # 64-bit gymnastics.
    result = rbigint.fromint(0)
    for i in range(n_limbs - 1, -1, -1):
        limb = limbs[i]
        # Split into hi/lo 32-bit halves.
        lo = intmask(rffi.cast(rffi.UINT, limb))
        hi = intmask(rffi.cast(rffi.UINT,
                               rffi.cast(rffi.ULONG, limb) >> 32))
        result = result.lshift(32).add(rbigint.fromint(hi))
        result = result.lshift(32).add(rbigint.fromint(lo))
    return result


def read_name(o):
    if _lean.is_scalar(o):
        return Name.ANONYMOUS
    key = _ptr_key(o)
    cached = _WALK.names.get(key, None)
    if cached is not None:
        return cached
    result = _read_name_uncached(o)
    _WALK.names[key] = result
    return result


def _read_name_uncached(o):
    tag = _lean.ptr_tag(o)
    if tag == 1:  # str
        parent = read_name(_lean.ctor_get(o, 0))
        suffix = _lean.string_cstr(_lean.ctor_get(o, 1))
        return parent.child(suffix)
    if tag == 2:  # num
        parent = read_name(_lean.ctor_get(o, 0))
        idx = read_nat(_lean.ctor_get(o, 1))
        return parent.num_child(idx)
    raise RuntimeError("read_name: unexpected tag")


def read_level(o):
    if _lean.is_scalar(o):
        # Level.zero is the only scalar we expect.
        return W_LEVEL_ZERO
    key = _ptr_key(o)
    cached = _WALK.levels.get(key, None)
    if cached is not None:
        return cached
    result = _read_level_uncached(o)
    _WALK.levels[key] = result
    return result


def _read_level_uncached(o):
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
        return read_name(_lean.ctor_get(o, 0)).as_level_param()
    raise RuntimeError("read_level: unexpected tag")


# `List α` walkers, specialised per element type and per call location.
# Without `@specialize.call_location`, RPython unifies the return type
# across callers — which makes the resulting list's element type wider
# than each caller actually needs, breaking downstream specialization.

@specialize.call_location()
def _read_name_list(o):
    out = []
    while not _lean.is_scalar(o) and _lean.ptr_tag(o) == 1:
        out.append(read_name(_lean.ctor_get(o, 0)))
        o = _lean.ctor_get(o, 1)
    return out


@specialize.call_location()
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
    key = _ptr_key(o)
    cached = _WALK.exprs.get(key, None)
    if cached is not None:
        return cached
    result = _read_expr_uncached(o)
    _WALK.exprs[key] = result
    return result


def _read_expr_uncached(o):
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
        # AxiomVal: scalar byte 0 = isUnsafe (no obj fields beyond
        # `toConstantVal`, so num_objs = 1).
        is_unsafe = _ctor_byte(val, 1, 0) != 0
        return name.axiom(type=type_expr, levels=levels, is_unsafe=is_unsafe)
    if tag == 1:  # defnInfo
        value = read_expr(_lean.ctor_get(val, 1))
        hint = _read_hints(_lean.ctor_get(val, 2))
        # DefinitionVal: scalar byte 0 = safety enum
        # (0=unsafe, 1=safe, 2=partial). 4 obj fields preceding.
        is_unsafe = _ctor_byte(val, 4, 0) == 0
        return name.definition(type=type_expr, value=value, hint=hint,
                               levels=levels, is_unsafe=is_unsafe)
    if tag == 2:  # thmInfo — always safe.
        value = read_expr(_lean.ctor_get(val, 1))
        return name.theorem(type=type_expr, value=value, levels=levels)
    if tag == 3:  # opaqueInfo
        value = read_expr(_lean.ctor_get(val, 1))
        # OpaqueVal: scalar byte 0 = isUnsafe. 3 obj fields.
        is_unsafe = _ctor_byte(val, 3, 0) != 0
        return name.opaque(type=type_expr, value=value, levels=levels,
                           is_unsafe=is_unsafe)
    if tag == 4:  # quotInfo — rpylean models Quot.{mk,lift,ind} as axioms.
        return name.axiom(type=type_expr, levels=levels)
    if tag == 5:  # inductInfo
        all_names = _read_name_list(_lean.ctor_get(val, 3))
        # InductiveVal.ctors lives at field 4 — list of ctor names in
        # source-declaration order. Authoritative for "what ctors does
        # this inductive have, in what order?".
        ctor_names = _read_name_list(_lean.ctor_get(val, 4))
        num_params = read_nat(_lean.ctor_get(val, 1)).toint()
        num_indices = read_nat(_lean.ctor_get(val, 2)).toint()
        num_nested = read_nat(_lean.ctor_get(val, 5)).toint()
        is_rec = _ctor_byte(val, 6, 0) != 0
        is_unsafe = _ctor_byte(val, 6, 1) != 0
        is_reflexive = _ctor_byte(val, 6, 2) != 0
        kind = W_Inductive(
            names=all_names if all_names else [name],
            constructors=[],
            recursors=[],
            num_params=num_params,
            num_indices=num_indices,
            num_nested=num_nested,
            is_recursive=is_rec,
            is_reflexive=is_reflexive,
            ctor_names=ctor_names,
        )
        return W_Declaration(name=name, type=type_expr, w_kind=kind,
                             levels=levels, is_unsafe=is_unsafe)
    if tag == 6:  # ctorInfo
        # ConstructorVal layout (nested ConstantVal at field 0):
        #   1: induct : Name
        #   2: cidx : Nat
        #   3: numParams : Nat
        #   4: numFields : Nat
        # + scalar byte 0 = isUnsafe (5 obj fields).
        cidx = read_nat(_lean.ctor_get(val, 2)).toint()
        num_params = read_nat(_lean.ctor_get(val, 3)).toint()
        num_fields = read_nat(_lean.ctor_get(val, 4)).toint()
        is_unsafe = _ctor_byte(val, 5, 0) != 0
        kind = W_Constructor(num_params=num_params, num_fields=num_fields,
                             cidx=cidx)
        return W_Declaration(name=name, type=type_expr, w_kind=kind,
                             levels=levels, is_unsafe=is_unsafe)
    if tag == 7:  # recInfo
        all_names = _read_name_list(_lean.ctor_get(val, 1))
        num_params = read_nat(_lean.ctor_get(val, 2)).toint()
        num_indices = read_nat(_lean.ctor_get(val, 3)).toint()
        num_motives = read_nat(_lean.ctor_get(val, 4)).toint()
        num_minors = read_nat(_lean.ctor_get(val, 5)).toint()
        # Read the rules list inline (specialised per call location like
        # _read_name_list, but easier to inline given it's the only caller).
        rules_obj = _lean.ctor_get(val, 6)
        rules = []
        while not _lean.is_scalar(rules_obj) and _lean.ptr_tag(rules_obj) == 1:
            rule = _lean.ctor_get(rules_obj, 0)
            rules.append(W_RecRule(
                ctor_name=read_name(_lean.ctor_get(rule, 0)),
                num_fields=read_nat(_lean.ctor_get(rule, 1)).toint(),
                rhs=read_expr(_lean.ctor_get(rule, 2)),
            ))
            rules_obj = _lean.ctor_get(rules_obj, 1)
        k = _ctor_byte(val, 7, 0) != 0
        is_unsafe = _ctor_byte(val, 7, 1) != 0
        kind = W_Recursor(
            names=all_names if all_names else [name],
            rules=rules,
            k=k,
            num_params=num_params,
            num_indices=num_indices,
            num_motives=num_motives,
            num_minors=num_minors,
        )
        return W_Declaration(name=name, type=type_expr, w_kind=kind,
                             levels=levels, is_unsafe=is_unsafe)
    raise RuntimeError("read_constant_info: unexpected tag")
    raise RuntimeError("read_constant_info: variant not yet supported")
