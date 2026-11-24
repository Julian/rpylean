"""
Tests for the call-by-need evaluator (`rpylean._eval`).
"""

from rpylean._eval import eval_closed_scalar
from rpylean.environment import Environment, TypeChecker
from rpylean.objects import (
    NAT,
    NAT_SUCC,
    NAT_ZERO,
    TYPE,
    Name,
    W_BVar,
    W_LEVEL_ZERO,
    W_LitNat,
    W_LitStr,
    W_RecRule,
    _BOOL_FALSE,
    _BOOL_TRUE,
    _NAT_ADD,
    _NAT_BEQ,
    _NAT_BLE,
    _NAT_DIV,
    _NAT_GCD,
    _NAT_LAND,
    _NAT_LOR,
    _NAT_MOD,
    _NAT_MUL,
    _NAT_POW,
    _NAT_SHIFT_LEFT,
    _NAT_SHIFT_RIGHT,
    _NAT_SUB,
    _NAT_XOR,
    forall,
    fun,
    names,
    syntactic_eq,
)


def _bool_nat_env(extra=None):
    """Minimal environment with Bool, Nat, Nat.rec, and native Nat ops."""
    x, y, m, z, s, n, ih = names("x", "y", "m", "z", "s", "n", "ih")
    Bool = Name.simple("Bool")
    bool_const = Bool.const()
    bool_false = _BOOL_FALSE.name.constructor(type=bool_const, cidx=0, induct=Bool)
    bool_true = _BOOL_TRUE.name.constructor(type=bool_const, cidx=1, induct=Bool)
    bool_ind = Bool.inductive(
        type=TYPE,
        constructors=[bool_false, bool_true],
    )

    Nat = Name.simple("Nat")
    nat_zero = NAT_ZERO.name.constructor(type=NAT, cidx=0, induct=Nat)
    nat_succ = NAT_SUCC.name.constructor(
        type=forall(x.binder(NAT))(NAT),
        num_fields=1,
        cidx=1,
        induct=Nat,
    )
    u = Name.simple("u")
    u_lvl = u.as_level_param()
    motive_ty = forall(n.binder(NAT))(u_lvl.sort())
    nat_rec_ty = forall(
        m.binder(motive_ty),
        z.binder(W_BVar(0).app(NAT_ZERO)),
        s.binder(forall(n.binder(NAT), ih.binder(W_BVar(3).app(W_BVar(0))))(
            W_BVar(4).app(NAT_SUCC.app(W_BVar(1))),
        )),
        n.binder(NAT),
    )(W_BVar(3).app(W_BVar(0)))
    nat_rec = Nat.child("rec").recursor(
        levels=[u],
        type=nat_rec_ty,
        all=[Nat],
        rules=[
            W_RecRule(NAT_ZERO.name, 0, fun(m.binder(motive_ty), z.binder(TYPE), s.binder(TYPE))(W_BVar(1))),
            W_RecRule(
                NAT_SUCC.name, 1,
                fun(m.binder(motive_ty), z.binder(TYPE), s.binder(TYPE), n.binder(NAT))(
                    W_BVar(1).app(W_BVar(0)).app(
                        Nat.child("rec").const([u_lvl]).app(
                            W_BVar(3), W_BVar(2), W_BVar(1), W_BVar(0),
                        ),
                    ),
                ),
            ),
        ],
        num_motives=1,
        num_minors=2,
    )
    nat_ind = Nat.inductive(
        type=TYPE,
        constructors=[nat_zero, nat_succ],
        recursors=[nat_rec],
        is_recursive=True,
    )

    bin_nat_ty = forall(x.binder(NAT), y.binder(NAT))(NAT)
    bin_bool_ty = forall(x.binder(NAT), y.binder(NAT))(bool_const)
    dummy_val = fun(x.binder(NAT), y.binder(NAT))(W_BVar(0))
    dummy_bool_val = fun(x.binder(NAT), y.binder(NAT))(_BOOL_TRUE)

    decls = [
        bool_ind, bool_false, bool_true,
        nat_ind, nat_zero, nat_succ, nat_rec,
    ]
    for op_name in [
        _NAT_ADD, _NAT_SUB, _NAT_MUL, _NAT_POW, _NAT_GCD, _NAT_MOD, _NAT_DIV,
        _NAT_LAND, _NAT_LOR, _NAT_XOR, _NAT_SHIFT_LEFT, _NAT_SHIFT_RIGHT,
    ]:
        decls.append(op_name.definition(type=bin_nat_ty, value=dummy_val))
    for op_name in [_NAT_BEQ, _NAT_BLE]:
        decls.append(op_name.definition(type=bin_bool_ty, value=dummy_bool_val))

    if extra:
        decls.extend(extra)
    return Environment.having(decls)


def _eval(env, expr):
    tc = TypeChecker(env, None)
    try:
        h = tc.machine.store.import_term(expr)
        res = eval_closed_scalar(tc.machine, h)
        if res == 0:
            return None
        return tc.machine.export(res)
    finally:
        tc.free()


def test_small_and_big_nat_ops():
    env = _bool_nat_env()
    add = _NAT_ADD.const()
    mul = _NAT_MUL.const()
    sub = _NAT_SUB.const()
    beq = _NAT_BEQ.const()
    ble = _NAT_BLE.const()
    gcd = _NAT_GCD.const()
    pow_ = _NAT_POW.const()

    assert syntactic_eq(_eval(env, add.app(W_LitNat.int(20), W_LitNat.int(22))), W_LitNat.int(42))
    assert syntactic_eq(_eval(env, mul.app(W_LitNat.int(6), W_LitNat.int(7))), W_LitNat.int(42))
    assert syntactic_eq(_eval(env, sub.app(W_LitNat.int(3), W_LitNat.int(10))), W_LitNat.int(0))
    assert syntactic_eq(_eval(env, gcd.app(W_LitNat.int(48), W_LitNat.int(18))), W_LitNat.int(6))
    assert syntactic_eq(_eval(env, beq.app(W_LitNat.int(7), W_LitNat.int(7))), _BOOL_TRUE)
    assert syntactic_eq(_eval(env, beq.app(W_LitNat.int(7), W_LitNat.int(8))), _BOOL_FALSE)
    assert syntactic_eq(_eval(env, ble.app(W_LitNat.int(7), W_LitNat.int(8))), _BOOL_TRUE)
    # BigNat overflow path: 2^100
    big = _eval(env, pow_.app(W_LitNat.int(2), W_LitNat.int(100)))
    assert syntactic_eq(big, W_LitNat.long(1 << 100))
    # Nat.succ chain unwrapping inside Nat.add
    e = add.app(NAT_SUCC.app(NAT_SUCC.app(W_LitNat.int(5))), NAT_SUCC.app(NAT_ZERO))
    assert syntactic_eq(_eval(env, e), W_LitNat.int(8))


def test_nat_rec_sum():
    """Sum 1..50 via Nat.rec."""
    n, ih = names("n", "ih")
    u1 = Name.simple("u").as_level_param()
    nat_rec = Name.simple("Nat").child("rec").const([u1])
    # Nat.rec (fun _ => Nat) 0 (fun n ih => Nat.add (Nat.add n 1) ih) 50
    expr = nat_rec.app(
        fun(n.binder(NAT))(NAT),
        W_LitNat.int(0),
        fun(n.binder(NAT), ih.binder(NAT))(
            _NAT_ADD.const().app(_NAT_ADD.const().app(W_BVar(1), W_LitNat.int(1)), W_BVar(0)),
        ),
        W_LitNat.int(50),
    )
    env = _bool_nat_env()
    assert syntactic_eq(_eval(env, expr), W_LitNat.int(1275))


def test_call_by_need_let_and_beta():
    """Shared let & deep beta ladder evaluate without exponential work."""
    x = Name.simple("x")
    env = _bool_nat_env()
    # let x := 10 + 11 in x + x  == 42
    e = x.let(
        type=NAT,
        value=_NAT_ADD.const().app(W_LitNat.int(10), W_LitNat.int(11)),
        body=_NAT_ADD.const().app(W_BVar(0), W_BVar(0)),
    )
    assert syntactic_eq(_eval(env, e), W_LitNat.int(42))

    # Beta ladder of depth 200
    body = W_LitNat.int(0)
    for i in range(200):
        body = _NAT_ADD.const().app(W_BVar(i), body)
    term = body
    for _ in range(200):
        term = fun(x.binder(NAT))(term).app(W_LitNat.int(1))
    assert syntactic_eq(_eval(env, term), W_LitNat.int(200))


def test_bails_cleanly_on_stuck_axiom():
    a = Name.simple("a")
    env = _bool_nat_env(extra=[a.axiom(type=NAT)])
    assert _eval(env, _NAT_ADD.const().app(a.const(), W_LitNat.int(1))) is None


def test_first_class_and_partial_native_nat_ops():
    """Passing Nat.add/Nat.pow as first-class values or partially applying them
    must still hit native Nat arithmetic, never unfolding the Lean body."""
    f, x = names("f", "x")
    env = _bool_nat_env()
    pow_ = _NAT_POW.const()
    add = _NAT_ADD.const()
    bin_ty = forall(x.binder(NAT), f.binder(NAT))(NAT)

    # First-class via lambda: (fun f => f 2 32) Nat.pow == 4294967296
    e1 = fun(f.binder(bin_ty))(W_BVar(0).app(W_LitNat.int(2), W_LitNat.int(32))).app(pow_)
    assert syntactic_eq(_eval(env, e1), W_LitNat.long(1 << 32))

    # First-class via let (forced with args=None into KUpdate):
    e2 = f.let(
        type=bin_ty,
        value=pow_,
        body=W_BVar(0).app(W_LitNat.int(2), W_LitNat.int(40)),
    )
    assert syntactic_eq(_eval(env, e2), W_LitNat.long(1 << 40))

    # Partially applied: (fun g => g 22) (Nat.add 20) == 42
    unary_ty = forall(x.binder(NAT))(NAT)
    e3 = fun(f.binder(unary_ty))(W_BVar(0).app(W_LitNat.int(22))).app(
        add.app(W_LitNat.int(20)),
    )
    assert syntactic_eq(_eval(env, e3), W_LitNat.int(42))

    # Small pow edge cases: 0^0 = 1, 0^5 = 0, 1^999 = 1, 3^5 = 243
    assert syntactic_eq(_eval(env, pow_.app(W_LitNat.int(0), W_LitNat.int(0))), W_LitNat.int(1))
    assert syntactic_eq(_eval(env, pow_.app(W_LitNat.int(0), W_LitNat.int(5))), W_LitNat.int(0))
    assert syntactic_eq(_eval(env, pow_.app(W_LitNat.int(1), W_LitNat.int(999))), W_LitNat.int(1))
    assert syntactic_eq(_eval(env, pow_.app(W_LitNat.int(3), W_LitNat.int(5))), W_LitNat.int(243))


def test_nat_shift_huge_counts_in_eval():
    env = _bool_nat_env()
    shl = _NAT_SHIFT_LEFT.const()
    shr = _NAT_SHIFT_RIGHT.const()
    huge = W_LitNat.long(1 << 64)

    assert syntactic_eq(_eval(env, shr.app(W_LitNat.int(42), huge)), W_LitNat.int(0))
    assert syntactic_eq(_eval(env, shl.app(W_LitNat.int(0), huge)), W_LitNat.int(0))
    assert _eval(env, shl.app(W_LitNat.int(1), huge)) is None


def test_litstr_lazy_expansion():
    """String literals expand lazily through `String.ofList` on projection."""
    u = Name.simple("u")
    u_lvl = u.as_level_param()
    alpha, a, h, t, cs = names("α", "a", "h", "t", "cs")
    List = Name.simple("List")
    list_ty = forall(alpha.binder(u_lvl.sort()))(u_lvl.sort())
    list_nil = List.child("nil").constructor(
        levels=[u],
        type=forall(alpha.binder(u_lvl.sort()))(List.const([u_lvl]).app(W_BVar(0))),
        num_params=1, num_fields=0, cidx=0, induct=List,
    )
    list_cons = List.child("cons").constructor(
        levels=[u],
        type=forall(
            alpha.binder(u_lvl.sort()),
            h.binder(W_BVar(0)),
            t.binder(List.const([u_lvl]).app(W_BVar(1))),
        )(List.const([u_lvl]).app(W_BVar(2))),
        num_params=1, num_fields=2, cidx=1, induct=List,
    )
    list_ind = List.inductive(
        levels=[u], type=list_ty, constructors=[list_nil, list_cons],
        num_params=1, is_recursive=True,
    )

    Char = Name.simple("Char")
    char_mk = Char.child("mk").constructor(
        type=forall(a.binder(NAT))(Char.const()),
        num_params=0, num_fields=1, cidx=0, induct=Char,
    )
    char_ind = Char.inductive(type=TYPE, constructors=[char_mk])
    char_of_nat = Char.child("ofNat").definition(
        type=forall(a.binder(NAT))(Char.const()),
        value=fun(a.binder(NAT))(char_mk.name.const().app(W_BVar(0))),
    )

    String = Name.simple("String")
    list_char = List.const([W_LEVEL_ZERO]).app(Char.const())
    str_mk = String.child("mk").constructor(
        type=forall(cs.binder(list_char))(String.const()),
        num_params=0, num_fields=1, cidx=0, induct=String,
    )
    str_ind = String.inductive(type=TYPE, constructors=[str_mk])
    str_of_list = String.child("ofList").definition(
        type=forall(cs.binder(list_char))(String.const()),
        value=fun(cs.binder(list_char))(str_mk.name.const().app(W_BVar(0))),
    )

    env = _bool_nat_env(extra=[
        list_ind, list_nil, list_cons,
        char_ind, char_mk, char_of_nat,
        str_ind, str_mk, str_of_list,
    ])
    # ("AB".0) -> List.cons (Char.mk 65) (List.cons (Char.mk 66) List.nil)
    # Project head char (field 0 of List.cons) then field 0 of Char.mk -> 65 ('A').
    lit = W_LitStr("AB")
    data = String.proj(0, lit)
    first_char = List.proj(0, data)
    first_code = Char.proj(0, first_char)
    assert syntactic_eq(_eval(env, first_code), W_LitNat.int(ord("A")))
    # Second char via tail projection -> 66 ('B') (reuses cached expansion).
    second_char = List.proj(0, List.proj(1, data))
    assert syntactic_eq(_eval(env, Char.proj(0, second_char)), W_LitNat.int(ord("B")))

    # Non-ASCII UTF-8 string ("é€😀"): 2-, 3-, and 4-byte codepoints decode to
    # scalar values [0xE9, 0x20AC, 0x1F600] rather than raw UTF-8 bytes.
    utf8_lit = W_LitStr("\xc3\xa9\xe2\x82\xac\xf0\x9f\x98\x80")
    utf8_data = String.proj(0, utf8_lit)
    c0 = Char.proj(0, List.proj(0, utf8_data))
    tail1 = List.proj(1, utf8_data)
    c1 = Char.proj(0, List.proj(0, tail1))
    tail2 = List.proj(1, tail1)
    c2 = Char.proj(0, List.proj(0, tail2))
    assert syntactic_eq(_eval(env, c0), W_LitNat.int(0xE9))
    assert syntactic_eq(_eval(env, c1), W_LitNat.int(0x20AC))
    assert syntactic_eq(_eval(env, c2), W_LitNat.int(0x1F600))


def test_direct_lam_def_and_rec_binding_paths():
    """Multi-arg CDef/CLam/CRec direct binding matches full, partial, and
    over-applied calls, and closed scalar def_eq memoizes M_WHNF."""
    x, y, z, n, ih = names("x", "y", "z", "n", "ih")
    add = _NAT_ADD.const()
    mul = _NAT_MUL.const()
    tri = Name.simple("tri").definition(
        type=forall(x.binder(NAT), y.binder(NAT), z.binder(NAT))(NAT),
        value=fun(x.binder(NAT), y.binder(NAT), z.binder(NAT))(
            add.app(mul.app(W_BVar(2), W_BVar(1)), W_BVar(0)),
        ),
    )
    # Over-applied def returning a lambda: (apply2 x y) z = x + y + z
    apply2 = Name.simple("apply2").definition(
        type=forall(x.binder(NAT), y.binder(NAT))(forall(z.binder(NAT))(NAT)),
        value=fun(x.binder(NAT), y.binder(NAT))(
            fun(z.binder(NAT))(add.app(add.app(W_BVar(2), W_BVar(1)), W_BVar(0))),
        ),
    )
    env = _bool_nat_env(extra=[tri, apply2])
    # Full CDef direct binding: tri 6 7 3 == 45
    assert syntactic_eq(
        _eval(env, tri.name.const().app(W_LitNat.int(6), W_LitNat.int(7), W_LitNat.int(3))),
        W_LitNat.int(45),
    )
    # Over-applied CDef -> inner CLam: apply2 10 20 12 == 42
    assert syntactic_eq(
        _eval(env, apply2.name.const().app(W_LitNat.int(10), W_LitNat.int(20), W_LitNat.int(12))),
        W_LitNat.int(42),
    )
    # Multi-arg CLam beta: (fun x y z => x * y + z) 5 8 2 == 42
    lam3 = fun(x.binder(NAT), y.binder(NAT), z.binder(NAT))(
        add.app(mul.app(W_BVar(2), W_BVar(1)), W_BVar(0)),
    )
    assert syntactic_eq(
        _eval(env, lam3.app(W_LitNat.int(5), W_LitNat.int(8), W_LitNat.int(2))),
        W_LitNat.int(42),
    )
    # Direct CRec with trailing extra argument:
    # (Nat.rec (fun _ => Nat -> Nat) (fun k => k) (fun n ih k => ih (k + 1)) 10) 32 == 42
    u1 = Name.simple("u").as_level_param()
    nat_rec = Name.simple("Nat").child("rec").const([u1])
    rec_extra = nat_rec.app(
        fun(n.binder(NAT))(forall(x.binder(NAT))(NAT)),
        fun(x.binder(NAT))(W_BVar(0)),
        fun(n.binder(NAT), ih.binder(forall(x.binder(NAT))(NAT)), x.binder(NAT))(
            W_BVar(1).app(add.app(W_BVar(0), W_LitNat.int(1))),
        ),
        W_LitNat.int(10),
        W_LitNat.int(32),
    )
    assert syntactic_eq(_eval(env, rec_extra), W_LitNat.int(42))

    # def_eq caches M_WHNF for closed compound scalar comparisons
    tc = TypeChecker(env, None)
    try:
        from rpylean.machine import M_WHNF

        h = tc.machine.store.import_term(
            tri.name.const().app(W_LitNat.int(6), W_LitNat.int(7), W_LitNat.int(3)),
        )
        h45 = tc.machine.store.import_term(W_LitNat.int(45))
        assert tc.machine.def_eq(h, h45)
        assert tc.machine.store.memo(h, M_WHNF) == h45
    finally:
        tc.free()


def test_unused_binders_bvar_closure_and_canon_bit():
    """Unused lambda/let/Nat.casesOn binders skip argument/IH thunks, CBVar
    closures bind directly, and `_CANON_BIT` preserves level normalization."""
    from rpylean.machine import _canonical_const, _canonical_sort
    from rpylean.objects import W_LEVEL_ZERO, W_Let, W_LevelMax, _CANON_BIT

    a, b, f, n, ih, x = names("a", "b", "f", "n", "ih", "x")
    add = _NAT_ADD.const()
    # Function with unused first & third parameters and higher-order CBVar call:
    #   ho (a : Type) (f : Nat -> Nat -> Nat) (unused : Nat) (x : Nat) :=
    #     let dead := Nat.add 1 2; f x x
    ho = Name.simple("ho").definition(
        type=forall(
            a.binder(TYPE),
            f.binder(forall(x.binder(NAT), b.binder(NAT))(NAT)),
            b.binder(NAT),
            x.binder(NAT),
        )(NAT),
        value=fun(
            a.binder(TYPE),
            f.binder(forall(x.binder(NAT), b.binder(NAT))(NAT)),
            b.binder(NAT),
            x.binder(NAT),
        )(
            W_Let(
                ih, NAT, add.app(W_LitNat.int(1), W_LitNat.int(2)),
                W_BVar(3).app(W_BVar(1), W_BVar(1)),
            ),
        ),
    )
    # Non-recursive Nat.rec (Nat.casesOn pattern): `ih` is unused!
    u0 = W_LEVEL_ZERO
    u1 = u0.succ()
    nat_rec = Name.simple("Nat").child("rec").const([u1])
    pred_or_99 = nat_rec.app(
        fun(n.binder(NAT))(NAT),
        W_LitNat.int(99),
        fun(n.binder(NAT), ih.binder(NAT))(W_BVar(1)),
        W_LitNat.int(43),
    )
    env = _bool_nat_env(extra=[ho])
    # Verify ho passes an opaque/stuck expression in unused positions without forcing it
    res = _eval(
        env,
        ho.name.const().app(
            NAT,
            fun(x.binder(NAT), b.binder(NAT))(add.app(W_BVar(1), W_BVar(0))),
            NAT,
            W_LitNat.int(21),
        ),
    )
    assert syntactic_eq(res, W_LitNat.int(42))
    assert syntactic_eq(_eval(env, pred_or_99), W_LitNat.int(42))

    # `_CANON_BIT` fast path vs non-normal `W_LevelMax` normalization
    c_norm = Name.simple("Poly").const([u1])
    assert (c_norm._packed & _CANON_BIT) != 0
    assert _canonical_const(c_norm) is c_norm
    max_raw = W_LevelMax(u0, u1)
    c_raw = Name.simple("Poly").const([max_raw])
    assert (c_raw._packed & _CANON_BIT) == 0
    c_can = _canonical_const(c_raw)
    assert syntactic_eq(c_can, c_norm)
    assert (c_can._packed & _CANON_BIT) != 0
    s_raw = max_raw.sort()
    assert (s_raw._packed & _CANON_BIT) == 0
    s_can = _canonical_sort(s_raw)
    assert syntactic_eq(s_can, u1.sort())
    assert (s_can._packed & _CANON_BIT) != 0
