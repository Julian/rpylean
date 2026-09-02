"""
Parity tests: the raw machine's reduction against the boxed kernel's.
"""

from rpylean._rawterms import RawBail, RawMachine
from rpylean.environment import Environment, TypeChecker
from rpylean.objects import (
    NAT,
    TYPE,
    Name,
    W_BVar,
    W_LitNat,
    W_RecRule,
    forall,
    fun,
    names,
    syntactic_eq,
)
from tests.test_whnf import TestIotaReduction, Quot, u, v

import pytest


a, f, x, y = names("a", "f", "x", "y")
b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)


def machine(env):
    return RawMachine(TypeChecker(env, None))


def assert_whnf_parity(env, e):
    expected = e.whnf(env)
    m = machine(env)
    try:
        h = m.store.import_term(e)
        got = m.store.export_term(m.whnf(h))
        assert syntactic_eq(got, expected), (got, expected)
        # And the result is a fixed point.
        assert m.whnf(m.whnf(h)) == m.whnf(h)
    finally:
        m.free()
    return expected


def test_leaves_and_binders_are_normal():
    env = Environment.having([Name.simple("Nat").axiom(type=TYPE)])
    for e in [NAT, TYPE, W_LitNat.int(3), fun(x.binder(type=NAT))(b0),
              forall(x.binder(type=NAT))(NAT)]:
        assert_whnf_parity(env, e)


def test_definition_unfolds_and_beta_reduces():
    ident = Name.simple("ident").definition(
        type=forall(x.binder(type=NAT))(NAT),
        value=fun(x.binder(type=NAT))(b0),
    )
    twice = Name.simple("twice").definition(
        type=forall(x.binder(type=NAT))(NAT),
        value=fun(x.binder(type=NAT))(ident.const().app(ident.const().app(b0))),
    )
    env = Environment.having([
        Name.simple("Nat").axiom(type=TYPE), a.axiom(type=NAT), ident, twice,
    ])
    assert_whnf_parity(env, ident.const())
    assert_whnf_parity(env, ident.const().app(a.const()))
    assert_whnf_parity(env, twice.const().app(a.const()))
    # Partial application stays a lambda-headed spine after unfolding.
    assert_whnf_parity(env, twice.const())


def test_opaque_and_axiom_stay_put():
    op = Name.simple("op").opaque(type=NAT, value=W_LitNat.int(1))
    env = Environment.having([
        Name.simple("Nat").axiom(type=TYPE), a.axiom(type=NAT),
        f.axiom(type=forall(x.binder(type=NAT))(NAT)), op,
    ])
    assert_whnf_parity(env, op.const())
    assert_whnf_parity(env, a.const())
    assert_whnf_parity(env, f.const().app(a.const()))


def test_zeta():
    env = Environment.having([
        Name.simple("Nat").axiom(type=TYPE), a.axiom(type=NAT),
        f.axiom(type=forall(x.binder(type=NAT), y.binder(type=NAT))(NAT)),
    ])
    e = x.let(type=NAT, value=a.const(), body=f.const().app(b0, b0))
    assert_whnf_parity(env, e)
    nested = x.let(type=NAT, value=a.const(), body=y.let(type=NAT, value=b0, body=b0))
    assert_whnf_parity(env, nested)


def test_iota_on_constructors():
    env, d = TestIotaReduction()._make_mybool_env()
    z_val = Name.simple("z_val").axiom(type=NAT)
    t_val = Name.simple("t_val").axiom(type=NAT)
    env = Environment.having(list(env.declarations.values()) + [z_val, t_val])
    one = u.succ()
    motive = fun(Name.simple("_").binder(type=d["MyBool"].const()))(NAT)
    for ctor, expected in [(d["true"], t_val), (d["false"], z_val)]:
        rec_app = (
            d["rec"].const(levels=[one])
            .app(motive, z_val.const(), t_val.const(), ctor.const())
        )
        result = assert_whnf_parity(env, rec_app)
        assert syntactic_eq(result, expected.const())


def test_iota_major_behind_definition():
    env, d = TestIotaReduction()._make_mybool_env()
    z_val = Name.simple("z_val").axiom(type=NAT)
    t_val = Name.simple("t_val").axiom(type=NAT)
    alias = Name.simple("alias").definition(
        type=d["MyBool"].const(), value=d["true"].const(),
    )
    env = Environment.having(list(env.declarations.values()) + [z_val, t_val, alias])
    motive = fun(Name.simple("_").binder(type=d["MyBool"].const()))(NAT)
    rec_app = (
        d["rec"].const(levels=[u.succ()])
        .app(motive, z_val.const(), t_val.const(), alias.const())
    )
    assert syntactic_eq(assert_whnf_parity(env, rec_app), t_val.const())


def test_nat_rec_on_literal_is_one_step():
    env, d = TestIotaReduction()._make_nat_env()
    hz = Name.simple("hz").axiom(type=NAT)
    hs = Name.simple("hs").axiom(type=forall(x.binder(type=NAT), y.binder(type=NAT))(NAT))
    env = Environment.having(list(env.declarations.values()) + [hz, hs])
    motive = fun(Name.simple("_").binder(type=NAT))(NAT)
    rec = d["Nat_rec"].const(levels=[d["u_level"].succ()])
    assert_whnf_parity(env, rec.app(motive, hz.const(), hs.const(), W_LitNat.int(0)))
    big = rec.app(motive, hz.const(), hs.const(), W_LitNat.int(1 << 40))
    result = assert_whnf_parity(env, big)
    # `hs (N-1) (Nat.rec … (N-1))`: the recursive call stays unevaluated.
    assert syntactic_eq(result.fn.arg, W_LitNat.int((1 << 40) - 1))


def test_native_nat_ops():
    Nat = Name.simple("Nat")
    decls = [Nat.axiom(type=TYPE), a.axiom(type=NAT)]
    for op in ["add", "sub", "mul", "pow", "gcd", "mod", "div", "beq", "ble",
               "land", "lor", "xor", "shiftLeft", "shiftRight"]:
        decls.append(Nat.child(op).axiom(type=forall(x.binder(type=NAT), y.binder(type=NAT))(NAT)))
    decls.append(Name.simple("Bool").inductive(type=TYPE))
    env = Environment.having(decls)
    for op, l, r in [("add", 2, 3), ("sub", 5, 3), ("sub", 3, 5), ("mul", 6, 7),
                     ("pow", 2, 10), ("gcd", 12, 18), ("mod", 17, 5), ("mod", 3, 0),
                     ("div", 17, 5), ("div", 3, 0), ("beq", 4, 4), ("beq", 4, 5),
                     ("ble", 4, 5), ("ble", 5, 5), ("ble", 6, 5), ("land", 12, 10),
                     ("lor", 12, 10), ("xor", 12, 10), ("shiftLeft", 3, 4),
                     ("shiftRight", 48, 4)]:
        e = Nat.child(op).const().app(W_LitNat.int(l), W_LitNat.int(r))
        assert_whnf_parity(env, e)
    # A non-literal argument leaves the op stuck on both engines.
    assert_whnf_parity(env, Nat.child("add").const().app(a.const(), W_LitNat.int(1)))
    # Arguments that reduce to literals through definitions.
    two = Name.simple("two").definition(type=NAT, value=W_LitNat.int(2))
    env = Environment.having(decls + [two])
    assert_whnf_parity(env, Nat.child("mul").const().app(two.const(), Nat.child("add").const().app(W_LitNat.int(1), two.const())))


def test_projection_of_constructor():
    Foo = Name.simple("Foo")
    Foo_mk = Foo.child("mk")
    mk_decl = Foo_mk.constructor(
        type=forall(a.binder(type=TYPE).to_implicit(), x.binder(type=b0))(Foo.const().app(b1)),
        num_params=1, num_fields=1,
    )
    foo_type = Foo.inductive(type=forall(a.binder(type=TYPE))(TYPE), constructors=[mk_decl], num_params=1)
    myVal = Name.simple("myVal").axiom(type=NAT)
    env = Environment.having([Name.simple("Nat").axiom(type=TYPE), foo_type, mk_decl, myVal])
    proj = Foo.proj(0, Foo_mk.const().app(NAT, myVal.const()))
    assert syntactic_eq(assert_whnf_parity(env, proj), myVal.const())
    stuck = Foo.proj(0, myVal.const())
    assert_whnf_parity(env, stuck)


def test_quot_lift():
    env = Environment.having([
        Name.simple("Nat").axiom(type=TYPE),
        a.axiom(type=NAT),
        f.axiom(type=forall(x.binder(type=NAT))(NAT)),
        Name.simple("r").axiom(type=TYPE),
        Name.simple("h").axiom(type=TYPE),
        Quot.child("mk").axiom(type=TYPE, levels=[u.name]),
        Quot.child("lift").axiom(type=TYPE, levels=[u.name, v.name]),
    ])
    mk_app = Quot.child("mk").const(levels=[u]).app(NAT, Name.simple("r").const(), a.const())
    lift_app = Quot.child("lift").const(levels=[u, v]).app(
        NAT, Name.simple("r").const(), NAT, f.const(), Name.simple("h").const(), mk_app,
    )
    assert syntactic_eq(assert_whnf_parity(env, lift_app), f.const().app(a.const()))


def test_whnf_core_does_not_unfold():
    ident = Name.simple("ident").definition(
        type=forall(x.binder(type=NAT))(NAT), value=fun(x.binder(type=NAT))(b0),
    )
    env = Environment.having([Name.simple("Nat").axiom(type=TYPE), a.axiom(type=NAT), ident])
    m = machine(env)
    try:
        e = ident.const().app(a.const())
        h = m.store.import_term(e)
        assert m.whnf_core(h) == h
        assert m.store.export_term(m.whnf(h)) is a.const()
        beta = fun(x.binder(type=NAT))(f.const().app(b0)).app(a.const())
        hb = m.store.import_term(beta)
        assert syntactic_eq(m.store.export_term(m.whnf_core(hb)), f.const().app(a.const()))
    finally:
        m.free()


def test_struct_eta_major_bails_for_now():
    Pair = Name.simple("Pair")
    Pair_mk = Pair.child("mk")
    Pair_rec = Pair.child("rec")
    u_name = Name.simple("u")
    u_level = u_name.level()
    fst_name, snd_name = Name.simple("fst"), Name.simple("snd")
    mk_decl = Pair_mk.constructor(
        type=forall(fst_name.binder(type=NAT), snd_name.binder(type=NAT))(Pair.const()),
        num_params=0, num_fields=2,
    )
    pair_decl = Pair.inductive(type=TYPE, constructors=[mk_decl])
    motive = Name.simple("motive")
    s_name = Name.simple("s")
    motive_type = forall(s_name.binder(type=Pair.const()))(u_level.sort())
    mk_case_type = forall(fst_name.binder(type=NAT), snd_name.binder(type=NAT))(
        W_BVar(2).app(Pair_mk.const().app(W_BVar(1), W_BVar(0))))
    rec_type = forall(
        motive.binder(type=motive_type),
        Name.simple("mk_case").binder(type=mk_case_type),
        s_name.binder(type=Pair.const()),
    )(W_BVar(2).app(W_BVar(0)))
    mk_rule_val = fun(
        motive.binder(type=motive_type),
        Name.simple("mk_case").binder(type=mk_case_type),
        fst_name.binder(type=NAT), snd_name.binder(type=NAT),
    )(W_BVar(2).app(W_BVar(1), W_BVar(0)))
    rec_decl = Pair_rec.recursor(
        type=rec_type,
        rules=[W_RecRule(ctor_name=Pair_mk, num_fields=2, rhs=mk_rule_val)],
        num_motives=1, num_params=0, num_indices=0, num_minors=1, levels=[u_name],
    )
    stuck = Name.simple("stuck").axiom(type=Pair.const())
    env = Environment.having([pair_decl, mk_decl, rec_decl, Name.simple("Nat").inductive(type=TYPE), stuck])
    motive_lam = fun(Name.simple("_t").binder(type=Pair.const()))(NAT)
    fst_minor = fun(fst_name.binder(type=NAT), snd_name.binder(type=NAT))(W_BVar(1))
    rec_app = Pair_rec.const(levels=[u.succ()]).app(motive_lam).app(fst_minor).app(stuck.const())
    # A constructor major still reduces through the machine.
    ctor_app = Pair_rec.const(levels=[u.succ()]).app(motive_lam).app(fst_minor).app(
        Pair_mk.const().app(W_LitNat.int(1), W_LitNat.int(2)))
    assert syntactic_eq(assert_whnf_parity(env, ctor_app), W_LitNat.int(1))
    m = machine(env)
    try:
        with pytest.raises(RawBail):
            m.whnf(m.store.import_term(rec_app))
    finally:
        m.free()
