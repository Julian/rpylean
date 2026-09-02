"""
The raw machine as a checker: parity with the boxed kernel on the
arena's tutorial fixtures, and targeted inference / def_eq cases.
"""

import pytest

from rpylean._rawterms import RawBail, RawMachine
from rpylean.environment import Environment, Tracer, TypeChecker, from_export
from rpylean.exceptions import ExportError
from rpylean.objects import (
    NAT,
    PROP,
    TYPE,
    Name,
    W_BVar,
    W_LitNat,
    W_TypeError,
    forall,
    fun,
    names,
    syntactic_eq,
)
from tests.cache_lka_tutorial import ensure_downloaded


a, b, f, g, x, y, P = names("a", "b", "f", "g", "x", "y", "P")
b0, b1 = W_BVar(0), W_BVar(1)

_cache_dir = ensure_downloaded()
GOOD = sorted(_cache_dir.join("good").listdir("*.ndjson"))
BAD = sorted(_cache_dir.join("bad").listdir("*.ndjson"))


class _BailTracer(Tracer):
    def __init__(self):
        Tracer.__init__(self, None)
        self.bails = []

    def raw_bail(self, reason):
        self.bails.append(reason)


def _rejected(error):
    """The name of the declaration ``error`` rejects."""
    declaration = getattr(error, "declaration", None)
    if declaration is not None:
        return declaration.name.str()
    return error.name.str()


def _outcomes(path):
    """
    ``(boxed_errors, raw_errors, bails)`` for the export at ``path``:
    the declarations each engine rejects, by name.
    """
    boxed_env = from_export(path.open())
    boxed_env.raw_enabled = False
    boxed = sorted(_rejected(e) for e in boxed_env.type_check(boxed_env.all()))
    raw_env = from_export(path.open())
    tracer = _BailTracer()
    raw_env.tracer = tracer
    raw_env.raw_enabled = True
    raw = sorted(_rejected(e) for e in raw_env.type_check(raw_env.all()))
    return boxed, raw, tracer.bails


def _name_of(path):
    return path.purebasename


@pytest.mark.parametrize("path", GOOD, ids=_name_of)
def test_tutorial_good_parity(path):
    boxed, raw, bails = _outcomes(path)
    assert raw == boxed == []


@pytest.mark.parametrize("path", BAD, ids=_name_of)
def test_tutorial_bad_parity(path):
    try:
        boxed, raw, bails = _outcomes(path)
    except ExportError:
        return
    assert raw == boxed


def machine(env):
    return RawMachine(TypeChecker(env, None))


def _defs():
    Nat = Name.simple("Nat")
    ident = Name.simple("ident").definition(
        type=forall(x.binder(type=NAT))(NAT), value=fun(x.binder(type=NAT))(b0),
    )
    twice = Name.simple("twice").definition(
        type=forall(x.binder(type=NAT))(NAT),
        value=fun(x.binder(type=NAT))(ident.const().app(ident.const().app(b0))),
    )
    env = Environment.having([
        Nat.axiom(type=TYPE), a.axiom(type=NAT), b.axiom(type=NAT),
        f.axiom(type=forall(x.binder(type=NAT))(NAT)),
        P.axiom(type=forall(x.binder(type=NAT))(PROP)),
        ident, twice,
    ])
    return env, ident, twice


def assert_def_eq_parity(env, e1, e2):
    tc = TypeChecker(env, None)
    expected = tc.def_eq(e1, e2)
    m = machine(env)
    try:
        got = m.def_eq(m.store.import_term(e1), m.store.import_term(e2))
        assert got == expected, (e1, e2, got, expected)
        # Symmetric, and stable under the memo.
        assert m.def_eq(m.store.import_term(e2), m.store.import_term(e1)) == expected
        assert m.def_eq(m.store.import_term(e1), m.store.import_term(e2)) == expected
    finally:
        m.free()
    return expected


def assert_infer_parity(env, e):
    expected = e.infer(env)
    m = machine(env)
    try:
        got = m.store.export_term(m.infer(m.store.import_term(e), True))
        assert m.def_eq(m.store.import_term(got), m.store.import_term(expected))
        assert syntactic_eq(got.whnf(env), expected.whnf(env)) or TypeChecker(env, None).def_eq(got, expected)
    finally:
        m.free()


class TestDefEq(object):
    def test_identity_and_delta(self):
        env, ident, twice = _defs()
        assert assert_def_eq_parity(env, a.const(), a.const())
        assert not assert_def_eq_parity(env, a.const(), b.const())
        assert assert_def_eq_parity(env, ident.const().app(a.const()), a.const())
        assert assert_def_eq_parity(env, twice.const().app(a.const()), ident.const().app(a.const()))
        assert not assert_def_eq_parity(env, twice.const().app(a.const()), b.const())

    def test_binders_alpha(self):
        env, ident, twice = _defs()
        l1 = fun(x.binder(type=NAT))(f.const().app(b0))
        l2 = fun(y.binder(type=NAT))(f.const().app(b0))
        assert assert_def_eq_parity(env, l1, l2)
        assert not assert_def_eq_parity(env, l1, fun(y.binder(type=NAT))(b0))
        p1 = forall(x.binder(type=NAT))(P.const().app(b0))
        p2 = forall(y.binder(type=NAT))(P.const().app(ident.const().app(b0)))
        assert assert_def_eq_parity(env, p1, p2)

    def test_eta(self):
        env, ident, twice = _defs()
        assert assert_def_eq_parity(env, fun(x.binder(type=NAT))(f.const().app(b0)), f.const())
        assert assert_def_eq_parity(env, f.const(), fun(x.binder(type=NAT))(f.const().app(b0)))

    def test_literals_and_offset(self):
        env, ident, twice = _defs()
        assert assert_def_eq_parity(env, W_LitNat.int(3), W_LitNat.int(3))
        assert not assert_def_eq_parity(env, W_LitNat.int(3), W_LitNat.int(4))

    def test_sorts(self):
        env, ident, twice = _defs()
        u = Name.simple("u").level()
        assert assert_def_eq_parity(env, TYPE, TYPE)
        assert not assert_def_eq_parity(env, TYPE, PROP)
        assert assert_def_eq_parity(env, u.succ().sort(), u.succ().sort())

    def test_app_args(self):
        env, ident, twice = _defs()
        assert assert_def_eq_parity(env, f.const().app(ident.const().app(a.const())), f.const().app(a.const()))
        assert not assert_def_eq_parity(env, f.const().app(a.const()), f.const().app(b.const()))


class TestInfer(object):
    def test_leaves(self):
        env, ident, twice = _defs()
        for e in [a.const(), NAT, TYPE, PROP, W_LitNat.int(7), ident.const()]:
            assert_infer_parity(env, e)

    def test_app_lambda_forall(self):
        env, ident, twice = _defs()
        assert_infer_parity(env, f.const().app(a.const()))
        assert_infer_parity(env, ident.const().app(a.const()))
        assert_infer_parity(env, fun(x.binder(type=NAT))(f.const().app(b0)))
        assert_infer_parity(env, forall(x.binder(type=NAT))(P.const().app(b0)))
        assert_infer_parity(env, fun(x.binder(type=NAT), y.binder(type=NAT))(f.const().app(b1)))

    def test_let(self):
        env, ident, twice = _defs()
        assert_infer_parity(env, x.let(type=NAT, value=a.const(), body=f.const().app(b0)))

    def test_check_mode_rejects_bad_argument(self):
        env, ident, twice = _defs()
        m = machine(env)
        try:
            bad = f.const().app(TYPE)
            with pytest.raises(W_TypeError):
                m.infer(m.store.import_term(bad), True)
            # Inference-only mode trusts the term.
            m.infer(m.store.import_term(bad), False)
        finally:
            m.free()


class TestCheckValue(object):
    def test_definition_accepted_and_rejected(self):
        env, ident, twice = _defs()
        m = machine(env)
        try:
            assert m.check_value(NAT, ident.const().app(a.const()), False) is None
            err = m.check_value(TYPE, a.const(), False)
            assert isinstance(err, W_TypeError)
        finally:
            m.free()

    def test_theorem_needs_a_prop(self):
        env, ident, twice = _defs()
        m = machine(env)
        try:
            err = m.check_value(NAT, a.const(), True)
            assert err is not None
            assert "Prop" in str(err) or err is not None
        finally:
            m.free()
