from rpython.rlib.rbigint import rbigint
import pytest

from rpylean.objects import (
    NAT,
    NAT_ZERO,
    PROP,
    TYPE,
    W_LEVEL_ZERO,
    Binder,
    Name,
    W_App,
    W_Axiom,
    W_BVar,
    W_Const,
    W_Constructor,
    W_Declaration,
    W_Definition,
    W_ForAll,
    W_Inductive,
    W_Lambda,
    W_Let,
    W_LevelIMax,
    W_LevelMax,
    W_LevelParam,
    W_LevelSucc,
    W_LitNat,
    W_Opaque,
    W_Proj,
    W_Recursor,
    W_Sort,
    W_Theorem,
    forall,
    fun,
    names,
)


Empty, x, y = names("Empty", "x", "y")
u, v = Name.simple("u").level(), Name.simple("v").level()


class TestName(object):
    def test_simple(self):
        assert Name.simple("foo") == Name(["foo"])

    def test_simple_hierarchical(self):
        assert Name.simple("foo.bar") == Name(["foo.bar"])

    def test_from_str(self):
        assert Name.from_str("foo") == Name(["foo"])

    def test_from_str_multipart(self):
        assert Name.from_str("foo.bar") == Name(["foo", "bar"])

    def test_child(self):
        assert Name.simple("foo").child("bar") == Name(["foo", "bar"])

    def test_child_anonymous(self):
        assert Name.ANONYMOUS.child("foo") == Name.simple("foo")

    @pytest.mark.parametrize(
        "base, name, expected",
        [
            (
                Name.simple("foo"),
                Name(["foo", "bar"]),
                Name.simple("bar"),
            ),
            (
                Name.simple("foo"),
                Name(["foo", "bar", "baz"]),
                Name(["bar", "baz"]),
            ),
            (
                Name(["foo", "bar"]),
                Name(["foo", "spam", "eggs"]),
                Name(["spam", "eggs"]),
            ),
            (
                Name.simple("foo"),
                Name.simple("bar"),
                Name.simple("bar"),
            ),
            (
                Name.ANONYMOUS,
                Name.simple("foo"),
                Name.simple("foo"),
            ),
            (
                Name.simple("foo"),
                Name.ANONYMOUS,
                Name.ANONYMOUS,
            ),
        ],
        ids=[
            "child_simple",
            "child_nested",
            "cousin",
            "unrelated",
            "in_anonymous",
            "anonymous",
        ],
    )
    def test_in_namespace(self, base, name, expected):
        assert name.in_namespace(base) == expected

    def test_is_private_via_prefix(self):
        assert Name(["_private", "foo"]).is_private()

    def test_is_private_via_nested(self):
        assert Name.from_str("foo._private.bar.0.baz").is_private()

    def test_not_private(self):
        assert not Name(["foo"]).is_private()

    def test_not_private_nested(self):
        assert not Name(["foo", "bar"]).is_private()

    def test_app(self):
        bar = Name(["foo", "bar"])
        bvar = W_BVar(0)
        assert bar.app(bvar) == W_App(bar.const(), bvar)

    def test_const_no_levels(self):
        bar = Name(["foo", "bar"])
        assert bar.const() == W_Const(bar, [])

    def test_const_with_levels(self):
        bar = Name(["foo", "bar"])
        assert bar.const([u, v]) == W_Const(bar, [u, v])

    def test_let(self):
        foo = Name.simple("foo")
        Nat = Name.simple("Nat")
        zero = Nat.child("zero")
        bvar = W_BVar(0)
        assert foo.let(
            type=Nat.const(),
            value=zero.const(),
            body=bvar,
        ) == W_Let(
            name=foo,
            type=Nat.const(),
            value=zero.const(),
            body=bvar,
        )

    def test_level(self):
        assert Name.simple("foo").level() == W_LevelParam(Name(["foo"]))

    def test_definition(self):
        foo = Name.simple("foo")
        Nat = Name.simple("Nat")
        zero = Nat.child("zero")
        assert foo.definition(
            type=Nat.const(),
            value=zero.const(),
        ) == W_Declaration(
            name=foo,
            type=Nat.const(),
            levels=[],
            w_kind=W_Definition(value=zero.const(), hint="R"),
        )

    def test_axiom(self):
        foo = Name.simple("foo")
        assert foo.axiom(type=NAT) == W_Declaration(
            name=foo,
            type=NAT,
            levels=[],
            w_kind=W_Axiom(),
        )

    def test_theorem(self):
        foo = Name.simple("foo")
        # FIXME: this theorem is not a Prop, but that's too annoying to make
        theorem = foo.theorem(type=NAT, value=NAT_ZERO)
        assert theorem == W_Declaration(
            name=Name.simple("foo"),
            type=NAT,
            levels=[],
            w_kind=W_Theorem(value=NAT_ZERO),
        )

    def test_inductive(self):
        assert Empty.inductive(type=TYPE) == W_Declaration(
            name=Empty,
            type=TYPE,
            levels=[],
            w_kind=W_Inductive(
                names=[Empty],
                constructors=[],
                num_nested=0,
                num_params=0,
                num_indices=0,
                is_recursive=False,
                is_reflexive=False,
            ),
        )

    def test_structure(self):
        Point = Name.simple("Point")
        x_nat, y_nat = x.binder(type=NAT), y.binder(type=NAT)
        constructor = forall(x_nat, y_nat)(Point.const())
        struct = Point.structure(type=TYPE, constructor=constructor)
        assert struct == Point.inductive(
            type=TYPE,
            constructors=[constructor],
        )

    def test_constructor(self):
        True_ = Name.simple("True")
        intro = True_.child("intro")
        assert intro.constructor(type=True_.const()) == W_Declaration(
            name=intro,
            type=True_.const(),
            levels=[],
            w_kind=W_Constructor(num_params=0, num_fields=0),
        )

    def test_recursor(self):
        rec = Empty.child("rec")
        assert rec.recursor(type=Empty.const()) == W_Declaration(
            name=rec,
            type=Empty.const(),
            levels=[],
            w_kind=W_Recursor(
                names=[rec],
                rules=[],
                num_motives=1,
                num_params=0,
                num_indices=0,
                num_minors=0,
                k=0,
            ),
        )

    def test_opaque(self):
        o = Name.simple("o")
        Nat = Name.simple("Nat")
        zero = Nat.child("zero")
        assert o.opaque(type=Nat.const(), value=zero.const()) == W_Declaration(
            name=o,
            type=Nat.const(),
            levels=[],
            w_kind=W_Opaque(value=zero.const()),
        )

    def test_proj(self):
        Prod = Name.simple("Prod")
        mk = Prod.child("mk")
        expr = mk.app(NAT_ZERO, NAT_ZERO)
        assert Prod.proj(0, expr) == W_Proj(Prod, 0, expr)

    def test_binder(self):
        Nat = Name.simple("Nat")
        assert x.binder(type=Nat) == Binder(
            name=x,
            type=Nat,
            left="(",
            right=")",
        )

    def test_implicit_binder(self):
        Nat = Name.simple("Nat")
        assert x.implicit_binder(type=Nat) == Binder(
            name=x,
            type=Nat,
            left="{",
            right="}",
        )

    def test_instance_implicit_binder(self):
        NeZero = Name.simple("NeZero")
        assert x.instance_binder(type=NeZero) == Binder(
            name=x,
            type=NeZero,
            left="[",
            right="]",
        )

    def test_strict_implicit_binder(self):
        Nat = Name.simple("Nat")
        assert x.strict_implicit_binder(type=Nat) == Binder(
            name=x,
            type=Nat,
            left="⦃",
            right="⦄",
        )

    def test_hash_is_order_sensitive(self):
        assert Name(["foo", "bar"]).hash() != Name(["bar", "foo"]).hash()


def test_names():
    assert names("foo", "A.b") == [Name.simple("foo"), Name(["A", "b"])]


class TestBinder(object):
    def test_to_implicit(self):
        Nat = Name.simple("Nat")
        binder = Binder.default(name=x, type=Nat).to_implicit()
        assert binder == Binder.implicit(name=x, type=Nat)

    def test_default_is_default(self):
        assert Name.simple("x").binder(type=NAT).is_default()

    def test_not_default_is_not_default(self):
        assert not Name.simple("x").implicit_binder(type=NAT).is_default()


class TestDeclaration(object):
    def test_const(self):
        decl = Name.simple("foo").axiom(type=NAT)
        assert decl.const() == W_Const(Name.simple("foo"), [])


class TestLevel(object):

    @pytest.mark.parametrize(
        "lhs, rhs, expected",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (
                W_LEVEL_ZERO.succ(),
                W_LEVEL_ZERO.succ().succ().succ(),
                W_LEVEL_ZERO.succ().succ().succ(),
            ),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ().succ(), W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u, u),
            (u, v, W_LevelMax(u, v)),
            (u.succ(), v, W_LevelMax(u.succ(), v)),
            (u, v.succ(), W_LevelMax(u, v.succ())),
            (u.succ(), v.succ(), u.max(v).succ()),
            (u.succ(), u, u.succ()),
            (u, u.succ(), u.succ()),
            (u, u.max(v), u.max(v)),
            (v, u.max(v), u.max(v)),
            (u, u.imax(v), u.imax(v)),
            (v, u.imax(v), u.imax(v)),
        ],
        ids=[
            "0_0",
            "0_1",
            "1_3",
            "1_0",
            "2_1",
            "u_u",
            "u_v",
            "u+1_v",
            "u_v+1",
            "u+1_v+1",
            "u+1_u",
            "u_u+1",
            "u_maxuv",
            "v_maxuv",
            "u_imaxuv",
            "v_imaxuv",
        ]
    )
    def test_max(self, lhs, rhs, expected):
        assert lhs.max(rhs) == expected

    @pytest.mark.parametrize(
        "lhs, rhs, expected",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO, W_LEVEL_ZERO),

            # imax 1 0 = 0
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO, W_LEVEL_ZERO),

            # in fact imax u 0 = 0 for any u
            (u, W_LEVEL_ZERO, W_LEVEL_ZERO),

            # but imax 0 1 = 1
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),

            # in fact imax 0 u = u for any u
            (W_LEVEL_ZERO, u, u),

            # and in fact imax 1 u = u for any u as well
            (W_LEVEL_ZERO.succ(), u, u),

            (u, u, u),
            (u, v, W_LevelIMax(u, v)),
        ],
        ids=[
            "0_0",
            "1_0",
            "u_0",
            "0_1",
            "0_u",
            "1_u",
            "u_u",
            "u_v",
        ]
    )
    def test_imax(self, lhs, rhs, expected):
        assert lhs.imax(rhs) == expected

    @pytest.mark.parametrize(
        "lhs, rhs",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u.succ()),
            (u, u.succ().succ()),
            (W_LEVEL_ZERO, u),
            (W_LEVEL_ZERO, u.max(v)),
            (W_LEVEL_ZERO, u.imax(v)),
            (u.max(v), u.succ().max(v.succ())),
            (u.imax(v), u.succ().imax(v.succ())),
        ],
        ids=[
            "0_1",
            "1_2",
            "u_u+1",
            "u_u+2",
            "0_u",
            "0_max_uv",
            "0_imax_uv",
            "max_uv_u+1v+1",
            "imax_uv_u+1v+1",
        ]
    )
    def test_leq_lt(self, lhs, rhs):
        assert lhs.leq(rhs)
        assert not rhs.leq(lhs)

    @pytest.mark.parametrize(
        "lhs, rhs",
        [
            (W_LEVEL_ZERO, W_LEVEL_ZERO),
            (W_LEVEL_ZERO.succ(), W_LEVEL_ZERO.succ()),
            (W_LEVEL_ZERO.succ().succ(), W_LEVEL_ZERO.succ().succ()),
            (u, u),
            (u.succ(), u.succ()),
            (u.succ().succ(), u.succ().succ()),
            (u.max(v), u.max(v)),
            (u.max(v).succ(), u.max(v).succ()),
            (u.imax(v), u.imax(v)),
            (u.imax(v).succ(), u.imax(v).succ()),
        ],
        ids=[
            "0_0",
            "1_1",
            "2_2",
            "u_u",
            "u+1_u+1",
            "u+2_u+2",
            "max_uv",
            "max_uv+1",
            "imax_uv",
            "imax_uv+1",
        ]
    )
    def test_leq_eq(self, lhs, rhs):
        assert lhs.leq(rhs)
        assert rhs.leq(lhs)
        assert lhs.eq(rhs)
        assert rhs.eq(lhs)

    def test_succ(self):
        assert u.succ() == W_LevelSucc(W_LevelParam(Name(["u"])))

    def test_succ_level_zero(self):
        assert W_LEVEL_ZERO.succ() == W_LevelSucc(W_LEVEL_ZERO)

    def test_sort(self):
        assert W_LEVEL_ZERO.sort() == W_Sort(W_LEVEL_ZERO) == PROP


class TestConst(object):
    def test_child(self):
        name = Name.simple("foo")
        assert name.const().child("bar") == name.child("bar").const()

    def test_app(self):
        bvar = W_BVar(0)
        id = Name.simple("id").const()
        assert id.app(bvar) == W_App(id, bvar)

    def test_app_multiarg(self):
        b0, b1, b2 = W_BVar(0), W_BVar(1), W_BVar(2)
        foo = Name.simple("foo").const()
        assert foo.app(b0, b1, b2) == W_App(W_App(W_App(foo, b0), b1), b2)


class TestLitNat(object):
    def test_char(self):
        assert W_LitNat.char("o") == W_LitNat.int(111)

    def test_int(self):
        assert W_LitNat.int(37) == W_LitNat(rbigint.fromint(37))


class TestForAll(object):
    def test_single(self):
        nat = x.binder(type=NAT)
        assert forall(nat)(y.const()) == W_ForAll(binder=nat, body=y.const())

    def test_multiple(self):
        P = Name.simple("P").const()
        x_nat = x.binder(type=NAT)
        y_type = y.binder(type=TYPE)
        assert forall(x_nat, y_type)(P) == W_ForAll(
            binder=x_nat,
            body=W_ForAll(binder=y_type, body=P),
        )


class TestFun(object):
    def test_single(self):
        nat = x.binder(type=NAT)
        assert fun(nat)(y.const()) == W_Lambda(binder=nat, body=y.const())

    def test_multiple(self):
        P = Name.simple("P").const()
        x_nat = x.binder(type=NAT)
        y_type = y.binder(type=TYPE)
        assert fun(x_nat, y_type)(P) == W_Lambda(
            binder=x_nat,
            body=W_Lambda(binder=y_type, body=P),
        )
