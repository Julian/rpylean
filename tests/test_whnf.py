"""
Tests for weak head normal form (WHNF) reduction.
"""

from rpylean.environment import Environment
from rpylean.objects import (
    NAT,
    TYPE,
    PROP,
    Name,
    W_BVar,
    W_LitNat,
    W_LitStr,
    W_RecRule,
    forall,
    fun,
    names,
    syntactic_eq,
)


S, a, b, f, x, y, z = names("S", "a", "b", "f", "x", "y", "z")
b0, b1, b2, b3 = W_BVar(0), W_BVar(1), W_BVar(2), W_BVar(3)
u = Name.simple("u").level()


class TestFVar:
    def test_already_whnf(self):
        fvar = x.binder(type=NAT).fvar()
        assert fvar.whnf(Environment.EMPTY) is fvar


class TestLitStr:
    def test_already_whnf(self):
        lit = W_LitStr("hello")
        assert lit.whnf(Environment.EMPTY) is lit


class TestLitNat:
    def test_already_whnf(self):
        lit = W_LitNat.int(42)
        assert lit.whnf(Environment.EMPTY) is lit


class TestSort:
    def test_already_whnf(self):
        assert TYPE.whnf(Environment.EMPTY) is TYPE
        assert PROP.whnf(Environment.EMPTY) is PROP

        sort_u = u.sort()
        assert sort_u.whnf(Environment.EMPTY) is sort_u


class TestLambda:
    def test_already_whnf(self):
        lam = fun(x.binder(type=NAT))(b0)
        assert lam.whnf(Environment.EMPTY) is lam

    def test_body_not_reduced(self):
        # f := fun x ↦ x
        f_decl = Name.simple("f").definition(
            type=forall(x.binder(type=NAT))(NAT),
            value=fun(x.binder(type=NAT))(b0),
        )
        env = Environment.having([f_decl])

        # fun y ↦ f y - the body contains an application that could reduce
        lam = fun(y.binder(type=NAT))(f_decl.const().app(b0))
        assert lam.whnf(env) is lam


class TestForAll:
    def test_already_whnf(self):
        fa = forall(x.binder(type=NAT))(NAT)
        assert fa.whnf(Environment.EMPTY) is fa


class TestConst:
    def test_axiom_already_whnf(self):
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])
        const = a_decl.const()
        assert const.whnf(env) is const

    def test_definition_unfolds_to_value(self):
        # a := b
        b_decl = b.axiom(type=NAT)
        a_decl = a.definition(type=NAT, value=b_decl.const())
        env = Environment.having([a_decl, b_decl])

        assert syntactic_eq(a_decl.const().whnf(env), b_decl.const())

    def test_nested_definitions_fully_reduce(self):
        # c is an axiom
        # b := c
        # a := b
        # a.whnf gives c
        c_decl = Name.simple("c").axiom(type=NAT)
        b_decl = b.definition(type=NAT, value=c_decl.const())
        a_decl = a.definition(type=NAT, value=b_decl.const())
        env = Environment.having([a_decl, b_decl, c_decl])

        assert syntactic_eq(a_decl.const().whnf(env), c_decl.const())


class TestApp:
    """W_App.whnf performs beta reduction when head is a lambda."""

    def test_app_of_axiom_is_whnf(self):
        """Application of axiom (non-lambda) is already in WHNF."""
        f_decl = f.axiom(type=forall(x.binder(type=NAT))(NAT))
        a_decl = a.axiom(type=NAT)
        env = Environment.having([f_decl, a_decl])

        app = f_decl.const().app(a_decl.const())
        # Can't reduce - f is an axiom, not a lambda
        assert syntactic_eq(app.whnf(env), app)

    def test_beta_reduction(self):
        """(fun x ↦ x) a reduces to a."""
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        identity = fun(x.binder(type=NAT))(b0)
        app = identity.app(a_decl.const())

        assert syntactic_eq(app.whnf(env), a_decl.const())

    def test_beta_reduction_via_delta(self):
        """f a reduces to a when f := fun x ↦ x."""
        a_decl = a.axiom(type=NAT)
        f_decl = f.definition(
            type=forall(x.binder(type=NAT))(NAT),
            value=fun(x.binder(type=NAT))(b0),
        )
        env = Environment.having([f_decl, a_decl])

        app = f_decl.const().app(a_decl.const())

        # f unfolds to identity, then beta reduces
        assert syntactic_eq(app.whnf(env), a_decl.const())

    def test_nested_beta_reduction(self):
        """(fun x ↦ fun y ↦ x) a b reduces to a."""
        a_decl = a.axiom(type=NAT)
        b_decl = b.axiom(type=NAT)
        env = Environment.having([a_decl, b_decl])

        # fun x ↦ fun y ↦ x (returns first argument)
        const_fn = fun(x.binder(type=NAT), y.binder(type=NAT))(b1)
        app = const_fn.app(a_decl.const(), b_decl.const())

        assert syntactic_eq(app.whnf(env), a_decl.const())

    def test_partial_application(self):
        """(fun x y ↦ x) a reduces to fun y ↦ a."""
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        const_fn = fun(x.binder(type=NAT), y.binder(type=NAT))(b1)
        partial = const_fn.app(a_decl.const())

        # fun y ↦ a
        expected = fun(y.binder(type=NAT))(a_decl.const())
        assert syntactic_eq(partial.whnf(env), expected)


class TestLet:
    def test_zeta(self):
        """
        let x := a in x reduces to a.
        """
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        let_expr = x.let(type=NAT, value=a_decl.const(), body=b0)

        assert syntactic_eq(let_expr.whnf(env), a_decl.const())

    def test_nested(self):
        """
        let x := a in let y := x in y reduces to a.
        """
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])

        inner_let = y.let(type=NAT, value=b0, body=b0)  # let y := x in y
        outer_let = x.let(type=NAT, value=a_decl.const(), body=inner_let)

        assert syntactic_eq(outer_let.whnf(env), a_decl.const())


class TestProj:
    def test_reduces_struct(self):
        a_decl = a.axiom(type=NAT)
        f_decl = f.definition(type=NAT, value=a_decl.const())
        env = Environment.having([a_decl, f_decl])

        # Create a projection where the struct expr can reduce
        # proj.0 (f) where f := a
        proj = S.proj(field_index=0, struct_expr=f_decl.const())

        expected = S.proj(field_index=0, struct_expr=a_decl.const())
        assert syntactic_eq(proj.whnf(env), expected)

    def test_extracts_field_from_constructor(self):
        """
        Projection reduction (structural iota) extracts a field from a
        constructor application.

        Model a structure with one type parameter and one field:

            structure Foo (α : Type) where
              val : α

        Then verify that proj(Foo, 0, Foo.mk Nat myVal) reduces to myVal.
        """
        Foo = Name.simple("Foo")
        Foo_mk = Foo.child("mk")

        # Foo.mk has 1 type parameter (α : Type) and 1 field (val : α)
        mk_decl = Foo_mk.constructor(
            type=forall(
                a.binder(type=TYPE).to_implicit(),  # (α : Type)
                x.binder(type=b0),  # (val : α)
            )(Foo.const().app(b1)),  # Foo α
            num_params=1,
            num_fields=1,
        )

        foo_type = Foo.inductive(
            type=forall(a.binder(type=TYPE))(TYPE),
            constructors=[mk_decl],
            num_params=1,
        )

        myVal = Name.simple("myVal")
        myVal_decl = myVal.axiom(type=NAT)

        env = Environment.having([foo_type, mk_decl, myVal_decl])

        # proj(Foo, 0, Foo.mk Nat myVal) should reduce to myVal
        ctor_app = Foo_mk.const().app(NAT, myVal_decl.const())
        proj = Foo.proj(field_index=0, struct_expr=ctor_app)

        result = proj.whnf(env)
        assert syntactic_eq(result, myVal_decl.const())

    def test_extracts_second_field_from_constructor(self):
        """
        Verify that projection of field index 1 extracts the second field.

            structure Pair (α β : Type) where
              fst : α
              snd : β

        Then proj(Pair, 1, Pair.mk Nat Nat a b) reduces to b.
        """
        Pair = Name.simple("Pair")
        Pair_mk = Pair.child("mk")
        alpha = Name.simple("alpha")
        beta = Name.simple("beta")

        mk_decl = Pair_mk.constructor(
            type=forall(
                alpha.binder(type=TYPE).to_implicit(),  # (α : Type)
                beta.binder(type=TYPE).to_implicit(),  # (β : Type)
                x.binder(type=b1),  # (fst : α)
                y.binder(type=b1),  # (snd : β)
            )(Pair.const().app(b3, b2)),  # Pair α β
            num_params=2,
            num_fields=2,
        )

        pair_type = Pair.inductive(
            type=forall(
                alpha.binder(type=TYPE),
                beta.binder(type=TYPE),
            )(TYPE),
            constructors=[mk_decl],
            num_params=2,
        )

        a_decl = a.axiom(type=NAT)
        b_axiom = b.axiom(type=NAT)
        env = Environment.having([pair_type, mk_decl, a_decl, b_axiom])

        # Pair.mk Nat Nat a b
        ctor_app = Pair_mk.const().app(NAT, NAT, a_decl.const(), b_axiom.const())

        # proj(Pair, 1, Pair.mk Nat Nat a b) should reduce to b
        proj = Pair.proj(field_index=1, struct_expr=ctor_app)
        result = proj.whnf(env)
        assert syntactic_eq(result, b_axiom.const())

        # proj(Pair, 0, Pair.mk Nat Nat a b) should reduce to a
        proj0 = Pair.proj(field_index=0, struct_expr=ctor_app)
        result0 = proj0.whnf(env)
        assert syntactic_eq(result0, a_decl.const())

    def test_projection_through_definition(self):
        """
        Projection reduces through a definition to extract a field.

        This models the real-world pattern where a typeclass instance
        (like instLTNat) is a definition whose value is a constructor
        application.

            structure Foo where
              val : Nat

            def myInst : Foo := Foo.mk myVal

            proj(Foo, 0, myInst) should reduce to myVal
        """
        Foo = Name.simple("Foo")
        Foo_mk = Foo.child("mk")

        mk_decl = Foo_mk.constructor(
            type=forall(x.binder(type=NAT))(Foo.const()),
            num_params=0,
            num_fields=1,
        )

        foo_type = Foo.structure(
            type=TYPE,
            constructor=mk_decl,
        )

        myVal = Name.simple("myVal")
        myVal_decl = myVal.axiom(type=NAT)

        myInst = Name.simple("myInst")
        myInst_decl = myInst.definition(
            type=Foo.const(),
            value=Foo_mk.const().app(myVal_decl.const()),
        )

        env = Environment.having([foo_type, mk_decl, myVal_decl, myInst_decl])

        # proj(Foo, 0, myInst) where myInst := Foo.mk myVal
        proj = Foo.proj(field_index=0, struct_expr=myInst_decl.const())

        result = proj.whnf(env)
        assert syntactic_eq(result, myVal_decl.const())


class TestIotaReduction:
    """Iota reduction: recursor applied to a constructor."""

    def _make_mybool_env(self, extra_decls=None):
        """
        Build a minimal environment with a Bool-like inductive type.

            inductive MyBool : Type where
              | false : MyBool
              | true : MyBool

        Plus MyBool.rec with rules for each constructor.
        Returns (env, declarations dict).
        """
        MyBool = Name.simple("MyBool")
        MyBool_false = MyBool.child("false")
        MyBool_true = MyBool.child("true")
        MyBool_rec = MyBool.child("rec")

        u_name = Name.simple("u")
        u_level = u_name.level()

        false_decl = MyBool_false.constructor(
            type=MyBool.const(),
            num_params=0,
            num_fields=0,
        )
        true_decl = MyBool_true.constructor(
            type=MyBool.const(),
            num_params=0,
            num_fields=0,
        )
        mybool_decl = MyBool.inductive(
            type=TYPE,
            constructors=[false_decl, true_decl],
        )

        # MyBool.rec.{u} :
        #   (motive : MyBool → Sort u) →
        #   motive MyBool.false →
        #   motive MyBool.true →
        #   (t : MyBool) → motive t
        motive = Name.simple("motive")
        t = Name.simple("t")
        motive_type = forall(t.binder(type=MyBool.const()))(u_level.sort())

        rec_type = forall(
            motive.binder(type=motive_type),
            Name.simple("hf").binder(
                type=W_BVar(0).app(MyBool_false.const()),
            ),
            Name.simple("ht").binder(
                type=W_BVar(1).app(MyBool_true.const()),
            ),
            t.binder(type=MyBool.const()),
        )(W_BVar(3).app(W_BVar(0)))

        # Rec rule for false:
        #   fun (motive) (hf) (ht) => hf
        false_rule_val = fun(
            motive.binder(type=motive_type),
            Name.simple("hf").binder(
                type=W_BVar(0).app(MyBool_false.const()),
            ),
            Name.simple("ht").binder(
                type=W_BVar(1).app(MyBool_true.const()),
            ),
        )(W_BVar(1))

        # Rec rule for true:
        #   fun (motive) (hf) (ht) => ht
        true_rule_val = fun(
            motive.binder(type=motive_type),
            Name.simple("hf").binder(
                type=W_BVar(0).app(MyBool_false.const()),
            ),
            Name.simple("ht").binder(
                type=W_BVar(1).app(MyBool_true.const()),
            ),
        )(W_BVar(0))

        rec_decl = MyBool_rec.recursor(
            type=rec_type,
            rules=[
                W_RecRule(
                    ctor_name=MyBool_false,
                    num_fields=0,
                    val=false_rule_val,
                ),
                W_RecRule(
                    ctor_name=MyBool_true,
                    num_fields=0,
                    val=true_rule_val,
                ),
            ],
            num_motives=1,
            num_params=0,
            num_indices=0,
            num_minors=2,
            levels=[u_name],
        )

        # Nat is needed when the motive returns Nat
        Nat_decl = Name.simple("Nat").inductive(type=TYPE)

        decls = [mybool_decl, false_decl, true_decl, rec_decl, Nat_decl]
        if extra_decls:
            for d in extra_decls:
                decls.append(d)
        env = Environment.having(decls)

        return env, {
            "MyBool": MyBool,
            "false": MyBool_false,
            "true": MyBool_true,
            "rec": MyBool_rec,
            "false_decl": false_decl,
            "true_decl": true_decl,
            "rec_decl": rec_decl,
            "u_name": u_name,
        }

    def test_iota_direct_constructor(self):
        """Recursor applied to a direct constructor reduces."""
        env, d = self._make_mybool_env()

        # MyBool.rec.{1} (fun _ => Nat) z_val t_val MyBool.true
        # should reduce to t_val
        z_val = Name.simple("z_val").axiom(type=NAT)
        t_val = Name.simple("t_val").axiom(type=NAT)
        env = Environment.having(
            list(env.declarations.itervalues()) + [z_val, t_val],
        )

        one = u.succ()  # Sort 1 = Type
        motive = fun(Name.simple("_").binder(type=d["MyBool"].const()))(NAT)

        app = (
            d["rec"]
            .const(levels=[one])
            .app(motive)
            .app(z_val.const())
            .app(t_val.const())
            .app(d["true"].const())
        )

        result = app.whnf(env)
        assert syntactic_eq(result, t_val.const())

    def test_iota_major_premise_behind_definition(self):
        """
        Iota reduction succeeds when the major premise is a definition
        that WHNF-reduces to a constructor.

        This is the bug scenario: without WHNF-reducing the major premise,
        the recursor sees a W_Const (the definition name) instead of the
        constructor, and fails to match any rec rule.
        """
        myTrue = Name.simple("myTrue")
        z_val = Name.simple("z_val").axiom(type=NAT)
        t_val = Name.simple("t_val").axiom(type=NAT)

        env, d = self._make_mybool_env()

        myTrue_decl = myTrue.definition(
            type=d["MyBool"].const(),
            value=d["true"].const(),
        )

        env = Environment.having(
            list(env.declarations.itervalues()) + [z_val, t_val, myTrue_decl],
        )

        one = u.succ()  # Sort 1 = Type
        motive = fun(Name.simple("_").binder(type=d["MyBool"].const()))(NAT)

        # MyBool.rec.{1} (fun _ => Nat) z_val t_val myTrue
        # myTrue := MyBool.true, so this should reduce to t_val
        app = (
            d["rec"]
            .const(levels=[one])
            .app(motive)
            .app(z_val.const())
            .app(t_val.const())
            .app(myTrue_decl.const())
        )

        result = app.whnf(env)
        assert syntactic_eq(result, t_val.const())
