"""
Tests for weak head normal form (WHNF) reduction.
"""

from rpylean.environment import Environment, Tracer
from rpylean.objects import (
    NAT,
    TYPE,
    PROP,
    Name,
    W_App,
    W_BVar,
    W_LitNat,
    W_LitStr,
    W_RecRule,
    forall,
    fun,
    names,
    syntactic_eq,
)


class _CollectingTracer(Tracer):
    """Tracer that records each form seen during WHNF reduction."""

    def __init__(self):
        Tracer.__init__(self, None)
        self.steps = []

    def whnf_step(self, expr, declarations):
        self.steps.append(expr)


Quot = Name.simple("Quot")
S, a, b, f, x, y, z = names("S", "a", "b", "f", "x", "y", "z")
b0, b1, b2, b3 = W_BVar(0), W_BVar(1), W_BVar(2), W_BVar(3)
u, v = Name.simple("u").level(), Name.simple("v").level()


class TestFVar(object):
    def test_already_whnf(self):
        fvar = x.binder(type=NAT).fvar()
        assert fvar.whnf(Environment.EMPTY) is fvar


class TestLitStr(object):
    def test_already_whnf(self):
        lit = W_LitStr("hello")
        assert lit.whnf(Environment.EMPTY) is lit


class TestLitNat(object):
    def test_already_whnf(self):
        lit = W_LitNat.int(42)
        assert lit.whnf(Environment.EMPTY) is lit


class TestSort(object):
    def test_already_whnf(self):
        assert TYPE.whnf(Environment.EMPTY) is TYPE
        assert PROP.whnf(Environment.EMPTY) is PROP

        sort_u = u.sort()
        assert sort_u.whnf(Environment.EMPTY) is sort_u


class TestLambda(object):
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


class TestForAll(object):
    def test_already_whnf(self):
        fa = forall(x.binder(type=NAT))(NAT)
        assert fa.whnf(Environment.EMPTY) is fa


class TestConst(object):
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

    def test_opaque_declaration_does_not_unfold(self):
        b_decl = b.axiom(type=NAT)
        a_decl = a.opaque(type=NAT, value=b_decl.const())
        env = Environment.having([a_decl, b_decl])

        const = a_decl.const()
        assert const.whnf(env) is const


class TestApp(object):
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

    def test_app_preserves_reduced_fn_when_not_further_reducible(self):
        """
        When ((fun _ => g) x) beta-reduces to g (an axiom), applying another
        argument should give (g y), not the original expression.

        Regression test: Previously, when the head reduced via beta to a constant
        that couldn't be further delta-reduced, whnf returned the original
        expression instead of the partially-reduced one.
        """
        # g is an axiom (can't be delta-reduced)
        g_decl = Name.simple("g").axiom(type=forall(x.binder(type=NAT))(NAT))
        a_decl = a.axiom(type=NAT)
        env = Environment.having([g_decl, a_decl])

        # ((fun _ => g) a b).whnf should give (g b)
        # First beta: (fun _ => g) a => g
        # Then we have (g b)
        inner = fun(x.binder(type=NAT))(g_decl.const())  # fun _ => g
        app = inner.app(a_decl.const()).app(a_decl.const())  # ((fun _ => g) a) a
        reduced = app.whnf(env)

        expected = g_decl.const().app(a_decl.const())  # g a
        assert syntactic_eq(reduced, expected)


class TestClosure(object):
    def test_resolves_inner_bvar(self):
        """Closure([fvar], BVar(0)) reduces to fvar."""
        fvar = x.binder(type=NAT).fvar()
        closure = b0.closure([fvar])
        assert syntactic_eq(closure.whnf(Environment.EMPTY), fvar)

    def test_shifts_outer_bvar_down(self):
        """Closure([fvar], BVar(2)) reduces to BVar(1) (env consumed bvar(0))."""
        fvar = x.binder(type=NAT).fvar()
        closure = b2.closure([fvar])
        assert syntactic_eq(closure.whnf(Environment.EMPTY), b1)

    def test_atomic_body_passes_through(self):
        """Closure([fvar], Const) is just Const."""
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])
        const = a_decl.const()
        # Const has no loose bvars, so .closure() should already collapse.
        # Construct W_Closure directly to exercise WHNF too.
        from rpylean.objects import W_Closure
        fvar = x.binder(type=NAT).fvar()
        closure = W_Closure([fvar], const)
        assert syntactic_eq(closure.whnf(env), const)

    def test_pushes_through_app_to_resolve_bvar(self):
        """Closure([arg], App(f, BVar(0))) reduces to App(f, arg)."""
        f_decl = f.axiom(type=forall(x.binder(type=NAT))(NAT))
        arg_decl = a.axiom(type=NAT)
        env = Environment.having([f_decl, arg_decl])
        body = f_decl.const().app(b0)
        closure = body.closure([arg_decl.const()])
        expected = f_decl.const().app(arg_decl.const())
        assert syntactic_eq(closure.whnf(env), expected)


class TestLet(object):
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


class TestProj(object):
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


class TestIotaReduction(object):
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
                    rhs=false_rule_val,
                ),
                W_RecRule(
                    ctor_name=MyBool_true,
                    num_fields=0,
                    rhs=true_rule_val,
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

    def _make_nat_env(self):
        """
        Build an environment with Nat, Nat.zero, Nat.succ, Nat.rec.

        Returns (env, dict of names).
        """
        Nat = Name.simple("Nat")
        Nat_zero = Nat.child("zero")
        Nat_succ = Nat.child("succ")
        Nat_rec = Nat.child("rec")

        u_name = Name.simple("u")
        u_level = u_name.level()

        zero_decl = Nat_zero.constructor(
            type=NAT,
            num_params=0,
            num_fields=0,
        )
        succ_decl = Nat_succ.constructor(
            type=forall(Name.simple("n").binder(type=NAT))(NAT),
            num_params=0,
            num_fields=1,
        )
        nat_decl = Nat.inductive(
            type=TYPE,
            constructors=[zero_decl, succ_decl],
        )

        # Nat.rec.{u} :
        #   (motive : Nat → Sort u) →
        #   motive Nat.zero →
        #   ((n : Nat) → motive n → motive (Nat.succ n)) →
        #   (t : Nat) → motive t
        motive = Name.simple("motive")
        n = Name.simple("n")
        ih = Name.simple("ih")
        t = Name.simple("t")
        motive_type = forall(t.binder(type=NAT))(u_level.sort())
        # In the hs binder context, motive is bvar 2 (after motive, hz).
        hs_binder_type = forall(
            n.binder(type=NAT),
            ih.binder(type=W_BVar(2).app(W_BVar(0))),
        )(W_BVar(3).app(Nat_succ.const().app(W_BVar(1))))

        rec_type = forall(
            motive.binder(type=motive_type),
            Name.simple("hz").binder(type=W_BVar(0).app(Nat_zero.const())),
            Name.simple("hs").binder(type=hs_binder_type),
            t.binder(type=NAT),
        )(W_BVar(3).app(W_BVar(0)))

        # Zero rule: λ motive hz hs => hz
        zero_rule_val = fun(
            motive.binder(type=motive_type),
            Name.simple("hz").binder(type=W_BVar(0).app(Nat_zero.const())),
            Name.simple("hs").binder(type=hs_binder_type),
        )(W_BVar(1))

        # Succ rule: λ motive hz hs n => hs n (Nat.rec.{u} motive hz hs n)
        succ_rule_val = fun(
            motive.binder(type=motive_type),
            Name.simple("hz").binder(type=W_BVar(0).app(Nat_zero.const())),
            Name.simple("hs").binder(type=hs_binder_type),
            n.binder(type=NAT),
        )(
            W_BVar(1).app(W_BVar(0)).app(
                Nat_rec.const(levels=[u_level])
                    .app(W_BVar(3))
                    .app(W_BVar(2))
                    .app(W_BVar(1))
                    .app(W_BVar(0))
            )
        )

        rec_decl = Nat_rec.recursor(
            type=rec_type,
            rules=[
                W_RecRule(ctor_name=Nat_zero, num_fields=0, rhs=zero_rule_val),
                W_RecRule(ctor_name=Nat_succ, num_fields=1, rhs=succ_rule_val),
            ],
            num_motives=1,
            num_params=0,
            num_indices=0,
            num_minors=2,
            levels=[u_name],
        )

        env = Environment.having([nat_decl, zero_decl, succ_decl, rec_decl])
        return env, {
            "Nat_rec": Nat_rec,
            "Nat_zero": Nat_zero,
            "u_level": u_level,
        }

    def test_iota_natrec_on_huge_litnat_is_lazy(self):
        """Nat.rec on a huge W_LitNat does one constructor step instead of building a deep succ chain."""
        env, d = self._make_nat_env()

        n = Name.simple("n")
        ih = Name.simple("ih")
        # Step: λ n ih => Nat.succ ih  (uses the IH but does not force its WHNF)
        Nat_succ = Name.simple("Nat").child("succ").const()
        ms = fun(
            n.binder(type=NAT),
            ih.binder(type=NAT),
        )(Nat_succ.app(W_BVar(0)))

        motive = fun(Name.simple("_").binder(type=NAT))(NAT)

        depth = 1000000
        app = (
            d["Nat_rec"].const(levels=[d["u_level"].succ()])
                .app(motive)
                .app(d["Nat_zero"].const())
                .app(ms)
                .app(W_LitNat.int(depth))
        )

        result = app.whnf(env)
        assert (isinstance(result, W_App)
                and syntactic_eq(result.fn, Nat_succ))


class TestNativeNatReduction(object):
    """Native nat kernel operations reduce in WHNF without unfolding definitions."""

    def test_nat_succ_not_natively_reduced(self):
        """Nat.succ is not natively reduced; it stays as a constructor app."""
        from rpylean.objects import _try_reduce_nat

        app = Name.simple("Nat").child("succ").const().app(W_LitNat.int(5))
        result = _try_reduce_nat(app, Environment.EMPTY)
        assert result is None

    def test_nat_add(self):
        app = (
            Name.simple("Nat")
            .child("add")
            .const()
            .app(W_LitNat.int(3))
            .app(W_LitNat.int(7))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "10"

    def test_nat_sub(self):
        app = (
            Name.simple("Nat")
            .child("sub")
            .const()
            .app(W_LitNat.int(10))
            .app(W_LitNat.int(3))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "7"

    def test_nat_sub_underflow_is_zero(self):
        app = (
            Name.simple("Nat")
            .child("sub")
            .const()
            .app(W_LitNat.int(3))
            .app(W_LitNat.int(10))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "0"

    def test_nat_mul(self):
        app = (
            Name.simple("Nat")
            .child("mul")
            .const()
            .app(W_LitNat.int(6))
            .app(W_LitNat.int(7))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "42"

    def test_nat_pow(self):
        app = (
            Name.simple("Nat")
            .child("pow")
            .const()
            .app(W_LitNat.int(2))
            .app(W_LitNat.int(32))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "4294967296"

    def test_nat_div(self):
        app = (
            Name.simple("Nat")
            .child("div")
            .const()
            .app(W_LitNat.int(10))
            .app(W_LitNat.int(3))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "3"

    def test_nat_div_by_zero(self):
        app = (
            Name.simple("Nat")
            .child("div")
            .const()
            .app(W_LitNat.int(10))
            .app(W_LitNat.int(0))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "0"

    def test_nat_mod(self):
        app = (
            Name.simple("Nat")
            .child("mod")
            .const()
            .app(W_LitNat.int(10))
            .app(W_LitNat.int(3))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "1"

    def test_nat_mod_by_zero(self):
        app = (
            Name.simple("Nat")
            .child("mod")
            .const()
            .app(W_LitNat.int(10))
            .app(W_LitNat.int(0))
        )
        result = app.whnf(Environment.EMPTY)
        assert isinstance(result, W_LitNat)
        assert result.val.str() == "10"

    def test_nat_beq_true(self):
        from rpylean.objects import _BOOL_TRUE

        app = (
            Name.simple("Nat")
            .child("beq")
            .const()
            .app(W_LitNat.int(5))
            .app(W_LitNat.int(5))
        )
        result = app.whnf(Environment.EMPTY)
        assert syntactic_eq(result, _BOOL_TRUE)

    def test_nat_beq_false(self):
        from rpylean.objects import _BOOL_FALSE

        app = (
            Name.simple("Nat")
            .child("beq")
            .const()
            .app(W_LitNat.int(5))
            .app(W_LitNat.int(3))
        )
        result = app.whnf(Environment.EMPTY)
        assert syntactic_eq(result, _BOOL_FALSE)

    def test_nat_ble_true(self):
        from rpylean.objects import _BOOL_TRUE

        app = (
            Name.simple("Nat")
            .child("ble")
            .const()
            .app(W_LitNat.int(3))
            .app(W_LitNat.int(5))
        )
        result = app.whnf(Environment.EMPTY)
        assert syntactic_eq(result, _BOOL_TRUE)

    def test_nat_ble_equal(self):
        from rpylean.objects import _BOOL_TRUE

        app = (
            Name.simple("Nat")
            .child("ble")
            .const()
            .app(W_LitNat.int(5))
            .app(W_LitNat.int(5))
        )
        result = app.whnf(Environment.EMPTY)
        assert syntactic_eq(result, _BOOL_TRUE)

    def test_nat_ble_false(self):
        from rpylean.objects import _BOOL_FALSE

        app = (
            Name.simple("Nat")
            .child("ble")
            .const()
            .app(W_LitNat.int(5))
            .app(W_LitNat.int(3))
        )
        result = app.whnf(Environment.EMPTY)
        assert syntactic_eq(result, _BOOL_FALSE)

    def test_non_literal_arg_falls_through(self):
        """Native reduction returns None when args are not nat literals."""
        from rpylean.objects import _try_reduce_nat

        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])
        app = (
            Name.simple("Nat")
            .child("add")
            .const()
            .app(a_decl.const())
            .app(W_LitNat.int(3))
        )
        # _try_reduce_nat returns None when an arg isn't a nat literal
        result = _try_reduce_nat(app, env)
        assert result is None

    def test_to_nat_val_succ_of_zero(self):
        """_to_nat_val extracts 1 from Nat.succ(Nat.zero)."""
        from rpylean.objects import _to_nat_val

        Nat_decl = Name.simple("Nat").inductive(type=TYPE)
        Nat_zero_decl = (
            Name.simple("Nat")
            .child("zero")
            .constructor(
                type=NAT,
                num_params=0,
                num_fields=0,
            )
        )
        env = Environment.having([Nat_decl, Nat_zero_decl])
        app = (
            Name.simple("Nat")
            .child("succ")
            .const()
            .app(Name.simple("Nat").child("zero").const())
        )
        result = _to_nat_val(app, env)
        assert result is not None
        assert result.str() == "1"

    def test_to_nat_val_deep_succ_chain(self):
        """_to_nat_val handles deep Nat.succ chains without stack overflow."""
        from rpylean.objects import _to_nat_val

        Nat_decl = Name.simple("Nat").inductive(type=TYPE)
        Nat_zero_decl = (
            Name.simple("Nat")
            .child("zero")
            .constructor(
                type=NAT,
                num_params=0,
                num_fields=0,
            )
        )
        Nat_succ_decl = (
            Name.simple("Nat")
            .child("succ")
            .constructor(
                type=forall(x.binder(type=NAT))(NAT),
                num_params=0,
                num_fields=1,
            )
        )
        env = Environment.having([Nat_decl, Nat_zero_decl, Nat_succ_decl])
        succ = Name.simple("Nat").child("succ").const()
        expr = Name.simple("Nat").child("zero").const()
        depth = 2000
        for _ in range(depth):
            expr = succ.app(expr)
        result = _to_nat_val(expr, env)
        assert result is not None
        assert result.str() == str(depth)

    def test_projection_of_constructor_reduces(self):
        """
        When projecting a field from a constructor application, whnf should
        extract the corresponding argument.

        Given:  structure S where mk :: (fld : Nat)
        Then:   (S.mk a).fld should reduce to a
        """
        # Create structure S with one field
        S_name = Name.simple("S")
        mk_name = S_name.child("mk")

        # S.mk : Nat → S
        mk_ctor = mk_name.constructor(
            type=forall(x.binder(type=NAT))(S_name.const()),
            num_params=0,
            num_fields=1,
        )
        S_inductive = S_name.inductive(
            type=TYPE,
            constructors=[mk_ctor],
            num_params=0,
        )

        a_decl = a.axiom(type=NAT)
        env = Environment.having([S_inductive, mk_ctor, a_decl])

        # Build: (S.mk a).0  -- projection of field 0
        ctor_app = mk_name.const().app(a_decl.const())
        proj = S_name.proj(field_index=0, struct_expr=ctor_app)

        # Should reduce to a
        reduced = proj.whnf(env)
        assert syntactic_eq(reduced, a_decl.const())


def test_quot_lift_reduction():
    """Quot.lift f h (Quot.mk r a) reduces to f a."""
    env = Environment.having([
        Name.simple("Nat").axiom(type=TYPE),
        a.axiom(type=NAT),
        f.axiom(type=forall(x.binder(type=NAT))(NAT)),
        Name.simple("r").axiom(type=TYPE),
        Name.simple("h").axiom(type=TYPE),
        Quot.child("mk").axiom(type=TYPE, levels=[u.name]),
        Quot.child("lift").axiom(type=TYPE, levels=[u.name, v.name]),
    ])

    # Quot.lift {α} {r} {β} f h (Quot.mk {α} r a)
    mk_app = Quot.child("mk").const(levels=[u]).app(
        NAT, Name.simple("r").const(), a.const(),
    )
    lift_app = Quot.child("lift").const(levels=[u, v]).app(
        NAT, Name.simple("r").const(), NAT,
        f.const(), Name.simple("h").const(), mk_app,
    )

    reduced = lift_app.whnf(env)
    assert syntactic_eq(reduced, f.const().app(a.const()))


def test_struct_eta_reduction_on_stuck_major():
    """
    `S.rec motive minor stuck` reduces to `minor (S.proj_0 stuck) ...`
    when `S` is a single-ctor non-recursive inductive (a structure) and
    `stuck` is not a constructor application — Lean's struct-eta-on-
    casesOn rule. Mirrors the `Prod.casesOn (Poly.cancel ...)` shape
    that stalls in `Nat.Linear.ExprCnstr.denote_toNormPoly`.
    """
    Pair = Name.simple("Pair")
    Pair_mk = Pair.child("mk")
    Pair_rec = Pair.child("rec")
    u_name = Name.simple("u")
    u_level = u_name.level()

    fst_name = Name.simple("fst")
    snd_name = Name.simple("snd")
    mk_decl = Pair_mk.constructor(
        type=forall(
            fst_name.binder(type=NAT),
            snd_name.binder(type=NAT),
        )(Pair.const()),
        num_params=0,
        num_fields=2,
    )
    pair_decl = Pair.inductive(type=TYPE, constructors=[mk_decl])

    # Pair.rec.{u} :
    #   {motive : Pair → Sort u} →
    #   ((fst snd : Nat) → motive (Pair.mk fst snd)) →
    #   (s : Pair) → motive s
    motive = Name.simple("motive")
    s_name = Name.simple("s")
    motive_type = forall(s_name.binder(type=Pair.const()))(u_level.sort())
    mk_case_type = forall(
        fst_name.binder(type=NAT),
        snd_name.binder(type=NAT),
    )(W_BVar(2).app(Pair_mk.const().app(W_BVar(1), W_BVar(0))))
    rec_type = forall(
        motive.binder(type=motive_type),
        Name.simple("mk_case").binder(type=mk_case_type),
        s_name.binder(type=Pair.const()),
    )(W_BVar(2).app(W_BVar(0)))

    # Rec rule for mk: fun motive mk_case fst snd => mk_case fst snd
    mk_rule_val = fun(
        motive.binder(type=motive_type),
        Name.simple("mk_case").binder(type=mk_case_type),
        fst_name.binder(type=NAT),
        snd_name.binder(type=NAT),
    )(W_BVar(2).app(W_BVar(1), W_BVar(0)))
    rec_decl = Pair_rec.recursor(
        type=rec_type,
        rules=[
            W_RecRule(ctor_name=Pair_mk, num_fields=2, rhs=mk_rule_val),
        ],
        num_motives=1,
        num_params=0,
        num_indices=0,
        num_minors=1,
        names=[Pair],  # `RecursorVal.all`: the inductives this rec is for.
        levels=[u_name],
    )

    Nat_decl = Name.simple("Nat").inductive(type=TYPE)
    stuck = Name.simple("stuck").axiom(type=Pair.const())
    env = Environment.having(
        [pair_decl, mk_decl, rec_decl, Nat_decl, stuck],
    )

    # Pair.rec.{1} (fun _ => Nat) (fun fst snd => fst) stuck
    one = u.succ()
    motive_lam = fun(Name.simple("_t").binder(type=Pair.const()))(NAT)
    fst_minor = fun(
        fst_name.binder(type=NAT),
        snd_name.binder(type=NAT),
    )(W_BVar(1))  # returns fst
    rec_app = (
        Pair_rec.const(levels=[one])
        .app(motive_lam)
        .app(fst_minor)
        .app(stuck.const())
    )

    # After struct-eta + beta: stuck.fst (Pair's first projection).
    expected = Pair.proj(0, stuck.const())
    assert syntactic_eq(rec_app.whnf(env), expected)


class TestTracer(object):
    """The tracer is invoked with each intermediate expression during WHNF."""

    def test_default_tracer_does_not_disturb_reduction(self):
        """WHNF returns the same result whether or not a tracer is observing."""
        a_decl = a.axiom(type=NAT)
        env = Environment.having([a_decl])
        assert syntactic_eq(a_decl.const().whnf(env), a_decl.const())

    def test_already_whnf_records_only_input(self):
        """An expression already in WHNF yields a single trace entry."""
        a_decl = a.axiom(type=NAT)
        tracer = _CollectingTracer()
        env = Environment.having([a_decl])
        env.tracer = tracer

        const = a_decl.const()
        const.whnf(env)

        assert len(tracer.steps) == 1
        assert tracer.steps[0] is const

    def test_beta_reduction_records_each_step(self):
        """(fun x ↦ x) a reduces in one step: traces input then result."""
        a_decl = a.axiom(type=NAT)
        tracer = _CollectingTracer()
        env = Environment.having([a_decl])
        env.tracer = tracer

        identity = fun(x.binder(type=NAT))(b0)
        app = identity.app(a_decl.const())
        app.whnf(env)

        assert len(tracer.steps) == 2
        assert tracer.steps[0] is app
        assert syntactic_eq(tracer.steps[1], a_decl.const())

    def test_delta_then_beta_records_full_chain(self):
        """f a where f := fun x ↦ x traces f a, (fun x ↦ x) a, then a."""
        a_decl = a.axiom(type=NAT)
        f_decl = f.definition(
            type=forall(x.binder(type=NAT))(NAT),
            value=fun(x.binder(type=NAT))(b0),
        )
        tracer = _CollectingTracer()
        env = Environment.having([f_decl, a_decl])
        env.tracer = tracer

        app = f_decl.const().app(a_decl.const())
        app.whnf(env)

        assert len(tracer.steps) == 3
        assert tracer.steps[0] is app
        assert syntactic_eq(
            tracer.steps[1],
            fun(x.binder(type=NAT))(b0).app(a_decl.const()),
        )
        assert syntactic_eq(tracer.steps[2], a_decl.const())

    def test_definition_unfold_records_each_step(self):
        """a := b traces a then b."""
        b_decl = b.axiom(type=NAT)
        a_decl = a.definition(type=NAT, value=b_decl.const())
        tracer = _CollectingTracer()
        env = Environment.having([a_decl, b_decl])
        env.tracer = tracer

        a_decl.const().whnf(env)

        assert len(tracer.steps) == 2
        assert syntactic_eq(tracer.steps[0], a_decl.const())
        assert syntactic_eq(tracer.steps[1], b_decl.const())

    def test_proj_nested_whnf_records_inner_steps(self):
        """
        Projection reduction whnfs its struct expression in a nested call,
        and the tracer sees the inner steps as well as the outer ones.
        """
        Foo = Name.simple("Foo")
        Foo_mk = Foo.child("mk")
        mk_decl = Foo_mk.constructor(
            type=forall(
                a.binder(type=TYPE).to_implicit(),
                x.binder(type=b0),
            )(Foo.const().app(b1)),
            num_params=1,
            num_fields=1,
        )
        foo_type = Foo.inductive(
            type=forall(a.binder(type=TYPE))(TYPE),
            constructors=[mk_decl],
            num_params=1,
        )

        myVal_decl = Name.simple("myVal").axiom(type=NAT)
        # def origin := Foo.mk Nat myVal — forces a nested whnf when projected.
        origin_decl = Name.simple("origin").definition(
            type=Foo.const().app(NAT),
            value=Foo_mk.const().app(NAT, myVal_decl.const()),
        )
        env = Environment.having([foo_type, mk_decl, myVal_decl, origin_decl])

        tracer = _CollectingTracer()
        env.tracer = tracer

        proj = Foo.proj(field_index=0, struct_expr=origin_decl.const())
        proj.whnf(env)

        # 1: outer proj input
        # 2: nested whnf on `origin` (input)
        # 3: nested whnf — `origin` deltas to `Foo.mk Nat myVal`
        # 4: outer proj iota extracts field, lands on `myVal`
        assert len(tracer.steps) == 4
        assert tracer.steps[0] is proj
        assert syntactic_eq(tracer.steps[1], origin_decl.const())
        assert syntactic_eq(
            tracer.steps[2],
            Foo_mk.const().app(NAT, myVal_decl.const()),
        )
        assert syntactic_eq(tracer.steps[3], myVal_decl.const())

    def test_stream_tracer_renders_each_step(self):
        """StreamTracer writes one indented `whnf <expr>` line per step."""
        from io import BytesIO
        from textwrap import dedent

        from rpylean._tokens import FORMAT_PLAIN, TokenWriter
        from rpylean.environment import StreamTracer

        b_decl = b.axiom(type=NAT)
        a_decl = a.definition(type=NAT, value=b_decl.const())
        env = Environment.having([a_decl, b_decl])

        out = BytesIO()
        env.tracer = StreamTracer(TokenWriter(out, FORMAT_PLAIN))
        a_decl.const().whnf(env)

        assert out.getvalue().decode("utf-8") == dedent(
            u"""\
            whnf a
            whnf b
            """,
        )
