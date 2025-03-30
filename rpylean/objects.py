from rpython.rlib.rbigint import rbigint

class NotDefEq(Exception):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "NotDefEq(%s, %s)" % (self.lhs, self.rhs)

    def __str__(self):
        return "NotDefEq:\nlhs=%s\nrhs=%s" % (self.lhs.pretty(), self.rhs.pretty())

class W_Item(object):
    def __repr__(self):
        fields = self.__dict__.iteritems()
        contents = ", ".join("%s=%r" % (k, v) for k, v in fields)
        return "<%s%s%s>" % (
            self.__class__.__name__,
            " " if contents else "",
            contents,
        )

    def pretty(self):
        return "<%s repr error>" % (self.__class__.__name__,)

# Based on https://github.com/gebner/trepplein/blob/c704ffe81941779dacf9efa20a75bf22832f98a9/src/main/scala/trepplein/level.scala#L100
class W_Level(W_Item):
    def simplify(self):
        if isinstance(self, W_LevelZero) or isinstance(self, W_LevelParam):
            return self
        if isinstance(self, W_LevelSucc):
            return W_LevelSucc(self.parent.simplify())
        if isinstance(self, W_LevelMax):
            return W_LevelMax.combining(self.lhs.simplify(), self.rhs.simplify())
        if isinstance(self, W_LevelIMax):
            b_simp = self.rhs.simplify()
            if isinstance(b_simp, W_LevelSucc):
                return W_LevelMax.combining(self.lhs, b_simp)
            if isinstance(b_simp, W_LevelZero):
                return W_LevelZero()
            return W_LevelIMax(self.lhs.simplify(), b_simp)
        raise RuntimeError("Unexpected level type: %s" % self)


    # See https://ammkrn.github.io/type_checking_in_lean4/levels.html?highlight=leq#partial-order-on-levels
    def leq(self, other, infcx, balance=0):
        if isinstance(self, W_LevelZero) and balance >= 0:
            return True
        if isinstance(other, W_LevelZero) and balance < 0:
            return False
        if isinstance(self, W_LevelParam) and isinstance(other, W_LevelParam):
            return self.name == other.name and balance == 0
        if isinstance(self, W_LevelParam) and isinstance(other, W_LevelZero):
            return False
        if isinstance(self, W_LevelZero) and isinstance(other, W_LevelParam):
            return balance >= 0
        if isinstance(self, W_LevelSucc):
            return self.parent.leq(other, infcx, balance - 1)
        if isinstance(other, W_LevelSucc):
            return self.leq(other.parent, infcx, balance + 1)

        if isinstance(self, W_LevelMax):
            return self.lhs.leq(other, infcx, balance) or self.rhs.leq(other, infcx, balance)

        if (isinstance(self, W_LevelParam) or isinstance(self, W_LevelZero)) and isinstance(other, W_LevelMax):
            return self.leq(other.lhs, infcx, balance) or self.leq(other.rhs, infcx, balance)

        # TODO - what equality is this?
        if isinstance(self, W_LevelIMax) and isinstance(other, W_LevelIMax) and self.lhs.antisymm_eq(other.lhs, infcx) and self.rhs.antisymm_eq(other.rhs, infcx):
            return True

        if isinstance(self, W_LevelIMax) and isinstance(self.rhs, W_LevelParam):
            warn("W_LevelIMax with W_LevelParam not yet implemented")
            return True

        if isinstance(other, W_LevelIMax) and isinstance(other.rhs, W_LevelParam):
            warn("W_LevelIMax with W_LevelParam not yet implemented")
            return True

        warn("Unimplemented level comparison: %s <= %s" % (self, other))
        return True

    def antisymm_eq(self, other, infcx):
        lhs = self.simplify()
        rhs = other.simplify()
        return lhs.leq(rhs, infcx) and rhs.leq(lhs, infcx)


class W_LevelZero(W_Level):
    def pretty(self):
        return "<W_LevelZero>"

    def subst_levels(self, substs):
        return self


class W_LevelSucc(W_Level):
    def __init__(self, parent):
        self.parent = parent

    def pretty(self):
        return "(Succ %s)" % self.parent.pretty()

    def subst_levels(self, substs):
        new_parent = self.parent.subst_levels(substs)
        return W_LevelSucc(new_parent)

class W_LevelMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def pretty(self):
        return "(Max %s %s)" % (self.lhs.pretty(), self.rhs.pretty())

    def subst_levels(self, substs):
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
        return W_LevelMax(new_lhs, new_rhs)

    @staticmethod
    def combining(lhs, rhs):
        if isinstance(lhs, W_LevelSucc) and isinstance(rhs, W_LevelSucc):
            return W_LevelSucc(W_LevelMax.combining(lhs.parent, rhs.parent))
        if isinstance(lhs, W_LevelZero):
            return rhs
        if isinstance(rhs, W_LevelZero):
            return lhs
        return W_LevelMax(lhs, rhs)

class W_LevelIMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

W_LEVEL_ZERO = W_LevelZero()


class W_LevelParam(W_Level):
    def __init__(self, name):
        self.name = name

    def pretty(self):
        return self.name.pretty()

    def subst_levels(self, substs):
        return substs.get(self.name, self)


class W_Expr(W_Item):

    def whnf(self, env):
        return self
    
    # Tries to perform a single step of strong reduction.
    # Currently implemented reduction steps:
    # * Delta reduction (definition unfolding)
    # * Beta reduction (function application)
    # * Iota reduction: simplification of ('InductiveType.recursor arg0 .. argN InductiveType.ctorName') using matching RecursorRule
    # 
    # Return (progress, new_expr), where `progress` indicates whether any reduction was performed
    def strong_reduce_step(self, infcx):
        return (False, self)


    # Replace all BVars with the id 'depth' with 'expr'
    def instantiate(self, expr, depth):
        return self

    def bind_fvar(self, fvar, depth):
        return self

    # Increments all free BVars in this expression by 'count'.
    # For example, 'fun x => BVar(1)' will become 'fun x => BVar(1 + count)',
    # while 'fun x => BVar(0)' wil be unchanged.
    # This is used when we add 'count' new binders above this expresssion
    def incr_free_bvars(self, count, depth):
        return self


class W_BVar(W_Expr):
    def __init__(self, id):
        self.id = int(id)

    def pretty(self):
        return "(BVar [%s])" % (self.id,)

    def instantiate(self, expr, depth):
        if self.id == depth:
            incr = expr.incr_free_bvars(depth, 0)
            return incr
        elif self.id > depth:
            # This variable is not bound here (e.g. 'fun x => BVar(1)')
            # Instantiation has removed the outermost binder, so we need to decrement this
            # TODO - should we take in a context instead of relying on 'bvar.id'?
            return W_BVar(self.id - depth)
        return self

    def incr_free_bvars(self, count, depth):
        if self.id >= depth:
            return W_BVar(self.id + count)
        return self

    def subst_levels(self, substs):
        return self

# RPython prevents mutating global variable bindings, so we need a class instance
class FVarCounter(object):
    def __init__(self):
        self.count = 0

FVAR_COUNTER = FVarCounter()

class W_FVar(W_Expr):
    def __init__(self, binder):
        global FVAR_COUNTER
        self.id = FVAR_COUNTER.count
        self.binder = binder
        FVAR_COUNTER.count += 1

    def infer(self, infcx):
        return self.binder.binder_type

    def bind_fvar(self, fvar, depth):
        if self.id == fvar.id:
            return W_BVar(depth)
        return self
    
    def __repr__(self):
        return "(FVar %s %s)" % (self.id, self.binder)

    def pretty(self):
        return "{%s}" % self.binder.binder_name.pretty()

class W_LitStr(W_Expr):
    def __init__(self, val):
        self.val = val

class W_LitNat(W_Expr):
    def __init__(self, val):
        self.val = val

class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level

    def pretty(self):
        return "Sort %s" % self.level.pretty()

    def infer(self, infcx):
        return W_Sort(W_LevelSucc(self.level))

    def subst_levels(self, substs):
        return W_Sort(self.level.subst_levels(substs))

# Takes the level params from 'const', and substitutes them into 'target'
def apply_const_level_params(const, target, env):
    decl = env.declarations.get(const.name)
    if len(decl.level_params) != len(const.levels):
        raise RuntimeError("W_Const.infer: expected %s levels, got %s" % (len(decl.level_params), len(const.levels)))
    params = decl.level_params
    substs = {}
    for i in range(len(params)):
        substs[params[i]] = const.levels[i]
    return target.subst_levels(substs)

class W_Const(W_Expr):
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels

    def pretty(self):
        return "`" + self.name.pretty() + "[%s]" % (", ".join([level.pretty() for level in self.levels]))

    def strong_reduce_step(self, infcx):
        reduced = self.try_delta_reduce(infcx.env)
        if reduced is not None:
            return (True, reduced)
        return (False, self)

    def try_delta_reduce(self, env, only_abbrev=False):
        decl = env.declarations.get(self.name)
        # TODO - use hint to decide whether to delta reduce or not
        val = decl.w_kind.get_delta_reduce_target()
        if not isinstance(decl.w_kind, W_Definition):
            return None
        
        if val is None:
            return None
        
        val = apply_const_level_params(self, val, env)
        return val

    def infer(self, infcx):
        decl = infcx.env.declarations[self.name]
        params = decl.level_params

        if len(params) == 0:
            return decl.get_type()

        res = apply_const_level_params(self, decl.get_type(), infcx.env)
        return res

    def subst_levels(self, substs):
        new_levels = []
        for level in self.levels:
            new_level = level.subst_levels(substs)
            new_levels.append(new_level)
        return W_Const(self.name, new_levels)

class W_Proj(W_Expr):
    def __init__(self, struct_type, field_idx, struct_expr):
        self.struct_type = struct_type
        self.field_idx = field_idx
        self.struct_expr = struct_expr

    def instantiate(self, expr, depth):
        return W_Proj(self.struct_type, self.field_idx, self.struct_expr.instantiate(expr, depth))

    def pretty(self):
        return "<W_Proj struct_type='%s' field_idx='%s' struct_expr='%s'>" % (
            self.struct_type.pretty(),
            self.field_idx,
            self.struct_expr.pretty(),
        )

    def infer(self, infcx):
        struct_expr_type = self.struct_expr.infer(infcx).whnf(infcx.env)

        # Unfold applications of a base inductive type (e.g. `MyList TypeA TypeB`)
        apps = []
        while isinstance(struct_expr_type, W_App):
            apps.append(struct_expr_type)
            struct_expr_type = struct_expr_type.fn

        # The base type should be a constant, referring to 'struct_type' (e.g. `MyList`)
        assert isinstance(struct_expr_type, W_Const), "Expected W_Const, got %s" % struct_expr_type
        target_const = infcx.env.declarations[struct_expr_type.name]
        assert target_const == self.struct_type, "Expected %s, got %s" % (target_const, struct_expr_type)

        assert isinstance(self.struct_type, W_Declaration)
        assert isinstance(self.struct_type.w_kind, W_Inductive)
        assert len(self.struct_type.w_kind.ctor_names) == 1

        ctor_decl = infcx.env.declarations[self.struct_type.w_kind.ctor_names[0]]
        assert isinstance(ctor_decl, W_Declaration)
        assert isinstance(ctor_decl.w_kind, W_Constructor)
        # Fields can depend on earlier fields, so the constructor takes in 'proj'
        # expressions for all of the previous fields ('self.field_idx' is 0-based)
        assert ctor_decl.w_kind.num_params == len(apps) + (self.field_idx)

        ctor_type = ctor_decl.w_kind.ctype

        # The last app pushed to 'apps' is the innermost application (applied directly to the `MyList const`),
        # so start iteration from the end
        # TODO: handle levels
        apps.reverse()
        for app in apps:
            ctor_type = ctor_type.whnf(infcx.env)
            assert isinstance(ctor_type, W_ForAll)
            new_type = ctor_type.body.instantiate(app.arg, 0)
            ctor_type = new_type

        # Substitute in 'proj' expressions for all of the previous fields
        for i in range(self.field_idx):
            ctor_type = ctor_type.whnf(infcx.env)
            assert isinstance(ctor_type, W_ForAll)
            ctor_type = ctor_type.body.instantiate(W_Proj(self.struct_type, i, self.struct_expr), 0)

        ctor_type = ctor_type.whnf(infcx.env)
        assert isinstance(ctor_type, W_ForAll)
        return ctor_type.binder_type



# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body
        if self.body is None:
            raise RuntimeError("W_FunBase: body cannot be None: %s" % self)
        if isinstance(self.binder_type, tuple):
            import pdb; pdb.set_trace()


    def strong_reduction_helper(self, infcx):
        progress, binder_type = self.binder_type.strong_reduce_step(infcx)
        if progress:
            return (True, (self.binder_name, binder_type, self.binder_info, self.body))
        
        fvar = W_FVar(self)
        open_body = self.body.instantiate(fvar, 0)
        progress, open_body = open_body.strong_reduce_step(infcx)
        new_body = open_body.bind_fvar(fvar, 0)
        if progress:
            return (True, (self.binder_name, binder_type, self.binder_info, new_body))
        return (False, (self.binder_name, self.binder_type, self.binder_info, self.body))
    
class W_ForAll(W_FunBase):
    def pretty(self):
        body_pretty = self.body.instantiate(W_FVar(self), 0).pretty()
        return "(∀ (%s : %s), %s)" % (
            self.binder_name.pretty(),
            self.binder_type.pretty(),
            body_pretty
        )

    def infer(self, infcx):
        binder_sort = infcx.infer_sort_of(self.binder_type)
        body_sort = infcx.infer_sort_of(self.body.instantiate(W_FVar(self), 0))
        return W_Sort(W_LevelIMax(binder_sort, body_sort))

    # TODO - double check this
    def instantiate(self, expr, depth):
        # Don't increment - not yet inside a binder
        new_binder = self.binder_type.instantiate(expr, depth)
        new_body = self.body.instantiate(expr, depth + 1)
        return W_ForAll(self.binder_name, new_binder, self.binder_info, new_body)

    def bind_fvar(self, fvar, depth):
        new_binder = self.binder_type.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        return W_ForAll(self.binder_name, new_binder, self.binder_info, new_body)

    def incr_free_bvars(self, count, depth):
        binder_type = self.binder_type.incr_free_bvars(count, depth)
        body = self.body.incr_free_bvars(count, depth + 1)
        return W_ForAll(
            self.binder_name,
            binder_type,
            self.binder_info,
            body
        )

    def strong_reduce_step(self, infcx):
        progress, args = self.strong_reduction_helper(infcx)
        return (progress, W_ForAll(*args))

    def subst_levels(self, levels):
        return W_ForAll(
            self.binder_name,
            self.binder_type.subst_levels(levels),
            self.binder_info,
            self.body.subst_levels(levels)
        )



class W_Lambda(W_FunBase):
    def pretty(self):
        body_pretty = self.body.instantiate(W_FVar(self), 0).pretty()
        return "(λ %s : %s => \b%s)" % (
            self.binder_name.pretty(),
            self.binder_type.pretty(),
            body_pretty
        )

    def bind_fvar(self, fvar, depth):
        new_binder = self.binder_type.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        return W_Lambda(self.binder_name, new_binder, self.binder_info, new_body)

    def instantiate(self, expr, depth):
        # Don't increment - not yet inside a binder
        new_binder = self.binder_type.instantiate(expr, depth)
        new_body = self.body.instantiate(expr, depth + 1)
        return W_Lambda(self.binder_name, new_binder, self.binder_info, new_body)

    def incr_free_bvars(self, count, depth):
        binder_type = self.binder_type.incr_free_bvars(count, depth)
        body = self.body.incr_free_bvars(count, depth + 1)
        return W_Lambda(
            self.binder_name,
            binder_type,
            self.binder_info,
            body,
        )

    def infer(self, infcx):
        # Run this for the side effect - throwing an exception if not a Sort
        infcx.infer_sort_of(self.binder_type)
        fvar = W_FVar(self)
        body_type_fvar = self.body.instantiate(fvar, 0).infer(infcx)
        body_type = body_type_fvar.bind_fvar(fvar, 0)
        if body_type is None:
            raise RuntimeError("W_Lambda.infer: body_type is None: %s" % self.pretty())
        res = W_ForAll(self.binder_name, self.binder_type, self.binder_info, body_type)
        return res
    
    def strong_reduce_step(self, infcx):
        progress, args = self.strong_reduction_helper(infcx)
        return (progress, W_Lambda(*args))

    def subst_levels(self, substs):
        return W_Lambda(
            self.binder_name,
            self.binder_type.subst_levels(substs),
            self.binder_info,
            self.body.subst_levels(substs)
        )


#(fun (x : N) => Vector.repeat(1, n))
#'(n: Nat) -> Vector n'

class W_Let(W_Expr):
    def __init__(self, name, def_type, def_val, body):
        self.name = name
        self.def_type = def_type
        self.def_val = def_val
        self.body = body

class W_App(W_Expr):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg

    def infer(self, infcx):
        fn_type_base = self.fn.infer(infcx)
        fn_type = fn_type_base.whnf(infcx.env)
        if not isinstance(fn_type, W_ForAll):
            raise RuntimeError("W_App.infer: expected function type, got %s" % fn_type)
        arg_type = self.arg.infer(infcx)
        if not infcx.def_eq(fn_type.binder_type, arg_type):
            raise RuntimeError("W_App.infer: type mismatch: %s != %s" % (fn_type.binder_type, arg_type))
        body_type = fn_type.body.instantiate(self.arg, 0)
        return body_type
    
    def try_iota_reduce(self, infcx):
        args = []
        target = self
        while isinstance(target, W_App):
            args.append(target.arg)
            target = target.fn

        if not isinstance(target, W_Const):
            return False, self
        
        decl = infcx.env.declarations.get(target.name)
        if not isinstance(decl.w_kind, W_Recursor):
            return False, self
        
        if decl.w_kind.num_motives != 1:
            warn("W_App.try_iota_reduce: unimplemented case num_motives != 1 for %s" % target.name)
            return False, self
        
        skip_count = decl.w_kind.num_params + decl.w_kind.num_indices + decl.w_kind.num_minors + decl.w_kind.num_motives
        major_idx = len(args) - 1 - skip_count

        for rec_rule_id in decl.w_kind.rule_idxs:
            rec_rule = infcx.env.rec_rules[rec_rule_id]

        # Not enough arguments in our current app - we cannot reduce, since we need to know the major premise
        # to pick the recursor rule to apply
        if major_idx < 0:
            return False, self
        major_premise = args[major_idx]
        
        # If the inductive type has parameters, we need to extract them from the major premise
        # (e.g. the 'p' in 'Decidable.isFalse p')
        # and add then as arguments to the recursor rule application (before the motive)
        major_premise_ctor = major_premise
        all_ctor_args = []
        while isinstance(major_premise_ctor, W_App):
            all_ctor_args.append(major_premise_ctor.arg)
            major_premise_ctor = major_premise_ctor.fn

        all_ctor_args.reverse()
        num_params = decl.w_kind.num_params
        assert num_params >= 0, "Found negative num_params on decl %s" % decl.pretty()
        # Get the fields, which come after the type-level parametesr
        # e.g. '(h : ¬p)' in 'Decidable.isFalse'
        ctor_fields = all_ctor_args[num_params:]

        if not isinstance(major_premise_ctor, W_Const):
            return False, self

        new_args = list(args)
        new_args.reverse()
        new_args.pop()

        # TODO - consider storing these by recursor name
        for rec_rule_id in decl.w_kind.rule_idxs:
            rec_rule = infcx.env.rec_rules[rec_rule_id]
            if rec_rule.ctor_name == major_premise_ctor.name:
                # Construct an application of the recursor rule, using all of the parameters except the major premise
                # (which is implied by the fact that we're using the corresponding recursor rule for the ctor, e.g. `Bool.false`)
                new_app = rec_rule.val
                # The rec rule value uses the level parameters from the corresponding inductive type declaration,
                # so apply the parameters from our recursor call
                new_app = apply_const_level_params(target, new_app, infcx.env)

                for arg in new_args:
                    new_app = W_App(new_app, arg)

                for ctor_field in ctor_fields:
                    new_app = W_App(new_app, ctor_field)

                # Type check the new application, to ensure that all of our args have the right types
                new_app_ty = new_app.infer(infcx)
                new_app = new_app.whnf(infcx.env)
                return True, new_app


        return False, self
        

    def whnf(self, env):
        fn = self.fn.whnf(env)
        arg = self.arg.whnf(env)

        # TODO - should we only delta reduce abbrevs here?
        if isinstance(fn, W_Const):
            reduced = fn.try_delta_reduce(env, only_abbrev=True)
            if reduced is not None:
                fn = reduced

        if isinstance(fn, W_FunBase):
            res = fn.body.instantiate(arg, 0)
            return res.whnf(env)

        else:
            return self
        
    def strong_reduce_step(self, infcx):
        # First, try beta reduction
        if isinstance(self.fn, W_FunBase):
            body = self.fn.body.instantiate(self.arg, 0)
            return (True, body)
        
        # Next, try strong reduction with the fn and body
        # After this, it might become possible to do beta
        # reduction (if the fn gets reduced to a W_FunBase)
        # We don't check for this case here - it will get checked when
        # `strong_reduce_step` is called on the new `W_App`, if the top-level
        # code decides to perform another strong reduction step.
        progress, new_fn = self.fn.strong_reduce_step(infcx)
        if progress:
            return (True, W_App(new_fn, self.arg))
        
        progress, new_arg = self.arg.strong_reduce_step(infcx)
        if progress:
            return (True, W_App(new_fn, new_arg))
        
        # Finally, try iota reduction after we've reduced everthing else as much as possible
        # This allows us to find a recursor constant and constructor constant
        # (both can be produced by earlier reduction steps, but neither can be further reduced
        # without iota reduction)
        return self.try_iota_reduce(infcx)
        
    def bind_fvar(self, fvar, depth):
        return W_App(self.fn.bind_fvar(fvar, depth), self.arg.bind_fvar(fvar, depth))

    def instantiate(self, expr, depth):
        return W_App(self.fn.instantiate(expr, depth), self.arg.instantiate(expr, depth))

    def incr_free_bvars(self, count, depth):
        return W_App(self.fn.incr_free_bvars(count, depth), self.arg.incr_free_bvars(count, depth))

    def pretty(self):
        return "(%s %s)" % (self.fn.pretty(), self.arg.pretty())


    def subst_levels(self, substs):
        return W_App(
            self.fn.subst_levels(substs),
            self.arg.subst_levels(substs)
        )


class W_RecRule(W_Item):
    def __init__(self, ctor_name, n_fields, val):
        self.ctor_name = ctor_name
        self.n_fields = n_fields
        self.val = val

    def pretty(self):
        return "<RecRule ctor_name='%s' n_fields='%s' val='%s'>" % (
            self.ctor_name.pretty(),
            self.n_fields,
            self.val.pretty(),
        )


class W_Declaration(W_Item):
    def __init__(self, name, level_params, w_kind):
        self.name = name
        self.level_params = level_params
        self.w_kind = w_kind

    def get_type(self):
        return self.w_kind.get_type()

    def pretty(self):
        return "<W_Declaration name='%s' level_params='%s' kind=%s>" % (
            self.name.pretty(),
            self.level_params,
            self.w_kind.pretty(),
        )


class W_DeclarationKind(W_Item):
    # Returns the value associated with this declaration kind.
    # This is the def value for a Definition, and `None` for things like Inductive
    def get_delta_reduce_target(self):
        return None


class DefOrTheorem(W_DeclarationKind):
    def __init__(self, def_type, def_val):
        self.def_type = def_type
        self.def_val = def_val

    def type_check(self, infcx):
        val_type = self.def_val.infer(infcx)
        if not infcx.def_eq(self.def_type, val_type):
            raise RuntimeError("W_Definition.type_check: type mismatch: %s != %s" % (self.def_type, val_type))


class W_Definition(DefOrTheorem):
    def __init__(self, def_type, def_val, hint):
        DefOrTheorem.__init__(self, def_type, def_val)
        self.hint = hint

    def get_type(self):
        return self.def_type

    def get_delta_reduce_target(self):
        return self.def_val

    def pretty(self):
        return "<W_Definition def_type='%s' def_val='%s' hint='%s'>" % (
            self.def_type.pretty(),
            self.def_val.pretty(),
            self.hint,
        )

class W_Opaque(W_Definition):
    def __init__(self, def_type, def_val):
        # An Opaque is like a definition with hint 'opaque', but even
        # stronger (we will never unfold it)
        W_Definition.__init__(self, def_type, def_val, hint="O")

    def pretty(self):
        return "<W_Opaque def_type='%s' def_val='%s'>" % (
            self.def_type.pretty(),
            self.def_val.pretty(),
        )

class W_Theorem(DefOrTheorem):
    def pretty(self):
        return "<W_Theorem def_type=%s def_val=%s>" % (
            self.def_type.pretty(),
            self.def_val.pretty(),
        )

    def get_type(self):
        return self.def_type

class W_Axiom(W_DeclarationKind):
    def __init__(self, def_type):
        self.def_type = def_type

    def type_check(self, infcx):
        # TODO - implement type checking
        pass

class W_Inductive(W_DeclarationKind):
    def __init__(self, expr, is_rec, is_nested, num_params, num_indices, ind_names, ctor_names):
        self.expr = expr
        self.is_rec = is_rec
        self.is_nested = is_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.ind_names = ind_names
        self.ctor_names = ctor_names

    def get_type(self):
        return self.expr

    def type_check(self, infcx):
        # TODO - implement type checking
        pass

    def pretty(self):
        return "<W_Inductive expr=%s is_rec=%s is_nested=%s num_params=%s num_indices=%s ind_names=%s ctor_names=%s>" % (
            self.expr.pretty(),
            self.is_rec,
            self.is_nested,
            self.num_params,
            self.num_indices,
            [each.pretty() for each in self.ind_names],
            [each.pretty() for each in self.ctor_names],
        )


class W_Constructor(W_DeclarationKind):
    def __init__(self, ctype, induct, cidx, num_params, num_fields):
        self.ctype = ctype
        self.induct = induct
        self.cidx = cidx
        self.num_params = num_params
        self.num_fields = num_fields

    def type_check(self, infcx):
        # TODO - implement type checking
        pass

    def get_type(self):
        if self.num_params != 0 or self.num_fields != 0:
            warn("W_Constructor.get_type not yet implemented for num_params=%s num_fields=%s" % (self.num_params, self.num_fields))
        return self.ctype

    def pretty(self):
        return "<W_Constructor ctype='%s' induct='%s' cidx='%s' num_params='%s' num_fields='%s'>" % (
            self.ctype.pretty(),
            self.induct,
            self.cidx,
            self.num_params,
            self.num_fields,
        )


class W_Recursor(W_DeclarationKind):
    def __init__(self,
        expr,
        k,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ind_names,
        rule_idxs,
    ):
        self.expr = expr
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.ind_names = ind_names
        self.rule_idxs = rule_idxs

    def type_check(self, infcx):
        # TODO - implement type checking
        pass

    def get_type(self):
        return self.expr

    def pretty(self):
        return "<W_Recursor expr='%s' k='%s' num_params='%s' num_indices='%s' num_motives='%s' num_minors='%s' ind_names='%s' rule_idxs='%s'>" % (
            self.expr.pretty(),
            self.k,
            self.num_params,
            self.num_indices,
            self.num_motives,
            self.num_minors,
            [each.pretty() for each in self.ind_names],
            self.rule_idxs,
        )


def warn(message):
    print("WARNING: %s" % (message,))
