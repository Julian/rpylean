class NotDefEq(Exception):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "NotDefEq(%s, %s)" % (self.lhs, self.rhs)
    
    def __str__(self):
        return "NotDefEq: %s != %s" % (self.lhs, self.rhs)

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
            raise RuntimeError("W_LevelIMax with W_LevelParam not yet implemented")
        
        if isinstance(other, W_LevelIMax) and isinstance(other.rhs, W_LevelParam):
            return self.lhs.leq(other.lhs, infcx) or self.rhs.leq(other.rhs, infcx)
        
        raise RuntimeError("Unimplemented level comparison: %s <= %s" % (self, other))
    
    def antisymm_eq(self, other, infcx):
        return self.leq(other, infcx) and other.leq(self, infcx)


class W_LevelZero(W_Level):
    def pretty(self):
        return "<W_LevelZero>"


class W_LevelSucc(W_Level):
    def __init__(self, parent):
        self.parent = parent

    def pretty(self):
        return "(Succ %s)" % self.parent.pretty()

class W_LevelMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

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


class W_Expr(W_Item):
    pass

    def whnf(self):
        return self

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

    
    def def_eq(self, other, infcx):
        assert isinstance(other, W_BVar)
        if self.id != other.id:
            raise NotDefEq(self, other)
        return True
    
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

    def def_eq(self, other, infcx):
        assert isinstance(other, W_FVar)
        if self.id != other.id:
            raise NotDefEq(self, other)
        return True
    
    def __repr__(self):
        return "(FVar %s %s)" % (self.id, self.binder)
    
    def pretty(self):
        return "{%s}" % self.binder.binder_name.pretty()


class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level

    def pretty(self):
        return "Sort %s" % self.level.pretty()
    
    def infer(self, infcx):
        return W_Sort(W_LevelSucc(self.level))
    
    def def_eq(self, other, infcx):
        assert isinstance(other, W_Sort)
        if not self.level.antisymm_eq(other.level, infcx):
            raise NotDefEq(self, other)
        return True
    
    def subst_levels(self, substs):
        if self.level in substs:
            return W_Sort(substs[self.level])
        return self


class W_Const(W_Expr):
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels

    def pretty(self):
        return "`" + self.name.pretty() + "[%s]" % (", ".join([level.pretty() for level in self.levels]))
    
    def infer(self, infcx):
        decl = infcx.env.declarations[self.name]
        params = decl.level_params
        if len(params) != len(self.levels):
            raise RuntimeError("W_Const.infer: expected %s levels, got %s" % (len(params), len(self.levels)))
        
        if len(params) == 0:
            return decl.get_type()

        substs = {}
        for i in range(len(params)):
            substs[W_LevelParam(params[i])] = self.levels[i]
        return decl.get_type().subst_levels(substs)
    
    def def_eq(self, other, infcx):
        assert isinstance(other, W_Const)
        if self.name != other.name:
            raise NotDefEq(self, other)
        if len(self.levels) != len(other.levels):
            raise NotDefEq(self, other)
        for i in range(len(self.levels)):
            if not self.levels[i].antisymm_eq(other.levels[i], infcx):
                raise NotDefEq(self, other)
        return True
    
    def subst_levels(self, substs):
        new_levels = []
        for level in self.levels:
            new_level = substs.get(level, level)
            new_levels.append(new_level)
        return W_Const(self.name, new_levels)

# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body
        if self.body is None:
            raise RuntimeError("W_FunBase: body cannot be None: %s" % self)

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

    def def_eq(self, other, infcx):
        assert isinstance(other, W_ForAll), "expected W_ForAll for %s" % other
        if not self.binder_type.def_eq(other.binder_type, infcx):
            raise NotDefEq(self, other)
        
        fvar = W_FVar(self)
        body = self.body.instantiate(fvar, 0)
        other_body = other.body.instantiate(fvar, 0)
        return body.def_eq(other_body, infcx)
    
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
    
    def def_eq(self, other, infcx):
        assert isinstance(other, W_Lambda)
        if not self.binder_type.def_eq(other.binder_type, infcx):
            raise NotDefEq(self, other)
        
        fvar = W_FVar(self)
        body = self.body.instantiate(fvar, 0)
        other_body = other.body.instantiate(fvar, 0)
        return body.def_eq(other_body, infcx)


#(fun (x : N) => Vector.repeat(1, n))
#'(n: Nat) -> Vector n'

class W_App(W_Expr):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg

    def infer(self, infcx):
        fn_type_base = self.fn.infer(infcx)
        fn_type = fn_type_base.whnf()
        if not isinstance(fn_type, W_ForAll):
            raise RuntimeError("W_App.infer: expected function type, got %s" % fn_type)
        arg_type = self.arg.infer(infcx)
        if not infcx.def_eq(fn_type.binder_type, arg_type):
            raise RuntimeError("W_App.infer: type mismatch: %s != %s" % (fn_type.binder_type, arg_type))
        body_type = fn_type.body.instantiate(self.arg, 0)
        return body_type
    
    def whnf(self):
        arg = self.arg.whnf()
        if isinstance(self.fn, W_FunBase):
            res = self.fn.instantiate(arg, 0)
            return res
        else:
            return W_App(self.fn, arg)

    def bind_fvar(self, fvar, depth):
        return W_App(self.fn.bind_fvar(fvar, depth), self.arg.bind_fvar(fvar, depth))
    
    def instantiate(self, expr, depth):
        return W_App(self.fn.instantiate(expr, depth), self.arg.instantiate(expr, depth))
    
    def incr_free_bvars(self, count, depth):
        return W_App(self.fn.incr_free_bvars(count, depth), self.arg.incr_free_bvars(count, depth))

    def pretty(self):
        return "(%s %s)" % (self.fn.pretty(), self.arg.pretty())
    
    def def_eq(self, other, infcx):
        assert isinstance(other, W_App)
        fn_eq = self.fn.def_eq(other.fn, infcx)
        arg_eq = self.arg.def_eq(other.arg, infcx)
        return fn_eq and arg_eq
    
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


class W_DeclarationKind(object):
    pass


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

    def pretty(self):
        return "<W_Definition def_type='%s' def_val='%s' hint='%s'>" % (
            self.def_type.pretty(),
            self.def_val.pretty(),
            self.hint,
        )


class W_Theorem(DefOrTheorem):
    def pretty(self):
        return "<W_Theorem def_type=%s def_val=%s>" % (
            self.def_type.pretty(),
            self.def_val.pretty(),
        )

    def get_type(self):
        return self.def_type


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
            self.ctype,
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
