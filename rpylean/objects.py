from rpython.rlib.rbigint import rbigint
from rpython.rlib.objectmodel import compute_hash


class W_TypeError(Exception):
    def __init__(self, w_term, w_expected_type):
        self.w_term = w_term
        self.w_expected_type = w_expected_type

    def __str__(self):
        return "%s is not of type %s" % (self.w_term.pretty(),
                                         self.w_expected_type.pretty())


class W_Item(object):
    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return vars(self) == vars(other)

    def __repr__(self):
        return self.pretty()

    def pretty(self):
        return "<%s repr error>" % (self.__class__.__name__,)


class Name(W_Item):
    def __init__(self, components):
        self.components = components

    def __hash__(self):
        hash_val = 0
        for c in self.components:
            hash_val = hash_val ^ compute_hash(c)
        return hash_val

    @staticmethod
    def simple(part):
        """
        A name with one part.
        """
        return Name([part])

    @staticmethod
    def from_str(s):
        """
        Construct a name by splitting a string on ``.``.
        """
        return Name(s.split("."))

    def eq(self, other):
        if len(self.components) != len(other.components):
            return False
        for i in range(len(self.components)):
            if self.components[i] != other.components[i]:
                return False
        return True

    def pretty(self):
        if not self.components:
            return "[anonymous]"
        return ".".join([pretty_part(each) for each in self.components])

    def child(self, part):
        """
        Construct a name nested inside this one.
        """
        return Name(self.components + [part])


Name.ANONYMOUS = Name([])


def pretty_part(part):
    """
    Pretty print a single component of a Name.
    """

    if isinstance(part, int):
        return str(part)
    if "." in part:
        return "«%s»" % (part,)
    return part


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
            return self.name.eq(other.name) and balance == 0
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
        if isinstance(self, W_LevelIMax) and isinstance(other, W_LevelIMax) and self.lhs.eq(other.lhs, infcx) and self.rhs.eq(other.rhs, infcx):
            return True

        if isinstance(self, W_LevelIMax) and isinstance(self.rhs, W_LevelParam):
            warn("W_LevelIMax with W_LevelParam not yet implemented")
            return True

        if isinstance(other, W_LevelIMax) and isinstance(other.rhs, W_LevelParam):
            warn("W_LevelIMax with W_LevelParam not yet implemented")
            return True

        warn("Unimplemented level comparison: %s <= %s" % (self, other))
        return True

    def eq(self, other, infcx):
        """
        Two levels are equal via antisymmetry.

        I.e. `a == b` if `a.leq(b)` and `b.leq(a)`.
        """
        lhs = self.simplify()
        rhs = other.simplify()
        return lhs.leq(rhs, infcx) and rhs.leq(lhs, infcx)


class W_LevelZero(W_Level):
    def pretty(self):
        return "<W_LevelZero>"

    def subst_levels(self, substs):
        return self

    def syntactic_eq(self, other):
        return isinstance(other, W_LevelZero)


W_LEVEL_ZERO = W_LevelZero()


class W_LevelSucc(W_Level):
    def __init__(self, parent):
        self.parent = parent

    def pretty(self):
        return "(Succ %s)" % self.parent.pretty()

    def subst_levels(self, substs):
        new_parent = self.parent.subst_levels(substs)
        return W_LevelSucc(new_parent)

    def syntactic_eq(self, other):
        return isinstance(other, W_LevelSucc) and self.parent.syntactic_eq(other.parent)


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

    def syntactic_eq(self, other):
        if not isinstance(other, W_LevelMax):
            return False
        return self.lhs.syntactic_eq(other.lhs) and self.rhs.syntactic_eq(other.rhs)

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

    def syntactic_eq(self, other):
        if not isinstance(other, W_LevelIMax):
            return False
        return self.lhs.syntactic_eq(other.lhs) and self.rhs.syntactic_eq(other.rhs)


class W_LevelParam(W_Level):
    def __init__(self, name):
        self.name = name

    def pretty(self):
        return self.name.pretty()

    def syntactic_eq(self, other):
        return isinstance(other, W_LevelParam) and self.name.eq(other.name)

    def subst_levels(self, substs):
        return substs.get(self.name, self)


class W_Expr(W_Item):
    # Tries to perform a single step of strong reduction.
    # Currently implemented reduction steps:
    # * Delta reduction (definition unfolding)
    # * Beta reduction (function application)
    # * Iota reduction: simplification of ('InductiveType.recursor arg0 .. argN InductiveType.ctorName') using matching RecursorRule
    #
    # Return (progress, new_expr), where `progress` indicates whether any reduction was performed
    def strong_reduce_step(self, infcx):
        return (False, self)


class W_BVar(W_Expr):
    def __init__(self, id):
        self.id = int(id)

    def pretty(self):
        return "(BVar [%s])" % (self.id,)

    def syntactic_eq(self, other):
        return isinstance(other, W_BVar) and self.id == other.id

    def bind_fvar(self, fvar, depth):
        return self

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

    def incr_free_bvars(self, count, depth):
        return self

    def instantiate(self, expr, depth):
        return self

    def whnf(self, infcx):
        return self

    def syntactic_eq(self, other):
        return isinstance(other, W_FVar) and self.id == other.id and self.binder.syntactic_eq(other.binder)

    def infer(self, infcx):
        return self.binder.binder_type

    def bind_fvar(self, fvar, depth):
        if self.id == fvar.id:
            return W_BVar(depth)
        return self

    def __repr__(self):
        return "(FVar %s %s)" % (self.id, self.binder)

    def pretty(self):
        return "{%s@%s}" % (self.binder.binder_name.pretty(), self.id)


class W_LitStr(W_Expr):
    def __init__(self, val):
        self.val = val

    def instantiate(self, expr, depth):
        return self

    def syntactic_eq(self, other):
        return isinstance(other, W_LitStr) and self.val == other.val


class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level

    def whnf(self, infcx):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth):
        return self

    def pretty(self):
        return "Sort %s" % self.level.pretty()

    def infer(self, infcx):
        return W_Sort(W_LevelSucc(self.level))

    def subst_levels(self, substs):
        return W_Sort(self.level.subst_levels(substs))

    def syntactic_eq(self, other):
        return isinstance(other, W_Sort) and self.level.syntactic_eq(other.level)


# Takes the level params from 'const', and substitutes them into 'target'
def apply_const_level_params(const, target, env):
    decl = env.declarations[const.name]
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

    def syntactic_eq(self, other):
        if not isinstance(other, W_Const):
            return False
        if self.name != other.name:
            return False

        assert len(self.levels) == len(other.levels), "W_Const syntactic_eq: levels length mismatch: %s vs %s" % (self.levels, other.levels)
        for i in range(len(self.levels)):
            if not self.levels[i].syntactic_eq(other.levels[i]):
                return False
        return True

    def strong_reduce_step(self, infcx):
        reduced = self.try_delta_reduce(infcx.env)
        if reduced is not None:
            return (True, reduced)
        return (False, self)

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def whnf(self, infcx):
        return self

    def try_delta_reduce(self, env, only_abbrev=False):
        decl = env.declarations[self.name]
        if decl is None:
            print("Missing decl: %s" % self.name.components)
            raise RuntimeError("Missing decl: %s" % self.pretty())
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


NAT = Name.simple("Nat")
NAT_CONST = W_Const(NAT, [])
NAT_ZERO = W_Const(NAT.child("zero"), [])
NAT_SUCC = W_Const(NAT.child("succ"), [])


class W_LitNat(W_Expr):
    def __init__(self, val):
        self.val = val

    def pretty(self):
        return "(LitNat %s)" % (self.val.str())

    def instantiate(self, expr, depth):
        return self

    def subst_levels(self, substs):
        return self

    def whnf(self, infcx):
        return self

    def syntactic_eq(self, other):
        return isinstance(other, W_LitNat) and self.val == other.val

    def build_nat_expr(self):
        if rbigint.fromint(100).lt(self.val):
            print("Building large nat expr for %s" % self.val)
        expr = NAT_ZERO
        i = rbigint.fromint(0)
        while i.lt(self.val):
            expr = W_App(NAT_SUCC, expr)
            i = i.add(rbigint.fromint(1))
        return expr

    def strong_reduce_step(self, infcx):
        return (False, self)
        if self.val == rbigint.fromint(0):
            return (True, NAT_ZERO)

        # Add a single 'Succ'
        sub = self.val.sub(rbigint.fromint(1))
        return (True, W_App(NAT_SUCC, W_LitNat(sub)))

    def bind_fvar(self, fvar, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def infer(self, infcx):
        return NAT_CONST


class W_Proj(W_Expr):
    def __init__(self, struct_type, field_idx, struct_expr):
        self.struct_type = struct_type
        self.field_idx = field_idx
        self.struct_expr = struct_expr

    def strong_reduce_step(self, infcx):
        progress, new_struct_expr = self.struct_expr.strong_reduce_step(infcx)
        if progress:
            return (True, W_Proj(self.struct_type, self.field_idx, new_struct_expr))


        # Look for a projection of a constructor, which allows us to just pick
        # out the argument corresponding to 'field_idx'

        args = []
        struct_expr = new_struct_expr
        while isinstance(struct_expr, W_App):
            # Collect arguments until we reach the base type
            args.append(struct_expr.arg)
            struct_expr = struct_expr.fn

        if not isinstance(struct_expr, W_Const):
            return (False, self)

        ctor_decl = infcx.env.declarations[struct_expr.name]
        if not isinstance(ctor_decl.w_kind, W_Constructor):
            return (False, self)

        num_params = ctor_decl.w_kind.num_params
        args.reverse()
        target_arg = args[num_params + self.field_idx]

        return (True, target_arg)

    def whnf(self, infcx):
        # TODO - do we need to try reducing the projection?
        return W_Proj(self.struct_type, self.field_idx, self.struct_expr.whnf(infcx))

    def incr_free_bvars(self, count, depth):
        return W_Proj(self.struct_type, self.field_idx, self.struct_expr.incr_free_bvars(count, depth))

    def bind_fvar(self, fvar, depth):
        return W_Proj(self.struct_type, self.field_idx, self.struct_expr.bind_fvar(fvar, depth))

    def instantiate(self, expr, depth):
        return W_Proj(self.struct_type, self.field_idx, self.struct_expr.instantiate(expr, depth))
    def pretty(self):
        return "<W_Proj struct_type='%s' field_idx='%s' struct_expr='%s'>" % (
            self.struct_type.pretty(),
            self.field_idx,
            self.struct_expr.pretty(),
        )

    def subst_levels(self, substs):
        return W_Proj(
            self.struct_type,
            self.field_idx,
            self.struct_expr.subst_levels(substs)
        )

    def syntactic_eq(self, other):
        # Our 'struct_type' is a 'W_Item' (which is only constructed once, during parsing),
        # so we can compare by object identity with '=='
        return isinstance(other, W_Proj) and self.struct_type == other.struct_type and self.field_idx == other.field_idx and self.struct_expr.syntactic_eq(other.struct_expr)

    def infer(self, infcx):
        struct_expr_type = self.struct_expr.infer(infcx).whnf(infcx)

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

        ctor_type = ctor_decl.w_kind.ctype
        ctor_type = apply_const_level_params(struct_expr_type, ctor_type, infcx.env)

        # The last app pushed to 'apps' is the innermost application (applied directly to the `MyList const`),
        # so start iteration from the end
        # TODO: handle levels
        apps.reverse()
        for app in apps:
            ctor_type = ctor_type.whnf(infcx)
            assert isinstance(ctor_type, W_ForAll)
            new_type = ctor_type.body.instantiate(app.arg, 0)
            ctor_type = new_type

        # Fields can depend on earlier fields, so the constructor takes in 'proj'
        # expressions for all of the previous fields ('self.field_idx' is 0-based)

        # Substitute in 'proj' expressions for all of the previous fields
        for i in range(self.field_idx):
            ctor_type = ctor_type.whnf(infcx)
            assert isinstance(ctor_type, W_ForAll)
            ctor_type = ctor_type.body.instantiate(W_Proj(self.struct_type, i, self.struct_expr), 0)

        ctor_type = ctor_type.whnf(infcx)
        assert isinstance(ctor_type, W_ForAll)
        return ctor_type.binder_type


# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    def __init__(self, binder_name, binder_type, binder_info, body):
        self.binder_name = binder_name
        self.binder_type = binder_type
        self.binder_info = binder_info
        self.body = body
        self.finished_reduce = False
        if self.body is None:
            raise RuntimeError("W_FunBase: body cannot be None: %s" % self)

        #if self.binder_type.pretty() == "`False[]" and isinstance(self.body, W_BVar) and self.body.id == 0:
        #    import pdb; pdb.set_trace()

    # Weak head normal form stops at forall/lambda
    def whnf(self, infcx):
        return self

    def syntactic_eq(self, other):
        # TODO - does syntactic equality really care about binder_info/name?
        if not isinstance(other, W_FunBase):
            return False
        if self.binder_name != other.binder_name:
            return False
        if not self.binder_type.syntactic_eq(other.binder_type):
            return False
        if self.binder_info != other.binder_info:
            return False
        # Compare the body expressions
        return self.body.syntactic_eq(other.body)

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

        self.finished_reduce = True
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
        if self.finished_reduce:
            return False, self
        progress, args = self.strong_reduction_helper(infcx)
        if not progress:
            return (False, self)
        return (progress, W_ForAll(*args))

    def subst_levels(self, levels):
        return W_ForAll(
            self.binder_name,
            self.binder_type.subst_levels(levels),
            self.binder_info,
            self.body.subst_levels(levels)
        )


class W_Lambda(W_FunBase):
    def __init__(self, binder_name, binder_type, binder_info, body):
        W_FunBase.__init__(self, binder_name, binder_type, binder_info, body)
        #if binder_name.components == ["a"] and isinstance(binder_type, W_Const) and binder_type.name.components == ["False"]:
        #    import pdb; pdb.set_trace()
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
        if self.finished_reduce:
            return False, self
        progress, args = self.strong_reduction_helper(infcx)
        if not progress:
            return (False, self)
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
        fn_type = fn_type_base.whnf(infcx)
        if not isinstance(fn_type, W_ForAll):
            raise RuntimeError("W_App.infer: expected function type, got %s" % type(fn_type))
        arg_type = self.arg.infer(infcx)
        if not infcx.def_eq(fn_type.binder_type, arg_type):
            raise RuntimeError("W_App.infer: type mismatch: %s != %s" % (fn_type.binder_type, arg_type))
        body_type = fn_type.body.instantiate(self.arg, 0)
        return body_type

    def syntactic_eq(self, other):
        if not isinstance(other, W_App):
            return False
        return self.fn.syntactic_eq(other.fn) and self.arg.syntactic_eq(other.arg)

    def try_iota_reduce(self, infcx):
        args = []
        target = self
        while isinstance(target, W_App):
            args.append(target.arg)
            target = target.fn


        if not isinstance(target, W_Const):
            return False, self

        decl = infcx.env.declarations[target.name]
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



        # TODO - when checking the declaration, verify that all of the requirements for k-like reduction
        # are met: https://ammkrn.github.io/type_checking_in_lean4/type_checking/reduction.html?highlight=k-li#k-like-reduction
        if decl.w_kind.k == 1:
            # Verify that our major premise type is correct (by checking the whole expression)
            # before we get rid of it
            self.infer(infcx)

            old_ty = major_premise.infer(infcx)
            old_ty_base = old_ty
            while isinstance(old_ty_base, W_App):
                old_ty_base = old_ty_base.fn
            assert isinstance(old_ty_base, W_Const)


            assert len(decl.w_kind.ind_names) == 1
            inductive_decl = infcx.env.declarations[decl.w_kind.ind_names[0]]
            assert isinstance(inductive_decl.w_kind, W_Inductive)

            assert len(inductive_decl.w_kind.ctor_names) == 1
            ctor_decl = infcx.env.declarations[inductive_decl.w_kind.ctor_names[0]]
            assert isinstance(ctor_decl.w_kind, W_Constructor)

            new_args = list(args)
            new_args.reverse()
            num_ctor_params = ctor_decl.w_kind.num_params

            major_premise_ctor = W_Const(inductive_decl.w_kind.ctor_names[0], old_ty_base.levels)
            assert num_ctor_params >= 0
            for arg in new_args[0:num_ctor_params]:
                major_premise_ctor = W_App(major_premise_ctor, arg)

            new_ty = major_premise_ctor.infer(infcx)
            if not infcx.def_eq(old_ty, new_ty):
                return False, self
            #print("Built new major premise: %s" % major_premise_ctor.pretty())
            major_premise = major_premise_ctor



            # import pdb; pdb.set_trace()
            # major_premise_ty = major_premise.infer(infcx)
            # print("K-like reduction with major_premise %s type: %s" % (major_premise.pretty(), major_premise_ty.pretty()))
            # k_like_args = []
            # while isinstance(major_premise_ty, W_App):
            #     k_like_args.append(major_premise_ty.arg)
            #     major_premise_ty = major_premise_ty.fn

            # k_like_args.reverse()
            # print("Unwrapped: %s" % major_premise_ty.pretty())
            # assert isinstance(major_premise_ty, W_Const)
            # base_decl = infcx.env.declarations[major_premise_ty.name]
            # assert isinstance(base_decl.w_kind, W_Inductive)
            # assert len(base_decl.w_kind.ctor_names) == 1
            # print("Ctor name: %s" % base_decl.w_kind.ctor_names[0])

            # ctor_decl = infcx.env.declarations[base_decl.w_kind.ctor_names[0]]

            # major_premise_ctor = W_Const(base_decl.w_kind.ctor_names[0], major_premise_ty.levels)
            # for arg in k_like_args[0:ctor_decl.w_kind.num_params]:
            #     major_premise_ctor = W_App(major_premise_ctor, arg)
            # print("Made new major premise ctor: %s" % major_premise_ctor.pretty())
            # major_premise = major_premise_ctor
            # #import pdb; pdb.set_trace()

        # We try to delay materializing LitNat expressions as late as possible,
        # so that we can rely on syntactic equality (e.g. 'W_LitNat(25) == W_LitNat(25)')
        # However, we need an actual constructor and application for iota reduction.
        # Hopefully we won't reach this spot with any especially large literals.
        if isinstance(major_premise, W_LitNat):
            major_premise = major_premise.build_nat_expr()

        # If the inductive type has parameters, we need to extract them from the major premise
        # (e.g. the 'p' in 'Decidable.isFalse p')
        # and add then as arguments to the recursor rule application (before the motive)
        major_premise_ctor = major_premise
        all_ctor_args = []
        while isinstance(major_premise_ctor, W_App):
            all_ctor_args.append(major_premise_ctor.arg)
            major_premise_ctor = major_premise_ctor.fn

        if not isinstance(major_premise_ctor, W_Const):
            return False, self

        all_ctor_args.reverse()
        # TODO - consider storing these by recursor name
        for rec_rule_id in decl.w_kind.rule_idxs:
            rec_rule = infcx.env.rec_rules[rec_rule_id]
            if rec_rule.ctor_name.eq(major_premise_ctor.name):
                #print("Have n_fields %s and num_params=%s" % (rec_rule.n_fields, decl.w_kind.num_params))uctor.get_type not yet implemented fo


                # num_params = decl.w_kind.num_params + decl.w_kind.num_motives + decl.w_kind.num_minors
                # import pdb; pdb.set_trace()
                # assert num_params >= 0, "Found negative num_params on decl %s" % decl.pretty()
                # # Get the fields, which come after the type-level parametesr
                # # e.g. '(h : ¬p)' in 'Decidable.isFalse'
                # if num_params >= len(all_ctor_args):
                #     ctor_fields = []
                # else:
                #     ctor_fields = all_ctor_args[num_params:]

                # if not isinstance(major_premise_ctor, W_Const):
                #     return False, self

                # new_args = list(args)
                # new_args.reverse()
                # # Remove the major premise
                # #new_args.pop()



                # Construct an application of the recursor rule, using all of the parameters except the major premise
                # (which is implied by the fact that we're using the corresponding recursor rule for the ctor, e.g. `Bool.false`)
                new_app = rec_rule.val
                # The rec rule value uses the level parameters from the corresponding inductive type declaration,
                # so apply the parameters from our recursor call
                new_app = apply_const_level_params(target, new_app, infcx.env)

                new_args = list(args)
                new_args.reverse()

                total_args = decl.w_kind.num_params + decl.w_kind.num_motives + decl.w_kind.num_minors
                assert total_args >= 0
                for arg in new_args[:total_args]:
                    new_app = W_App(new_app, arg)
                # We want to include all of the arguments up to the motive (which is the major premise)

                ctor_start = decl.w_kind.num_params
                ctor_end = decl.w_kind.num_params + rec_rule.n_fields
                assert ctor_start >= 0
                assert ctor_end >= 0

                for ctor_field in all_ctor_args[ctor_start:ctor_end]:
                    new_app = W_App(new_app, ctor_field)

                i = major_idx - 1
                while i >= 0:
                    #print("Adding back extra arg: %s" % new_args[i].pretty())
                    new_app = W_App(new_app, args[i])
                    i -= 1

                # Type check the new application, to ensure that all of our args have the right types
                #if decl.w_kind.k == 1:
                    #import pdb; pdb.set_trace()
                new_app_ty = new_app.infer(infcx)
                old_ty = self.infer(infcx)
                # TODO - this should actually be in the k-like reduction check above
                if not infcx.def_eq(new_app_ty, old_ty):
                    #print("DefEq failed, bailing from iota")
                    return False, self
                #new_app = new_app.whnf(infcx.env)
                return True, new_app


        return False, self


    # https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#weak-head-normalisation
    def whnf(self, infcx):
        fn = self.fn.whnf(infcx)
        # Simple case - beta reduction
        if isinstance(fn, W_FunBase):
            body = fn.body.instantiate(self.arg, 0)
            return body.whnf(infcx)

        # Handle recursor in head position
        progress, reduced = self.try_iota_reduce(infcx)
        if progress:
            return reduced.whnf(infcx)

        if isinstance(fn, W_Const):
            reduced = fn.try_delta_reduce(infcx.env)
            if reduced is not None:
                return W_App(reduced, self.arg).whnf(infcx)
            else:
                # We must have a constructor (or a recusor that we failed to iota-reduce earlier),
                # so there's nothing we can do to reduce further in whnf
                return self
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

    def type_check(self, *args):
        return self.w_kind.type_check(*args)

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
            raise W_TypeError(self.def_type, val_type)


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
        # This includes checking that num_params and num_fields match the declared ctype
        pass

    def get_type(self):
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
    def __init__(
        self,
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
