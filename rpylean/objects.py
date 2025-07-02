from rpython.rlib.objectmodel import compute_hash
from rpython.rlib.rbigint import rbigint

from rpylean._rlib import count


class W_TypeError(object):
    """
    A term does not type check.
    """
    def __init__(self, environment, term, expected_type):  # TODO: inferred_type
        self.environment = environment
        self.term = term
        self.expected_type = expected_type

    def str(self):
        return "%s is not of type %s" % (
            self.environment.pretty(self.term),
            self.environment.pretty(self.expected_type),
        )


class _Item(object):
    """
    A common type for all Lean items.

    The "item" nomenclature comes from the export format documentation (and
    possibly is used elsewhere).

    Don't put any Lean behavior here, it's strictly used to satisfy RPython
    (by making sure all Lean objects have the same base class) and to give Lean
    objects some sane default Python behavior for tests.
    """

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return vars(self) == vars(other)

    def __ne__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return not self == other

    def __repr__(self):
        parts = []
        for k, v in vars(self).items():
            if isinstance(v, bool):
                if v:
                    parts.append(k)
            elif isinstance(v, (int, list)):
                if v:
                    parts.append("=".join((k, repr(v))))
            else:
                parts.append("=".join((k, repr(v))))
        return "<%s %s>" % (self.__class__.__name__, " ".join(parts))


def name_with_levels(name, levels):
    pretty = name.str()
    if not levels:
        return pretty
    return "%s.{%s}" % (
        pretty,
        ", ".join([level.str() for level in levels]),
    )


class Name(_Item):
    def __init__(self, components):
        self.components = components

    def __repr__(self):
        return "<Name %s>" % (self.str(),)

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

    def child(self, part):
        """
        Construct a name nested inside this one.
        """
        return Name(self.components + [part])

    def eq(self, other):
        return self.components == other.components

    def hash(self):
        hash_val = 0
        for c in self.components:
            hash_val ^= compute_hash(c)
        return hash_val

    def pretty(self, constants):
        return self.str()

    def str(self):
        if not self.components:
            return "[anonymous]"
        return ".".join([pretty_part(each) for each in self.components])

    def in_namespace(self, base):
        """
        Calculate what this name looks like inside the given base namespace.

        Essentially, remove common parts from this name which match the base.
        """
        i = 0
        for i, part in enumerate(self.components):
            if i >= len(base.components) or base.components[i] != part:
                break
        return Name(self.components[i:])

    def binder(self, type):
        """
        Bind this name in a (default) binder.
        """
        return Binder.default(name=self, type=type)

    def implicit_binder(self, type):
        """
        Bind this name in an implicit binder.
        """
        return Binder.implicit(name=self, type=type)

    def instance_binder(self, type):
        """
        Bind this name in an instance-implicit binder.
        """
        return Binder.instance(name=self, type=type)

    def strict_implicit_binder(self, type):
        """
        Bind this name in a strict implicit binder.
        """
        return Binder.strict_implicit(name=self, type=type)

    def const(self, levels=None):
        """
        Construct a constant expression for this name.
        """
        return W_Const(name=self, levels=[] if levels is None else levels)

    def declaration(self, type, w_kind, levels=None):
        """
        Make a declaration with this name.
        """
        return W_Declaration(
            name=self,
            type=type,
            levels=[] if levels is None else levels,
            w_kind=w_kind,
        )

    def constructor(self, type, num_params=0, num_fields=0, levels=None):
        """
        Make a constructor declaration with this name.
        """
        constructor = W_Constructor(
            num_params=num_params,
            num_fields=num_fields,
        )
        return self.declaration(type=type, w_kind=constructor, levels=levels)

    def inductive(
        self,
        type,
        names=None,
        constructors=None,
        num_nested=0,
        num_params=0,
        num_indices=0,
        is_reflexive=False,
        is_recursive=False,
        levels=None,
    ):
        """
        Make an inductive type declaration with this name.
        """
        inductive = W_Inductive(
            names=[self] if names is None else names,
            constructors=[] if constructors is None else constructors,
            num_nested=num_nested,
            num_params=num_params,
            num_indices=num_indices,
            is_reflexive=is_reflexive,
            is_recursive=is_recursive,
        )
        return self.declaration(type=type, w_kind=inductive, levels=levels)

    def definition(self, type, value, hint="R", levels=None):
        """
        Make a definition of the given type and value with this name.
        """
        definition = W_Definition(value=value, hint=hint)
        return self.declaration(type=type, w_kind=definition, levels=levels)

    def opaque(self, type, value, levels=None):
        """
        Make an opaque declaration with this name.
        """
        opaque = W_Opaque(value=value)
        return self.declaration(type=type, w_kind=opaque, levels=levels)

    def axiom(self, type, levels=None):
        """
        Make an axiom with this name.
        """
        return self.declaration(type=type, w_kind=W_Axiom(), levels=levels)

    def theorem(self, type, value, levels=None):
        """
        Make a theorem with this name.
        """
        theorem = W_Theorem(value=value)
        return self.declaration(type=type, w_kind=theorem, levels=levels)

    def recursor(
        self,
        type,
        rules=None,
        num_motives=1,
        num_params=0,
        num_indices=0,
        num_minors=0,
        k=0,
        names=None,
        levels=None,
    ):
        """
        Make a recursor with this name.
        """
        recursor = W_Recursor(
            names=[self] if names is None else names,
            rules=[] if rules is None else rules,
            k=k,
            num_params=num_params,
            num_indices=num_indices,
            num_motives=num_motives,
            num_minors=num_minors,
        )
        return self.declaration(type=type, w_kind=recursor, levels=levels)

    def let(self, type, value, body):
        """
        Construct a let expression with this name.
        """
        return W_Let(name=self, type=type, value=value, body=body)

    def level(self):
        """
        Construct a level parameter from this name.
        """
        return W_LevelParam(self)


def names(*many):
    """
    Create a bunch of names at once.
    """
    return [Name.from_str(each) for each in many]


#: The anonymous name.
Name.ANONYMOUS = Name([])


class Binder(_Item):
    """
    A binder within a Lambda or ForAll.

    Only `type` is really functionally important, the other attributes are
    strictly for pretty printing.
    """

    @staticmethod
    def default(name, type):
        """
        A default style binder.
        """
        return Binder(name=name, type=type, left="(", right=")")

    @staticmethod
    def implicit(name, type):
        """
        An implicit style binder.
        """
        return Binder(name=name, type=type, left="{", right="}")

    @staticmethod
    def instance(name, type):
        """
        An intance-implicit style binder.
        """
        return Binder(name=name, type=type, left="[", right="]")

    @staticmethod
    def strict_implicit(name, type):
        """
        A strict implicit style binder.
        """
        return Binder(name=name, type=type, left="⦃", right="⦄")

    def __init__(self, name, type, left, right):
        self.name = name
        self.type = type
        self.left = left
        self.right = right

    def __repr__(self):
        return "<Binder %s>" % (self.name.str())

    def to_implicit(self):
        return Binder.implicit(name=self.name, type=self.type)

    def forall(self, body):
        return W_ForAll(binder=self, body=body)

    def fun(self, body):
        return W_Lambda(binder=self, body=body)

    def pretty(self, constants):
        return "%s%s : %s%s" % (
            self.left,
            self.name.str(),
            self.type.pretty(constants),
            self.right,
        )

    def is_default(self):
        """
        Is this a default binder (i.e. not implicit, instance or strict)?
        """
        return (self.left, self.right) == ("(", ")")

    def is_instance(self):
        """
        Is this a typeclass instance binder?
        """
        return (self.left, self.right) == ("[", "]")

    def fvar(self):
        """
        An FVar for this binder.
        """
        return W_FVar(self)

    def bind_fvar(self, fvar, depth):
        return self.with_type(type=self.type.bind_fvar(fvar, depth))

    def incr_free_bvars(self, expr, depth):
        return self.with_type(type=self.type.incr_free_bvars(expr, depth))

    def instantiate(self, expr, depth):
        return self.with_type(type=self.type.instantiate(expr, depth))

    def subst_levels(self, subts):
        return self.with_type(type=self.type.subst_levels(subts))

    def syntactic_eq(self, other):
        """
        Check if this binder is syntactically equal to another.
        """
        # TODO - does syntactic equality really care about binder info/name?
        return (
            self.name.eq(other.name)
            and self.left == other.left
            and syntactic_eq(self.type, other.type)
        )

    def with_type(self, type):
        """
        Create a new binder of the same name and kind but with a new type.
        """
        return Binder(
            name=self.name,
            type=type,
            left=self.left,
            right=self.right,
        )


def pretty_part(part):
    """
    Pretty print a single component of a Name.
    """

    if isinstance(part, int):
        return str(part)
    if "." in part:
        return "«%s»" % (part,)
    return part


def leq(fn):
    def leq(self, other, balance=0):
        if self == other:
            return balance >= 0
        return fn(self, other, balance)
    return leq


# Based on https://github.com/gebner/trepplein/blob/c704ffe81941779dacf9efa20a75bf22832f98a9/src/main/scala/trepplein/level.scala#L100
class W_Level(_Item):
    def pretty(self, constants):
        return self.str()

    def str(self):
        parts = []
        text, balance = self.pretty_parts()
        if text:
            parts.append(text)
        if balance:
            parts.append(str(balance))
        # FIXME: Actually get rid of this and implement it on each level type
        return " + ".join(parts)

    def eq(self, other):
        """
        Two levels are equal via antisymmetry.

        I.e. `a == b` if `a.leq(b)` and `b.leq(a)`.
        """
        return self.leq(other) and other.leq(self)

    def sort(self):
        """
        Return a Sort for this level.
        """
        return W_Sort(self)

    def succ(self):
        """
        Return the level which is successor to this one.
        """
        return W_LevelSucc(self)

    def max(self, other):
        """
        Return the (simplified) max of this level with another.
        """
        if self is other:
            return self

        if isinstance(self, W_LevelSucc):
            if isinstance(other, W_LevelSucc):
                return self.parent.max(other.parent).succ()
            if self.parent == other:
                return self
        if isinstance(other, W_LevelSucc) and other.parent == self:
            return other
        if isinstance(self, W_LevelZero):
            return other
        if isinstance(other, W_LevelZero):
            return self
        if isinstance(other, W_LevelIMax) or isinstance(other, W_LevelMax):
            if self.leq(other.lhs) or self.leq(other.rhs):
                return other
        return W_LevelMax(self, other)

    def imax(self, other):
        """
        Return the (simplified) imax of this level with another.
        """
        if self is other:
            return self

        if isinstance(other, W_LevelZero):
            return W_LEVEL_ZERO
        if isinstance(self, W_LevelZero) or self == W_LEVEL_ZERO.succ():
            return other
        return W_LevelIMax(self, other)


class W_LevelZero(W_Level):
    def __repr__(self):
        return "<Level 0>"

    @leq
    def leq(self, other, balance):
        if balance >= 0:
            return True
        if isinstance(other, W_LevelParam):
            return balance >= 0
        return other.gt(self, -balance)

    def pretty_parts(self):
        return "", 0

    def subst_levels(self, substs):
        return self

    def syntactic_eq(self, other):
        return True


W_LEVEL_ZERO = W_LevelZero()


class W_LevelSucc(W_Level):
    def __init__(self, parent):
        self.parent = parent

    def __repr__(self):
        joined = " + ".join(str(part) for part in self.pretty_parts() if part)
        return "<Level {}>".format(joined)

    @leq
    def leq(self, other, balance):
        return self.parent.leq(other, balance - 1)

    def gt(self, lhs, balance):
        return lhs.leq(self.parent, -balance + 1)

    def pretty_parts(self):
        text, balance = self.parent.pretty_parts()
        return text, balance + 1

    def subst_levels(self, substs):
        new_parent = self.parent.subst_levels(substs)
        return new_parent.succ()

    def syntactic_eq(self, other):
        return syntactic_eq(self.parent, other.parent)


class W_LevelMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "<Level max({!r} {!r})>".format(self.lhs, self.rhs)

    @leq
    def leq(self, other, balance):
        return self.lhs.leq(other, balance) and self.rhs.leq(other, balance)

    def gt(self, other, balance):
        # XXX
        return False

    def pretty_parts(self):
        left, balance = self.lhs.pretty_parts()
        if not left:
            lhs = str(balance)
        elif balance == 0:
            lhs = left
        else:
            lhs = "(%s + %s)" % (left, balance)

        right, balance = self.rhs.pretty_parts()
        if not right:
            rhs = str(balance)
        elif balance == 0:
            rhs = right
        else:
            rhs = "(%s + %s)" % (right, balance)

        return "(max %s %s)" % (lhs, rhs), 0

    def subst_levels(self, substs):
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
        return new_lhs.max(new_rhs)

    def syntactic_eq(self, other):
        return (
            syntactic_eq(self.lhs, other.lhs)
            and syntactic_eq(self.rhs, other.rhs)
        )


class W_LevelIMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "<Level imax({!r} {!r})>".format(self.lhs, self.rhs)

    @leq
    def leq(self, other, balance):
        return self.lhs.leq(other, balance) or self.rhs.leq(other, balance)

    def gt(self, other, balance):
        # XXX
        return self.lhs.gt(other, balance) or self.rhs.gt(other, balance)

    def pretty_parts(self):
        lhs, _ = self.lhs.pretty_parts()
        rhs, _ = self.rhs.pretty_parts()
        return "(imax %s %s)" % (lhs, rhs), 0

    def subst_levels(self, substs):
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
        return new_lhs.imax(new_rhs)

    def syntactic_eq(self, other):
        return (
            syntactic_eq(self.lhs, other.lhs)
            and syntactic_eq(self.rhs, other.rhs)
        )


class W_LevelParam(W_Level):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "<Level {}>".format(self.name.str())

    @leq
    def leq(self, other, balance):
        if isinstance(other, W_LevelZero):
            return False

        if isinstance(other, W_LevelParam):
            return balance >= 0 and self.name.eq(other.name)
        if isinstance(other, W_LevelMax):
            return self.leq(other.lhs, balance) or self.leq(other.rhs, balance)

        return other.gt(self, -balance)

    def gt(self, other, balance):
        # XXX
        return False

    def pretty_parts(self):
        return self.name.str(), 0

    def syntactic_eq(self, other):
        return self.name.eq(other.name)

    def subst_levels(self, substs):
        return substs.get(self.name, self)


class W_Expr(_Item):
    def app(self, arg):
        """
        Apply this (which better be a function) to an argument.
        """
        return W_App(fn=self, arg=arg)

    # Tries to perform a single step of strong reduction.
    # Currently implemented reduction steps:
    # * Delta reduction (definition unfolding)
    # * Beta reduction (function application)
    # * Iota reduction: simplification of ('InductiveType.recursor arg0 .. argN InductiveType.ctorName') using matching RecursorRule
    #
    # Return (progress, new_expr), where `progress` indicates whether any reduction was performed
    def strong_reduce_step(self, env):
        return (False, self)


class W_BVar(W_Expr):
    def __init__(self, id):
        self.id = id

    def __repr__(self):
        return "<BVar %s>" % (self.id,)

    def pretty(self, constants):
        return self.str()

    def str(self):
        return "(BVar [%s])" % (self.id,)

    def syntactic_eq(self, other):
        return self.id == other.id

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
            return W_BVar(self.id - 1)
        return self

    def incr_free_bvars(self, count, depth):
        if self.id >= depth:
            return W_BVar(self.id + count)
        return self

    def subst_levels(self, substs):
        return self


class W_FVar(W_Expr):

    _counter = count()

    def __init__(self, binder):
        self.id = next(self._counter)
        assert isinstance(binder, Binder)
        self.binder = binder

    def __repr__(self):
        return "<FVar id={} binder={!r}>".format(self.id, self.binder)

    def incr_free_bvars(self, count, depth):
        return self

    def instantiate(self, expr, depth):
        return self

    def whnf(self, env):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_FVar)
        return (
            self.id == other.id
            and syntactic_eq(self.binder, other.binder)
        )

    def infer(self, env):
        """
        A free variable's type comes from the binder's type which it replaced.
        """
        return self.binder.type

    def bind_fvar(self, fvar, depth):
        if self.id == fvar.id:
            return W_BVar(depth)
        return self

    def pretty(self, constants):
        return self.str()

    def str(self):
        return self.binder.name.str()


class W_LitStr(W_Expr):
    def __init__(self, val):
        assert isinstance(val, str)
        self.val = val

    def __repr__(self):
        return repr(self.val)

    def infer(self, env):
        """
        String literals infer as the constant named String.
        """
        return STRING

    def pretty(self, constants):
        return self.str()

    def str(self):
        return '"%s"' % (self.val,)

    def instantiate(self, expr, depth):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitStr)
        return self.val == other.val


class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level

    def __repr__(self):
        # No class name here, as we wouldn't want to see <Sort Type>
        return "<%s>" % (self.str(),)

    def pretty(self, constants):
        """
        Pretty format this Sort.
        """
        return self.str()

    def str(self):
        text, balance = self.level.pretty_parts()

        if balance == 0:
            if not text:
                return "Prop"
            prefix = "Sort"
        else:
            prefix, balance = "Type", balance - 1

        if not text:
            if balance == 0:
                return "Type"
            return "%s %s" % (prefix, balance)

        if balance == 0:
            return "%s %s" % (prefix, text)
        return "%s (%s + %s)" % (prefix, text, balance)

    def whnf(self, env):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth):
        return self

    def infer(self, env):
        return self.level.succ().sort()

    def subst_levels(self, substs):
        return self.level.subst_levels(substs).sort()

    def syntactic_eq(self, other):
        assert isinstance(other, W_Sort)
        return syntactic_eq(self.level, other.level)


PROP = W_LEVEL_ZERO.sort()
TYPE = W_LEVEL_ZERO.succ().sort()


# Takes the level params from 'const', and substitutes them into 'target'
def apply_const_level_params(const, target, env):
    decl = env.declarations[const.name]
    if len(decl.levels) != len(const.levels):
        raise RuntimeError("W_Const.infer: expected %s levels, got %s" % (len(decl.levels), len(const.levels)))
    params = decl.levels
    substs = {}
    for i in range(len(params)):
        substs[params[i]] = const.levels[i]
    return target.subst_levels(substs)


class W_Const(W_Expr):
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels

    def child(self, part):
        """
        A child constant of this one.
        """
        return self.name.child(part).const()

    def pretty(self, constants):
        return name_with_levels(self.name, self.levels)

    def str(self):
        return self.name.str()

    def syntactic_eq(self, other):
        if self.name != other.name or len(self.levels) != len(other.levels):
            return False
        for i, level in enumerate(self.levels):
            if not syntactic_eq(level, other.levels[i]):
                return False
        return True

    def strong_reduce_step(self, env):
        reduced = self.try_delta_reduce(env)
        if reduced is not None:
            return (True, reduced)
        return (False, self)

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def whnf(self, env):
        return self

    def try_delta_reduce(self, env, only_abbrev=False):
        decl = env.declarations[self.name]
        if decl is None:
            print("Missing decl: %s" % self.name.components)
            raise RuntimeError("Missing decl: %s" % self.str())
        # TODO - use hint to decide whether to delta reduce or not
        val = decl.w_kind.get_delta_reduce_target()
        if not isinstance(decl.w_kind, W_Definition):
            return None

        if val is None:
            return None

        return apply_const_level_params(self, val, env)

    def infer(self, env):
        decl = env.declarations[self.name]
        params = decl.levels

        if not params:
            return decl.type

        return apply_const_level_params(self, decl.type, env)

    def subst_levels(self, substs):
        new_levels = []
        for level in self.levels:
            new_level = level.subst_levels(substs)
            new_levels.append(new_level)
        return self.name.const(new_levels)


NAT = Name.simple("Nat").const()
NAT_ZERO = NAT.child("zero")
NAT_SUCC = NAT.child("succ")
STRING = Name.simple("String").const()


class W_LitNat(W_Expr):
    def __init__(self, val):
        self.val = val

    def __repr__(self):
        return "<LitNat %s>" % (self.val.str(),)

    def pretty(self, constants):
        return self.str()

    def str(self):
        return self.val.str()

    def instantiate(self, expr, depth):
        return self

    def subst_levels(self, substs):
        return self

    def whnf(self, env):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitNat)
        return self.val == other.val

    def build_nat_expr(self):
        if rbigint.fromint(100).lt(self.val):
            print("Building large nat expr for %s" % self.val)
        expr = NAT_ZERO
        i = rbigint.fromint(0)
        while i.lt(self.val):
            expr = NAT_SUCC.app(expr)
            i = i.add(rbigint.fromint(1))
        return expr

    def strong_reduce_step(self, env):
        return (False, self)
        if self.val == rbigint.fromint(0):
            return (True, NAT_ZERO)

        # Add a single 'Succ'
        sub = self.val.sub(rbigint.fromint(1))
        return (True, NAT_SUCC.app(W_LitNat(sub)))

    def bind_fvar(self, fvar, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def infer(self, env):
        """
        Nat literals infer as the constant named Nat.
        """
        return NAT


class W_Proj(W_Expr):
    def __init__(self, struct_name, field_idx, struct_expr):
        self.struct_name = struct_name
        self.field_idx = field_idx
        self.struct_expr = struct_expr

    def strong_reduce_step(self, env):
        progress, new_struct_expr = self.struct_expr.strong_reduce_step(env)
        if progress:
            return (True, W_Proj(self.struct_name, self.field_idx, new_struct_expr))

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

        ctor_decl = env.declarations[struct_expr.name]
        if not isinstance(ctor_decl.w_kind, W_Constructor):
            return (False, self)

        num_params = ctor_decl.w_kind.num_params
        args.reverse()
        target_arg = args[num_params + self.field_idx]

        return (True, target_arg)

    def whnf(self, env):
        # TODO - do we need to try reducing the projection?
        return W_Proj(self.struct_name, self.field_idx, self.struct_expr.whnf(env))

    def incr_free_bvars(self, count, depth):
        return W_Proj(self.struct_name, self.field_idx, self.struct_expr.incr_free_bvars(count, depth))

    def bind_fvar(self, fvar, depth):
        return W_Proj(self.struct_name, self.field_idx, self.struct_expr.bind_fvar(fvar, depth))

    def instantiate(self, expr, depth):
        return W_Proj(self.struct_name, self.field_idx, self.struct_expr.instantiate(expr, depth))

    def pretty(self, constants):
        return "<W_Proj struct_name='%s' field_idx='%s' struct_expr='%s'>" % (
            self.struct_name.str(),
            self.field_idx,
            self.struct_expr.pretty(constants),
        )

    def subst_levels(self, substs):
        return W_Proj(
            self.struct_name,
            self.field_idx,
            self.struct_expr.subst_levels(substs)
        )

    def syntactic_eq(self, other):
        # Our 'struct_type' is a '_Item' (which is only constructed once, during parsing),
        # so we can compare by object identity with '=='
        return (
            self.struct_name == other.struct_name
            and self.field_idx == other.field_idx
            and syntactic_eq(self.struct_expr, other.struct_expr)
        )

    def infer(self, env):
        struct_expr_type = self.struct_expr.infer(env).whnf(env)

        # Unfold applications of a base inductive type (e.g. `MyList TypeA TypeB`)
        apps = []
        while isinstance(struct_expr_type, W_App):
            apps.append(struct_expr_type)
            struct_expr_type = struct_expr_type.fn

        struct_type = env.declarations[self.struct_name]

        # The base type should be a constant, referring to 'struct_type' (e.g. `MyList`)
        assert isinstance(struct_expr_type, W_Const), "Expected W_Const, got %s" % struct_expr_type
        target_const = env.declarations[struct_expr_type.name]
        assert target_const == struct_type, "Expected %s, got %s" % (target_const, struct_type)

        assert isinstance(struct_type, W_Declaration)
        assert isinstance(struct_type.w_kind, W_Inductive)
        assert len(struct_type.w_kind.constructors) == 1

        ctor_decl = struct_type.w_kind.constructors[0]
        assert isinstance(ctor_decl, W_Declaration)
        assert isinstance(ctor_decl.w_kind, W_Constructor)

        ctor_type = apply_const_level_params(
            struct_expr_type,
            ctor_decl.type,
            env,
        )

        # The last app pushed to 'apps' is the innermost application (applied directly to the `MyList const`),
        # so start iteration from the end
        # TODO: handle levels
        apps.reverse()
        for app in apps:
            ctor_type = ctor_type.whnf(env)
            assert isinstance(ctor_type, W_ForAll)
            new_type = ctor_type.body.instantiate(app.arg, 0)
            ctor_type = new_type

        # Fields can depend on earlier fields, so the constructor takes in 'proj'
        # expressions for all of the previous fields ('self.field_idx' is 0-based)

        # Substitute in 'proj' expressions for all of the previous fields
        for i in range(self.field_idx):
            ctor_type = ctor_type.whnf(env)
            assert isinstance(ctor_type, W_ForAll)
            ctor_type = ctor_type.body.instantiate(W_Proj(struct_type, i, self.struct_expr), 0)

        ctor_type = ctor_type.whnf(env)
        assert isinstance(ctor_type, W_ForAll)
        return ctor_type.binder.type


# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    def __init__(self, binder, body):
        assert body is not None
        assert isinstance(binder, Binder)
        self.binder = binder
        self.body = body
        self.finished_reduce = False

    # Weak head normal form stops at forall/lambda
    def whnf(self, env):
        return self

    def strong_reduction_helper(self, env):
        progress, binder_type = self.binder.type.strong_reduce_step(env)
        if progress:
            return (True, (self.binder.with_type(binder_type), self.body))

        fvar = self.binder.fvar()
        open_body = self.body.instantiate(fvar, 0)
        progress, open_body = open_body.strong_reduce_step(env)
        new_body = open_body.bind_fvar(fvar, 0)
        if progress:
            return (True, (self.binder.with_type(binder_type), new_body))

        self.finished_reduce = True
        return (False, (self.binder, self.body))


class W_ForAll(W_FunBase):
    def pretty(self, constants):
        """
        Render either as an arrow (``x → y``) or else really using ``∀ _, _``.

        ForAll represents two concepts which implementation-wise are
        "the "same", but which are differentiated when pretty printing.
        Those are:

            * universally quantified propositions, i.e. "true" foralls
            * dependent function types

        We try to follow Lean's real pretty printer for deciding when to
        render which.
        """
        lhs_type = None
        if isinstance(self.binder.type, W_Const):
            lhs_type = constants.get(self.binder.type.name, None)

        rhs = self.body.instantiate(self.binder.fvar(), 0)
        rhs_type = None
        if isinstance(rhs, W_Const):
            rhs_type = constants.get(rhs.name, None)
        if lhs_type is not PROP and rhs_type is PROP:
            return "∀ %s, %s" % (
                self.binder.pretty(constants),
                rhs.pretty(constants),
            )
        else:
            lhs = self.binder.type if self.binder.is_default() else self.binder
            return "%s → %s" % (
                lhs.pretty(constants),
                rhs.pretty(constants),
            )

    def infer(self, env):
        binder_sort = env.infer_sort_of(self.binder.type)
        body_sort = env.infer_sort_of(self.body.instantiate(self.binder.fvar(), 0))
        return binder_sort.imax(body_sort).sort()

    # TODO - double check this
    def instantiate(self, expr, depth):
        # Don't increment - not yet inside a binder
        return self.binder.instantiate(expr, depth).forall(
            body=self.body.instantiate(expr, depth + 1),
        )

    def syntactic_eq(self, other):
        assert isinstance(other, W_ForAll)
        return (
            syntactic_eq(self.binder, other.binder)
            and syntactic_eq(self.body, other.body)
        )

    def bind_fvar(self, fvar, depth):
        return self.binder.bind_fvar(fvar, depth).forall(
            body=self.body.bind_fvar(fvar, depth + 1),
        )

    def incr_free_bvars(self, count, depth):
        return self.binder.incr_free_bvars(count, depth).forall(
            body=self.body.incr_free_bvars(count, depth + 1),
        )

    def strong_reduce_step(self, env):
        if self.finished_reduce:
            return False, self
        progress, args = self.strong_reduction_helper(env)
        if not progress:
            return (False, self)
        return (progress, W_ForAll(*args))

    def subst_levels(self, levels):
        return self.binder.subst_levels(levels).forall(
            body=self.body.subst_levels(levels),
        )


def group_to_str(group):
    assert not group[-1].is_instance()

    names = " ".join([each.name.str() for each in group])
    if group[-1].is_default():
        return names

    return "%s%s%s" % (group[-1].left, names, group[-1].right)


class W_Lambda(W_FunBase):
    def pretty(self, constants):
        binders = []
        current = self
        while isinstance(current, W_Lambda):
            binders.append(current.binder)
            current = current.body

        groups, current_group, last_style = [], [], binders[0].left

        for binder in binders:
            if binder.is_instance():  # always shown separate
                if current_group:
                    groups.append(group_to_str(current_group))
                    current_group = []
                groups.append(
                    "%s%s : %s%s" % (
                        binder.left,
                        binder.name.str(),
                        binder.type.pretty(constants),
                        binder.right,
                    ),
                )
                last_style = None
            elif binder.left != last_style and current_group:
                groups.append(group_to_str(current_group))
                current_group, last_style = [binder], binder.left
            else:
                current_group.append(binder)
        if current_group:
            groups.append(group_to_str(current_group))

        body = current
        for binder in reversed(binders):
            body = body.instantiate(binder.fvar(), 0)

        return "fun %s ↦ %s" % (
            " ".join(groups),
            body.pretty(constants),
        )

    def syntactic_eq(self, other):
        assert isinstance(other, W_Lambda)
        return (
            syntactic_eq(self.binder, other.binder)
            and syntactic_eq(self.body, other.body)
        )

    def bind_fvar(self, fvar, depth):
        return self.binder.bind_fvar(fvar, depth).fun(
            body=self.body.bind_fvar(fvar, depth + 1),
        )

    def instantiate(self, expr, depth):
        # Don't increment - not yet inside a binder
        return self.binder.instantiate(expr, depth).fun(
            body=self.body.instantiate(expr, depth + 1),
        )

    def incr_free_bvars(self, count, depth):
        return self.binder.incr_free_bvars(count, depth).fun(
            body=self.body.incr_free_bvars(count, depth + 1),
        )

    def infer(self, env):
        # Run this for the side effect - throwing an exception if not a Sort
        env.infer_sort_of(self.binder.type)
        fvar = self.binder.fvar()
        body_type_fvar = self.body.instantiate(fvar, 0).infer(env)
        body_type = body_type_fvar.bind_fvar(fvar, 0)
        if body_type is None:
            raise RuntimeError("W_Lambda.infer: body_type is None: %s" % env.pretty(self))
        return self.binder.forall(body=body_type)

    def strong_reduce_step(self, env):
        if self.finished_reduce:
            return False, self
        progress, args = self.strong_reduction_helper(env)
        if not progress:
            return (False, self)
        return (progress, W_Lambda(*args))

    def subst_levels(self, substs):
        return self.binder.subst_levels(substs).fun(
            body=self.body.subst_levels(substs),
        )


class W_Let(W_Expr):
    def __init__(self, name, type, value, body):
        self.name = name
        self.type = type
        self.value = value
        self.body = body

    def pretty(self, constants):
        fvar = self.name.binder(type=self.type).fvar()
        return "let %s : %s := %s\n%s" % (
            self.name.str(),
            self.type.pretty(constants),
            self.value.pretty(constants),
            self.body.instantiate(fvar, 0).pretty(constants),
        )

    def instantiate(self, expr, depth):
        return self.name.let(
            type=self.type.instantiate(expr, depth),
            value=self.value.instantiate(expr, depth),
            body=self.body.instantiate(expr, depth + 1),
        )

    def syntactic_eq(self, other):
        return (
            self.name.eq(other.name)
            and syntactic_eq(self.type, other.type)
            and syntactic_eq(self.value, other.value)
            and syntactic_eq(self.body, other.body)
        )


class W_App(W_Expr):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg

    def pretty(self, constants):
        args = []
        current = self
        while isinstance(current, W_App):
            args.append(current.arg)
            current = current.fn

        fn_pretty = current.pretty(constants)
        if isinstance(current, W_Lambda):
            fn_pretty = "(%s)" % fn_pretty

        arg_parts = []
        for i in range(len(args) - 1, 0, -1):
            arg = args[i]
            arg_pretty = arg.pretty(constants)
            if isinstance(arg, W_Lambda) or isinstance(arg, W_App):
                arg_pretty = "(%s)" % arg_pretty
            arg_parts.append(arg_pretty)

        last_arg = args[0]
        last_arg_pretty = last_arg.pretty(constants)
        if isinstance(last_arg, W_App):
            last_arg_pretty = "(%s)" % last_arg_pretty
        arg_parts.append(last_arg_pretty)

        return "%s %s" % (fn_pretty, " ".join(arg_parts))

    def infer(self, env):
        fn_type_base = self.fn.infer(env)
        fn_type = fn_type_base.whnf(env)
        if not isinstance(fn_type, W_ForAll):
            raise RuntimeError("W_App.infer: expected function type, got %s" % type(fn_type))
        arg_type = self.arg.infer(env)
        if not env.def_eq(fn_type.binder.type, arg_type):
            raise RuntimeError(
                "W_App.infer: type mismatch:\n%s\n  !=\n%s" % (
                    env.pretty(fn_type.binder.type),
                    env.pretty(arg_type),
                ),
            )
        body_type = fn_type.body.instantiate(self.arg, 0)
        return body_type

    def syntactic_eq(self, other):
        return (
            syntactic_eq(self.fn, other.fn)
            and syntactic_eq(self.arg, other.arg)
        )

    def try_iota_reduce(self, env):
        args = []
        target = self
        while isinstance(target, W_App):
            args.append(target.arg)
            target = target.fn

        if not isinstance(target, W_Const):
            return False, self

        decl = env.declarations[target.name]
        if not isinstance(decl.w_kind, W_Recursor):
            return False, self

        if decl.w_kind.num_motives != 1:
            warn("W_App.try_iota_reduce: unimplemented case num_motives != 1 for %s" % target.name)
            return False, self

        skip_count = decl.w_kind.num_params + decl.w_kind.num_indices + decl.w_kind.num_minors + decl.w_kind.num_motives
        major_idx = len(args) - 1 - skip_count

        # for rec_rule in decl.w_kind.rules:
        #     pass

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
            self.infer(env)

            old_ty = major_premise.infer(env)
            old_ty_base = old_ty
            while isinstance(old_ty_base, W_App):
                old_ty_base = old_ty_base.fn
            assert isinstance(old_ty_base, W_Const)

            assert len(decl.w_kind.names) == 1
            inductive_decl = env.declarations[decl.w_kind.names[0]]
            assert isinstance(inductive_decl.w_kind, W_Inductive)

            assert len(inductive_decl.w_kind.constructors) == 1
            ctor_decl = inductive_decl.w_kind.constructors[0]
            assert isinstance(ctor_decl.w_kind, W_Constructor)

            new_args = list(args)
            new_args.reverse()
            num_ctor_params = ctor_decl.w_kind.num_params

            major_premise_ctor = ctor_decl.name.const(old_ty_base.levels)
            assert num_ctor_params >= 0
            for arg in new_args[0:num_ctor_params]:
                major_premise_ctor = major_premise_ctor.app(arg)

            new_ty = major_premise_ctor.infer(env)
            if not env.def_eq(old_ty, new_ty):
                return False, self
            #print("Built new major premise: %s" % major_premise_ctor.pretty())
            major_premise = major_premise_ctor

            # major_premise_ty = major_premise.infer(env)
            # print("K-like reduction with major_premise %s type: %s" % (major_premise.pretty(), major_premise_ty.pretty()))
            # k_like_args = []
            # while isinstance(major_premise_ty, W_App):
            #     k_like_args.append(major_premise_ty.arg)
            #     major_premise_ty = major_premise_ty.fn

            # k_like_args.reverse()
            # print("Unwrapped: %s" % major_premise_ty.pretty())
            # assert isinstance(major_premise_ty, W_Const)
            # base_decl = env.declarations[major_premise_ty.name]
            # assert isinstance(base_decl.w_kind, W_Inductive)
            # assert len(base_decl.w_kind.ctor_names) == 1
            # print("Ctor name: %s" % base_decl.w_kind.ctor_names[0])

            # ctor_decl = env.declarations[base_decl.w_kind.ctor_names[0]]

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
        for rec_rule in decl.w_kind.rules:
            if rec_rule.ctor_name.eq(major_premise_ctor.name):
                #print("Have num_fields %s and num_params=%s" % (rec_rule.num_fields, decl.w_kind.num_params))uctor.get_type not yet implemented fo
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
                new_app = apply_const_level_params(target, new_app, env)

                new_args = list(args)
                new_args.reverse()

                total_args = decl.w_kind.num_params + decl.w_kind.num_motives + decl.w_kind.num_minors
                assert total_args >= 0
                for arg in new_args[:total_args]:
                    new_app = new_app.app(arg)
                # We want to include all of the arguments up to the motive (which is the major premise)

                ctor_start = decl.w_kind.num_params
                ctor_end = decl.w_kind.num_params + rec_rule.num_fields
                assert ctor_start >= 0
                assert ctor_end >= 0

                for ctor_field in all_ctor_args[ctor_start:ctor_end]:
                    new_app = new_app.app(ctor_field)

                i = major_idx - 1
                while i >= 0:
                    #print("Adding back extra arg: %s" % new_args[i].pretty())
                    new_app = new_app.app(args[i])
                    i -= 1

                # Type check the new application, to ensure that all of our args have the right types
                #if decl.w_kind.k == 1:
                    #import pdb; pdb.set_trace()
                new_app_ty = new_app.infer(env)
                old_ty = self.infer(env)
                # TODO - this should actually be in the k-like reduction check above
                if not env.def_eq(new_app_ty, old_ty):
                    #print("DefEq failed, bailing from iota")
                    return False, self
                #new_app = new_app.whnf(env)
                return True, new_app

        return False, self

    # https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#weak-head-normalisation
    def whnf(self, env):
        fn = self.fn.whnf(env)
        # Simple case - beta reduction
        if isinstance(fn, W_FunBase):
            body = fn.body.instantiate(self.arg, 0)
            return body.whnf(env)

        # Handle recursor in head position
        progress, reduced = self.try_iota_reduce(env)
        if progress:
            return reduced.whnf(env)

        if isinstance(fn, W_Const):
            reduced = fn.try_delta_reduce(env)
            if reduced is not None:
                return reduced.app(self.arg).whnf(env)
            else:
                # We must have a constructor (or a recusor that we failed to iota-reduce earlier),
                # so there's nothing we can do to reduce further in whnf
                return self
        return self

    def strong_reduce_step(self, env):
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
        progress, new_fn = self.fn.strong_reduce_step(env)
        if progress:
            return (True, new_fn.app(self.arg))

        progress, new_arg = self.arg.strong_reduce_step(env)
        if progress:
            return (True, new_fn.app(new_arg))

        # Finally, try iota reduction after we've reduced everthing else as much as possible
        # This allows us to find a recursor constant and constructor constant
        # (both can be produced by earlier reduction steps, but neither can be further reduced
        # without iota reduction)
        return self.try_iota_reduce(env)

    def bind_fvar(self, fvar, depth):
        return self.fn.bind_fvar(fvar, depth).app(
            self.arg.bind_fvar(fvar, depth),
        )

    def instantiate(self, expr, depth):
        return self.fn.instantiate(expr, depth).app(
            self.arg.instantiate(expr, depth),
        )

    def incr_free_bvars(self, count, depth):
        return self.fn.incr_free_bvars(count, depth).app(
            self.arg.incr_free_bvars(count, depth),
        )

    def subst_levels(self, substs):
        return self.fn.subst_levels(substs).app(self.arg.subst_levels(substs))


class W_RecRule(_Item):
    def __init__(self, ctor_name, num_fields, val):
        self.ctor_name = ctor_name
        self.num_fields = num_fields
        self.val = val

    def pretty(self, constants):
        return "<RecRule ctor_name='%s' num_fields='%s' val='%s'>" % (
            self.ctor_name.str(),
            self.num_fields,
            self.val.pretty(constants),
        )


class W_Declaration(_Item):
    def __init__(self, name, type, w_kind, levels):
        self.name = name
        self.type = type
        self.w_kind = w_kind
        self.levels = levels

    def const(self, **kwargs):
        """
        Create a constant referring to this declaration by name.
        """
        return self.name.const(**kwargs)

    def pretty(self, constants):
        # Is delaborate the right vocabulary for what we're doing?!
        pretty = name_with_levels(self.name, self.levels)
        return self.w_kind.delaborate(pretty, self.type, constants)

    def type_check(self, env):
        return self.w_kind.type_check(self.type, env)


class W_DeclarationKind(_Item):
    # Returns the value associated with this declaration kind.
    # This is the def value for a Definition, and `None` for things like Inductive
    def get_delta_reduce_target(self):
        return None


class DefOrTheorem(W_DeclarationKind):
    def type_check(self, type, env):
        val_type = self.value.infer(env)
        if not env.def_eq(type, val_type):
            return W_TypeError(env, type, val_type)


class W_Definition(DefOrTheorem):
    def __init__(self, value, hint):
        self.value = value
        self.hint = hint

    def delaborate(self, name_with_levels, type, constants):
        return "def %s : %s := %s" % (
            name_with_levels,
            type.pretty(constants),
            self.value.pretty(constants),
        )

    def get_delta_reduce_target(self):
        return self.value


class W_Opaque(W_Definition):
    """
    An Opaque definition.

    This is like a definition with hint 'opaque', but even
    stronger (we will never unfold it).
    """
    def __init__(self, value):
        self.value = value
        self.hint = "O"


class W_Theorem(DefOrTheorem):
    def __init__(self, value):
        self.value = value

    def delaborate(self, name_with_levels, type, constants):
        return "theorem %s : %s := %s" % (
            name_with_levels,
            type.pretty(constants),
            self.value.pretty(constants),
        )


class W_Axiom(W_DeclarationKind):
    def delaborate(self, name_with_levels, type, constants):
        return "axiom %s : %s" % (name_with_levels, type.pretty(constants))

    def type_check(self, type, env):
        # TODO - implement type checking
        pass


class W_Inductive(W_DeclarationKind):
    def __init__(
        self,
        names,       # ??: What is this? Inductives know their names?
                     #     Is this for mutual inductives which have multiple?
        constructors,
        num_nested,
        num_params,
        num_indices,
        is_reflexive,
        is_recursive,
    ):
        self.names = names
        self.constructors = constructors
        self.num_nested = num_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.is_reflexive = is_reflexive
        self.is_recursive = is_recursive

    def type_check(self, type, env):
        # TODO - implement type checking
        pass

    def delaborate(self, name_with_levels, type, constants):
        ctors = [
            each.w_kind.delaborate_in(
                constructor_name=each.name,
                type=each.type,
                inductive=self,
                constants=constants,
            )
            for each in self.constructors
        ]
        return "inductive %s : %s%s" % (
            name_with_levels,
            type.pretty(constants),
            ("\n" + "\n".join(ctors)) if ctors else "",
        )


class W_Constructor(W_DeclarationKind):
    def __init__(self, num_params, num_fields):
        self.num_params = num_params
        self.num_fields = num_fields

    def type_check(self, type, env):
        # TODO - implement type checking
        # This includes checking that num_params and num_fields match the declared ctype
        pass

    def delaborate(self, name_with_levels, type, constants):
        return "constructor %s : %s" % (
            name_with_levels,
            type.pretty(constants),
        )

    def delaborate_in(
        self,
        constructor_name,
        type,
        inductive,
        constants,
    ):
        name = constructor_name.in_namespace(inductive.names[0])
        if type in [each.const() for each in inductive.names]:
            # TODO: is this right? Probably it needs to use some _eq method
            return "| %s" % (name.str(),)
        return "| %s : %s" % (
            name.str(),
            type.pretty(constants),
        )


class W_Recursor(W_DeclarationKind):
    def __init__(
        self,
        names,
        rules,
        num_motives,
        num_params,
        num_indices,
        num_minors,
        k,
    ):
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.names = names
        self.rules = rules

    def type_check(self, type, env):
        # TODO - implement type checking
        pass

    def delaborate(self, name_with_levels, type, constants):
        return "recursor %s : %s" % (
            name_with_levels,
            type.pretty(constants),
        )


def syntactic_eq(expr1, expr2):
    """
    Check if two expressions are syntactically equal.
    """
    if expr1.__class__ is not expr2.__class__:
        return False
    return expr1.syntactic_eq(expr2)


def warn(message):
    print("WARNING: %s" % (message,))
