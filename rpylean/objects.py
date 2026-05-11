from rpython.rlib.jit import JitDriver, elidable, promote, unroll_safe
from rpython.rlib.objectmodel import (
    compute_hash, compute_identity_hash, not_rpython, specialize,
)
from rpython.rlib.rbigint import rbigint

from rpylean._rlib import count, warn
from rpylean._tokens import (
    BINDER_NAME,
    DECL_NAME,
    Diagnostic,
    FORMAT_PLAIN,
    KEYWORD,
    LEVEL,
    LITERAL,
    MESSAGE,
    NO_SPAN,
    OPERATOR,
    PLAIN,
    PUNCT,
    SORT,
)
from rpylean._tokens import indent
from rpylean.exceptions import (
    InvalidProjection,
    W_Error,
)


def _whnf_printable_location(expr_class):
    """
    Return a human-readable description of the current WHNF trace.

    Called by the JIT to label traces in PYPYLOG output.
    """
    return "whnf: %s" % expr_class.__name__


# JIT driver for the WHNF reduction loop - the core hot path of type checking.
# greens: expr_class determines which reduction rule applies
# reds: the mutable state during reduction
whnf_jitdriver = JitDriver(
    greens=["expr_class"],
    reds=["made_progress", "expr", "env"],
    name="whnf",
    get_printable_location=_whnf_printable_location,
)


@elidable
def get_decl(declarations, name):
    """
    Look up a declaration by name.

    This is a hot path during type checking - called for every constant.
    The declarations dict is immutable after environment construction,
    so this lookup is pure and can be elided by the JIT when the name
    is known at trace time.
    """
    return declarations[name]


class W_CheckError(W_Error):
    """
    Base class for type-checking errors returned by type_check.
    """

    name = None
    declaration = None

    def as_diagnostic(self):
        """Return this error as a ``Diagnostic``."""
        raise NotImplementedError

    def tokens(self):
        """Return a flat token list (without caret spans)."""
        d = self.as_diagnostic()
        return d.tokens + d.message

    def __str__(self):
        return FORMAT_PLAIN(self.tokens())

    def write_to(self, writer):
        """Write this error as a diagnostic with caret underlines."""
        writer.writeline_diagnostic(self.as_diagnostic())


def _append_marked_tokens(result, span_holder, expr, constants, mark):
    """
    Append tokens for ``expr`` to ``result``, tracking ``mark``.

    If ``mark`` is ``expr`` (by identity), record the token index range
    into ``span_holder[0]`` as a ``(start, end)`` tuple.
    Otherwise, pass ``mark`` through to ``expr.tokens()`` so that
    subexpressions can be matched.

    ``expr`` is any object with a ``tokens(constants, mark, span_holder)``
    method -- typically a ``W_Expr`` or ``Binder``.
    """
    if mark is not None and mark is expr:
        start = len(result)
        result += expr.tokens(constants)
        span_holder[0] = (start, len(result))
        return
    if mark is not None and span_holder is not None and span_holder[0] == NO_SPAN:
        inner = [NO_SPAN]
        tokens = expr.tokens(constants, mark, inner)
        if inner[0] != NO_SPAN:
            offset = len(result)
            span_holder[0] = (inner[0][0] + offset, inner[0][1] + offset)
        result += tokens
    else:
        result += expr.tokens(constants)


def _error_diagnostic(declaration, name, expr, prefix, message, declarations):
    """
    Build a ``Diagnostic`` for a type-checking error.

    When ``declaration`` is available, the full declaration is rendered
    with the offending ``expr`` span-marked.  Otherwise, a fallback
    showing ``prefix``, ``name``, and ``expr`` inline is used.
    """
    if declaration is not None:
        span_holder = [NO_SPAN]
        result = declaration.tokens(
            declarations, mark=expr, span_holder=span_holder,
        )
        return Diagnostic(result, span_holder[0], message)
    if name is None:
        name = Name.ANONYMOUS
    result = [PLAIN.emit(prefix)]
    result += name.tokens(declarations)
    result.append(PUNCT.emit(":\n  "))
    result += expr.tokens(declarations)
    return Diagnostic(result, NO_SPAN, message)


class W_TypeError(W_CheckError):
    """
    A term does not type check.
    """

    def __init__(self, environment, term, expected_type, inferred_type, name=None):
        self.environment = environment
        self.term = term
        self.expected_type = expected_type
        self.inferred_type = inferred_type
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\nhas type\n  ")]
        message += self.inferred_type.tokens(declarations)
        message += [MESSAGE.emit("\nbut is expected to have type\n  ")]
        message += self.expected_type.tokens(declarations)
        return _error_diagnostic(
            self.declaration, self.name, self.term,
            "Type mismatch in ", message, declarations,
        )


class W_InvalidConstructorResult(W_CheckError):
    """
    A constructor's result type is not a valid application of its inductive.
    """

    def __init__(self, environment, ctor_type, name=None):
        self.environment = environment
        self.ctor_type = ctor_type
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\ninvalid return type")]
        return _error_diagnostic(
            self.declaration, self.name, self.ctor_type,
            "Invalid constructor ", message, declarations,
        )


class W_ConstructorFieldCountMismatch(W_CheckError):
    """
    A constructor's declared num_fields does not match its type's binders.
    """

    def __init__(self, environment, ctor_type, declared, actual, name=None):
        self.environment = environment
        self.ctor_type = ctor_type
        self.declared = declared
        self.actual = actual
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit(
            "\nconstructor declares %d field%s"
            " but type has %d" % (
                self.declared,
                "s" if self.declared != 1 else "",
                self.actual,
            ),
        )]
        return _error_diagnostic(
            self.declaration, self.name, self.ctor_type,
            "Invalid constructor ", message, declarations,
        )


class W_InvalidRecursorRule(W_CheckError):
    """
    A recursor's rule doesn't match its inductive's structure: missing
    or extra rules, a rule whose `ctor` isn't a constructor of the
    inductive, or a mismatched `nfields`.
    """

    def __init__(self, environment, summary, name=None):
        self.environment = environment
        self.summary = summary
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\n" + self.summary)]
        return _error_diagnostic(
            self.declaration, self.name, None,
            "Invalid recursor ", message, declarations,
        )


class W_NonPositiveOccurrence(W_CheckError):
    """
    A constructor field type has the inductive in a non-positive position.
    """

    def __init__(self, environment, field_type, field_number, name=None):
        self.environment = environment
        self.field_type = field_type
        self.field_number = field_number
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [
            MESSAGE.emit(
                "\narg #%d has a non-positive occurrence of the datatype"
                " being declared" % self.field_number,
            ),
        ]
        return _error_diagnostic(
            self.declaration, self.name, self.field_type,
            "Invalid constructor ", message, declarations,
        )


class W_NotASort(W_CheckError):
    """
    An expression does not have a Sort (Type or Prop) as its type.
    """

    def __init__(self, environment, expr, inferred_type, name=None):
        self.environment = environment
        self.expr = expr
        self.inferred_type = inferred_type
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\nhas type\n  ")]
        message += self.inferred_type.tokens(declarations)
        message += [MESSAGE.emit("\nbut is expected to be a Sort (Type or Prop)")]
        return _error_diagnostic(
            self.declaration, self.name, self.expr,
            "in ", message, declarations,
        )


class W_NotAProp(W_CheckError):
    """
    The type of a theorem is not a proposition (Sort 0).
    """

    def __init__(self, environment, expr, inferred_sort, name=None):
        self.environment = environment
        self.expr = expr
        self.inferred_sort = inferred_sort
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\nhas sort\n  ")]
        message += self.inferred_sort.tokens(declarations)
        message += [MESSAGE.emit(
            "\nbut the type of a theorem must be a proposition (Prop)",
        )]
        return _error_diagnostic(
            self.declaration, self.name, self.expr,
            "in ", message, declarations,
        )


class W_NotAFunction(W_CheckError):
    """
    A non-function expression is being applied to an argument.
    """

    def __init__(self, environment, expr, inferred_type, name=None):
        self.environment = environment
        self.expr = expr
        self.inferred_type = inferred_type
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\nfunction expected, term has type\n  ")]
        message += self.inferred_type.tokens(declarations)
        return _error_diagnostic(
            self.declaration, self.name, self.expr,
            "in ", message, declarations,
        )


class W_HeartbeatError(W_CheckError):
    """
    The heartbeat limit was exceeded while checking a declaration.
    """

    def __init__(self, name, heartbeats, max_heartbeat):
        self.name = name
        self.heartbeats = heartbeats
        self.max_heartbeat = max_heartbeat

    def as_diagnostic(self):
        tokens = [
            PLAIN.emit("in "),
            DECL_NAME.emit(self.name.str()),
        ]
        message = [MESSAGE.emit(
            ":\nheartbeat limit exceeded (%s def_eq calls, limit %s)"
            % (self.heartbeats, self.max_heartbeat),
        )]
        return Diagnostic(tokens, NO_SPAN, message)


class W_UniverseTooHigh(W_CheckError):
    """
    A constructor field's type lives in a universe too high for the inductive.
    """

    def __init__(
        self, environment, ctor_type, field_type,
        field_level, inductive_level, name=None,
    ):
        self.environment = environment
        self.ctor_type = ctor_type
        self.field_type = field_type
        self.field_level = field_level
        self.inductive_level = inductive_level
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\nhas field of type\n  ")]
        message += self.field_type.tokens(declarations)
        message += [
            MESSAGE.emit(
                "\nat universe level %s, but the inductive is at"
                " universe level %s" % (
                    self.field_level.str(),
                    self.inductive_level.str(),
                ),
            ),
        ]
        return _error_diagnostic(
            self.declaration, self.name, self.ctor_type,
            "Invalid constructor ", message, declarations,
        )


@not_rpython
def _public_vars(obj):
    """``vars(obj)`` filtered to public attributes only.

    Used by ``_Item.__eq__`` so that mutable, by-design implementation
    details (inline caches, JIT-relevant state) don't make two otherwise
    equal Lean items compare unequal — comparison reflects the *Lean
    object* the instance represents, not its current cache state.
    """
    return {k: v for k, v in vars(obj).iteritems() if not k.startswith("_")}


class _Item(object):
    """
    A common type for all Lean items.

    The "item" nomenclature comes from the export format documentation (and
    possibly is used elsewhere).

    Don't put any Lean behavior here, it's strictly used to satisfy RPython
    (by making sure all Lean objects have the same base class) and to give Lean
    objects some sane default Python behavior for tests.
    """

    @not_rpython
    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return _public_vars(self) == _public_vars(other)

    @not_rpython
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
        return "<%s%s%s>" % (
            self.__class__.__name__,
            " " if parts else "",
            " ".join(parts),
        )

    def is_named(self, name):
        """Whether this item is a leaf (constant, level parameter) with the given name."""
        return False


def name_with_levels(name, levels):
    pretty = name.str()
    if not levels:
        return pretty
    # FIXME: somehow LEVEL_ZERO needs to do this
    strs = []
    for level in levels:
        each = level.str()
        strs.append(each if each else "0")
    return "%s.{%s}" % (pretty, ", ".join(strs))


def name_with_levels_tokens(name, levels, constants):
    """Produce tokens for a declaration name with optional universe levels."""
    result = name.tokens(constants)
    if levels:
        result.append(PUNCT.emit(".{"))
        for i, level in enumerate(levels):
            if i > 0:
                result.append(PUNCT.emit(", "))
            each = level.str()
            result.append(LEVEL.emit(each if each else "0"))
        result.append(PUNCT.emit("}"))
    return result


@elidable
def name_eq(name, other):
    # FIXME: this duplicates Name.syntactic_eq, but if we remove it and use
    #        that directly, RPython seems unable to be convinced that name and
    #        other are always Names no matter how much I assert.
    #
    # Marked @elidable so the JIT can fold calls to this function at
    # trace-compile time when both arguments are promoted.  This collapses
    # all 14 sequential nat-op comparisons in _try_reduce_nat into constants.
    return name.components == other.components


@specialize.call_location()
def name_dict():
    """A fresh empty `r_dict` keyed by `Name`.

    Both the value annotation AND the hash function need to be
    specialised per call site. RPython merges the arg type of any
    function shared across r_dict instances; if we used a single
    module-level ``_name_hash``, the annotator would widen its arg to
    `_Item` once we had multiple `name_dict()` sites with differing
    value types, and r_dict's hlinvoke would mismatch its callers
    (which always pass `Name`). Defining the eq/hash funcs *inside*
    this call_location-specialised helper gives each call site its
    own pair of function PBCs, breaking the merge.
    """
    from rpython.rlib.objectmodel import r_dict

    def _eq(a, b):
        return a.components == b.components

    def _hash(name):
        return name.hash()

    return r_dict(_eq, _hash)


class Name(_Item):
    def __init__(self, components):
        self.components = components

    def __repr__(self):
        return "`%s" % (self.str(),)

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

    def tokens(self, constants, mark=None, span_holder=None):
        """Return a token list for this name, tagged as a declaration name."""
        return [DECL_NAME.emit(self.str())]

    def has_macro_scopes(self):
        """
        Does this name have hygienic macro scopes?

        A name has macro scopes iff, stripping any trailing numeric components,
        its last component is the string ``_hyg``.

        See ``Lean.Name.hasMacroScopes`` in ``Init.Prelude``.
        """
        for part in reversed(self.components):
            if part == "_hyg":
                return True
            if isinstance(part, int) or (isinstance(part, str) and part.isdigit()):
                continue
            return False
        return False

    def erase_macro_scopes(self):
        """
        Erase macro scopes from this name.

        A hygienic name is encoded as ``<actual-name>._@.<context-and-scopes>._hyg.<scopes>``.
        This method returns everything before the first ``_@`` component.

        See ``Lean.Name.eraseMacroScopes`` in ``Init.Prelude``.
        """
        parts = []
        for part in self.components:
            if part == "_@":
                return Name(parts) if parts else Name.ANONYMOUS
            parts.append(part)
        return self

    def str(self):
        parts = []
        for part in self.components:
            if part == "_@":
                break
            parts.append(part)
        if not parts:
            return "[anonymous]"
        return ".".join([pretty_part(each) for each in parts])

    @elidable
    def hash(self):
        hash_val = 0x345678
        for each in self.components:
            hash_val = (hash_val * 1000003) ^ compute_hash(each)
        return hash_val & 0xFFFFFFFF

    @not_rpython
    def __hash__(self):
        return self.hash()

    def syntactic_eq(self, other):
        return self.components == other.components

    @property
    def is_private(self):
        """
        Is this a private name?

        See `Lean.PrivateName` for Lean's "real" implementation which we try to
        follow here.
        """
        for part in self.components:
            if part == "_private":
                return True
        return False

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

    def app(self, *args):
        """
        Apply this name to the given argument(s).
        """
        return self.const().app(*args)

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

    def constructor(self, type, num_params=0, num_fields=0, cidx=0,
                    levels=None):
        """
        Make a constructor declaration with this name.
        """
        constructor = W_Constructor(
            num_params=num_params,
            num_fields=num_fields,
            cidx=cidx,
        )
        return self.declaration(type=type, w_kind=constructor, levels=levels)

    def inductive(
        self,
        type,
        names=None,
        constructors=None,
        recursors=None,
        num_nested=0,
        num_params=0,
        num_indices=0,
        is_reflexive=False,
        is_recursive=False,
        levels=None,
        ctor_names=None,
    ):
        """
        Make an inductive type declaration with this name.
        """
        inductive = W_Inductive(
            names=[self] if names is None else names,
            constructors=[] if constructors is None else constructors,
            recursors=[] if recursors is None else recursors,
            num_nested=num_nested,
            num_params=num_params,
            num_indices=num_indices,
            is_reflexive=is_reflexive,
            is_recursive=is_recursive,
            ctor_names=ctor_names,
        )
        return self.declaration(type=type, w_kind=inductive, levels=levels)

    def structure(self, type, constructor, levels=None):
        """
        Make a structure declaration with this name.

        Structures are inductive types that have only a single constructor and
        no indices.
        """

        return self.inductive(
            type=type,
            constructors=[constructor],
            num_indices=0,
            levels=levels,
        )

    def definition(self, type, value, hint=1, levels=None):
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
        k=False,
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

    def proj(self, field_index, struct_expr):
        """
        Construct a projection with this name.
        """
        return W_Proj(self, field_index, struct_expr)

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
        self._fvar = None

    def __repr__(self):
        return "<Binder %s>" % (self.name.str())

    def export_info_name(self):
        """The `binderInfo` discriminator string used in `lean4export`'s
        NDJSON encoding of lambda/forall binders."""
        if self.left == "{":
            return "implicit"
        if self.left == "[":
            return "instImplicit"
        if self.left == "⦃":
            return "strictImplicit"
        return "default"

    def to_implicit(self):
        return Binder.implicit(name=self.name, type=self.type)

    def tokens(self, constants, mark=None, span_holder=None):
        result = [PUNCT.emit(self.left)]
        result.append(BINDER_NAME.emit(self.name.str()))
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, self.type, constants, mark)
        result.append(PUNCT.emit(self.right))
        return result

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

        Returns the same FVar each time so that identity comparisons
        work across inference and rendering.
        """
        fvar = self._fvar
        if fvar is None:
            fvar = W_FVar(self)
            self._fvar = fvar
        return fvar

    def bind_fvar(self, fvar, depth):
        return self.with_type(type=self.type.bind_fvar(fvar, depth))

    def incr_free_bvars(self, expr, depth):
        if self.type.loose_bvar_range <= depth:
            return self
        return self.with_type(type=self.type.incr_free_bvars(expr, depth))

    def instantiate(self, expr, depth=0):
        if self.type.loose_bvar_range <= depth:
            return self
        return self.with_type(type=self.type.instantiate(expr, depth))

    def subst_levels(self, subts):
        return self.with_type(type=self.type.subst_levels(subts))

    def syntactic_eq(self, other):
        """
        Check if this binder is syntactically equal to another.
        """
        # TODO - does syntactic equality really care about binder info/name?
        return (
            self.left == other.left
            and syntactic_eq(self.name, other.name)
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

    for c in part:
        if ord(c) > 127 or c.isalnum() or c in "'_":
            continue
        return "«%s»" % (part,)
    return part


def leq(fn):
    def leq(self, other, balance=0):
        if self is other or syntactic_eq(self, other):
            return balance >= 0
        return fn(self, other, balance)

    return leq


# Based on https://github.com/gebner/trepplein/blob/c704ffe81941779dacf9efa20a75bf22832f98a9/src/main/scala/trepplein/level.scala#L100
class W_Level(_Item):
    def emit_to(self, exporter):
        """
        Emit this level as a `lean4export`-format record, returning the
        assigned id. Each non-zero subclass implements; `W_LevelZero`
        is handled directly by `Exporter.level_id` (reserved id 0) and
        never reaches this hook.
        """
        raise NotImplementedError

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

    def imax_leq(self, imax, other, balance):
        """Check imax ≤ other when self is the imax's rhs."""
        return imax.lhs.leq(other, balance) or self.leq(other, balance)

    def imax_gt(self, imax, other, balance):
        """Check other ≤ imax when self is the imax's rhs."""
        return imax.lhs.gt(other, balance) or self.gt(other, balance)

    def max(self, other):
        """
        Return the (simplified) max of this level with another.
        """
        if self is other:
            return self

        if isinstance(other, W_LevelSucc) and syntactic_eq(other.parent, self):
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
        if syntactic_eq(self, W_LEVEL_ZERO.succ()):
            return other
        if isinstance(other, W_LevelSucc) or (
            isinstance(other, W_LevelMax)
            and (
                isinstance(other.lhs, W_LevelSucc) or isinstance(other.rhs, W_LevelSucc)
            )
        ):
            return self.max(other)
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

    def max(self, other):
        return other

    def imax(self, other):
        return other


W_LEVEL_ZERO = W_LevelZero()


class W_LevelSucc(W_Level):
    def __init__(self, parent):
        self.parent = parent

    def __repr__(self):
        joined = " + ".join(str(part) for part in self.pretty_parts() if part)
        return "<Level {}>".format(joined)

    def emit_to(self, exporter):
        parent = exporter.level_id(self.parent)
        lid = exporter.next_level_id()
        exporter.stream.write('{"il":%d,"succ":%d}\n' % (lid, parent))
        return lid

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

    def max(self, other):
        if self is other:
            return self
        if isinstance(other, W_LevelSucc):
            return self.parent.max(other.parent).succ()
        if syntactic_eq(self.parent, other):
            return self
        return W_Level.max(self, other)


class W_LevelMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "<Level max({!r} {!r})>".format(self.lhs, self.rhs)

    def emit_to(self, exporter):
        l = exporter.level_id(self.lhs)
        r = exporter.level_id(self.rhs)
        lid = exporter.next_level_id()
        exporter.stream.write('{"il":%d,"max":[%d,%d]}\n' % (lid, l, r))
        return lid

    @leq
    def leq(self, other, balance):
        return self.lhs.leq(other, balance) and self.rhs.leq(other, balance)

    def gt(self, other, balance):
        return other.leq(self.lhs, balance) or other.leq(self.rhs, balance)

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
        return syntactic_eq(self.lhs, other.lhs) and syntactic_eq(self.rhs, other.rhs)


class W_LevelIMax(W_Level):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "<Level imax({!r} {!r})>".format(self.lhs, self.rhs)

    def emit_to(self, exporter):
        l = exporter.level_id(self.lhs)
        r = exporter.level_id(self.rhs)
        lid = exporter.next_level_id()
        exporter.stream.write('{"il":%d,"imax":[%d,%d]}\n' % (lid, l, r))
        return lid

    @leq
    def leq(self, other, balance):
        return self.rhs.imax_leq(self, other, balance)

    def gt(self, other, balance):
        return self.rhs.imax_gt(self, other, balance)

    def pretty_parts(self):
        lhs, _ = self.lhs.pretty_parts()
        rhs, _ = self.rhs.pretty_parts()
        return "(imax %s %s)" % (lhs, rhs), 0

    def subst_levels(self, substs):
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
        return new_lhs.imax(new_rhs)

    def syntactic_eq(self, other):
        return syntactic_eq(self.lhs, other.lhs) and syntactic_eq(self.rhs, other.rhs)


class W_LevelParam(W_Level):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "<Level {}>".format(self.name.str())

    def emit_to(self, exporter):
        nid = exporter.name_id(self.name)
        lid = exporter.next_level_id()
        exporter.stream.write('{"il":%d,"param":%d}\n' % (lid, nid))
        return lid

    @leq
    def leq(self, other, balance):
        if isinstance(other, W_LevelZero):
            return False

        if isinstance(other, W_LevelParam):
            return balance >= 0 and syntactic_eq(self.name, other.name)
        if isinstance(other, W_LevelMax):
            return self.leq(other.lhs, balance) or self.leq(other.rhs, balance)

        return other.gt(self, -balance)

    def gt(self, other, balance):
        if isinstance(other, W_LevelZero):
            return balance >= 0
        if isinstance(other, W_LevelParam):
            return balance >= 0 and syntactic_eq(self.name, other.name)
        return False

    def pretty_parts(self):
        return self.name.str(), 0

    def syntactic_eq(self, other):
        return syntactic_eq(self.name, other.name)

    def is_named(self, name):
        return self.name.syntactic_eq(name)

    def subst_levels(self, substs):
        return substs.get(self.name, self)

    def imax_leq(self, imax, other, balance):
        """Check imax ≤ other by case-splitting on this param."""
        subst_zero = {self.name: W_LEVEL_ZERO}
        subst_succ = {self.name: self.succ()}
        return (
            imax.subst_levels(subst_zero).leq(
                other.subst_levels(subst_zero), balance,
            )
            and imax.subst_levels(subst_succ).leq(
                other.subst_levels(subst_succ), balance,
            )
        )

    def imax_gt(self, imax, other, balance):
        """Check other ≤ imax by case-splitting on this param."""
        subst_zero = {self.name: W_LEVEL_ZERO}
        subst_succ = {self.name: self.succ()}
        return (
            other.subst_levels(subst_zero).leq(
                imax.subst_levels(subst_zero), balance,
            )
            and other.subst_levels(subst_succ).leq(
                imax.subst_levels(subst_succ), balance,
            )
        )


class W_Expr(_Item):
    def collect_consts_into(self, out, seen):
        """
        Append every `W_Const` name reachable from this expression
        into ``out``, using ``seen`` (a name-keyed dict) to dedup.
        Base case: nothing to collect. Subclasses that hold sub-exprs
        override this to recurse; `W_Const` is the only leaf that adds.
        """

    def emit_to(self, exporter):
        """
        Emit this expression as a `lean4export`-format record, returning
        the assigned id. Each concrete W_Expr subclass implements its
        own record shape; the default raises so that an unimplemented
        variant fails loudly rather than silently producing nothing.
        """
        raise RuntimeError("emit_to: unsupported expression")

    def head(self):
        """
        The head of an application spine.

        For ``f a b c``, returns ``f``. For non-applications, returns self.
        """
        expr = self
        while isinstance(expr, W_App):
            expr = expr.fn
        return expr

    def unapp(self):
        """
        Decompose an application spine into head and reversed arg list.

        For ``f a b c``, returns ``(f, [c, b, a])``. The args are
        reversed because they are peeled outermost-first; callers that
        need left-to-right order should reverse the result.
        """
        args = []
        expr = self
        while isinstance(expr, W_App):
            args.append(expr.arg)
            expr = expr.fn
        return expr, args

    def open_all_binders(self):
        """
        Open all leading forall binders, instantiating each with a fresh fvar.

        Returns ``(fvars, body)``.
        """
        fvars = []
        expr = self
        while isinstance(expr, W_ForAll):
            fvar = expr.binder.fvar()
            fvars.append(fvar)
            expr = expr.body.instantiate(fvar, 0)
        return fvars, expr

    def contains_const(self, name):
        """
        Whether this expression contains a constant with the given name.
        """
        return False

    def _any_subexpr_invalid_index(self, inductive):
        """Recurse into subexpressions for invalid index occurrences."""
        return False

    def is_strictly_positive(self, inductive, env):
        """
        Whether *inductive* occurs only in strictly positive positions.

        A non-positive occurrence is one on the left side of an arrow
        (in the binder type of a ``\u2200``).
        """
        return True

    def app(self, arg, *more):
        """
        Apply this (which better be a function) to the given argument(s).
        """
        expr = W_App(self, arg)
        if not more:
            return expr
        return expr.app(*more)

    def closure(self, env):
        """
        Wrap this expression in a closure that defers ``env``'s substitution.
        """
        if not env:
            return self
        if self.loose_bvar_range == 0:
            return self
        return W_Closure(env, self)

    def _whnf_under_closure(self, closure_env):
        """
        One WHNF step for ``W_Closure(closure_env, self)``.

        Default: the closure has no further effect on this expression
        (e.g. atoms have no bvars to resolve), so emit ``self`` and let
        the outer WHNF loop continue from there.
        """
        return self

    def whnf_with_progress(self, env):
        """
        Reduce this expression to weak head normal form.
        This is the same as W_Expr.whnf, but returns (expr, made_progress)
        where progress is True if we reduced the expression at all, and False otherwise

        Uses an iterative loop with the JIT driver to avoid deep
        recursion and allow the tracing JIT to compile efficient loops.
        """
        expr = self
        made_progress = False
        while True:
            expr_class = expr.__class__
            whnf_jitdriver.jit_merge_point(
                expr_class=expr_class,
                expr=expr,
                env=env,
                made_progress=made_progress,
            )
            env.tracer.whnf_step(expr, env.declarations)
            next = expr._whnf_core(env)
            if next is None:
                return (expr, made_progress)
            expr = next
            made_progress = True

    def whnf(self, env):
        """
        Reduce this expression to weak head normal form.

        Uses an iterative loop with the JIT driver to avoid deep
        recursion and allow the tracing JIT to compile efficient loops.
        """
        (expr, _progress) = self.whnf_with_progress(env)
        return expr

    def _whnf_core(self, env):
        """
        Perform one WHNF reduction step.

        Returns the reduced expression to keep reducing, or None if
        this expression is already in WHNF.
        """
        return None

    def expect_sort(self, env):
        raise W_NotASort(env, self, inferred_type=self, name=None)

    def binder_name(self, index):
        """The name of the ``index``-th binder, or None."""
        expr = self
        i = 0
        while isinstance(expr, W_ForAll):
            if i == index:
                return expr.binder.name.str()
            i += 1
            expr = expr.body
        return None

    def tokens(self, constants, mark=None, span_holder=None):
        """Return a token list for this expression, defaulting to plain text."""
        return [PLAIN.emit(self.str())]


class W_BVar(W_Expr):
    def __init__(self, id):
        self.id = id
        self.loose_bvar_range = id + 1

    def __repr__(self):
        return "<BVar %s>" % (self.id,)

    def str(self):
        return "#%s" % (self.id,)

    def tokens(self, constants, mark=None, span_holder=None):
        return [BINDER_NAME.emit(self.str())]

    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write('{"bvar":%d,"ie":%d}\n' % (self.id, eid))
        return eid

    def syntactic_eq(self, other):
        return self.id == other.id

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth=0):
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

    def closure(self, env):
        if not env:
            return self
        if self.id < len(env):
            return env[self.id]
        return W_BVar(self.id - len(env))

    def _whnf_under_closure(self, closure_env):
        if self.id < len(closure_env):
            return closure_env[self.id]
        return W_BVar(self.id - len(closure_env))


class W_FVar(W_Expr):
    """An FVar which refers to its binder by identity."""

    _counter = count()

    def __init__(self, binder):
        self.id = next(self._counter)
        assert isinstance(binder, Binder)
        self.binder = binder
        self.loose_bvar_range = 0

    def __repr__(self):
        return "<FVar id={} binder={!r}>".format(self.id, self.binder)

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_FVar)
        return self.id == other.id

    def str(self):
        return self.binder.name.str()

    def tokens(self, constants, mark=None, span_holder=None):
        return [BINDER_NAME.emit(self.str())]

    def incr_free_bvars(self, count, depth):
        return self

    def instantiate(self, expr, depth=0):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_FVar)
        return self.id == other.id and syntactic_eq(self.binder, other.binder)

    def infer(self, env):
        """
        A free variable's type comes from the binder's type which it replaced.
        """
        return self.binder.type

    def bind_fvar(self, fvar, depth):
        if self.id == fvar.id:
            return W_BVar(depth)
        return self


class W_LitStr(W_Expr):
    def __init__(self, val):
        assert isinstance(val, str)
        self.val = val
        self.loose_bvar_range = 0

    def __repr__(self):
        return repr(self.val)

    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"strVal":%s}\n' % (eid, exporter.quote(self.val)),
        )
        return eid

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_LitStr)
        return self.val == other.val

    def str(self):
        result = ['"']
        for c in self.val:
            if c == '"':
                result.append('\\"')
            elif c == "\\":
                result.append("\\\\")
            elif c == "\n":
                result.append("\\n")
            elif c == "\t":
                result.append("\\t")
            elif c == "\r":
                result.append("\\r")
            else:
                result.append(c)
        result.append('"')
        return "".join(result)

    def tokens(self, constants, mark=None, span_holder=None):
        """Return a token list tagging this string literal."""
        return [LITERAL.emit(self.str())]

    def build_str_expr(self, env):
        if len(self.val) > 5:
            print("Building large str expr for %s" % self.val[:10])
        Char = Name.simple("Char").const()
        cons = Name(["List", "cons"]).const([W_LEVEL_ZERO]).app(Char)
        expr = Name(["List", "nil"]).const([W_LEVEL_ZERO]).app(Char)
        for i in range(len(self.val) - 1, -1, -1):
            char_expr = Name(["Char", "ofNat"]).app(W_LitNat.char(self.val[i]))
            expr = cons.app(char_expr, expr)
        return Name(["String", "mk"]).app(expr)

    def infer(self, env):
        """
        String literals infer as the constant named String.
        """
        return STRING

    def instantiate(self, expr, depth=0):
        return self

    def subst_levels(self, substs):
        return self

    def bind_fvar(self, fvar, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitStr)
        return self.val == other.val


class W_Sort(W_Expr):
    def __init__(self, level):
        self.level = level
        self.loose_bvar_range = 0

    def __repr__(self):
        # No class name here, as we wouldn't want to see <Sort Type>
        return "<%s>" % (self.str(),)

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_Sort)
        return self.level.eq(other.level)

    def emit_to(self, exporter):
        lid = exporter.level_id(self.level)
        eid = exporter.next_expr_id()
        exporter.stream.write('{"ie":%d,"sort":%d}\n' % (eid, lid))
        return eid

    def tokens(self, constants, mark=None, span_holder=None):
        """Return a token list for this Sort, tagged as a sort."""
        return [SORT.emit(self.str())]

    def str(self):
        """Pretty format this Sort."""
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

    def incr_free_bvars(self, count, depth):
        return self

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth=0):
        return self

    def infer(self, env):
        return self.level.succ().sort()

    def expect_sort(self, env):
        return self.level

    def subst_levels(self, substs):
        return self.level.subst_levels(substs).sort()

    def syntactic_eq(self, other):
        assert isinstance(other, W_Sort)
        return syntactic_eq(self.level, other.level)


PROP = W_LEVEL_ZERO.sort()
TYPE = W_LEVEL_ZERO.succ().sort()


# Takes the level params from 'const', and substitutes them into 'target'
@unroll_safe
def apply_const_level_params(const, target, env):
    # Promote for the same reason as W_Const._whnf_core / try_delta_reduce.
    name = promote(const.name)
    declarations = promote(env.declarations)
    decl = get_decl(declarations, name)
    if len(decl.levels) != len(const.levels):
        raise RuntimeError(
            "W_Const.infer: expected %s levels, got %s"
            % (len(decl.levels), len(const.levels))
        )
    params = decl.levels
    substs = {}
    for i in range(len(params)):
        substs[params[i]] = const.levels[i]
    return target.subst_levels(substs)


class W_Const(W_Expr):
    def __init__(self, name, levels):
        self.name = name
        for each in levels:
            assert isinstance(each, W_Level), "%s is not a W_Level" % (each,)
        self.levels = levels
        self.loose_bvar_range = 0
        # Inline infer cache. References to a constant in a proof term hit
        # the same shared instance (every use of e.g. ``Nat.add`` resolves
        # to one ``W_Const``), so caching on identity is effectively a
        # per-name cache.
        self._infer_cache_result = None

    def __repr__(self):
        return "`%s" % self.str()

    def collect_consts_into(self, out, seen):
        if self.name not in seen:
            seen[self.name] = True
            out.append(self.name)

    def emit_to(self, exporter):
        nid = exporter.name_id(self.name)
        level_ids = [exporter.level_id(l) for l in self.levels]
        eid = exporter.next_expr_id()
        us = "[" + ",".join([str(l) for l in level_ids]) + "]"
        exporter.stream.write(
            '{"const":{"name":%d,"us":%s},"ie":%d}\n' % (nid, us, eid),
        )
        return eid

    def child(self, part):
        """
        A child constant of this one.
        """
        return self.name.child(part).const()

    def contains_const(self, name):
        return self.is_named(name)

    def is_named(self, name):
        return self.name.syntactic_eq(name)

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_Const)
        if len(self.levels) != len(other.levels):
            return False
        for i, level in enumerate(self.levels):
            if not level.eq(other.levels[i]):
                return False
        return True

    def tokens(self, constants, mark=None, span_holder=None):
        """Return a token list for this constant reference."""
        return name_with_levels_tokens(self.name, self.levels, constants)

    def str(self):
        return name_with_levels(self.name, self.levels)

    def syntactic_eq(self, other):
        if not self.name.syntactic_eq(other.name) or len(self.levels) != len(
            other.levels
        ):
            return False
        for i, level in enumerate(self.levels):
            if not syntactic_eq(level, other.levels[i]):
                return False
        return True

    def bind_fvar(self, fvar, depth):
        return self

    def instantiate(self, expr, depth=0):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def _whnf_core(self, env):
        # Promote name and declarations so the JIT can specialise one trace
        # per hot constant and fold the get_decl lookup to a compile-time
        # constant via the @elidable annotation.
        name = promote(self.name)
        declarations = promote(env.declarations)
        if name not in declarations:
            return None
        return self.try_delta_reduce(env)

    def try_delta_reduce(self, env, only_abbrev=False):
        # Promote for the same reason as _whnf_core: lets the JIT fold
        # get_decl (and the second call inside apply_const_level_params)
        # to compile-time constants when this constant is hot.
        name = promote(self.name)
        declarations = promote(env.declarations)
        decl = get_decl(declarations, name)
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
        decl = get_decl(env.declarations, self.name)
        params = decl.levels

        if not params:
            return decl.type

        return apply_const_level_params(self, decl.type, env)

    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    @unroll_safe
    def subst_levels(self, substs):
        new_levels = []
        for level in self.levels:
            new_level = level.subst_levels(substs)
            new_levels.append(new_level)
        return self.name.const(new_levels)


NAT = Name.simple("Nat").const()
NAT_ZERO = NAT.child("zero")
NAT_SUCC = NAT.child("succ")
CHAR = Name.simple("Char").const()
STRING = Name.simple("String").const()

# Names for native nat kernel operations (matching Lean's kernel)
_NAT_NAME = Name.simple("Nat")
_NAT_ADD = _NAT_NAME.child("add")
_NAT_SUB = _NAT_NAME.child("sub")
_NAT_MUL = _NAT_NAME.child("mul")
_NAT_POW = _NAT_NAME.child("pow")
_NAT_GCD = _NAT_NAME.child("gcd")
_NAT_MOD = _NAT_NAME.child("mod")
_NAT_DIV = _NAT_NAME.child("div")
_NAT_BEQ = _NAT_NAME.child("beq")
_NAT_BLE = _NAT_NAME.child("ble")
_NAT_LAND = _NAT_NAME.child("land")
_NAT_LOR = _NAT_NAME.child("lor")
_NAT_XOR = _NAT_NAME.child("xor")
_NAT_SHIFT_LEFT = _NAT_NAME.child("shiftLeft")
_NAT_SHIFT_RIGHT = _NAT_NAME.child("shiftRight")
_NAT_SUCC_NAME = _NAT_NAME.child("succ")

_BOOL_TRUE = Name.simple("Bool").child("true").const()
_BOOL_FALSE = Name.simple("Bool").child("false").const()

# Max exponent for Nat.pow to prevent excessive computation
_REDUCE_POW_MAX_EXP = rbigint.fromint(1 << 24)


def _to_nat_val(expr, env):
    """
    If expr (already WHNF'd) is a nat literal, Nat.zero, or a chain of
    Nat.succ applications on a nat value, return its rbigint value.
    Otherwise return None.

    Iterative to avoid stack overflow on large Nat.succ chains.
    """
    succs = 0
    while True:
        if isinstance(expr, W_LitNat):
            return expr.val.add(rbigint.fromint(succs))
        if isinstance(expr, W_Const):
            if expr.name.syntactic_eq(NAT_ZERO.name):
                return rbigint.fromint(succs)
        if isinstance(expr, W_App):
            head = expr.fn
            if isinstance(head, W_Const) and head.name.syntactic_eq(
                _NAT_SUCC_NAME,
            ):
                succs += 1
                expr = expr.arg.whnf(env)
                continue
        return None


class W_LitNat(W_Expr):
    def __init__(self, val):
        self.val = val
        self.loose_bvar_range = 0

    def __repr__(self):
        return "<LitNat %s>" % (self.val.str(),)

    @staticmethod
    def char(char):
        return W_LitNat(rbigint.fromint(ord(char)))

    @staticmethod
    def int(i):
        return W_LitNat(rbigint.fromint(i))

    @staticmethod
    def long(i):
        return W_LitNat(rbigint.fromlong(i))

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_LitNat)
        return self.val.eq(other.val)

    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"natVal":%s}\n'
            % (eid, exporter.quote(self.val.str())),
        )
        return eid

    def str(self):
        return self.val.str()

    def tokens(self, constants, mark=None, span_holder=None):
        """Return a token list tagging this nat literal."""
        return [LITERAL.emit(self.str())]

    def instantiate(self, expr, depth=0):
        return self

    def subst_levels(self, substs):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitNat)
        return self.val.eq(other.val)

    def build_nat_expr(self):
        if rbigint.fromint(100).lt(self.val):
            print("Building large nat expr for %s" % self.val)
        expr = NAT_ZERO
        i = rbigint.fromint(0)
        while i.lt(self.val):
            expr = NAT_SUCC.app(expr)
            i = i.add(rbigint.fromint(1))
        return expr

    def one_step_constructor(self):
        """
        Expose one Nat constructor: ``Nat.zero`` if the value is zero,
        otherwise ``Nat.succ (W_LitNat (val - 1))``.

        Used by iota reduction so the inductive step sees a concrete
        constructor without materialising the full Nat.succ chain.
        """
        if self.val.eq(rbigint.fromint(0)):
            return NAT_ZERO
        return NAT_SUCC.app(W_LitNat(self.val.sub(rbigint.fromint(1))))

    def bind_fvar(self, fvar, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def infer(self, env):
        """
        Nat literals infer as the constant named Nat.
        """
        return NAT


def _try_reduce_nat(expr, env):
    """
    Try to natively reduce a nat kernel operation.

    Matches the Lean kernel's ``reduce_nat`` function: given an application
    expression, extract the head constant and arguments *without* first
    WHNF-reducing them, then WHNF the arguments to see if they are nat
    literals.  If so, compute the result natively using rbigint.

    Returns a W_LitNat (or Bool constant) on success, None on failure.
    """
    # Collect the application spine (unreduced) to find the head constant
    # and count args.  args are collected in reverse (innermost first).
    target, args = expr.unapp()

    if not isinstance(target, W_Const):
        return None

    # Promote the head name and arg count so the JIT can specialise one
    # trace per head constant and fold all 14 syntactic_eq checks below
    # to compile-time booleans.  For non-nat constants (the common case)
    # every comparison folds to False and the whole function compiles away.
    name = promote(target.name)
    nargs = promote(len(args))

    if nargs == 1:
        # Nat.succ is handled via _to_nat_val instead of here,
        # to avoid converting constructor applications to W_LitNat
        # which would then need build_nat_expr in iota reduction.
        return None

    if nargs != 2:
        return None

    # For binary ops, args[1] is the first argument, args[0] is the second
    # (because we collected them innermost-first).

    # Use name_eq (which is @elidable) so that with a promoted name the JIT
    # folds every comparison to a compile-time constant and removes the whole
    # chain from the hot trace for non-nat constants.
    if name_eq(name, _NAT_ADD):
        return _reduce_bin_nat_op_add(args, env)
    if name_eq(name, _NAT_SUB):
        return _reduce_bin_nat_op_sub(args, env)
    if name_eq(name, _NAT_MUL):
        return _reduce_bin_nat_op_mul(args, env)
    if name_eq(name, _NAT_POW):
        return _reduce_nat_pow(args, env)
    if name_eq(name, _NAT_GCD):
        return _reduce_bin_nat_op_gcd(args, env)
    if name_eq(name, _NAT_MOD):
        return _reduce_bin_nat_op_mod(args, env)
    if name_eq(name, _NAT_DIV):
        return _reduce_bin_nat_op_div(args, env)
    if name_eq(name, _NAT_BEQ):
        return _reduce_bin_nat_pred_beq(args, env)
    if name_eq(name, _NAT_BLE):
        return _reduce_bin_nat_pred_ble(args, env)
    if name_eq(name, _NAT_LAND):
        return _reduce_bin_nat_op_land(args, env)
    if name_eq(name, _NAT_LOR):
        return _reduce_bin_nat_op_lor(args, env)
    if name_eq(name, _NAT_XOR):
        return _reduce_bin_nat_op_xor(args, env)
    if name_eq(name, _NAT_SHIFT_LEFT):
        return _reduce_bin_nat_op_shiftleft(args, env)
    if name_eq(name, _NAT_SHIFT_RIGHT):
        return _reduce_bin_nat_op_shiftright(args, env)

    return None


def _get_bin_nat_args(args, env):
    """
    WHNF both arguments and extract their nat values.

    Returns (v1, v2) as rbigint pair, or (None, None) if either
    argument is not a nat literal.
    """
    arg1 = args[1].whnf(env)
    v1 = _to_nat_val(arg1, env)
    if v1 is None:
        return None, None
    arg2 = args[0].whnf(env)
    v2 = _to_nat_val(arg2, env)
    if v2 is None:
        return None, None
    return v1, v2


def _reduce_bin_nat_op_add(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.add(v2))


def _reduce_bin_nat_op_sub(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v1.lt(v2):
        return W_LitNat(rbigint.fromint(0))
    return W_LitNat(v1.sub(v2))


def _reduce_bin_nat_op_mul(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.mul(v2))


def _reduce_nat_pow(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v2.gt(_REDUCE_POW_MAX_EXP):
        return None
    return W_LitNat(v1.pow(v2))


def _reduce_bin_nat_op_gcd(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    # Euclidean algorithm
    a = v1
    b = v2
    zero = rbigint.fromint(0)
    while b.gt(zero):
        a, b = b, a.mod(b)
    return W_LitNat(a)


def _reduce_bin_nat_op_mod(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v2.eq(rbigint.fromint(0)):
        return W_LitNat(v1)
    return W_LitNat(v1.mod(v2))


def _reduce_bin_nat_op_div(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v2.eq(rbigint.fromint(0)):
        return W_LitNat(rbigint.fromint(0))
    return W_LitNat(v1.div(v2))


def _reduce_bin_nat_pred_beq(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v1.eq(v2):
        return _BOOL_TRUE
    return _BOOL_FALSE


def _reduce_bin_nat_pred_ble(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v1.le(v2):
        return _BOOL_TRUE
    return _BOOL_FALSE


def _reduce_bin_nat_op_land(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.and_(v2))


def _reduce_bin_nat_op_lor(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.or_(v2))


def _reduce_bin_nat_op_xor(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.xor(v2))


def _reduce_bin_nat_op_shiftleft(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.lshift(v2.toint()))


def _reduce_bin_nat_op_shiftright(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return W_LitNat(v1.rshift(v2.toint()))


class W_Proj(W_Expr):
    def __init__(self, struct_name, field_index, struct_expr):
        self.struct_name = struct_name
        self.field_index = field_index
        self.struct_expr = struct_expr
        self.loose_bvar_range = struct_expr.loose_bvar_range

    def contains_const(self, name):
        return self.struct_expr.contains_const(name)

    def collect_consts_into(self, out, seen):
        self.struct_expr.collect_consts_into(out, seen)

    def emit_to(self, exporter):
        sid = exporter.expr_id(self.struct_expr)
        tid = exporter.name_id(self.struct_name)
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"proj":{"idx":%d,"struct":%d,"typeName":%d}}\n'
            % (eid, self.field_index, sid, tid),
        )
        return eid

    def _any_subexpr_invalid_index(self, inductive):
        return inductive._has_invalid_index_occurrence(self.struct_expr)

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_Proj)
        return (
            self.struct_name.syntactic_eq(other.struct_name)
            and self.field_index == other.field_index
            and def_eq(self.struct_expr, other.struct_expr)
        )

    def _field_name(self, constants):
        """The name of the projected field, or its numeric index as a string."""
        decl = constants.get(self.struct_name, None)
        if decl is not None:
            name = decl.w_kind.field_name(self.field_index)
            if name is not None:
                return name
        return "%d" % self.field_index

    def tokens(self, constants, mark=None, span_holder=None):
        # When the struct_expr is the marked expression, widen the span
        # to cover the whole projection (struct_expr + "." + field_name)
        # rather than just the struct_expr alone.
        mark_whole = (
            mark is not None
            and span_holder is not None
            and span_holder[0] == NO_SPAN
            and mark is self.struct_expr
        )
        field_name = self._field_name(constants)
        result = []
        needs_parens = isinstance(self.struct_expr, W_App)
        if needs_parens:
            result.append(PUNCT.emit("("))
        _append_marked_tokens(
            result, span_holder, self.struct_expr, constants,
            None if mark_whole else mark,
        )
        if needs_parens:
            result.append(PUNCT.emit(")"))
        result.append(PUNCT.emit("."))
        result.append(DECL_NAME.emit(field_name))
        if mark_whole:
            span_holder[0] = (0, len(result))
        return result

    def _whnf_core(self, env):
        reduced_struct = self.struct_expr.whnf(env)

        # Try to perform projection reduction (structural iota reduction).
        # If the struct expression reduces to a constructor application,
        # extract the field at the appropriate index.
        head, ctor_args = reduced_struct.unapp()

        if isinstance(head, W_Const):
            decl = get_decl(env.declarations, head.name)
            if isinstance(decl.w_kind, W_Constructor):
                ctor_args.reverse()
                # Constructor args = params ++ fields
                # The field we want is at index num_params + field_index
                idx = decl.w_kind.num_params + self.field_index
                if idx < len(ctor_args):
                    return ctor_args[idx]

        # Projection is stuck but we may have reduced the struct expr.
        if reduced_struct is not self.struct_expr:
            # Replace self with a projection over the reduced struct
            # so that we don't redo the struct reduction if whnf is
            # called again (e.g. from def_eq).  Returning None here
            # tells the loop we are done (self.with_expr returns a
            # new W_Proj which has _whnf_core returning None because
            # the struct_expr is already in WHNF).
            self.struct_expr = reduced_struct
        return None

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return self.with_expr(self.struct_expr.incr_free_bvars(count, depth))

    def bind_fvar(self, fvar, depth):
        return self.with_expr(self.struct_expr.bind_fvar(fvar, depth))

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range <= depth:
            return self
        return self.with_expr(self.struct_expr.instantiate(expr, depth))

    def subst_levels(self, substs):
        return self.with_expr(self.struct_expr.subst_levels(substs))

    def with_expr(self, expr):
        return self.struct_name.proj(self.field_index, expr)

    def _whnf_under_closure(self, closure_env):
        return self.with_expr(self.struct_expr.closure(closure_env))

    def syntactic_eq(self, other):
        return (
            self.struct_name.syntactic_eq(other.struct_name)
            and self.field_index == other.field_index
            and syntactic_eq(self.struct_expr, other.struct_expr)
        )

    def infer(self, env):
        struct_expr_type = self.struct_expr.infer(env).whnf(env)

        # Unfold applications of a base inductive type (e.g. `MyList TypeA TypeB`)
        apps = []
        while isinstance(struct_expr_type, W_App):
            apps.append(struct_expr_type)
            struct_expr_type = struct_expr_type.fn

        try:
            struct_type = get_decl(env.declarations, self.struct_name)
        except KeyError:
            raise InvalidProjection.unknown_structure(
                self.struct_name, self.field_index, self.struct_expr,
            )

        # The base type should be a constant, referring to 'struct_type' (e.g. `MyList`)
        assert isinstance(struct_expr_type, W_Const), (
            "Expected W_Const, got %s" % struct_expr_type
        )
        target_const = get_decl(env.declarations, struct_expr_type.name)
        assert target_const is struct_type, "Expected %s, got %s" % (
            target_const,
            struct_type,
        )

        assert isinstance(struct_type, W_Declaration)
        assert isinstance(struct_type.w_kind, W_Inductive)
        if len(struct_type.w_kind.constructors) != 1:
            raise InvalidProjection.not_a_structure(
                self.struct_name, self.field_index,
                len(struct_type.w_kind.constructors), self.struct_expr,
            )

        ind_type_whnf = apply_const_level_params(
            struct_expr_type, struct_type.type, env
        ).whnf(env)
        is_prop_type = isinstance(ind_type_whnf, W_Sort) and ind_type_whnf.level.eq(
            W_LEVEL_ZERO
        )

        ctor_decl = struct_type.w_kind.constructors[0]
        assert isinstance(ctor_decl, W_Declaration)
        assert isinstance(ctor_decl.w_kind, W_Constructor)

        ctor_type = apply_const_level_params(
            struct_expr_type,
            ctor_decl.type,
            env,
        )

        # apps is collected outermost-first; reversed gives innermost-first order,
        # matching the constructor type's parameter order.
        for app in reversed(apps):
            ctor_type = ctor_type.whnf(env)
            assert isinstance(ctor_type, W_ForAll)
            new_type = ctor_type.body.instantiate(app.arg)
            ctor_type = new_type

        # Fields can depend on earlier fields, so the constructor takes in 'proj'
        # expressions for all of the previous fields ('self.field_idx' is 0-based).
        # For Prop-valued structures, any field that is depended upon by later fields
        # must itself live in Prop (matching the Lean kernel's infer_proj rule).
        i = -1
        for i in range(self.field_index):
            ctor_type = ctor_type.whnf(env)
            if not isinstance(ctor_type, W_ForAll):
                raise InvalidProjection.out_of_bounds(
                    self.struct_name, self.field_index, i + 1,
                    self.struct_expr,
                )
            if ctor_type.body.loose_bvar_range > 0:
                # Later fields depend on this one; for Prop structs the field must be Prop.
                if is_prop_type:
                    field_sort = ctor_type.binder.type.infer(env).whnf(env)
                    if not (
                        isinstance(field_sort, W_Sort)
                        and field_sort.level.eq(W_LEVEL_ZERO)
                    ):
                        raise InvalidProjection.non_prop_field(
                            self.struct_name, self.field_index,
                            self.struct_expr,
                        )
                proj = self.struct_name.proj(i, self.struct_expr)
                ctor_type = ctor_type.body.instantiate(proj)
            else:
                # Non-dependent field: body doesn't refer to it, skip instantiation.
                ctor_type = ctor_type.body

        ctor_type = ctor_type.whnf(env)
        if not isinstance(ctor_type, W_ForAll):
            raise InvalidProjection.out_of_bounds(
                self.struct_name, self.field_index, i + 1, self.struct_expr,
            )

        # For Prop-valued structures the target field itself must live in Prop.
        if is_prop_type:
            field_sort = ctor_type.binder.type.infer(env).whnf(env)
            if not (
                isinstance(field_sort, W_Sort) and field_sort.level.eq(W_LEVEL_ZERO)
            ):
                raise InvalidProjection.non_prop_field(
                    self.struct_name, self.field_index, self.struct_expr,
                )

        return ctor_type.binder.type


def _is_prop_type(expr, constants):
    stack = [expr]
    while stack:
        current = stack.pop()
        if isinstance(current, W_Sort):
            if current.level.eq(W_LEVEL_ZERO):
                return True
        elif isinstance(current, W_FVar):
            stack.append(current.binder.type)
        elif isinstance(current, W_ForAll):
            # imax(sort_of(A), sort_of(B)) = 0 whenever sort_of(B) = 0,
            # so \u2200 (x : A), B is Prop iff B is Prop.
            stack.append(current.body.instantiate(current.binder.fvar()))
        elif isinstance(current, W_Const) and current.name in constants:
            stack.append(constants[current.name].type)
        elif isinstance(current, W_App):
            head, args = current.unapp()
            args.reverse()
            if isinstance(head, W_Const):
                decl = constants.get(head.name, None)
                if decl is not None:
                    val = decl.w_kind.get_delta_reduce_target()
                    if val is not None:
                        # Definition: delta-reduce by applying args to the value.
                        # Apply universe-level substitution from the const's levels.
                        if decl.levels:
                            substs = {}
                            for i in range(len(decl.levels)):
                                substs[decl.levels[i]] = head.levels[i]
                            val = val.subst_levels(substs)
                        # Beta-reduce by applying each arg to the lambda body.
                        for arg in args:
                            if isinstance(val, W_Lambda):
                                val = val.body.instantiate(arg)
                            else:
                                break
                        stack.append(val)
                    else:
                        # Axiom or other non-definition: use type-level reasoning.
                        # The return type after applying all args tells us the sort.
                        decl_type = decl.type
                        for arg in args:
                            if isinstance(decl_type, W_ForAll):
                                decl_type = decl_type.body.instantiate(arg)
                            else:
                                break
                        stack.append(decl_type)
    return False


# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    def __init__(self, binder, body):
        assert body is not None
        assert isinstance(binder, Binder)
        self.binder = binder
        self.body = body
        self.finished_reduce = False
        body_range = body.loose_bvar_range - 1
        if body_range < 0:
            body_range = 0
        binder_range = binder.type.loose_bvar_range
        if binder_range > body_range:
            self.loose_bvar_range = binder_range
        else:
            self.loose_bvar_range = body_range
        # 1-entry inline instantiate cache.
        self._inst_cache_expr = None
        self._inst_cache_depth = -1
        self._inst_cache_result = None
        # Inline infer cache.
        self._infer_cache_result = None
        # 1-entry inline closure cache, keyed on env identity. Critical
        # for DAG-shared lambdas: when ``λ`` appears N times under the
        # same env (e.g. wrap2 lam lam) all N calls return the same
        # ``W_Closure``, preserving the inferred-type cache across
        # references and avoiding exponential blowup.
        self._closure_cache_env = None
        self._closure_cache_result = None

    def closure(self, env):
        if not env:
            return self
        if self.loose_bvar_range == 0:
            return self
        if self._closure_cache_env is env:
            return self._closure_cache_result
        result = W_Closure(env, self)
        self._closure_cache_env = env
        self._closure_cache_result = result
        return result

    def contains_const(self, name):
        return (self.binder.type.contains_const(name)
                or self.body.contains_const(name))

    def collect_consts_into(self, out, seen):
        self.binder.type.collect_consts_into(out, seen)
        self.body.collect_consts_into(out, seen)

    # Subclasses (W_Lambda, W_ForAll) set this to their lean4export tag.
    _export_tag = ""

    def emit_to(self, exporter):
        bnid = exporter.name_id(self.binder.name)
        tid = exporter.expr_id(self.binder.type)
        bid = exporter.expr_id(self.body)
        eid = exporter.next_expr_id()
        bi = self.binder.export_info_name()
        exporter.stream.write(
            '{"%s":{"binderInfo":"%s","body":%d,"name":%d,"type":%d},"ie":%d}\n'
            % (self._export_tag, bi, bid, bnid, tid, eid),
        )
        return eid

    def _any_subexpr_invalid_index(self, inductive):
        return (inductive._has_invalid_index_occurrence(self.binder.type)
                or inductive._has_invalid_index_occurrence(self.body))

    def is_strictly_positive(self, inductive, env):
        """The binder type must not mention any inductive in the block."""
        if inductive._contains_any_inductive(self.binder.type):
            return False
        return self.body.instantiate(self.binder.fvar()).whnf(env).is_strictly_positive(
            inductive, env,
        )

    def def_eq(self, other, def_eq):
        """
        Compare binders and bodies without regard for bound variable names.

        (This is alpha equivalence.)
        """
        assert isinstance(other, W_FunBase)
        if not def_eq(self.binder.type, other.binder.type):
            return False

        fvar = self.binder.fvar()
        body = self.body.instantiate(fvar)
        other_body = other.body.instantiate(fvar)

        return def_eq(body, other_body)

    def _whnf_under_closure(self, closure_env):
        # Closure-of-lambda (or -ForAll) is itself a value in WHNF.
        return None


class W_ForAll(W_FunBase):
    _export_tag = "forallE"

    def infer(self, env):
        return _iter_infer(env, self)

    def _infer_recursive(self, env):
        binder_sort = self.binder.type.infer(env).whnf(env).expect_sort(env)
        body_sort = (
            self.body.instantiate(self.binder.fvar())
            .infer(env)
            .whnf(env)
            .expect_sort(env)
        )
        return binder_sort.imax(body_sort).sort()

    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    def instantiate(self, expr, depth=0):
        return _iter_instantiate(self, expr, depth)

    def syntactic_eq(self, other):
        assert isinstance(other, W_ForAll)
        return syntactic_eq(self.binder, other.binder) and syntactic_eq(
            self.body, other.body
        )

    def bind_fvar(self, fvar, depth):
        return forall(self.binder.bind_fvar(fvar, depth))(
            self.body.bind_fvar(fvar, depth + 1),
        )

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return forall(self.binder.incr_free_bvars(count, depth))(
            self.body.incr_free_bvars(count, depth + 1),
        )

    def subst_levels(self, levels):
        return forall(self.binder.subst_levels(levels))(
            self.body.subst_levels(levels),
        )

    def tokens(self, constants, mark=None, span_holder=None):
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
        lhs_type = self.binder.type
        if isinstance(lhs_type, W_Const):
            lhs_type = constants[lhs_type.name].type
        elif isinstance(lhs_type, W_FVar):
            lhs_type = lhs_type.binder.type

        rhs = self.body.instantiate(self.binder.fvar())
        if (
            not _is_prop_type(lhs_type, constants) and _is_prop_type(rhs, constants)
        ) or (self.body.loose_bvar_range > 0 and _is_prop_type(rhs, constants)):
            result = [KEYWORD.emit("∀"), PLAIN.emit(" ")]
            _append_marked_tokens(
                result, span_holder, self.binder, constants, mark,
            )
            result.append(PUNCT.emit(", "))
            _append_marked_tokens(result, span_holder, rhs, constants, mark)
            return result
        else:
            result = []
            if self.binder.is_default() and not self.body.loose_bvar_range > 0:
                if isinstance(self.binder.type, W_ForAll):
                    result.append(PUNCT.emit("("))
                _append_marked_tokens(
                    result, span_holder, self.binder.type, constants, mark,
                )
                if isinstance(self.binder.type, W_ForAll):
                    result.append(PUNCT.emit(")"))
            elif (
                self.binder.is_instance()
                and not self.body.loose_bvar_range > 0
                and self.binder.name.has_macro_scopes()
            ):
                result.append(PUNCT.emit("["))
                _append_marked_tokens(
                    result, span_holder, self.binder.type, constants, mark,
                )
                result.append(PUNCT.emit("]"))
            else:
                _append_marked_tokens(
                    result, span_holder, self.binder, constants, mark,
                )
            result.append(OPERATOR.emit(" → "))
            _append_marked_tokens(result, span_holder, rhs, constants, mark)
            return result


def group_to_str(group):
    assert not group[-1].is_instance()

    names = " ".join([each.name.str() for each in group])
    if group[-1].is_default():
        return names

    return "%s%s%s" % (group[-1].left, names, group[-1].right)


def _binder_group_tokens(group, constants):
    names = " ".join([binder.name.str() for binder in group])
    if group[-1].is_default():
        return [BINDER_NAME.emit(names)]
    else:
        result = [PUNCT.emit(group[-1].left)]
        for i, binder in enumerate(group):
            if i > 0:
                result.append(PLAIN.emit(" "))
            result.append(BINDER_NAME.emit(binder.name.str()))
        result.append(PUNCT.emit(group[-1].right))
        return result


class W_Lambda(W_FunBase):
    _export_tag = "lam"

    def tokens(self, constants, mark=None, span_holder=None):
        binders = []
        binder_used = []
        current = self
        while isinstance(current, W_Lambda):
            binders.append(current.binder)
            binder_used.append(current.body.loose_bvar_range > 0)
            current = current.body

        result = [KEYWORD.emit("fun"), PLAIN.emit(" ")]

        groups, current_group, last_style = [], [], binders[0].left

        for i, binder in enumerate(binders):
            if binder.is_instance():
                if current_group:
                    result += _binder_group_tokens(current_group, constants)
                    result.append(PLAIN.emit(" "))
                    current_group = []
                if binder_used[i]:
                    result += binder.tokens(constants)
                else:
                    result.append(PUNCT.emit("["))
                    _append_marked_tokens(
                        result, span_holder, binder.type, constants, mark,
                    )
                    result.append(PUNCT.emit("]"))
                if i < len(binders) - 1:
                    result.append(PLAIN.emit(" "))
                last_style = None
            elif binder.left != last_style and current_group:
                result += _binder_group_tokens(current_group, constants)
                result.append(PLAIN.emit(" "))
                current_group, last_style = [binder], binder.left
            else:
                current_group.append(binder)
                last_style = binder.left
        if current_group:
            result += _binder_group_tokens(current_group, constants)

        result.append(OPERATOR.emit(" ↦ "))

        body = current
        for binder in reversed(binders):
            body = body.instantiate(binder.fvar())

        _append_marked_tokens(result, span_holder, body, constants, mark)
        return result

    def syntactic_eq(self, other):
        assert isinstance(other, W_Lambda)
        return syntactic_eq(self.binder, other.binder) and syntactic_eq(
            self.body, other.body
        )

    def bind_fvar(self, fvar, depth):
        return fun(self.binder.bind_fvar(fvar, depth))(
            self.body.bind_fvar(fvar, depth + 1),
        )

    def instantiate(self, expr, depth=0):
        return _iter_instantiate(self, expr, depth)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return fun(self.binder.incr_free_bvars(count, depth))(
            self.body.incr_free_bvars(count, depth + 1),
        )

    def infer(self, env):
        return _iter_infer(env, self)

    def subst_levels(self, substs):
        return fun(self.binder.subst_levels(substs))(
            self.body.subst_levels(substs),
        )


class W_Let(W_Expr):
    def __init__(self, name, type, value, body):
        self.name = name
        self.type = type
        self.value = value
        self.body = body
        body_range = body.loose_bvar_range - 1
        if body_range < 0:
            body_range = 0
        r = type.loose_bvar_range
        vr = value.loose_bvar_range
        if vr > r:
            r = vr
        if body_range > r:
            r = body_range
        self.loose_bvar_range = r

    def contains_const(self, name):
        return (self.type.contains_const(name)
                or self.value.contains_const(name)
                or self.body.contains_const(name))

    def collect_consts_into(self, out, seen):
        self.type.collect_consts_into(out, seen)
        self.value.collect_consts_into(out, seen)
        self.body.collect_consts_into(out, seen)

    def emit_to(self, exporter):
        nid = exporter.name_id(self.name)
        tid = exporter.expr_id(self.type)
        vid = exporter.expr_id(self.value)
        bid = exporter.expr_id(self.body)
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"letE":{"body":%d,"name":%d,"nondep":false,'
            '"type":%d,"value":%d}}\n' % (eid, bid, nid, tid, vid),
        )
        return eid

    def _any_subexpr_invalid_index(self, inductive):
        return (inductive._has_invalid_index_occurrence(self.type)
                or inductive._has_invalid_index_occurrence(self.value)
                or inductive._has_invalid_index_occurrence(self.body))

    def tokens(self, constants, mark=None, span_holder=None):
        fvar = self.name.binder(type=self.type).fvar()
        result = [KEYWORD.emit("let"), PLAIN.emit(" ")]
        result.append(BINDER_NAME.emit(self.name.str()))
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, self.type, constants, mark)
        result.append(OPERATOR.emit(" := "))
        _append_marked_tokens(result, span_holder, self.value, constants, mark)
        result.append(PLAIN.emit("\n"))
        body = self.body.instantiate(fvar)
        _append_marked_tokens(result, span_holder, body, constants, mark)
        return result

    def infer(self, env):
        self.type.infer(env).whnf(env).expect_sort(env)
        # The let's value must match the declared type. Surface a real
        # W_TypeError instead of asserting so malformed exports (like
        # the arena's `constlevels` regression) get cleanly rejected
        # rather than crashing the process.
        inferred_value_type = self.value.infer(env)
        if not env.def_eq(inferred_value_type, self.type):
            raise W_TypeError(
                env, self.value, self.type,
                inferred_type=inferred_value_type,
            )
        body_type = self.body.instantiate(self.value)
        return body_type.infer(env)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range <= depth:
            return self
        return self.name.let(
            type=self.type.instantiate(expr, depth),
            value=self.value.instantiate(expr, depth),
            body=self.body.instantiate(expr, depth + 1),
        )

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return self.name.let(
            type=self.type.incr_free_bvars(count, depth),
            value=self.value.incr_free_bvars(count, depth),
            body=self.body.incr_free_bvars(count, depth + 1),
        )

    def bind_fvar(self, fvar, depth):
        return self.name.let(
            type=self.type.bind_fvar(fvar, depth),
            value=self.value.bind_fvar(fvar, depth),
            body=self.body.bind_fvar(fvar, depth + 1),
        )

    def syntactic_eq(self, other):
        return (
            syntactic_eq(self.name, other.name)
            and syntactic_eq(self.type, other.type)
            and syntactic_eq(self.value, other.value)
            and syntactic_eq(self.body, other.body)
        )

    def _whnf_core(self, env):
        return self.body.instantiate(self.value)

    def subst_levels(self, substs):
        return self.name.let(
            type=self.type.subst_levels(substs),
            value=self.value.subst_levels(substs),
            body=self.body.subst_levels(substs),
        )

    def _whnf_under_closure(self, closure_env):
        # let x := val in body  ⇒  body[x ↦ val], all under closure_env.
        return self.body.closure([self.value]).closure(closure_env)


class W_App(W_Expr):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg
        fn_range = fn.loose_bvar_range
        arg_range = arg.loose_bvar_range
        if fn_range > arg_range:
            self.loose_bvar_range = fn_range
        else:
            self.loose_bvar_range = arg_range
        # 1-entry inline instantiate cache.
        self._inst_cache_expr = None
        self._inst_cache_depth = -1
        self._inst_cache_result = None
        # Inline infer cache.
        self._infer_cache_result = None
        # Inline whnf cache.
        self._whnf_cache_result = None

    def contains_const(self, name):
        return self.fn.contains_const(name) or self.arg.contains_const(name)

    def collect_consts_into(self, out, seen):
        self.fn.collect_consts_into(out, seen)
        self.arg.collect_consts_into(out, seen)

    def emit_to(self, exporter):
        fn = exporter.expr_id(self.fn)
        arg = exporter.expr_id(self.arg)
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"app":{"arg":%d,"fn":%d},"ie":%d}\n' % (arg, fn, eid),
        )
        return eid

    def _any_subexpr_invalid_index(self, inductive):
        return (inductive._has_invalid_index_occurrence(self.fn)
                or inductive._has_invalid_index_occurrence(self.arg))

    def __repr__(self):
        current, args = self.unapp()
        args.reverse()
        return "<W_App fn={!r} args={!r}>".format(current, args)

    def def_eq(self, other, def_eq):
        assert isinstance(other, W_App)
        if isinstance(self.fn, W_FunBase):
            body = self.fn.body.instantiate(self.arg)
            if def_eq(body, other):
                return True
        if isinstance(other.fn, W_FunBase):
            body = other.fn.body.instantiate(other.arg)
            if def_eq(self, body):
                return True
        # Iterative spine walk to avoid stack overflow on deep W_App trees.
        # Collect args from both sides while both fns are W_App, then
        # compare heads and args pairwise via def_eq.
        self_args = []
        other_args = []
        lhs = self
        rhs = other
        while isinstance(lhs, W_App) and isinstance(rhs, W_App):
            self_args.append(lhs.arg)
            other_args.append(rhs.arg)
            lhs = lhs.fn
            rhs = rhs.fn
        if not def_eq(lhs, rhs):
            return False
        if len(self_args) != len(other_args):
            return False
        i = len(self_args) - 1
        while i >= 0:
            if not def_eq(self_args[i], other_args[i]):
                return False
            i -= 1
        return True

    def tokens(self, constants, mark=None, span_holder=None):
        current, args = self.unapp()

        explicit_mask = None
        fn_tokens = None
        if isinstance(current, W_Const):
            decl = constants.get(current.name, None)
            if decl is not None:
                n = len(args)
                mask = []
                decl_type = decl.type
                if decl.levels and current.levels:
                    substs = {}
                    for k in range(len(decl.levels)):
                        substs[decl.levels[k]] = current.levels[k]
                    decl_type = decl_type.subst_levels(substs)
                for j in range(n - 1, -1, -1):
                    if isinstance(decl_type, W_ForAll):
                        mask.append(decl_type.binder.is_default())
                        decl_type = decl_type.body.instantiate(args[j])
                    else:
                        mask.append(True)
                has_implicit = False
                for m in mask:
                    if not m:
                        has_implicit = True
                        break
                if has_implicit:
                    explicit_mask = mask
                    fn_tokens = [DECL_NAME.emit(current.name.str())]

        result = []
        if fn_tokens is None:
            wrap_fn = isinstance(current, W_Lambda)
            if wrap_fn:
                result.append(PUNCT.emit("("))
            _append_marked_tokens(result, span_holder, current, constants, mark)
            if wrap_fn:
                result.append(PUNCT.emit(")"))
        else:
            result = fn_tokens

        n = len(args)
        for idx in range(n - 1, -1, -1):
            arg = args[idx]
            if explicit_mask is not None:
                mask_idx = n - 1 - idx
                if not explicit_mask[mask_idx]:
                    continue
            needs_parens = (
                (idx == 0 and (isinstance(arg, W_App) or isinstance(arg, W_ForAll)))
                or (idx > 0 and (isinstance(arg, W_FunBase) or isinstance(arg, W_App)))
            )
            result.append(PLAIN.emit(" "))
            if needs_parens:
                result.append(PUNCT.emit("("))
            _append_marked_tokens(result, span_holder, arg, constants, mark)
            if needs_parens:
                result.append(PUNCT.emit(")"))

        return result

    def infer(self, env):
        return _iter_infer(env, self)

    def whnf(self, env):
        cached = self._whnf_cache_result
        if cached is not None:
            return cached
        (expr, _progress) = self.whnf_with_progress(env)
        self._whnf_cache_result = expr
        return expr

    def expect_sort(self, env):
        return self.whnf(env).expect_sort(env)

    def syntactic_eq(self, other):
        # Iterative spine walk to avoid stack overflow on deep W_App trees
        lhs = self
        rhs = other
        while isinstance(lhs, W_App) and isinstance(rhs, W_App):
            if not syntactic_eq(lhs.arg, rhs.arg):
                return False
            lhs = lhs.fn
            rhs = rhs.fn
        return syntactic_eq(lhs, rhs)

    _QUOT_LIFT = Name(["Quot", "lift"])
    _QUOT_MK = Name(["Quot", "mk"])

    def try_quot_lift_reduce(self, env):
        """
        Quot.lift {α} {r} {β} f h (Quot.mk {α} r a) ≡ f a
        """
        # Quot.lift needs 6 args, last must be Quot.mk with 3 args.
        head, args = self.unapp()
        if not isinstance(head, W_Const):
            return None
        if not head.name.syntactic_eq(self._QUOT_LIFT):
            return None
        if len(args) != 6:
            return None

        # args are reversed: args[0] is the last arg (the Quot.mk application)
        quot_mk_app = args[0].whnf(env)
        mk_head, mk_args = quot_mk_app.unapp()
        if not isinstance(mk_head, W_Const):
            return None
        if not mk_head.name.syntactic_eq(self._QUOT_MK):
            return None
        if len(mk_args) != 3:
            return None

        # args[5-0]: {α} {r} {β} f h q — f is args[2] (reversed)
        f = args[2]
        # mk_args[2-0]: {α} r a — a is mk_args[0] (reversed)
        a = mk_args[0]
        return f.app(a)

    def try_iota_reduce(self, env):
        target, args = self.unapp()

        if not isinstance(target, W_Const):
            return False, self

        decl = get_decl(env.declarations, target.name)
        if not isinstance(decl.w_kind, W_Recursor):
            return False, self

        if decl.w_kind.num_motives != 1:
            warn(
                "W_App.try_iota_reduce: unimplemented case num_motives != 1 for %s"
                % target.name
            )
            return False, self

        skip_count = (
            decl.w_kind.num_params
            + decl.w_kind.num_indices
            + decl.w_kind.num_minors
            + decl.w_kind.num_motives
        )
        major_idx = len(args) - 1 - skip_count

        # for rec_rule in decl.w_kind.rules:
        #     pass

        # Not enough arguments in our current app - we cannot reduce, since we need to know the major premise
        # to pick the recursor rule to apply
        if major_idx < 0:
            return False, self
        major_premise = args[major_idx].whnf(env)

        # TODO - when checking the declaration, verify that all of the requirements for k-like reduction
        # are met: https://ammkrn.github.io/type_checking_in_lean4/type_checking/reduction.html?highlight=k-li#k-like-reduction
        if decl.w_kind.k == 1:
            # Verify that our major premise type is correct (by checking the whole expression)
            # before we get rid of it
            self.infer(env)

            old_ty = major_premise.infer(env)
            old_ty_base = old_ty.head()
            # The major premise's inferred-type head can be non-W_Const
            # when iota is invoked inside an unfinished def-eq probe
            # against a still-stuck term — observed for `Eq.rec` while
            # checking some Init theorems whose proofs run congruence
            # through chains of `Eq.mpr`. Bail rather than asserting:
            # the caller will treat this app as irreducible, the
            # def-eq attempt fails up the stack, and a real type error
            # surfaces in a context where we can report it.
            if not isinstance(old_ty_base, W_Const):
                return False, self

            # Mutual-inductive blocks legitimately have len(names) > 1;
            # k-like reduction can only operate on a single-inductive
            # context. Same bail-out reasoning.
            if len(decl.w_kind.names) != 1:
                return False, self
            inductive_decl = get_decl(env.declarations, decl.w_kind.names[0])
            assert isinstance(inductive_decl.w_kind, W_Inductive)

            # `_register_mutual_inductive` leaves `constructors=[]`,
            # so k-like for a mutual block's inductive would index out
            # of range. Stay safe.
            if len(inductive_decl.w_kind.constructors) != 1:
                return False, self
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
            # print("Built new major premise: %s" % major_premise_ctor.pretty())
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
        # Expose one constructor (Nat.zero or Nat.succ of W_LitNat predecessor)
        # so iota can fire one step; the predecessor stays a W_LitNat and is only
        # re-expanded lazily on the next WHNF iteration. This avoids materialising
        # an N-deep Nat.succ chain up front for large literals.
        if isinstance(major_premise, W_LitNat):
            major_premise = major_premise.one_step_constructor()

        # If the inductive type has parameters, we need to extract them from the major premise
        # (e.g. the 'p' in 'Decidable.isFalse p')
        # and add then as arguments to the recursor rule application (before the motive)
        major_premise_ctor, all_ctor_args = major_premise.unapp()

        if not isinstance(major_premise_ctor, W_Const):
            return False, self

        all_ctor_args.reverse()
        # TODO - consider storing these by recursor name
        for rec_rule in decl.w_kind.rules:
            if syntactic_eq(rec_rule.ctor_name, major_premise_ctor.name):
                # print("Have num_fields %s and num_params=%s" % (rec_rule.num_fields, decl.w_kind.num_params))uctor.get_type not yet implemented fo
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
                new_app = rec_rule.rhs
                # The rec rule value uses the level parameters from the corresponding inductive type declaration,
                # so apply the parameters from our recursor call
                new_app = apply_const_level_params(target, new_app, env)

                new_args = list(args)
                new_args.reverse()

                total_args = (
                    decl.w_kind.num_params
                    + decl.w_kind.num_motives
                    + decl.w_kind.num_minors
                )
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
                    # print("Adding back extra arg: %s" % new_args[i].pretty())
                    new_app = new_app.app(args[i])
                    i -= 1

                return True, new_app

        return False, self

    # https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#weak-head-normalisation
    def _whnf_core(self, env):
        # Try native nat reduction before any WHNF on subexpressions.
        # This must happen first because WHNF'ing fn would delta-reduce
        # Nat.add etc. into their recursive definitions.
        reduced = _try_reduce_nat(self, env)
        if reduced is not None:
            return reduced

        # Reduce the head by a single step rather than calling
        # whnf_with_progress (which spawns its own JIT-driver loop).
        # Returning a new App here lets the *outer* whnf_with_progress
        # loop iterate over the entire reduction chain — every step
        # goes through the same W_App merge-point, giving the RPython
        # JIT enough iterations to compile a useful trace.
        fn_next = self.fn._whnf_core(env)
        if fn_next is not None:
            return fn_next.app(self.arg)

        # self.fn is now in WHNF.
        fn = self.fn

        # Beta reduction
        if isinstance(fn, W_FunBase):
            return fn.body.instantiate(self.arg)

        # Handle recursor in head position
        iota_progress, reduced = self.try_iota_reduce(env)
        if iota_progress:
            return reduced

        # Quot.lift reduction: Quot.lift {α} {r} {β} f h (Quot.mk {α} r a) ≡ f a
        reduced = self.try_quot_lift_reduce(env)
        if reduced is not None:
            return reduced

        return None

    def bind_fvar(self, fvar, depth):
        return self.fn.bind_fvar(fvar, depth).app(
            self.arg.bind_fvar(fvar, depth),
        )

    def instantiate(self, expr, depth=0):
        return _iter_instantiate(self, expr, depth)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return self.fn.incr_free_bvars(count, depth).app(
            self.arg.incr_free_bvars(count, depth),
        )

    def subst_levels(self, substs):
        return self.fn.subst_levels(substs).app(self.arg.subst_levels(substs))

    def _whnf_under_closure(self, closure_env):
        return self.fn.closure(closure_env).app(self.arg.closure(closure_env))


class W_Closure(W_Expr):
    """
    A deferred substitution: ``body`` evaluated under ``env``.

    Represents the result of substituting ``[bvar(0) ↦ env[0],
    bvar(1) ↦ env[1], ...]`` into ``body``, with bvars at indices
    ``>= len(env)`` shifted down by ``len(env)``. Each entry of
    ``env`` lives in the closure's outer scope (i.e. the scope
    containing the closure itself).
    """

    def __init__(self, env, body):
        self.env = env
        self.body = body
        n = len(env)
        body_outside = body.loose_bvar_range - n
        if body_outside < 0:
            body_outside = 0
        max_loose = body_outside
        for v in env:
            if v.loose_bvar_range > max_loose:
                max_loose = v.loose_bvar_range
        self.loose_bvar_range = max_loose
        self._whnf_cache_result = None
        self._infer_cache_result = None

    def whnf(self, env):
        cached = self._whnf_cache_result
        if cached is not None:
            return cached
        (expr, _progress) = self.whnf_with_progress(env)
        self._whnf_cache_result = expr
        return expr

    def _whnf_core(self, env):
        return self.body._whnf_under_closure(self.env)

    def _whnf_under_closure(self, closure_env):
        # Nested closure: peel inner first, then re-wrap.
        inner_step = self.body._whnf_under_closure(self.env)
        if inner_step is None:
            return None
        return inner_step.closure(closure_env)

    def force(self):
        """
        Materialize the closure-free form by performing the deferred
        substitution eagerly.
        """
        n = len(self.env)
        result = self.body
        # Substitute outermost-first (env[n-1] for bvar(n-1) at depth n-1)
        # down to innermost (env[0] for bvar(0) at depth 0). This keeps
        # already-substituted env entries' free bvars from being
        # over-substituted by later iterations.
        k = n - 1
        while k >= 0:
            result = result.instantiate(self.env[k], k)
            k -= 1
        return result

    def syntactic_eq(self, other):
        return syntactic_eq(self.force(), other)

    def infer(self, env):
        return self.force().infer(env)

    def instantiate(self, expr, depth=0):
        return self.force().instantiate(expr, depth)

    def bind_fvar(self, fvar, depth):
        return self.force().bind_fvar(fvar, depth)

    def incr_free_bvars(self, count, depth):
        return self.force().incr_free_bvars(count, depth)

    def subst_levels(self, substs):
        return self.force().subst_levels(substs)

    def def_eq(self, other, def_eq):
        # Re-dispatch through env.def_eq so the forced LHS gets WHNF'd
        # against ``other`` (which may itself still be a closure).
        return def_eq(self.force(), other)

    def tokens(self, constants, mark=None, span_holder=None):
        return self.force().tokens(constants, mark=mark, span_holder=span_holder)

    def expect_sort(self, env):
        return self.force().expect_sort(env)

    def contains_const(self, name):
        return self.force().contains_const(name)

    def _any_subexpr_invalid_index(self, inductive):
        return self.force()._any_subexpr_invalid_index(inductive)

    def is_strictly_positive(self, inductive, env):
        return self.force().is_strictly_positive(inductive, env)


class W_RecRule(_Item):
    def __init__(self, ctor_name, num_fields, rhs):
        self.ctor_name = ctor_name
        self.num_fields = num_fields
        self.rhs = rhs


class W_Declaration(_Item):
    def __init__(self, name, type, w_kind, levels):
        self.name = name
        self.type = type
        self.w_kind = w_kind
        for each in levels:
            assert isinstance(each, Name), "%s is not a level name" % (each,)
        self.levels = levels

    @property
    def is_private(self):
        """
        Is this a private declaration?
        """
        return self.name.is_private

    def const(self, levels=None):
        """
        Create a constant referring to this declaration by name.
        """
        return self.name.const(levels=levels)

    def const_with_level_params(self):
        """
        Create a constant referring to this declaration at its level params.

        The returned const carries one ``W_LevelParam`` per declared level
        parameter, so substituting the declaration's value through this const
        leaves the value unchanged (the identity reference to this decl).
        """
        levels = []
        for param in self.levels:
            # Narrow the type for RPython's annotator: other classes (e.g.
            # W_Sort) also expose a ``.level`` member, and without this the
            # loop variable would unify to a wider type than Name.
            assert isinstance(param, Name)
            levels.append(param.level())
        return self.name.const(levels=levels)

    def tokens(self, constants, mark=None, span_holder=None):
        """
        Produce a token stream for syntax-highlighted output.

        When ``mark`` is provided, it identifies an expression whose token
        span should be recorded into ``span_holder[0]`` as a
        ``(start_idx, end_idx)`` tuple.
        """
        return self.w_kind.decl_tokens(
            self.name, self.levels, self.type, constants,
            mark=mark, span_holder=span_holder,
        )

    def type_check(self, env):
        try:
            error = self.w_kind.type_check(self.type, env)
        except W_CheckError as error:
            error.name = self.name
            error.declaration = self
            return error
        if error is not None:
            error.name = self.name
            error.declaration = self
        return error


class W_DeclarationKind(_Item):
    # Returns the value associated with this declaration kind.
    # This is the def value for a Definition, and `None` for things like Inductive
    def get_delta_reduce_target(self):
        return None

    def field_name(self, index):
        """The name of the field at ``index``, or None."""
        return None

    def dump_to(self, exporter, decl):
        """Emit ``decl`` as a `lean4export`-format record.

        Default behaviour: emit as an axiom (covers `W_Axiom` and the
        walker's `quotInfo`-as-axiom collapse). Subclasses that need a
        different record shape override.
        """
        exporter.begin_decl(decl)
        exporter.emit_axiom(decl)


#: Reducibility hints. For regular we use positive ints.
HINT_OPAQUE = -2
HINT_ABBREV = -1


class W_Definition(W_DeclarationKind):
    def __init__(self, value, hint):
        self.value = value
        self.hint = hint

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_def(decl, self.value, self.hint)

    def type_check(self, type, env):
        type_type = type.infer(env)
        if not isinstance(type_type.whnf(env), W_Sort):
            return W_NotASort(env, type, inferred_type=type_type, name=None)
        val_type = self.value.infer(env)
        if not env.def_eq(type, val_type):
            return W_TypeError(env, self.value, type, inferred_type=val_type)

    def decl_tokens(self, name, levels, type, constants, mark=None, span_holder=None):
        result = [KEYWORD.emit("def"), PLAIN.emit(" ")]
        result += name_with_levels_tokens(name, levels, constants)
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, type, constants, mark)
        result.append(OPERATOR.emit(" :="))
        if mark is not None:
            result.append(PLAIN.emit("\n  "))
            _append_marked_tokens(result, span_holder, self.value, constants, mark)
        else:
            result += indent(
                [PLAIN.emit("\n")] + self.value.tokens(constants),
                "  ",
            )
        return result

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
        self.hint = HINT_OPAQUE

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_opaque(decl, self.value)

    def get_delta_reduce_target(self):
        return None


class W_Theorem(W_DeclarationKind):
    def __init__(self, value):
        self.value = value

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_thm(decl, self.value)

    def type_check(self, type, env):
        type_type = type.infer(env)
        type_type_whnf = type_type.whnf(env)
        if not isinstance(type_type_whnf, W_Sort):
            return W_NotASort(env, type, inferred_type=type_type, name=None)
        if not type_type_whnf.level.eq(W_LEVEL_ZERO):
            return W_NotAProp(env, type, inferred_sort=type_type_whnf, name=None)
        val_type = self.value.infer(env)
        if not env.def_eq(type, val_type):
            return W_TypeError(env, self.value, type, inferred_type=val_type)

    def decl_tokens(self, name, levels, type, constants, mark=None, span_holder=None):
        result = [KEYWORD.emit("theorem"), PLAIN.emit(" ")]
        result += name_with_levels_tokens(name, levels, constants)
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, type, constants, mark)
        result.append(OPERATOR.emit(" := "))
        _append_marked_tokens(result, span_holder, self.value, constants, mark)
        return result


class W_Axiom(W_DeclarationKind):
    def decl_tokens(self, name, levels, type, constants, mark=None, span_holder=None):
        result = [KEYWORD.emit("axiom"), PLAIN.emit(" ")]
        result += name_with_levels_tokens(name, levels, constants)
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, type, constants, mark)
        return result

    def type_check(self, type, env):
        type_type = type.infer(env)
        if not isinstance(type_type.whnf(env), W_Sort):
            return W_NotASort(env, type, inferred_type=type_type, name=None)


class W_Inductive(W_DeclarationKind):
    def __init__(
        self,
        names,
        constructors,
        recursors,
        num_nested,
        num_params,
        num_indices,
        is_reflexive,
        is_recursive,
        ctor_names=None,
    ):
        self.names = names
        self.constructors = constructors
        self.recursors = recursors
        self.num_nested = num_nested
        self.num_params = num_params
        self.num_indices = num_indices
        self.is_reflexive = is_reflexive
        self.is_recursive = is_recursive
        #: The constructor names in their source-declaration order, as
        #: stored on Lean's `InductiveVal.ctors`. This is authoritative
        #: for "what constructors does this inductive have, in what
        #: order?". `self.constructors` is the same set but as walked
        #: `W_Declaration`s (and is sometimes empty for the FFI walker
        #: path, since ctors arrive as separate `each_constant` items).
        if ctor_names is None:
            ctor_names = [c.name for c in constructors]
        self.ctor_names = ctor_names

    def dump_to(self, exporter, decl):
        # Mark every mutual-block member visited up front so dep walks
        # cycling back through any of them short-circuit before the
        # block emit completes.
        for n in self.names:
            exporter.mark_emitted(n)
        ctor_pairs = []   # [(induct_name, ctor_decl)]
        rec_decls = []
        for n in self.names:
            for cname in exporter.ctors_of(n):
                cd = exporter.decls.get(cname, None)
                if cd is not None:
                    exporter.mark_emitted(cname)
                    ctor_pairs.append((n, cd))
            for rname in exporter.recs_of(n):
                rd = exporter.decls.get(rname, None)
                if rd is not None:
                    exporter.mark_emitted(rname)
                    rec_decls.append(rd)
        # Dep walks in the order lean4export uses: every member's type,
        # then every ctor's type, then every recursor's type plus the
        # rhs of each of its rules.
        for n in self.names:
            d = exporter.decls.get(n, None)
            if d is not None:
                exporter.dump_deps(d.type)
        for (_n, cd) in ctor_pairs:
            exporter.dump_deps(cd.type)
        for rd in rec_decls:
            exporter.dump_deps(rd.type)
            rkind = rd.w_kind
            assert isinstance(rkind, W_Recursor)
            for rule in rkind.rules:
                exporter.dump_deps(rule.rhs)
        exporter.emit_inductive_block(decl, ctor_pairs, rec_decls)

    def field_name(self, index):
        if len(self.constructors) != 1:
            return None
        return self.constructors[0].type.binder_name(self.num_params + index)

    def type_check(self, type, env):
        target = type
        for depth in range(self.num_params + self.num_indices):
            if not isinstance(target, W_ForAll):
                return W_NotASort(env, type, inferred_type=target, name=None)
            target = target.body.instantiate(target.binder.fvar(), depth)
        target_sort = target.whnf(env)
        if not isinstance(target_sort, W_Sort):
            return W_NotASort(
                env, type, inferred_type=target.infer(env), name=None,
            )
        for ctor in self.constructors:
            error = self._check_constructor(ctor, target_sort.level, env)
            if error is not None:
                return error

    def _check_constructor(self, ctor, inductive_level, env):
        """
        Verify a constructor is valid for this inductive.

        Checks the result type, index arguments, universe levels,
        and strict positivity of field types.
        """
        num_params = ctor.w_kind.num_params
        assert num_params >= 0
        ind_name = self.names[0]
        error = W_InvalidConstructorResult(env, ctor.type, name=ctor.name)
        all_fvars, ctor_type = ctor.type.open_all_binders()
        if len(all_fvars) < num_params:
            return error
        param_fvars = all_fvars[:num_params]
        remaining_fvars = all_fvars[num_params:]
        if len(remaining_fvars) != ctor.w_kind.num_fields:
            return W_ConstructorFieldCountMismatch(
                env, ctor.type,
                declared=ctor.w_kind.num_fields,
                actual=len(remaining_fvars),
                name=ctor.name,
            )
        # ctor_type is now the result type, e.g. Ind p1 p2 ... idx1 idx2 ...
        head, rev_args = ctor_type.unapp()
        if not head.is_named(ind_name):
            return error
        if len(head.levels) != len(ctor.levels):
            return error
        for i in range(len(ctor.levels)):
            if not head.levels[i].is_named(ctor.levels[i]):
                return error
        rev_args.reverse()
        if len(rev_args) < num_params:
            return error
        for i in range(num_params):
            if not syntactic_eq(rev_args[i], param_fvars[i]):
                return error
        # Index args must not contain the inductive being defined.
        for i in range(num_params, len(rev_args)):
            if rev_args[i].contains_const(ind_name):
                return error
        # Check field types for invalid occurrences of the inductive.
        for i in range(len(remaining_fvars)):
            field_type = remaining_fvars[i].binder.type
            # Inductive in its own index (e.g. I (I x)).
            if self._has_invalid_index_occurrence(field_type):
                return error
            # Universe level: the field's sort must be ≤ the inductive's.
            # Prop inductives are exempt (their fields can be in any universe).
            field_sort = field_type.infer(env).whnf(env).expect_sort(env)
            if (
                not isinstance(inductive_level, W_LevelZero)
                and not field_sort.leq(inductive_level)
            ):
                return W_UniverseTooHigh(
                    env, ctor.type, field_type,
                    field_level=field_sort,
                    inductive_level=inductive_level,
                    name=ctor.name,
                )
            # Strict positivity: the inductive must not appear in a
            # negative position (left of an arrow).
            if not field_type.whnf(env).is_strictly_positive(self, env):
                # Walk the un-opened type to get the original field
                # expression for diagnostic span marking.
                original = ctor.type
                for _ in range(num_params + i):
                    assert isinstance(original, W_FunBase)
                    original = original.body
                assert isinstance(original, W_FunBase)
                return W_NonPositiveOccurrence(
                    env, original.binder.type,
                    field_number=i + 1,
                    name=ctor.name,
                )

    def _has_invalid_index_occurrence(self, expr):
        """
        Whether *expr* contains an application of this inductive whose
        index arguments themselves contain this inductive.
        """
        ind_name = self.names[0]
        head, rev_args = expr.unapp()
        if head.is_named(ind_name):
            # Check index args (those after the params) for occurrences.
            rev_args.reverse()
            for i in range(self.num_params, len(rev_args)):
                if rev_args[i].contains_const(ind_name):
                    return True
            # Recurse into all args for nested invalid occurrences.
            for i in range(len(rev_args)):
                if self._has_invalid_index_occurrence(rev_args[i]):
                    return True
            return False
        return expr._any_subexpr_invalid_index(self)

    def _contains_any_inductive(self, expr):
        """Whether *expr* mentions any of the inductives in this block."""
        for name in self.names:
            if expr.contains_const(name):
                return True
        return False

    def decl_tokens(self, name, levels, type, constants, mark=None, span_holder=None):
        result = [KEYWORD.emit("inductive"), PLAIN.emit(" ")]
        result += name_with_levels_tokens(name, levels, constants)
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, type, constants, mark)
        for each in self.constructors:
            result.append(PLAIN.emit("\n"))
            inner = [NO_SPAN]
            ctor_tokens = list(
                each.w_kind.constructor_tokens(
                    constructor_name=each.name,
                    type=each.type,
                    inductive=self,
                    constants=constants,
                    mark=mark,
                    span_holder=inner,
                )
            )
            if (
                span_holder is not None
                and span_holder[0] == NO_SPAN
                and inner[0] != NO_SPAN
            ):
                offset = len(result)
                span_holder[0] = (
                    inner[0][0] + offset, inner[0][1] + offset,
                )
            result += ctor_tokens
        return result


class W_Constructor(W_DeclarationKind):
    def __init__(self, num_params, num_fields, cidx=0):
        self.num_params = num_params
        self.num_fields = num_fields
        #: This constructor's index within its parent inductive's
        #: source-order ctor list. From `ConstructorVal.cidx`.
        self.cidx = cidx

    def dump_to(self, exporter, decl):
        induct_name = exporter.parent_inductive(decl.name)
        if induct_name is not None and induct_name in exporter.decls:
            exporter.dump_constant(exporter.decls[induct_name])
            return
        # Unattached ctor (parent inductive wasn't registered) — emit
        # as an axiom so the output stays self-contained.
        exporter.begin_decl(decl)
        exporter.emit_axiom(decl)

    def type_check(self, type, env):
        # TODO - implement type checking
        # This includes checking that num_params and num_fields match the declared ctype
        pass

    def decl_tokens(self, name, levels, type, constants, mark=None, span_holder=None):
        result = [KEYWORD.emit("constructor"), PLAIN.emit(" ")]
        result += name_with_levels_tokens(name, levels, constants)
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, type, constants, mark)
        return result

    def constructor_tokens(
        self, constructor_name, type, inductive, constants,
        mark=None, span_holder=None,
    ):
        name = constructor_name.in_namespace(inductive.names[0])
        result = [PUNCT.emit("| "), DECL_NAME.emit(name.str())]
        if type not in [each.const() for each in inductive.names]:
            result.append(PUNCT.emit(" : "))
            _append_marked_tokens(result, span_holder, type, constants, mark)
        return result


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

    def dump_to(self, exporter, decl):
        # Each mutual-block inductive's `dump_to` emits the whole
        # group (types + ctors + recs). Recursors come back via that
        # path; the standalone recursor visit just routes there.
        for ind in self.names:
            if ind in exporter.decls:
                exporter.dump_constant(exporter.decls[ind])

    def type_check(self, type, env):
        # Shape-level + rhs-head validation. Catches malformed exports
        # where:
        #   - the rec rules don't align with the inductive's ctors
        #     (extra/missing rules, ctor name typos, wrong nfields)
        #   - the rhs body's head isn't the minor for the rule's
        #     constructor (e.g. arena's `nat-rec-rules`: a fabricated
        #     `Nat.rec` succ rule whose body returns the zero-case
        #     minor instead of the succ-case minor).
        #
        # Doesn't catch every wrong-rhs class: a body using the right
        # minor with the wrong args still slips through. Full canonical
        # rhs derivation + def-eq comparison would be a separate piece
        # of work.
        #
        # Skip validation entirely if the parent inductive isn't yet in
        # scope — for the streaming FFI checker, recursors can arrive
        # before their inductive is registered. The check will fire
        # later under the standard (parser-based) flow where inductives
        # are registered in their block before their recursors.
        all_ctors = []
        for ind_name in self.names:
            if ind_name not in env.declarations:
                return None
            ind_decl = env.declarations[ind_name]
            ind_kind = ind_decl.w_kind
            if not isinstance(ind_kind, W_Inductive):
                return W_InvalidRecursorRule(
                    env,
                    "recursor refers to %s which is not an inductive"
                    % ind_name.str(),
                )
            for ctor in ind_kind.constructors:
                all_ctors.append(ctor)
        if len(self.rules) != len(all_ctors):
            return W_InvalidRecursorRule(
                env,
                "recursor has %d rule(s) but its inductive%s has %d "
                "constructor(s)" % (
                    len(self.rules),
                    "s" if len(self.names) > 1 else "",
                    len(all_ctors),
                ),
            )
        # ctor_name → ctor decl, for looking up `num_fields` per rule.
        ctor_by_name = name_dict()
        for ctor in all_ctors:
            ctor_by_name[ctor.name] = ctor
        for rule_idx in range(len(self.rules)):
            rule = self.rules[rule_idx]
            if rule.ctor_name not in ctor_by_name:
                return W_InvalidRecursorRule(
                    env,
                    "rule's ctor %s is not a constructor of "
                    "the inductive" % rule.ctor_name.str(),
                )
            ctor = ctor_by_name[rule.ctor_name]
            ctor_kind = ctor.w_kind
            assert isinstance(ctor_kind, W_Constructor)
            if rule.num_fields != ctor_kind.num_fields:
                return W_InvalidRecursorRule(
                    env,
                    "rule for %s claims %d fields but the ctor has %d"
                    % (rule.ctor_name.str(),
                       rule.num_fields,
                       ctor_kind.num_fields),
                )
            # The minor for this rule is bound at position `rule_idx`
            # in the recursor's minor lambda chain — minor lambdas
            # appear in the same order as `rules`, since both reflect
            # the constructors' source-declaration order.
            error = self._check_rule_rhs_head(env, rule, rule_idx)
            if error is not None:
                return error

    def _check_rule_rhs_head(self, env, rule, ctor_idx):
        """Verify the rule's rhs is `λ params... motives... minors...
        fields... ⇒ minor_c args` — i.e. peeled to its body, its head
        spine is the minor for the corresponding constructor.

        The recursor's iota reduction expects this layout: when the
        rec is applied to `params, motives, minors, c fields`, the
        rhs beta-reduces by feeding those into its outer lambdas,
        leaving the body to apply the right minor to the c-fields
        and the appropriate IHs.
        """
        num_lambdas = (self.num_params + self.num_motives
                       + self.num_minors + rule.num_fields)
        body = rule.rhs
        for _ in range(num_lambdas):
            if not isinstance(body, W_Lambda):
                return W_InvalidRecursorRule(
                    env,
                    "rule for %s rhs has fewer than %d outer "
                    "lambdas (expected one each for params, motives, "
                    "minors, and the ctor's fields)"
                    % (rule.ctor_name.str(), num_lambdas),
                )
            body = body.body
        # Inside the body, after wrapping `fun params, motives, minors,
        # fields ⇒ body`, the minor for ctor at index `ctor_idx` is at
        # bvar position `num_fields + (num_minors - 1 - ctor_idx)` —
        # innermost-binds-lowest puts fields at 0..num_fields-1, then
        # the minors (last minor at num_fields, first at num_fields +
        # num_minors - 1).
        expected_bvar = rule.num_fields + self.num_minors - 1 - ctor_idx
        head = body.head()
        if not isinstance(head, W_BVar) or head.id != expected_bvar:
            return W_InvalidRecursorRule(
                env,
                "rule for %s rhs head is not the corresponding minor "
                "(expected bvar #%d)"
                % (rule.ctor_name.str(), expected_bvar),
            )

    def decl_tokens(self, name, levels, type, constants, mark=None, span_holder=None):
        result = [KEYWORD.emit("recursor"), PLAIN.emit(" ")]
        result += name_with_levels_tokens(name, levels, constants)
        result.append(PUNCT.emit(" : "))
        _append_marked_tokens(result, span_holder, type, constants, mark)
        return result


def syntactic_eq(expr1, expr2):
    """
    Check if two expressions are syntactically equal.
    """
    if expr1 is expr2:
        return True
    if isinstance(expr1, W_Closure):
        expr1 = expr1.force()
    if isinstance(expr2, W_Closure):
        expr2 = expr2.force()
    if expr1.__class__ is not expr2.__class__:
        return False
    return expr1.syntactic_eq(expr2)


class _InferCacheEntry(object):
    """An entry in ``Environment._infer_cache``, keyed by expression identity."""

    def __init__(self, expr, result):
        self.expr = expr
        self.result = result


# Iterative instantiate driver. Same shape as the infer driver below.
class _InstWork(object):
    pass


class _InstVisit(_InstWork):
    def __init__(self, expr, depth):
        self.expr = expr
        self.depth = depth


class _InstBuildApp(_InstWork):
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg


class _InstBuildLambda(_InstWork):
    def __init__(self, binder):
        self.binder = binder


class _InstBuildForAll(_InstWork):
    def __init__(self, binder):
        self.binder = binder


class _InstStore(_InstWork):
    def __init__(self, expr, depth):
        self.expr = expr
        self.depth = depth


def _iter_instantiate(root, expr, depth):
    """
    Iteratively substitute ``expr`` for the bvar at ``depth`` in ``root``.

    Drives the ``W_App`` / ``W_Lambda`` / ``W_ForAll`` alternation through
    an explicit work stack so deeply nested terms (e.g. ``app-lam``) do
    not blow the host stack. Per-instance 1-entry inline cache breaks
    the 2^N work that DAG-shared subexpressions would cause, with no
    dict allocation per call.
    """
    if root.loose_bvar_range <= depth:
        return root
    work = [_InstVisit(root, depth)]
    values = []
    while len(work) > 0:
        item = work.pop()
        if isinstance(item, _InstVisit):
            cur = item.expr
            d = item.depth
            if cur.loose_bvar_range <= d:
                values.append(cur)
                continue
            cls = cur.__class__
            if cls is W_App:
                assert isinstance(cur, W_App)
                if (cur._inst_cache_expr is expr
                        and cur._inst_cache_depth == d):
                    values.append(cur._inst_cache_result)
                    continue
                fn = cur.fn
                arg = cur.arg
                fn_static = fn.loose_bvar_range <= d
                arg_static = arg.loose_bvar_range <= d
                work.append(_InstStore(cur, d))
                work.append(_InstBuildApp(
                    fn if fn_static else None,
                    arg if arg_static else None,
                ))
                if not arg_static:
                    work.append(_InstVisit(arg, d))
                if not fn_static:
                    work.append(_InstVisit(fn, d))
            elif cls is W_Lambda:
                assert isinstance(cur, W_FunBase)
                if (cur._inst_cache_expr is expr
                        and cur._inst_cache_depth == d):
                    values.append(cur._inst_cache_result)
                    continue
                new_binder = cur.binder.instantiate(expr, d)
                work.append(_InstStore(cur, d))
                work.append(_InstBuildLambda(new_binder))
                work.append(_InstVisit(cur.body, d + 1))
            elif cls is W_ForAll:
                assert isinstance(cur, W_FunBase)
                if (cur._inst_cache_expr is expr
                        and cur._inst_cache_depth == d):
                    values.append(cur._inst_cache_result)
                    continue
                new_binder = cur.binder.instantiate(expr, d)
                work.append(_InstStore(cur, d))
                work.append(_InstBuildForAll(new_binder))
                work.append(_InstVisit(cur.body, d + 1))
            else:
                values.append(cur.instantiate(expr, d))
        elif isinstance(item, _InstBuildApp):
            if item.arg is None:
                arg = values.pop()
            else:
                arg = item.arg
            if item.fn is None:
                fn = values.pop()
            else:
                fn = item.fn
            values.append(fn.app(arg))
        elif isinstance(item, _InstBuildLambda):
            body = values.pop()
            values.append(W_Lambda(item.binder, body))
        elif isinstance(item, _InstBuildForAll):
            body = values.pop()
            values.append(W_ForAll(item.binder, body))
        else:
            assert isinstance(item, _InstStore)
            res = values[len(values) - 1]
            item.expr._inst_cache_expr = expr
            item.expr._inst_cache_depth = item.depth
            item.expr._inst_cache_result = res
    return values[0]


# Iterative infer driver. The work stack carries items of the following
# kinds; pushes use LIFO ordering so the bottom of the stack runs last.
class _InferWork(object):
    pass


class _InferVisit(_InferWork):
    def __init__(self, expr):
        self.expr = expr


class _InferAppStep(_InferWork):
    """One arg in an application spine.

    ``head`` is the spine origin (the leftmost expression) and ``args`` is
    the immutable, outermost-first list of arguments; ``j`` is the index
    of *this* step's argument. We carry the triple instead of a
    pre-built ``spine_so_far`` so ``_iter_infer`` doesn't allocate ``N``
    intermediate ``W_App``s per application — those would only be read
    for the rare error-diagnostic case, and we can rebuild the spine
    on demand there.
    """

    def __init__(self, head, args, j):
        self.head = head
        self.args = args
        self.j = j

    def arg(self):
        return self.args[self.j]

    def spine_so_far(self):
        spine = self.head
        i = len(self.args) - 1
        while i > self.j:
            spine = spine.app(self.args[i])
            i -= 1
        return spine


class _InferBindLambda(_InferWork):
    def __init__(self, binder, fvar):
        self.binder = binder
        self.fvar = fvar


class _InferBindForAll(_InferWork):
    def __init__(self, binder_sort):
        self.binder_sort = binder_sort


class _InferStore(_InferWork):
    def __init__(self, expr):
        self.expr = expr


def _iter_infer(env, root):
    """
    Iteratively infer the type of ``root`` for the recursive expression
    constructors (``W_App``, ``W_Lambda``, ``W_ForAll``).

    Avoids the mutual recursion between ``W_App.infer`` and
    ``W_Lambda.infer`` that grows the host stack linearly with the
    nesting depth (e.g. ~4000 levels in ``app-lam.ndjson``). Other
    expression types fall back to their recursive ``infer``.

    Reuses ``env._infer_cache`` so DAG-shared subexpressions are
    inferred only once.
    """
    work = [_InferVisit(root)]
    values = []
    while len(work) > 0:
        item = work.pop()
        if isinstance(item, _InferVisit):
            cur = item.expr
            cls = cur.__class__
            # Cache lookup. Recursive types (App/Lambda/ForAll/Closure)
            # keep a per-instance inline result; non-recursive expression
            # types are passed through env.infer (which has its own cache
            # fallback) and pushed straight onto the value stack.
            if (cls is W_App or cls is W_Lambda or cls is W_ForAll
                    or cls is W_Closure):
                cached = cur._infer_cache_result
                if cached is not None:
                    values.append(cached)
                    continue
            else:
                values.append(env.infer(cur))
                continue
            if cls is W_Lambda:
                assert isinstance(cur, W_FunBase)
                cur.binder.type.infer(env).whnf(env).expect_sort(env)
                fvar = cur.binder.fvar()
                body_with_fvar = cur.body.closure([fvar])
                work.append(_InferStore(cur))
                work.append(_InferBindLambda(cur.binder, fvar))
                work.append(_InferVisit(body_with_fvar))
            elif cls is W_ForAll:
                assert isinstance(cur, W_FunBase)
                binder_sort = cur.binder.type.infer(env).whnf(env).expect_sort(env)
                fvar = cur.binder.fvar()
                body_with_fvar = cur.body.closure([fvar])
                work.append(_InferStore(cur))
                work.append(_InferBindForAll(binder_sort))
                work.append(_InferVisit(body_with_fvar))
            elif cls is W_App:
                assert isinstance(cur, W_App)
                target, args = cur.unapp()
                # Process: VISIT(target), then for each arg outermost-first,
                # VISIT(arg) then APP_STEP. args is innermost-first; pushing
                # in increasing index puts the outermost on top after LIFO.
                work.append(_InferStore(cur))
                k = 0
                n = len(args)
                while k < n:
                    work.append(_InferAppStep(target, args, k))
                    work.append(_InferVisit(args[k]))
                    k += 1
                work.append(_InferVisit(target))
            elif cls is W_Closure:
                assert isinstance(cur, W_Closure)
                inner = cur.body
                closure_env = cur.env
                inner_cls = inner.__class__
                if inner_cls is W_App:
                    assert isinstance(inner, W_App)
                    # Push the closure through to the App's pieces.
                    new_app = inner.fn.closure(closure_env).app(
                        inner.arg.closure(closure_env),
                    )
                    work.append(_InferStore(cur))
                    work.append(_InferVisit(new_app))
                elif inner_cls is W_Lambda or inner_cls is W_ForAll:
                    assert isinstance(inner, W_FunBase)
                    # Open the binder while keeping body shared. The
                    # new env extends the closure's env with a fresh
                    # fvar at position 0 (innermost).
                    new_binder_type = inner.binder.type.closure(closure_env)
                    new_binder_type.infer(env).whnf(env).expect_sort(env)
                    if new_binder_type is inner.binder.type:
                        new_binder = inner.binder
                    else:
                        new_binder = inner.binder.with_type(type=new_binder_type)
                    fvar = new_binder.fvar()
                    new_env = [fvar]
                    for v in closure_env:
                        new_env.append(v)
                    body_with_fvar = inner.body.closure(new_env)
                    work.append(_InferStore(cur))
                    if inner_cls is W_Lambda:
                        work.append(_InferBindLambda(new_binder, fvar))
                    else:
                        binder_sort = new_binder_type.infer(env).whnf(env).expect_sort(env)
                        work.append(_InferBindForAll(binder_sort))
                    work.append(_InferVisit(body_with_fvar))
                else:
                    # Atoms / BVar / Let / Proj / nested Closure: fall back
                    # to forcing.
                    values.append(env.infer(cur))
            else:
                values.append(cur.infer(env))
        elif isinstance(item, _InferAppStep):
            arg_type = values.pop()
            fn_type_base = values.pop()
            fn_type = fn_type_base.whnf(env)
            if isinstance(fn_type, W_Closure):
                fn_type = fn_type.force()
            arg = item.arg()
            if not isinstance(fn_type, W_ForAll):
                raise W_NotAFunction(
                    env, item.spine_so_far(), inferred_type=fn_type_base,
                )
            if not env.def_eq(fn_type.binder.type, arg_type):
                raise W_TypeError(
                    env, arg, fn_type.binder.type,
                    inferred_type=arg_type,
                )
            values.append(fn_type.body.instantiate(arg))
        elif isinstance(item, _InferBindLambda):
            body_type = values.pop()
            body_type = body_type.bind_fvar(item.fvar, 0)
            values.append(forall(item.binder)(body_type))
        elif isinstance(item, _InferBindForAll):
            body_sort = values.pop().whnf(env).expect_sort(env)
            values.append(item.binder_sort.imax(body_sort).sort())
        else:
            assert isinstance(item, _InferStore)
            item.expr._infer_cache_result = values[len(values) - 1]
    return values[0]


class Telescope(object):
    def __init__(self, *binders):
        assert len(binders) > 0
        self._binders = list(binders)

    def forall(self, body):
        forall = W_ForAll(self._binders[-1], body)
        for binder in reversed(self._binders[:-1]):
            forall = W_ForAll(binder, forall)
        return forall

    def fun(self, body):
        fun = W_Lambda(self._binders[-1], body)
        for binder in reversed(self._binders[:-1]):
            fun = W_Lambda(binder, fun)
        return fun


def forall(*binders):
    return Telescope(*binders).forall


def fun(*binders):
    return Telescope(*binders).fun
