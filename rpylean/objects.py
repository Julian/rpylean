from rpython.rlib.jit import (
    dont_look_inside, elidable, promote, unroll_safe,
)
from rpython.rlib.objectmodel import (
    always_inline, compute_hash, dont_inline, instantiate, newlist_hint,
    not_rpython, r_dict, specialize, we_are_translated,
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
from rpylean import _format
from rpylean.exceptions import (
    InvalidProjection,
    UnknownDeclaration,
    W_Error,
)


#: A declaration's `DefinitionSafety`. Ordered by how much a declaration
#: is trusted to do: one may use exactly the constants whose safety is
#: at most its own, so a safe declaration never rests on a partial or
#: unsafe one and a partial declaration never rests on an unsafe one.
SAFETY_SAFE = 0
SAFETY_PARTIAL = 1
SAFETY_UNSAFE = 2


def _safety_of(is_unsafe):
    return SAFETY_UNSAFE if is_unsafe else SAFETY_SAFE


_CACHE_GEN_LIMIT = 1 << 31


class _CacheGen(object):
    _attrs_ = ['count']

    def __init__(self):
        self.count = 0


_CACHE_GEN = _CacheGen()


@always_inline
def _next_cache_gen():
    g = _CACHE_GEN.count + 1
    if g < _CACHE_GEN_LIMIT:
        _CACHE_GEN.count = g
        return g
    return -1


def get_decl(declarations, name):
    """
    Look up a declaration by name.

    This is a hot path during type checking — called for every constant.
    The name-side inline cache (`Name._decl_dict` / `_decl_cached`)
    answers repeat lookups with two field reads instead of the r_dict
    probe (whose custom hash/eq run through indirect calls).
    """
    if name._decl_dict is declarations:
        return name._decl_cached
    try:
        decl = _get_decl(declarations, name)
    except KeyError:
        decl = _demand_decl(declarations, name)
    name._decl_dict = declarations
    name._decl_cached = decl
    return decl


@elidable
def _get_decl(declarations, name):
    return declarations[name]


@dont_look_inside
def _demand_decl(declarations, name):
    """
    Miss path for `get_decl`: ask the installed `Resolver` (if any) to
    demand-load `name`, then re-read the dict.

    Kept outside the `@elidable` inner so the fast path stays foldable:
    a name misses at most once — after the resolver registers it the
    binding is immutable, the same effective-purity argument the
    streaming parser's append-only dict already relies on. The fresh
    dict read (rather than trusting `_get_decl`'s raise) also keeps
    this correct if the JIT baked a miss into a trace.
    """
    if name not in declarations:
        resolver = _RESOLVER.current
        if resolver is not None:
            resolver.resolve(name)
    if name not in declarations:
        raise UnknownDeclaration(name)
    return declarations[name]


def find_decl(declarations, name):
    """
    `get_decl`, but with a `None` miss instead of an `UnknownDeclaration`.

    For "classify this constant" probes (is it a recursor? is it
    delta-reducible?) which bail out of a reduction strategy when the
    name is absent — routing them through `get_decl` keeps them
    demand-loading under `ffi check`, where a raw `.get` would
    misclassify a merely not-yet-walked constant.
    """
    try:
        return get_decl(declarations, name)
    except UnknownDeclaration:
        return None


class Resolver(object):
    """
    Demand-loads declarations that a `get_decl` lookup missed.

    Installed via `set_resolver` when a backing store can produce
    declarations the environment hasn't registered yet — `ffi check`'s
    hash-ordered bucket walk being the motivating case. `resolve`
    registers the named declaration when the store has it and returns
    nothing either way; the caller re-reads the dict afterwards and
    raises `KeyError` if the name is still absent.
    """

    _attrs_ = []

    def resolve(self, name):
        raise NotImplementedError


class _ResolverHolder(object):
    def __init__(self):
        self.current = None


_RESOLVER = _ResolverHolder()


def set_resolver(resolver):
    """
    Install the `Resolver` consulted on declaration-lookup misses, or
    uninstall it by passing `None`.
    """
    _RESOLVER.current = resolver


class W_CheckError(W_Error):
    """
    Base class for type-checking errors returned by type_check.
    """

    _attrs_ = ['name', 'declaration']

    name = None
    declaration = None

    def as_diagnostic(self):
        """Return this error as a ``Diagnostic``."""
        raise NotImplementedError

    def tokens(self):
        """Return a flat token list (without caret spans)."""
        _RENDER_BUDGET.remaining = _DIAGNOSTIC_RENDER_LIMIT
        d = self.as_diagnostic()
        _RENDER_BUDGET.remaining = -1
        return d.tokens + d.message

    def __str__(self):
        return FORMAT_PLAIN(self.tokens())

    def write_to(self, writer):
        """Write this error as a diagnostic with caret underlines."""
        _RENDER_BUDGET.remaining = _DIAGNOSTIC_RENDER_LIMIT
        d = self.as_diagnostic()
        _RENDER_BUDGET.remaining = -1
        writer.writeline_diagnostic(d)


class _RenderBudget(object):
    """
    A walk bound for diagnostic rendering.

    `to_format()` un-shares the expression DAG: every occurrence of a
    shared subterm is walked again, so rendering a failing
    declaration whose value is a heavily-shared reduction product can
    take effectively forever (a Mathlib `CategoryTheory.Quotient`
    def_eq error spent an hour of GC-bound walking before being
    killed) — and none of it ticks the wall-time guard. Diagnostic
    entry points arm the budget; `_sub` spends one
    unit per subexpression visit and cuts the walk off with an
    ellipsis when it runs out. `remaining == -1` means unlimited (the
    REPL / `dump` paths, where the caller asked for the full term).
    """

    _attrs_ = ['remaining']

    def __init__(self):
        self.remaining = -1


_RENDER_BUDGET = _RenderBudget()

#: Subexpression visits allowed per rendered diagnostic — generous
#: enough for the megabyte-scale statements BVDecide lemmas print,
#: while bounding the un-shared walk.
_DIAGNOSTIC_RENDER_LIMIT = 200000


class _Marker(object):
    """
    Tracks the sub-expression whose rendered span should be reported.

    ``mark`` is the expression (by identity, or for a free variable by
    binding position) to locate when building a ``Format``; ``found``
    records whether the (first) occurrence has been wrapped already.
    Hash-consing means the same interned sub-expression can appear at
    many syntactic positions, so we wrap only the first one seen in
    source order -- the caret then lands where a reader would look for
    it.  A ``mark`` of ``None`` matches nothing.
    """

    _attrs_ = ['mark', 'found']

    def __init__(self, mark):
        self.mark = mark
        self.found = False

    def matches(self, expr):
        mark = self.mark
        if mark is expr:
            return True
        if isinstance(mark, W_FVar) and isinstance(expr, W_FVar):
            return mark.id == expr.id
        return False


#: Shared marker for the common no-mark case (its ``found`` is never set,
#: since a ``None`` mark matches nothing).
_NO_MARK = _Marker(None)


def _marker_for(mark):
    if mark is None:
        return _NO_MARK
    return _Marker(mark)


def _tokens_from_format(fmt, span_holder):
    """
    Render ``fmt`` to a flat token list, recording any marked span.

    ``span_holder``, when given, is a one-element list whose slot is set to
    the ``(start, end)`` token-index range covered by the marked
    sub-expression (see :class:`_Marker`).
    """
    tokens, span = _format.render(fmt, _format.RENDER_WIDTH.width)
    if span_holder is not None and span != NO_SPAN and span_holder[0] == NO_SPAN:
        span_holder[0] = span
    return tokens


def _sub(marker, expr, constants):
    """
    Build the ``Format`` for the child ``expr``, threading diagnostics.

    Spends one unit of the diagnostic render budget per visit, cutting the
    walk off with an ellipsis when it runs out, and wraps the first
    occurrence of ``marker.mark`` in a span tag.  ``expr`` is anything with
    a ``to_format(constants, marker)`` method -- a ``W_Expr`` or ``Binder``.
    """
    budget = _RENDER_BUDGET
    if budget.remaining == 0:
        return _format.NIL
    if budget.remaining > 0:
        budget.remaining -= 1
        if budget.remaining == 0:
            return _format.text(MESSAGE, " …⟨diagnostic truncated⟩")
    if marker.mark is not None and not marker.found and marker.matches(expr):
        marker.found = True
        return _format.tag(_format.MARK_TAG, expr.to_format(constants, marker))
    return expr.to_format(constants, marker)


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

    _attrs_ = ['environment', 'term', 'expected_type', 'inferred_type']

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

    _attrs_ = ['environment', 'ctor_type']

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


class W_InvalidQuotient(W_CheckError):
    """
    A quotient declaration does not match Lean's fixed quotient signatures
    or prerequisites.
    """

    _attrs_ = ['environment', 'reason', 'quot_type']

    def __init__(self, environment, reason, quot_type, name=None):
        self.environment = environment
        self.reason = reason
        self.quot_type = quot_type
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit("\n" + self.reason)]
        return _error_diagnostic(
            self.declaration, self.name, self.quot_type,
            "Invalid quotient ", message, declarations,
        )


class W_ConstructorFieldCountMismatch(W_CheckError):
    """
    A constructor's declared num_fields does not match its type's binders.
    """

    _attrs_ = ['environment', 'ctor_type', 'declared', 'actual']

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

    _attrs_ = ['environment', 'summary']

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


class W_NotYetDeclared(W_CheckError):
    """
    A declaration uses a constant not declared before it: a later
    declaration, or itself.
    """

    _attrs_ = ['environment', 'const']

    def __init__(self, environment, const, name=None):
        self.environment = environment
        self.const = const
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        message = [MESSAGE.emit(
            "\n`%s` is not yet declared" % (self.const.name.str(),),
        )]
        return _error_diagnostic(
            self.declaration, self.name, self.const,
            "Invalid declaration ", message, declarations,
        )


class W_UnsafeReference(W_CheckError):
    """
    A declaration uses a constant less safe than itself: a safe one
    uses something partial or unsafe, or a partial one uses something
    unsafe.
    """

    _attrs_ = ['environment', 'const', 'target_safety']

    def __init__(self, environment, const, target_safety, name=None):
        self.environment = environment
        self.const = const
        self.target_safety = target_safety
        self.name = name

    def as_diagnostic(self):
        declarations = self.environment.declarations
        target = self.const.name.str()
        if self.target_safety == SAFETY_UNSAFE:
            summary = (
                "\n`%s` is unsafe; only an unsafe declaration may use it"
                % (target,)
            )
        else:
            summary = (
                "\n`%s` is partial; a safe declaration may not use it"
                % (target,)
            )
        message = [MESSAGE.emit(summary)]
        return _error_diagnostic(
            self.declaration, self.name, self.const,
            "Invalid declaration ", message, declarations,
        )


class W_NonPositiveOccurrence(W_CheckError):
    """
    A constructor field type has the inductive in a non-positive position.
    """

    _attrs_ = ['environment', 'field_type', 'field_number']

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

    _attrs_ = ['environment', 'expr', 'inferred_type']

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

    _attrs_ = ['environment', 'expr', 'inferred_sort']

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

    _attrs_ = ['environment', 'expr', 'inferred_type']

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


class W_DeepRecursion(W_CheckError):
    """
    Checking the declaration nested deeper than the stack allows.
    """

    _attrs_ = ['operation']

    def __init__(self, operation, name=None):
        #: What was recursing: the machine operation that ran out of stack.
        self.operation = operation
        self.name = name

    def as_diagnostic(self):
        tokens = []
        if self.name is not None:
            tokens = [PLAIN.emit("in "), DECL_NAME.emit(self.name.str())]
        message = [MESSAGE.emit(
            ":\ndeep recursion detected (in %s)" % self.operation,
        )]
        return Diagnostic(tokens, NO_SPAN, message)


class W_WallTimeError(W_CheckError):
    """
    The per-declaration wall-time limit was exceeded.
    """

    _attrs_ = ['elapsed', 'max_wall_time']

    def __init__(self, name, elapsed, max_wall_time):
        self.name = name
        self.elapsed = elapsed
        self.max_wall_time = max_wall_time

    def as_diagnostic(self):
        tokens = [
            PLAIN.emit("in "),
            DECL_NAME.emit(self.name.str()),
        ]
        message = [MESSAGE.emit(
            ":\nwall-time limit exceeded (%fs elapsed, limit %fs)"
            % (self.elapsed, self.max_wall_time),
        )]
        return Diagnostic(tokens, NO_SPAN, message)


class W_MemoryError(W_CheckError):
    """
    The per-declaration memory limit was exceeded.
    """

    _attrs_ = ['used', 'max_memory']

    def __init__(self, name, used, max_memory):
        self.name = name
        self.used = used
        self.max_memory = max_memory

    def as_diagnostic(self):
        tokens = [
            PLAIN.emit("in "),
            DECL_NAME.emit(self.name.str()),
        ]
        message = [MESSAGE.emit(
            ":\nmemory limit exceeded (%d MB, limit %d MB)"
            % (self.used // (1024 * 1024),
               self.max_memory // (1024 * 1024)),
        )]
        return Diagnostic(tokens, NO_SPAN, message)


class W_UniverseTooHigh(W_CheckError):
    """
    A constructor field's type lives in a universe too high for the inductive.
    """

    _attrs_ = [
        'environment', 'ctor_type', 'field_type',
        'field_level', 'inductive_level',
    ]

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

    _attrs_ = []

    def get_binder(self):
        raise NotImplementedError

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


def name_with_levels_format(name, levels, constants):
    """A ``Format`` for a declaration name with optional universe levels."""
    result = _format.text(DECL_NAME, name.user_name().str())
    if levels:
        result = _format.append(result, _format.text(PUNCT, ".{"))
        for i, level in enumerate(levels):
            if i > 0:
                result = _format.append(result, _format.text(PUNCT, ", "))
            each = level.str()
            result = _format.append(
                result, _format.text(LEVEL, each if each else "0"),
            )
        result = _format.append(result, _format.text(PUNCT, "}"))
    return result


def _decl_signature_format(keyword, name, levels, type, constants, marker):
    """A ``Format`` for ``<keyword> <name> : <type>`` (no value)."""
    return _format.concat([
        _format.text(KEYWORD, keyword),
        _format.text(PLAIN, " "),
        name_with_levels_format(name, levels, constants),
        _format.text(PUNCT, " : "),
        _sub(marker, type, constants),
    ])


def _decl_with_value_format(keyword, name, levels, type, value,
                            constants, marker):
    """
    A ``Format`` for ``<keyword> <name> : <type> := <value>``.

    The value always begins on its own line, indented by 2, matching Lean's
    ``declValSimple`` (``" :=" >> ppHardLineUnlessUngrouped >> declBody``),
    whose ``ppHardLineUnlessUngrouped`` is a mandatory newline in the
    (grouped) declaration context.
    """
    head = _format.concat([
        _format.text(KEYWORD, keyword),
        _format.text(PLAIN, " "),
        name_with_levels_format(name, levels, constants),
        _format.text(PUNCT, " : "),
        _sub(marker, type, constants),
        _format.text(OPERATOR, " :="),
    ])
    return _format.concat([
        head,
        _format.nest(2, _format.append(
            _format.text(PLAIN, "\n"), _sub(marker, value, constants),
        )),
    ])


@always_inline
def name_eq(name, other):
    # Names are globally hash-consed, so structural equality is pointer identity.
    return name is other


@specialize.call_location()
def name_dict():
    """A fresh empty dict keyed by `Name`.

    All `Name` instances are globally hash-consed (`_mk_str_name`,
    `_mk_num_name`, `Name.ANONYMOUS`), so plain identity dicts replace
    `r_dict` and eliminate indirect hash/eq calls on hot lookups.
    """
    return {}


# ---- Hash-consing intern tables -----------------------------------------
#
# One global ``dict[int, list[T]]`` per interned kind, keyed by a
# scalar hash computed directly from the already-stored ``_hash``
# fields of the interned components (or, for primitive-keyed types,
# the primitive). Collision buckets are short Python lists scanned
# with ``is``-comparisons.
#
# Why this shape:
#   * native ``dict[int, ...]`` ops are inlined by the JIT — unlike
#     ``r_dict`` (which dispatches its eq/hash through function
#     pointers and stays opaque to the tracer);
#   * no allocation on hit — the lookup never builds a probe instance,
#     it just hashes two ints and walks a bucket;
#   * no per-instance carrier overhead — one shared structure rather
#     than thousands of tiny dicts attached to each ``fn``/``binder``;
#   * the per-construction work the JIT sees is just two field loads,
#     one ``dict.get``, and a few ``is``-checks — every step
#     constant-foldable when the components are promoted.
#
# Two primitive-keyed exceptions: ``W_BVar`` (small ``int`` index ─
# preallocated array fast path) and ``W_LitStr`` (``str`` value ─
# native ``dict[str, ...]``). ``W_LitNat`` mixes both: a preallocated
# array for the small-nat fast path, plus a string-keyed dict for big
# nats.

# Bucket scan helpers. Each takes the existing instance's stored
# components and compares them to the proposed ones via identity.
# Kept tiny so the JIT inlines them.

_HASH_MASK = 0x7FFFFFFF


# The `* 1000003 ^` mixing step is CPython's tuple-hash primitive,
# inlined here so we can combine already-precomputed `_hash` slots
# from W_Expr / W_Level / Name fields without allocating a tuple per
# call (which `compute_hash((a, b))` would). Keep `_HASH_MASK` applied
# only at the boundary of the public `_mixN` helpers; intermediate
# accumulators in loops (see `_mk_w_const`) skip the mask to preserve
# entropy across steps.

def _mix1(a):
    return (a * 1000003) & _HASH_MASK


def _mix2(a, b):
    return ((a * 1000003) ^ b) & _HASH_MASK


def _mix3(a, b, c):
    h = (a * 1000003) ^ b
    return ((h * 1000003) ^ c) & _HASH_MASK


def _mix4(a, b, c, d):
    h = (a * 1000003) ^ b
    h = (h * 1000003) ^ c
    return ((h * 1000003) ^ d) & _HASH_MASK


# ---- Primitive-keyed tables ---------------------------------------------

_W_BVAR_PREALLOC = 1024
_W_BVAR_ARRAY = [None] * _W_BVAR_PREALLOC  # type: list  # filled lazily
_W_BVAR_BIG = {}  # int -> W_BVar (idx >= _W_BVAR_PREALLOC)


def _mk_w_bvar(idx):
    if 0 <= idx < _W_BVAR_PREALLOC:
        existing = _W_BVAR_ARRAY[idx]
        if existing is not None:
            return existing
        e = W_BVar(idx)
        _W_BVAR_ARRAY[idx] = e
        return e
    existing = _W_BVAR_BIG.get(idx, None)
    if existing is not None:
        return existing
    e = W_BVar(idx)
    _W_BVAR_BIG[idx] = e
    return e


_W_LITSTR_TABLE = {}  # str -> W_LitStr


def _mk_w_litstr(val):
    existing = _W_LITSTR_TABLE.get(val, None)
    if existing is not None:
        return existing
    e = W_LitStr(val)
    _W_LITSTR_TABLE[val] = e
    return e


_W_LITNAT_PREALLOC = 1024
_W_LITNAT_ARRAY = [None] * _W_LITNAT_PREALLOC  # filled lazily
_W_LITNAT_BIG = {}  # str(val) -> W_LitNat (big nats only)


def _mk_w_litnat(val):
    # Small fast path: nats that fit in a native int are pre-arrayed.
    if val.int_le(_W_LITNAT_PREALLOC - 1):
        i = val.toint()
        if i >= 0:
            existing = _W_LITNAT_ARRAY[i]
            if existing is not None:
                return existing
            e = W_LitNat(val)
            _W_LITNAT_ARRAY[i] = e
            return e
    key = val.str()
    existing = _W_LITNAT_BIG.get(key, None)
    if existing is not None:
        return existing
    e = W_LitNat(val)
    _W_LITNAT_BIG[key] = e
    return e


# ---- Globally-interned content-keyed tables -----------------------------

class _StrNameTable(object):
    """Compact open-addressed hash table for globally interned `StrName`s.

    Stores `(hash:31 << 32) | (entry_idx + 1)` in a pointer-free `list[int]`
    and appends objects densely to `entries`, avoiding GC card-marking storms
    on random inserts and pointer chasing on misses/resizes.
    """

    _attrs_ = ['indexes', 'entries', 'mask']

    def __init__(self, initial_cap):
        self.indexes = [0] * initial_cap
        self.entries = []
        self.mask = initial_cap - 1

    @dont_inline
    def _grow(self):
        old = self.indexes
        new_cap = (self.mask + 1) * 2
        new_mask = new_cap - 1
        ni = [0] * new_cap
        for v in old:
            if v != 0:
                h = v >> 32
                slot = (h ^ (h >> 15)) & new_mask
                while ni[slot] != 0:
                    slot = (slot + 1) & new_mask
                ni[slot] = v
        self.indexes = ni
        self.mask = new_mask


class _NumNameTable(object):
    """Compact open-addressed hash table for globally interned `NumName`s."""

    _attrs_ = ['indexes', 'entries', 'mask']

    def __init__(self, initial_cap):
        self.indexes = [0] * initial_cap
        self.entries = []
        self.mask = initial_cap - 1

    @dont_inline
    def _grow(self):
        old = self.indexes
        new_cap = (self.mask + 1) * 2
        new_mask = new_cap - 1
        ni = [0] * new_cap
        for v in old:
            if v != 0:
                h = v >> 32
                slot = (h ^ (h >> 15)) & new_mask
                while ni[slot] != 0:
                    slot = (slot + 1) & new_mask
                ni[slot] = v
        self.indexes = ni
        self.mask = new_mask


_STR_NAME_TABLE = _StrNameTable(1 << 12)
_NUM_NAME_TABLE = _NumNameTable(1 << 12)
_EMPTY_LEVELS = []         # shared empty list[W_Level] for monomorphic W_Const
_EMPTY_LEVEL_NAMES = []    # shared empty list[Name] for monomorphic W_Declaration
# The expression tables map each content hash to a single node — on a
# collision the newest node simply takes the slot. Losing the displaced
# node only costs sharing (a future structurally-equal request allocates
# anew); nothing relies on interned-expression identity for correctness.
# One-node slots keep the table at a dict entry per node where chained
# buckets cost a `list` + backing array apiece — tens of millions of
# entries on Mathlib-sized exports. The name/level tables stay chained:
# they are small, and keeping every name canonical preserves the `is`
# fast paths and per-instance caches (`_level_cache`) at full strength.
_CONST_CACHE_SIZE = 1 << 16
_CONST_CACHE_MASK = _CONST_CACHE_SIZE - 1
_CONST_CACHE = [None] * _CONST_CACHE_SIZE
_INTERN_W_SORT = {}        # int -> list[W_Sort]
_INTERN_LEVEL_SUCC = {}    # int -> list[W_LevelSucc]
_INTERN_LEVEL_MAX = {}     # int -> list[W_LevelMax]
_INTERN_LEVEL_IMAX = {}    # int -> list[W_LevelIMax]
_INTERN_LEVEL_PARAM = {}   # int -> list[W_LevelParam]
# NOT hash-consed (see comments by their `_mk_*` factories):
#   * W_App / W_Proj / W_Let — `lean4export` already DAG-shares parsed terms
#     by `ie` index and `TermStore` hash-conses them per declaration; keeping
#     strong refs in global dicts pinned dead theorem proofs across Mathlib.
#   * W_Lambda / W_ForAll — their binders can't be interned (below).
#   * Binder — `_fvar` is *per-binding-position* mutable state that
#     interning would silently share across distinct positions.


# A process-global monotonic id stamped on every `W_Expr` at
# construction: a cheap, stable per-node integer for identity-keyed
# tables (the machine's import memo), where the GC's identity hash would
# force a shadow object and an address lookup per node. Two
# structurally-equal-but-distinct nodes get distinct uids.
_EXPR_UID = count()


@always_inline
def _next_uid():
    uid = _EXPR_UID.count + 1
    _EXPR_UID.count = uid
    return uid


def intern_stats():
    """
    Entry counts of the persistent intern tables, for leak hunting.
    """
    return 0, 0, _CONST_CACHE_SIZE


def _mk_str_name(parent, suffix):
    assert isinstance(parent, Name)
    h = ((parent._hash * 1000003) ^ compute_hash(suffix)) & 0x7FFFFFFF
    table = _STR_NAME_TABLE
    indexes = table.indexes
    entries = table.entries
    mask = table.mask
    slot = (h ^ (h >> 15)) & mask
    while True:
        v = indexes[slot]
        if v == 0:
            break
        if (v >> 32) == h:
            cand = entries[(v & 0xFFFFFFFF) - 1]
            if cand.parent is parent and cand.suffix == suffix:
                return cand
        slot = (slot + 1) & mask
    e = StrName(parent, suffix, h)
    idx = len(entries)
    entries.append(e)
    if (idx + 1) * 2 > mask + 1:
        table._grow()
        indexes = table.indexes
        mask = table.mask
        slot = (h ^ (h >> 15)) & mask
        while indexes[slot] != 0:
            slot = (slot + 1) & mask
    indexes[slot] = (h << 32) | (idx + 1)
    return e


def _mk_num_name_int(parent, idx):
    assert isinstance(parent, Name)
    assert idx >= 0
    ih = ((idx * 1000003) ^ (idx >> 16)) ^ 0x5A5A5A5A
    h = ((parent._hash * 1000003) ^ ih) & 0x7FFFFFFF
    table = _NUM_NAME_TABLE
    indexes = table.indexes
    entries = table.entries
    mask = table.mask
    slot = (h ^ (h >> 15)) & mask
    while True:
        v = indexes[slot]
        if v == 0:
            break
        if (v >> 32) == h:
            cand = entries[(v & 0xFFFFFFFF) - 1]
            if cand._small_idx == idx and cand.parent is parent:
                return cand
        slot = (slot + 1) & mask
    e = NumName(parent, idx, None, h)
    eidx = len(entries)
    entries.append(e)
    if (eidx + 1) * 2 > mask + 1:
        table._grow()
        indexes = table.indexes
        mask = table.mask
        slot = (h ^ (h >> 15)) & mask
        while indexes[slot] != 0:
            slot = (slot + 1) & mask
    indexes[slot] = (h << 32) | (eidx + 1)
    return e


def _mk_num_name(parent, idx):
    assert isinstance(parent, Name)
    try:
        iv = idx.toint()
    except OverflowError:
        iv = -1
    if iv >= 0:
        return _mk_num_name_int(parent, iv)
    ih = idx.hash() ^ 0x5A5A5A5A
    h = ((parent._hash * 1000003) ^ ih) & 0x7FFFFFFF
    table = _NUM_NAME_TABLE
    indexes = table.indexes
    entries = table.entries
    mask = table.mask
    slot = (h ^ (h >> 15)) & mask
    while True:
        v = indexes[slot]
        if v == 0:
            break
        if (v >> 32) == h:
            cand = entries[(v & 0xFFFFFFFF) - 1]
            if cand._small_idx < 0 and cand.parent is parent:
                big = cand._big_idx
                assert big is not None
                if big.eq(idx):
                    return cand
        slot = (slot + 1) & mask
    e = NumName(parent, -1, idx, h)
    eidx = len(entries)
    entries.append(e)
    if (eidx + 1) * 2 > mask + 1:
        table._grow()
        indexes = table.indexes
        mask = table.mask
        slot = (h ^ (h >> 15)) & mask
        while indexes[slot] != 0:
            slot = (slot + 1) & mask
    indexes[slot] = (h << 32) | (eidx + 1)
    return e


def _sort_levels(levels):
    """Sort ``levels`` in place by `norm_lt` (they are few)."""
    i = 1
    while i < len(levels):
        j = i
        while j > 0 and levels[j].norm_lt(levels[j - 1]):
            levels[j], levels[j - 1] = levels[j - 1], levels[j]
            j -= 1
        i += 1


def _mk_level_succ(parent):
    assert isinstance(parent, W_Level)
    h = _mix1(parent.hash())
    bucket = _INTERN_LEVEL_SUCC.get(h, None)
    if bucket is None:
        e = W_LevelSucc(parent)
        _INTERN_LEVEL_SUCC[h] = [e]
        return e
    for existing in bucket:
        if existing.parent is parent:
            return existing
    e = W_LevelSucc(parent)
    bucket.append(e)
    return e


def level_max(lhs, rhs):
    """
    ``max lhs rhs`` exactly as written, for a level read from an
    export: a parsed level keeps its shape so it can be written back
    and compared the way the kernel that produced it would.
    """
    return _mk_level_max(lhs, rhs)


def level_imax(lhs, rhs):
    """``imax lhs rhs`` exactly as written (see `level_max`)."""
    return _mk_level_imax(lhs, rhs)


def _mk_level_max(lhs, rhs):
    assert isinstance(lhs, W_Level)
    assert isinstance(rhs, W_Level)
    h = _mix2(lhs.hash(), rhs.hash())
    bucket = _INTERN_LEVEL_MAX.get(h, None)
    if bucket is None:
        e = W_LevelMax(lhs, rhs)
        _INTERN_LEVEL_MAX[h] = [e]
        return e
    for existing in bucket:
        if existing.lhs is lhs and existing.rhs is rhs:
            return existing
    e = W_LevelMax(lhs, rhs)
    bucket.append(e)
    return e


def _mk_level_imax(lhs, rhs):
    assert isinstance(lhs, W_Level)
    assert isinstance(rhs, W_Level)
    h = _mix2(lhs.hash(), rhs.hash())
    bucket = _INTERN_LEVEL_IMAX.get(h, None)
    if bucket is None:
        e = W_LevelIMax(lhs, rhs)
        _INTERN_LEVEL_IMAX[h] = [e]
        return e
    for existing in bucket:
        if existing.lhs is lhs and existing.rhs is rhs:
            return existing
    e = W_LevelIMax(lhs, rhs)
    bucket.append(e)
    return e


def _mk_level_param(name):
    assert isinstance(name, Name)
    h = _mix1(name.hash())
    bucket = _INTERN_LEVEL_PARAM.get(h, None)
    if bucket is None:
        e = W_LevelParam(name)
        _INTERN_LEVEL_PARAM[h] = [e]
        return e
    for existing in bucket:
        if existing.name is name:
            return existing
    e = W_LevelParam(name)
    bucket.append(e)
    return e


def _mk_w_sort(level):
    assert isinstance(level, W_Level)
    h = _mix1(level.hash())
    bucket = _INTERN_W_SORT.get(h, None)
    if bucket is None:
        e = W_Sort(level)
        _INTERN_W_SORT[h] = [e]
        return e
    for existing in bucket:
        if existing.level is level:
            return existing
    e = W_Sort(level)
    bucket.append(e)
    return e


def _mk_w_const(name, levels):
    assert isinstance(name, Name)
    h = name.hash()
    for lvl in levels:
        assert isinstance(lvl, W_Level)
        h = (h * 1000003) ^ lvl.hash()
    slot = (h ^ (h >> 16)) & _CONST_CACHE_MASK
    existing = _CONST_CACHE[slot]
    if existing is not None and existing.name is name:
        el = existing.levels
        if len(el) == len(levels):
            match = True
            for i in range(len(levels)):
                if el[i] is not levels[i]:
                    match = False
                    break
            if match:
                return existing
    e = W_Const(name=name, levels=levels)
    _CONST_CACHE[slot] = e
    return e


def _mk_w_const1(name, l0):
    assert isinstance(name, Name)
    assert isinstance(l0, W_Level)
    h = (name.hash() * 1000003) ^ l0.hash()
    slot = (h ^ (h >> 16)) & _CONST_CACHE_MASK
    existing = _CONST_CACHE[slot]
    if existing is not None and existing.name is name:
        el = existing.levels
        if len(el) == 1 and el[0] is l0:
            return existing
    e = W_Const(name=name, levels=[l0])
    _CONST_CACHE[slot] = e
    return e


def _mk_w_const2(name, l0, l1):
    assert isinstance(name, Name)
    assert isinstance(l0, W_Level)
    assert isinstance(l1, W_Level)
    h = (((name.hash() * 1000003) ^ l0.hash()) * 1000003) ^ l1.hash()
    slot = (h ^ (h >> 16)) & _CONST_CACHE_MASK
    existing = _CONST_CACHE[slot]
    if existing is not None and existing.name is name:
        el = existing.levels
        if len(el) == 2 and el[0] is l0 and el[1] is l1:
            return existing
    e = W_Const(name=name, levels=[l0, l1])
    _CONST_CACHE[slot] = e
    return e


# Binder style is fixed per `_mk_binder_*` factory, so we use one
# table per style. The hash mixes name + type only; left/right are
# implied by which table you're in.

# Binders are NOT hash-consed. Each `Binder` instance carries a
# mutable `_fvar` slot used by `binder.fvar()` to hand out a stable
# `W_FVar` for that *binding occurrence*. Interning would collapse two
# distinct binding positions that happen to share `(name, type)` into
# one instance, so both positions would receive the *same* FVar — the
# type-checker uses FVar identity to distinguish enclosing binders, so
# this silently corrupts inferred types (e.g. `∀ p p, Eq p p` checks
# even where the declared signature was `∀ p a, Eq p a`).

def _mk_binder_default(name, type):
    return Binder(name, type, style=_BINDER_DEFAULT)


def _mk_binder_implicit(name, type):
    return Binder(name, type, style=_BINDER_IMPLICIT)


def _mk_binder_instance(name, type):
    return Binder(name, type, style=_BINDER_INSTANCE)


def _mk_binder_strict_implicit(name, type):
    return Binder(name, type, style=_BINDER_STRICT_IMPLICIT)


# W_App is hash-consed via `_INTERN_W_APP`. Its fields (`fn`, `arg`)
# are themselves W_Exprs, mostly drawn from already-interned classes
# (`W_Const`, `W_Sort`, `W_Proj`, …) or from other interned W_Apps,
# so identity-keyed bucket lookup finds duplicates reliably during
# reduction (the case `assemble*`-family `init.ndjson` decls hit).
#
# W_Lambda / W_ForAll have no intern table: their binders carry a
# mutable `_fvar` slot used by `binder.fvar()` to hand out a stable
# FVar for that *binding occurrence*, so binders themselves can't be
# interned (see the comment by `_mk_binder_default`).

def _mk_app(fn, arg):
    """Allocate a `W_App(fn, arg)`."""
    assert isinstance(fn, W_Expr)
    assert isinstance(arg, W_Expr)
    return W_App(fn, arg)


def _mk_w_lambda(binder, body):
    return W_Lambda(binder, body)


def _mk_w_forall(binder, body):
    return W_ForAll(binder, body)


@always_inline
def _mk_w_lambda_flat(name, style, btype, body):
    e = instantiate(W_Lambda)
    e._init_flat(name, btype, body, style, None)
    return e


@always_inline
def _mk_w_forall_flat(name, style, btype, body):
    e = instantiate(W_ForAll)
    e._init_flat(name, btype, body, style, None)
    return e


def _mk_w_proj(struct_name, field_index, struct_expr):
    assert isinstance(struct_name, Name)
    assert isinstance(struct_expr, W_Expr)
    return W_Proj(struct_name, field_index, struct_expr)


def _mk_w_let(name, type, value, body):
    assert isinstance(name, Name)
    assert isinstance(type, W_Expr)
    assert isinstance(value, W_Expr)
    assert isinstance(body, W_Expr)
    return W_Let(name=name, type=type, value=value, body=body)


class Name(_Item):
    """
    Lean's ``Name`` inductive type — a linked structure mirroring::

        inductive Name | anonymous | str (p : Name) (s : String) | num (p : Name) (n : Nat)

    Use the ``Name.ANONYMOUS`` singleton for the anonymous case, then
    build up via ``.child(suffix)`` for ``Name.str`` parts and
    ``.num_child(idx)`` for ``Name.num`` parts. Build from a flat list
    of string parts via ``Name.of([...])``.

    Subclasses ``_AnonymousName``, ``StrName``, and ``NumName`` provide
    the actual data; this base class is abstract-in-spirit (don't
    construct it directly).
    """

    _attrs_ = [
        '_level_cache', '_empty_const', 'parent', '_hash',
        'is_internal', 'is_private',
        '_decl_dict', '_decl_cached',
    ]
    _immutable_fields_ = ['parent', '_hash', 'is_internal', 'is_private']

    def __init__(self):
        # Lazy cache for `as_level_param()`; populated on first call.
        # Subclasses set their own `parent` / `_hash` / `is_internal` /
        # `is_private` fields after calling this.
        self._level_cache = None
        # Lazy cache for `const()` with no universe levels.
        self._empty_const = None
        # Inline cache for `get_decl`: the declarations dict this name
        # was last resolved in, and the declaration it resolved to.
        # Names are interned, so this turns the hot Name-keyed r_dict
        # probe (indirect hash/eq calls) into two field reads. Sound for
        # the same reason `_get_decl` may be `@elidable`: a registered
        # binding is never replaced (`AlreadyDeclared`), and the dict
        # identity check keeps distinct environments apart.
        self._decl_dict = None
        self._decl_cached = None

    @staticmethod
    def simple(part):
        """A name with one (string) part."""
        return Name.ANONYMOUS.child(part)

    @staticmethod
    def from_str(s):
        """Construct a name by splitting a string on ``.``. A digit-only
        part becomes a *numeric* part -- the inverse of how names print,
        so e.g. the ``.0.`` component of a private name round-trips
        (an all-string parse can never equal such a name)."""
        name = Name.ANONYMOUS
        for p in s.split("."):
            if p and p.isdigit():
                name = name.num_child(rbigint.fromdecimalstr(p))
            else:
                name = name.child(p)
        return name

    @staticmethod
    @not_rpython
    def of(parts):
        """
        Test helper: build a name from a flat list of parts. ``str``
        parts become ``Name.str``; ``int`` parts become ``Name.num``.

        Not used in translated code — call ``.child(s)`` / ``.num_child(idx)``
        directly there.
        """
        name = Name.ANONYMOUS
        for p in parts:
            if isinstance(p, int):
                name = name.num_child(rbigint.fromint(p))
            else:
                name = name.child(p)
        return name

    def child(self, suffix):
        """Construct a ``Name.str`` child of this name."""
        return _mk_str_name(self, suffix)

    def num_child(self, idx):
        """
        Construct a ``Name.num`` child of this name. ``idx`` is the
        integer index (an ``rbigint`` since Lean's ``Nat`` is unbounded).
        """
        return _mk_num_name(self, idx)

    def num_child_int(self, idx):
        """Construct a ``Name.num`` child from a non-negative machine int."""
        return _mk_num_name_int(self, idx)

    def __repr__(self):
        return "`%s" % (self.str(),)

    @elidable
    def hash(self):
        return self._hash

    @not_rpython
    def __hash__(self):
        return self.hash()

    @not_rpython
    def __eq__(self, other):
        # Override `_Item.__eq__`: that compares `__dict__` items, which
        # would recurse infinitely through the self-link in
        # `_AnonymousName.parent`. We have `syntactic_eq` already
        # implemented per-subclass — use it.
        if not isinstance(other, Name):
            return NotImplemented
        return self.syntactic_eq(other)

    @not_rpython
    def __ne__(self, other):
        if not isinstance(other, Name):
            return NotImplemented
        return not self.syntactic_eq(other)

    def is_anonymous(self):
        # Default for `StrName` / `NumName`; `_AnonymousName` overrides.
        return False

    def to_format(self, constants, marker):
        """
        A ``Format`` for this name. We display the user-facing name
        (the ``MacroScopesView.name`` recovered from any hygienic
        encoding), not the raw Lean-canonical string — so a hygienic
        ``a._@.M._hyg.1`` shows as just ``a``.
        """
        return _format.text(DECL_NAME, self.user_name().str())

    def tokens(self, constants, mark=None, span_holder=None):
        return _tokens_from_format(
            self.to_format(constants, _marker_for(mark)), span_holder,
        )

    @always_inline
    def syntactic_eq(self, other):
        """
        Lean's ``Name.beq``: all `Name`s are globally hash-consed, so
        structural equality is pointer identity.
        """
        return self is other

    def user_name(self):
        """
        The user-facing prefix of this name — everything before the
        ``_@`` macro-scope marker introduced by Lean's ``MacroScopesView``
        encoding. If there is no ``_@`` marker, returns ``self`` unchanged.

        This is the inverse of ``MacroScopesView.review``: given a
        hygienic name like ``a._@.M._hygCtx._hyg.7``, returns ``a``.
        """
        # Walk leaf-to-root, tracking the root-most `_@` we encounter
        # (the boundary between the user-typed name and the macro
        # context). Per-subclass `is_at_marker()` keeps the loop free
        # of isinstance checks.
        last_marker = None
        cur = self
        while not cur.is_anonymous():
            if cur.is_at_marker():
                last_marker = cur
            cur = cur.parent
        if last_marker is None:
            return self
        return last_marker.parent

    def is_at_marker(self):
        """True if this is the ``_@`` macro-scope-boundary marker."""
        return False  # only StrName overrides

    def str(self):
        """
        Lean's ``Name.toString``: dot-joined parts, with non-identifier
        suffixes wrapped in ``«»``. Walked leaf-to-root so deep names
        don't blow the C stack on translated builds.
        """
        if self.is_anonymous():
            return "[anonymous]"
        parts = []
        cur = self
        while not cur.is_anonymous():
            parts.append(cur._part_str())
            cur = cur.parent
        # parts is leaf-first; reverse to render root-first.
        parts.reverse()
        return ".".join(parts)

    def depth(self):
        """Number of components in this name (0 for anonymous)."""
        n = 0
        cur = self
        while not cur.is_anonymous():
            n += 1
            cur = cur.parent
        return n

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

    def const_empty(self):
        """Construct the cached universe-monomorphic constant for this name."""
        c = self._empty_const
        if c is None:
            c = W_Const(name=self, levels=_EMPTY_LEVELS)
            self._empty_const = c
        return c

    @unroll_safe
    def const(self, levels=None):
        """
        Construct a constant expression for this name.
        """
        if levels is None or len(levels) == 0:
            return self.const_empty()
        return _mk_w_const(self, levels)

    def declaration(self, type, w_kind, levels=None, safety=SAFETY_SAFE):
        """
        Make a declaration with this name.
        """
        return W_Declaration(
            name=self,
            type=type,
            levels=_EMPTY_LEVEL_NAMES if (levels is None or len(levels) == 0) else levels,
            w_kind=w_kind,
            safety=safety,
        )

    def constructor(self, type, num_params=0, num_fields=0, cidx=0,
                    levels=None, is_unsafe=False, induct=None):
        """
        Make a constructor declaration with this name.
        """
        constructor = W_Constructor(
            num_params=num_params,
            num_fields=num_fields,
            cidx=cidx,
            induct=self.parent if induct is None else induct,
        )
        return self.declaration(
            type=type, w_kind=constructor, levels=levels,
            safety=_safety_of(is_unsafe),
        )

    def inductive(
        self,
        type,
        all=None,
        constructors=None,
        recursors=None,
        num_nested=0,
        num_params=0,
        num_indices=0,
        is_reflexive=False,
        is_recursive=False,
        levels=None,
        ctor_names=None,
        is_unsafe=False,
    ):
        """
        Make an inductive type declaration with this name.

        ``all`` is the list of inductives in the mutual block; defaults
        to ``[self]`` for a non-mutual inductive. Matches Lean's
        ``InductiveVal.all``.
        """
        inductive = W_Inductive(
            name=self,
            all=[self] if all is None else all,
            constructors=[] if constructors is None else constructors,
            recursors=[] if recursors is None else recursors,
            num_nested=num_nested,
            num_params=num_params,
            num_indices=num_indices,
            is_reflexive=is_reflexive,
            is_recursive=is_recursive,
            ctor_names=ctor_names,
        )
        return self.declaration(
            type=type, w_kind=inductive, levels=levels,
            safety=_safety_of(is_unsafe),
        )

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

    def definition(self, type, value, hint=1, levels=None,
                   safety=SAFETY_SAFE, all=None):
        """
        Make a definition of the given type and value with this name.

        ``all`` lists the members of the definition's mutual block when
        it has one (`DefinitionVal.all`).
        """
        definition = W_Definition(value=value, hint=hint, all=all)
        return self.declaration(type=type, w_kind=definition, levels=levels,
                                safety=safety)

    def opaque(self, type, value, levels=None, is_unsafe=False):
        """
        Make an opaque declaration with this name.
        """
        opaque = W_Opaque(value=value)
        return self.declaration(type=type, w_kind=opaque, levels=levels,
                                safety=_safety_of(is_unsafe))

    def axiom(self, type, levels=None, is_unsafe=False):
        """
        Make an axiom with this name.
        """
        return self.declaration(type=type, w_kind=W_Axiom(), levels=levels,
                                safety=_safety_of(is_unsafe))

    def quotient(self, type, kind, levels=None):
        """
        Make a Quot kernel-axiom declaration with this name.
        ``kind`` is one of the ``W_Quotient.KIND_*`` constants
        (type/ctor/lift/ind).
        """
        return self.declaration(type=type, w_kind=W_Quotient(kind=kind),
                                levels=levels)

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
        all=None,
        levels=None,
        is_unsafe=False,
    ):
        """
        Make a recursor with this name.

        ``all`` is the list of inductives this recursor is for (Lean's
        ``RecursorVal.all``). For a non-mutual recursor named
        ``Foo.rec``, the default is ``[Foo]`` — the recursor's parent
        name. Mutual recursors must pass ``all`` explicitly.
        """
        if all is None:
            all = [self.parent]
        recursor = W_Recursor(
            all=all,
            rules=[] if rules is None else rules,
            k=k,
            num_params=num_params,
            num_indices=num_indices,
            num_motives=num_motives,
            num_minors=num_minors,
        )
        return self.declaration(
            type=type, w_kind=recursor, levels=levels,
            safety=_safety_of(is_unsafe),
        )

    def let(self, type, value, body):
        """
        Construct a let expression with this name.
        """
        return _mk_w_let(self, type, value, body)

    def proj(self, field_index, struct_expr):
        """
        Construct a projection with this name.
        """
        return _mk_w_proj(self, field_index, struct_expr)


    def as_level_param(self):
        """
        Return this name's `W_LevelParam`. Cached: every reader
        (the FFI walker's `read_level` for `Lean.Level.param`, the
        exporter's pre-emit, tests, etc.) sees the same instance,
        so `compute_unique_id`-based dedup in the exporter works
        without a separate name-keyed cache.

        Spelled `as_level_param` rather than `level` because the
        latter would shadow `W_Sort.level` in RPython's annotator
        (both are read as `.level`; the union of an instancemethod
        PBC and `W_Level` is then unanalysable).
        """
        if self._level_cache is None:
            self._level_cache = _mk_level_param(self)
        return self._level_cache

    # Kept for backwards-compat with test fixtures that call `.level()`
    # — they don't run through the annotator in the same way, so the
    # name collision is harmless there.
    level = as_level_param


class _AnonymousName(Name):
    """
    Lean's ``Name.anonymous``. Singleton — use ``Name.ANONYMOUS``.

    Self-links ``parent`` to itself so generic walkers don't have to
    null-check; callers gate on ``is_anonymous()`` before recursing.
    """

    _attrs_ = []

    def __init__(self):
        Name.__init__(self)
        self.parent = self
        self._hash = 0x345678
        self.is_internal = False
        self.is_private = False

    def is_anonymous(self):
        return True

    def has_macro_scopes(self):
        return False

    def _part_str(self):
        # Anonymous never contributes a part to `str()` — the iterative
        # walk in `Name.str()` stops before calling this.
        return ""


class StrName(Name):
    """Lean's ``Name.str p s``: a string-suffixed name nested in ``p``."""

    _attrs_ = ['suffix']
    _immutable_fields_ = ['suffix']

    def __init__(self, parent, suffix, h):
        Name.__init__(self)
        self.parent = parent
        self.suffix = suffix
        self._hash = h
        self.is_internal = (
            parent.is_internal
            or (len(suffix) > 0 and suffix[0] == "_")
        )
        self.is_private = parent.is_private or suffix == "_private"

    def has_macro_scopes(self):
        # Lean: `.str _ s => s == "_hyg"`
        return self.suffix == "_hyg"

    def is_at_marker(self):
        return self.suffix == "_@"

    def _part_str(self):
        # Lean's `escapePart`: wrap suffix in `«»` if any non-identifier
        # character is present.
        s = self.suffix
        for c in s:
            if ord(c) > 127 or c.isalnum() or c in "'_":
                continue
            return "\xc2\xab" + s + "\xc2\xbb"
        return s


class NumName(Name):
    """
    Lean's ``Name.num p n``: a numerically-indexed name nested in ``p``.
    Non-negative indices that fit in a machine int are stored directly in
    ``_small_idx`` without allocating an ``rbigint``; larger indices store
    ``_small_idx = -1`` and the ``rbigint`` in ``_big_idx``.
    """

    _attrs_ = ['_small_idx', '_big_idx']
    _immutable_fields_ = ['_small_idx', '_big_idx']

    def __init__(self, parent, small_idx, big_idx, h):
        Name.__init__(self)
        self.parent = parent
        self._small_idx = small_idx
        self._big_idx = big_idx
        self._hash = h
        # Lean's `isInternal` / private-name checks: num parts don't
        # trigger themselves but they don't block parent propagation.
        self.is_internal = parent.is_internal
        self.is_private = parent.is_private

    def has_macro_scopes(self):
        # Lean: `.num n _ => hasMacroScopes n`
        return self.parent.has_macro_scopes()

    def idx_str(self):
        if self._small_idx >= 0:
            return str(self._small_idx)
        assert self._big_idx is not None
        return self._big_idx.str()

    def idx_int(self):
        if self._small_idx >= 0:
            return self._small_idx
        assert self._big_idx is not None
        return self._big_idx.toint()

    def _part_str(self):
        return self.idx_str()


def names(*many):
    """
    Create a bunch of names at once.
    """
    return [Name.from_str(each) for each in many]


#: The anonymous name.
Name.ANONYMOUS = _AnonymousName()


_BINDER_DEFAULT = 0
_BINDER_IMPLICIT = 1
_BINDER_INSTANCE = 2
_BINDER_STRICT_IMPLICIT = 3
_BINDER_LEFT = ["(", "{", "[", "\xe2\xa6\x83"]
_BINDER_RIGHT = [")", "}", "]", "\xe2\xa6\x84"]
_BINDER_INFO_NAMES = ["default", "implicit", "instImplicit", "strictImplicit"]


class Binder(_Item):
    """
    A binder within a Lambda or ForAll.

    Only `type` is really functionally important, the other attributes are
    strictly for pretty printing.
    """

    _attrs_ = ['name', 'type', '_pos_style', '_fvar']
    _immutable_fields_ = ['name', 'type']

    @staticmethod
    def default(name, type):
        """
        A default style binder.
        """
        return _mk_binder_default(name, type)

    @staticmethod
    def implicit(name, type):
        """
        An implicit style binder.
        """
        return _mk_binder_implicit(name, type)

    @staticmethod
    def instance(name, type):
        """
        An intance-implicit style binder.
        """
        return _mk_binder_instance(name, type)

    @staticmethod
    def strict_implicit(name, type):
        """
        A strict implicit style binder.
        """
        return _mk_binder_strict_implicit(name, type)

    def __init__(self, name, type, left=None, right=None, style=_BINDER_DEFAULT):
        if left is not None:
            if left == "{":
                style = _BINDER_IMPLICIT
            elif left == "[":
                style = _BINDER_INSTANCE
            elif left == "\xe2\xa6\x83":
                style = _BINDER_STRICT_IMPLICIT
            else:
                style = _BINDER_DEFAULT
        self.name = name
        self.type = type
        #: Packs `(position << 2) | style`: the binding position this binder
        #: stands at (shared by `with_type`, carried as its fvar's id) plus
        #: its 2-bit binder style (`_BINDER_*`).
        self._pos_style = (next(W_FVar._counter) << 2) | style
        self._fvar = None

    def style(self):
        return self._pos_style & 3

    def get_binder(self):
        return self

    def left_bracket(self):
        return _BINDER_LEFT[self._pos_style & 3]

    def right_bracket(self):
        return _BINDER_RIGHT[self._pos_style & 3]

    def hash(self):
        h = self.name.hash() ^ self.type.hash()
        h = (h * 1000003) ^ (self._pos_style & 3)
        return h & 0xFFFFFFFF

    def __repr__(self):
        return "<Binder %s>" % (self.name.str())

    def export_info_name(self):
        """The `binderInfo` discriminator string used in `lean4export`'s
        NDJSON encoding of lambda/forall binders."""
        return _BINDER_INFO_NAMES[self._pos_style & 3]

    def to_implicit(self):
        return Binder.implicit(name=self.name, type=self.type)

    def to_format(self, constants, marker):
        s = self._pos_style & 3
        return _format.concat([
            _format.text(PUNCT, _BINDER_LEFT[s]),
            _format.text(BINDER_NAME, self.name.user_name().str()),
            _format.text(PUNCT, " : "),
            _sub(marker, self.type, constants),
            _format.text(PUNCT, _BINDER_RIGHT[s]),
        ])

    def tokens(self, constants, mark=None, span_holder=None):
        return _tokens_from_format(
            self.to_format(constants, _marker_for(mark)), span_holder,
        )

    def is_default(self):
        """
        Is this a default binder (i.e. not implicit, instance or strict)?
        """
        return (self._pos_style & 3) == _BINDER_DEFAULT

    def is_instance(self):
        """
        Is this a typeclass instance binder?
        """
        return (self._pos_style & 3) == _BINDER_INSTANCE

    def fvar(self):
        """
        An FVar for this binder.

        Returns the same FVar each time so that identity comparisons
        work across inference and rendering.
        """
        fvar = self._fvar
        if fvar is None:
            fvar = W_FVar(self, self._pos_style >> 2)
            self._fvar = fvar
        return fvar

    def bind_fvar(self, fvar, depth):
        if not self.type.has_fvar():
            return self
        new_type = self.type.bind_fvar(fvar, depth)
        if new_type is self.type:
            return self
        return self.with_type(type=new_type)

    def incr_free_bvars(self, expr, depth):
        if self.type.loose_bvar_range() <= depth:
            return self
        return self.with_type(type=self.type.incr_free_bvars(expr, depth))

    def instantiate(self, expr, depth=0):
        if self.type.loose_bvar_range() <= depth:
            return self
        return self.with_type(type=self.type.instantiate(expr, depth))

    def subst_levels(self, subts):
        new_type = self.type.subst_levels(subts)
        if new_type is self.type:
            return self
        return self.with_type(type=new_type)

    def syntactic_eq(self, other):
        """
        Check if this binder is syntactically equal to another.
        """
        assert isinstance(other, Binder)
        # TODO - does syntactic equality really care about binder info/name?
        return (
            (self._pos_style & 3) == (other._pos_style & 3)
            and syntactic_eq(self.name, other.name)
            and syntactic_eq(self.type, other.type)
        )

    def with_type(self, type):
        """
        Create a new binder of the same name and kind but with a new type.
        """
        binder = Binder(self.name, type, style=self._pos_style & 3)
        binder._pos_style = self._pos_style
        return binder


def leq(fn):
    def leq(self, other, balance=0):
        if self is other or syntactic_eq(self, other):
            return balance >= 0
        return fn(self, other, balance)

    return leq


# Based on https://github.com/gebner/trepplein/blob/c704ffe81941779dacf9efa20a75bf22832f98a9/src/main/scala/trepplein/level.scala#L100
class W_Level(_Item):
    _attrs_ = ['_hash', '_normal', '_sort_cache', '_succ_cache', 'has_param']
    _immutable_fields_ = ['_hash', 'has_param']

    #: The normal form, once computed (levels are immutable and
    #: interned, so it never changes).
    _normal = None
    _sort_cache = None
    _succ_cache = None

    def check_params(self, allowed):
        """Return the first `W_LevelParam` name not in ``allowed``, or None."""
        return None

    @elidable
    def hash(self):
        """
        A content hash. Subclasses set ``self._hash`` eagerly in
        ``__init__`` (mixing parent / lhs+rhs / name hashes), so this
        is O(1) and JIT-foldable.
        """
        return self._hash

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
        Whether two levels denote the same universe for every
        assignment of their parameters: their normal forms coincide,
        or each is at most the other.
        """
        if self is other:
            return True
        n1 = self.normalize()
        n2 = other.normalize()
        if syntactic_eq(n1, n2):
            return True
        return n1.leq(n2) and n2.leq(n1)

    def to_offset(self):
        """``(base, k)`` with ``self = base + k`` and ``base`` not a successor."""
        return self, 0

    def normalize(self):
        """
        A canonical form: the arguments of a max are flattened, sorted,
        and merged (an explicit universe subsumed by a larger offset, a
        base kept only at its largest offset), and a successor of a max
        is pushed into each argument. Equal universes have syntactically
        equal normal forms far more often than not, which is what makes
        `eq` decide the reorderings that structural comparison cannot.
        """
        normal = self._normal
        if normal is None:
            normal = self.normalize_at(0)
            self._normal = normal
        return normal

    def normalize_at(self, k):
        """The normal form of ``self + k`` (``self`` not a successor)."""
        return self.succ_n(k)

    def norm_kind(self):
        """Ordering class among level kinds in a normal form."""
        return 0

    def norm_lt(self, other):
        """A total order on levels, for sorting a max's arguments."""
        if self is other:
            return False
        b1, k1 = self.to_offset()
        b2, k2 = other.to_offset()
        if b1 is not b2 and not syntactic_eq(b1, b2):
            kind1 = b1.norm_kind()
            kind2 = b2.norm_kind()
            if kind1 != kind2:
                return kind1 < kind2
            return b1.norm_lt_same_kind(b2)
        return k1 < k2

    def norm_lt_same_kind(self, other):
        return False

    def is_not_zero(self):
        """Whether this level is nonzero under every assignment of its
        parameters."""
        return False

    def push_max_args(self, out):
        """Append this level's max arguments (itself, unless a max)."""
        out.append(self)

    def succ_n(self, k):
        level = self
        while k > 0:
            level = level.succ()
            k -= 1
        return level

    def sort(self):
        """
        Return a Sort for this level.
        """
        s = self._sort_cache
        if s is None:
            s = _mk_w_sort(self)
            self._sort_cache = s
        return s

    def succ(self):
        """
        Return the level which is successor to this one.
        """
        s = self._succ_cache
        if s is None:
            s = _mk_level_succ(self)
            self._succ_cache = s
        return s

    def gt(self, other, balance):
        """Whether ``other + balance ≤ self``; every `leq` is
        ``self ≤ other + balance``, so the two convert with a sign flip."""
        raise NotImplementedError

    def imax_leq(self, imax, other, balance):
        """Check imax ≤ other when self is the imax's rhs: both sides of
        the imax must fit, since it is their max unless this rhs is
        zero (when it is zero itself)."""
        return imax.lhs.leq(other, balance) and self.leq(other, balance)

    def imax_gt(self, imax, other, balance):
        """Check other ≤ imax when self is the imax's rhs: only the rhs
        can be relied on, since a zero rhs zeroes the whole imax."""
        return self.gt(other, balance)

    def max(self, other):
        """
        Return the (simplified) max of this level with another: one
        side is dropped only when the other is at least as large for
        every assignment of the parameters.
        """
        if self is other:
            return self
        if isinstance(other, W_LevelZero):
            return self
        if isinstance(other, W_LevelMax):
            if syntactic_eq(other.lhs, self) or syntactic_eq(other.rhs, self):
                return other
        if other.leq(self):
            return self
        if self.leq(other):
            return other
        return _mk_level_max(self, other)

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
        if other.is_not_zero():
            return self.max(other)
        return _mk_level_imax(self, other)


class W_LevelZero(W_Level):
    _attrs_ = []

    def __init__(self):
        self._hash = 0x4C5A  # arbitrary distinct from other level kinds
        self.has_param = False
        self._normal = self

    def __repr__(self):
        return "<Level 0>"

    @leq
    def leq(self, other, balance):
        if balance >= 0:
            return True
        if isinstance(other, W_LevelParam):
            return balance >= 0
        return other.gt(self, -balance)

    def gt(self, other, balance):
        if isinstance(other, W_LevelZero):
            return balance <= 0
        return False

    def pretty_parts(self):
        return "", 0

    def subst_levels(self, substs):
        return self

    def subst_levels_lists(self, params, levels):
        return self

    def syntactic_eq(self, other):
        return True

    def max(self, other):
        return other

    def imax(self, other):
        return other


W_LEVEL_ZERO = W_LevelZero()


class W_LevelSucc(W_Level):
    _attrs_ = ['parent']
    _immutable_fields_ = ['parent']

    def __init__(self, parent):
        self.parent = parent
        self.has_param = parent.has_param
        self._hash = ((parent.hash() * 1000003) ^ 0x53C7) & 0xFFFFFFFF
        if (parent._normal is parent
                and not isinstance(parent, W_LevelMax)
                and not isinstance(parent, W_LevelIMax)):
            self._normal = self

    def check_params(self, allowed):
        if not self.has_param:
            return None
        return self.parent.check_params(allowed)

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

    def to_offset(self):
        base, k = self.parent.to_offset()
        return base, k + 1

    def normalize(self):
        normal = self._normal
        if normal is None:
            base, k = self.to_offset()
            normal = base.normalize_at(k)
            self._normal = normal
        return normal

    def norm_kind(self):
        return 1

    def is_not_zero(self):
        return True

    def pretty_parts(self):
        text, balance = self.parent.pretty_parts()
        return text, balance + 1

    def subst_levels(self, substs):
        if not self.has_param:
            return self
        new_parent = self.parent.subst_levels(substs)
        if new_parent is self.parent:
            return self
        return new_parent.succ()

    def subst_levels_lists(self, params, levels):
        if not self.has_param:
            return self
        new_parent = self.parent.subst_levels_lists(params, levels)
        if new_parent is self.parent:
            return self
        return new_parent.succ()

    def syntactic_eq(self, other):
        assert isinstance(other, W_LevelSucc)
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
    _attrs_ = ['lhs', 'rhs']
    _immutable_fields_ = ['lhs', 'rhs']

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        self.has_param = lhs.has_param or rhs.has_param
        h = (lhs.hash() * 1000003) ^ rhs.hash()
        self._hash = ((h * 1000003) ^ 0x6D4A) & 0xFFFFFFFF

    def check_params(self, allowed):
        if not self.has_param:
            return None
        bad = self.lhs.check_params(allowed)
        if bad is not None:
            return bad
        return self.rhs.check_params(allowed)

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
        return (
            other.leq(self.lhs, -balance) or other.leq(self.rhs, -balance)
        )

    def norm_kind(self):
        return 2

    def norm_lt_same_kind(self, other):
        assert isinstance(other, W_LevelMax)
        if not syntactic_eq(self.lhs, other.lhs):
            return self.lhs.norm_lt(other.lhs)
        return self.rhs.norm_lt(other.rhs)

    def is_not_zero(self):
        return self.lhs.is_not_zero() or self.rhs.is_not_zero()

    def push_max_args(self, out):
        self.lhs.push_max_args(out)
        self.rhs.push_max_args(out)

    def normalize_at(self, k):
        todo = []
        self.push_max_args(todo)
        args = []
        for each in todo:
            each.normalize().push_max_args(args)
        _sort_levels(args)
        # An explicit universe k is subsumed by any argument at offset
        # >= k; keep the largest explicit one only when nothing does.
        i = 0
        n = len(args)
        if isinstance(args[i].to_offset()[0], W_LevelZero):
            while i + 1 < n and isinstance(args[i + 1].to_offset()[0], W_LevelZero):
                i += 1
            explicit = args[i].to_offset()[1]
            j = i + 1
            while j < n:
                if args[j].to_offset()[1] >= explicit:
                    break
                j += 1
            if j < n:
                i += 1
        kept = [args[i]]
        prev_base, prev_off = args[i].to_offset()
        i += 1
        while i < n:
            base, off = args[i].to_offset()
            if syntactic_eq(prev_base, base):
                if prev_off < off:
                    prev_off = off
                    kept[len(kept) - 1] = args[i]
            else:
                prev_base = base
                prev_off = off
                kept.append(args[i])
            i += 1
        result = kept[len(kept) - 1].succ_n(k)
        i = len(kept) - 2
        while i >= 0:
            result = _mk_level_max(kept[i].succ_n(k), result)
            i -= 1
        return result

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
        if not self.has_param:
            return self
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
        if new_lhs is self.lhs and new_rhs is self.rhs:
            return self
        return new_lhs.max(new_rhs)

    def subst_levels_lists(self, params, levels):
        if not self.has_param:
            return self
        new_lhs = self.lhs.subst_levels_lists(params, levels)
        new_rhs = self.rhs.subst_levels_lists(params, levels)
        if new_lhs is self.lhs and new_rhs is self.rhs:
            return self
        return new_lhs.max(new_rhs)

    def syntactic_eq(self, other):
        assert isinstance(other, W_LevelMax)
        return syntactic_eq(self.lhs, other.lhs) and syntactic_eq(self.rhs, other.rhs)


class W_LevelIMax(W_Level):
    _attrs_ = ['lhs', 'rhs']
    _immutable_fields_ = ['lhs', 'rhs']

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        self.has_param = lhs.has_param or rhs.has_param
        h = (lhs.hash() * 1000003) ^ rhs.hash()
        self._hash = ((h * 1000003) ^ 0x694D) & 0xFFFFFFFF

    def check_params(self, allowed):
        if not self.has_param:
            return None
        bad = self.lhs.check_params(allowed)
        if bad is not None:
            return bad
        return self.rhs.check_params(allowed)

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
        # A max on the right may contain this imax outright; look
        # there before decomposing the imax, which loses information.
        if isinstance(other, W_LevelMax):
            if self.leq(other.lhs, balance) or self.leq(other.rhs, balance):
                return True
        return self.rhs.imax_leq(self, other, balance)

    def gt(self, other, balance):
        return self.rhs.imax_gt(self, other, balance)

    def norm_kind(self):
        return 3

    def norm_lt_same_kind(self, other):
        assert isinstance(other, W_LevelIMax)
        if not syntactic_eq(self.lhs, other.lhs):
            return self.lhs.norm_lt(other.lhs)
        return self.rhs.norm_lt(other.rhs)

    def is_not_zero(self):
        return self.rhs.is_not_zero()

    def normalize_at(self, k):
        result = self.lhs.normalize().imax(self.rhs.normalize())
        if not isinstance(result, W_LevelIMax):
            # The imax turned into a max (or a side) that the flattening
            # and sorting of normal forms still has to reach.
            result = result.normalize()
        return result.succ_n(k)

    def pretty_parts(self):
        return "(imax %s %s)" % (self.lhs.str(), self.rhs.str()), 0

    def subst_levels(self, substs):
        if not self.has_param:
            return self
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
        if new_lhs is self.lhs and new_rhs is self.rhs:
            return self
        return new_lhs.imax(new_rhs)

    def subst_levels_lists(self, params, levels):
        if not self.has_param:
            return self
        new_lhs = self.lhs.subst_levels_lists(params, levels)
        new_rhs = self.rhs.subst_levels_lists(params, levels)
        if new_lhs is self.lhs and new_rhs is self.rhs:
            return self
        return new_lhs.imax(new_rhs)

    def syntactic_eq(self, other):
        assert isinstance(other, W_LevelIMax)
        return syntactic_eq(self.lhs, other.lhs) and syntactic_eq(self.rhs, other.rhs)


class W_LevelParam(W_Level):
    _attrs_ = ['name']
    _immutable_fields_ = ['name']

    def __init__(self, name):
        self.name = name
        self.has_param = True
        self._hash = ((name.hash() * 1000003) ^ 0x5041) & 0xFFFFFFFF
        self._normal = self

    def check_params(self, allowed):
        for each in allowed:
            if self.name.syntactic_eq(each):
                return None
        return self.name

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
            return balance <= 0
        if isinstance(other, W_LevelParam):
            return balance <= 0 and syntactic_eq(self.name, other.name)
        return False

    def pretty_parts(self):
        return self.name.str(), 0

    def syntactic_eq(self, other):
        assert isinstance(other, W_LevelParam)
        return syntactic_eq(self.name, other.name)

    def is_named(self, name):
        return self.name.syntactic_eq(name)

    def subst_levels(self, substs):
        return substs.get(self.name, self)

    def subst_levels_lists(self, params, levels):
        name = self.name
        n = len(params)
        if n == 1:
            return levels[0] if name is params[0] else self
        i = 0
        while i < n:
            if name is params[i]:
                return levels[i]
            i += 1
        return self

    def norm_kind(self):
        return 4

    def norm_lt_same_kind(self, other):
        assert isinstance(other, W_LevelParam)
        return self.name.str() < other.name.str()

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
        # `gt` carries its offset on the other side from `leq`.
        return (
            other.subst_levels(subst_zero).leq(
                imax.subst_levels(subst_zero), -balance,
            )
            and other.subst_levels(subst_succ).leq(
                imax.subst_levels(subst_succ), -balance,
            )
        )


_LP_BIT = 1 << 62
_STYLE_SHIFT = 60
_CANON_BIT = 1 << 59
_LOOSE_MASK = 0x03FFFFFF
_NON_STYLE_UPPER_MASK = (_LOOSE_MASK << 33) | (1 << 32) | _LP_BIT


class W_Expr(_Item):
    # Five per-node immutable scalars are packed into one `_packed` word:
    #
    #   bits  0-31 : the content `hash()` (already masked to 32 bits)
    #   bit     32 : `has_fvar` (does any free variable occur)
    #   bits 33-58 : `loose_bvar_range` (largest loose de-Bruijn index + 1)
    #   bit     59 : `_CANON_BIT` (on `W_Const`/`W_Sort`: levels already normal)
    #   bits 60-61 : `binder_style` (0..3 on `W_FunBase`, 0 elsewhere)
    #   bit     62 : `has_level_param` (does any universe level param occur)
    #
    # Each was its own machine word before (`_hash`, plus a `_bvar_fvar`
    # that already folded the latter two). They are all small — a term's
    # bvar depth is tiny and the hash is 32-bit — so one word holds them
    # with bit 62 tracking universe-parameter presence for O(1) skips
    # during polymorphic constant import.
    _attrs_ = ['_packed', '_cache']
    _immutable_fields_ = ['_packed']
    #: Intrusive generation-stamped handle cache `(gen << 32) | handle` for
    #: `TermStore.import_term`, `leaf_for`, and `_import_with_levels` (0 = empty).
    _cache = 0

    @always_inline
    def hash(self):
        """
        A content hash (the low 32 bits of `_packed`). Subclasses mix
        the hashes of their sub-expressions / levels / names into it in
        ``__init__``. Used by the exporter's content-keyed dedup to
        match `lean4export`'s `HashMap Expr Nat`.
        """
        return self._packed & 0xFFFFFFFF

    @always_inline
    def loose_bvar_range(self):
        """The largest loose de-Bruijn index occurring + 1 (0 if none)."""
        return (self._packed >> 33) & _LOOSE_MASK

    @always_inline
    def has_fvar(self):
        """Whether any free variable (`W_FVar`) occurs in this term."""
        return ((self._packed >> 32) & 1) != 0

    @always_inline
    def has_level_param(self):
        """Whether any universe level parameter (`W_LevelParam`) occurs."""
        return (self._packed & _LP_BIT) != 0


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
        # Most spines we see are 1-4 args; preallocating skips the
        # first 2-3 list resizes per call (this is a hot path —
        # profiles consistently put `unapp` near the top).
        args = newlist_hint(4)
        expr = self
        while isinstance(expr, W_App):
            args.append(expr.arg)
            expr = expr.fn
        return expr, args

    def whnf(self, checker):
        """The weak head normal form of this expression."""
        return checker.whnf(self)

    def infer(self, checker):
        """The type of this expression, checking it along the way."""
        return checker.infer(self)

    def open_all_binders(self):
        """
        Open all leading forall binders, instantiating each with a fresh fvar.

        Returns ``(fvars, body)``.
        """
        fvars = []
        expr = self
        while isinstance(expr, W_ForAll):
            fvar = expr.get_binder().fvar()
            fvars.append(fvar)
            expr = expr.body.instantiate(fvar, 0)
        return fvars, expr

    def contains_const(self, name):
        """
        Whether this expression contains a constant with the given name.
        """
        return False

    @unroll_safe
    def app(self, arg, *more):
        """
        Apply this (which better be a function) to the given argument(s).
        """
        expr = _mk_app(self, arg)
        if not more:
            return expr
        return expr.app(*more)


    def expect_sort(self, env):
        raise W_NotASort(env, self, inferred_type=self, name=None)

    def binder_name(self, index):
        """The name of the ``index``-th binder, or None."""
        expr = self
        i = 0
        while isinstance(expr, W_ForAll):
            if i == index:
                return expr.name.user_name().str()
            i += 1
            expr = expr.body
        return None

    def to_format(self, constants, marker):
        """A ``Format`` for this expression, defaulting to plain text."""
        return _format.text(PLAIN, self.str())

    def tokens(self, constants, mark=None, span_holder=None):
        """Render this expression to a flat token list."""
        return _tokens_from_format(
            self.to_format(constants, _marker_for(mark)), span_holder,
        )


class W_BVar(W_Expr):
    _attrs_ = ['id']
    _immutable_fields_ = ['id']

    def __init__(self, id):
        self.id = id
        bf = (id + 1) << 1
        self._packed = (((id * 1000003) ^ 0xB7A8) & 0xFFFFFFFF) | (bf << 32)

    def __repr__(self):
        return "<BVar %s>" % (self.id,)

    def str(self):
        return "#%s" % (self.id,)

    def to_format(self, constants, marker):
        return _format.text(BINDER_NAME, self.str())

    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write('{"bvar":%d,"ie":%d}\n' % (self.id, eid))
        return eid

    def syntactic_eq(self, other):
        assert isinstance(other, W_BVar)
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
            return _mk_w_bvar(self.id - 1)
        return self

    def incr_free_bvars(self, count, depth):
        if self.id >= depth:
            return _mk_w_bvar(self.id + count)
        return self

    def subst_levels(self, substs):
        return self

    def subst_levels_lists(self, params, levels):
        return self


class W_FVar(W_Expr):
    """An FVar which refers to its binder by identity."""

    _attrs_ = ['id', 'binder', '_uid']
    _immutable_fields_ = ['id', 'binder', '_uid']

    _counter = count()

    def __init__(self, binder, id=-1):
        if id < 0:
            id = next(self._counter)
        self.id = id
        assert isinstance(binder, Binder)
        self.binder = binder
        bf = 1
        # FVars are unique by id, so hashing on id alone is fine.
        self._uid = _next_uid()
        self._packed = (((self.id * 1000003) ^ 0xF7A8) & 0xFFFFFFFF) | (bf << 32)

    def __repr__(self):
        return "<FVar id={} binder={!r}>".format(self.id, self.binder)


    def str(self):
        return self.binder.name.user_name().str()

    def to_format(self, constants, marker):
        return _format.text(BINDER_NAME, self.str())

    def incr_free_bvars(self, count, depth):
        return self

    def instantiate(self, expr, depth=0):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_FVar)
        return self.id == other.id and syntactic_eq(self.binder, other.binder)


    def bind_fvar(self, fvar, depth):
        if self.id == fvar.id:
            return _mk_w_bvar(depth)
        return self


def _utf8_codepoints(s):
    """Decode UTF-8 bytes ``s`` into a list of Unicode codepoints."""
    out = []
    n = len(s)
    i = 0
    while i < n:
        b0 = ord(s[i])
        if b0 < 0x80:
            out.append(b0)
            i += 1
        elif (
            (b0 & 0xE0) == 0xC0
            and i + 1 < n
            and (ord(s[i + 1]) & 0xC0) == 0x80
        ):
            b1 = ord(s[i + 1])
            out.append(((b0 & 0x1F) << 6) | (b1 & 0x3F))
            i += 2
        elif (
            (b0 & 0xF0) == 0xE0
            and i + 2 < n
            and (ord(s[i + 1]) & 0xC0) == 0x80
            and (ord(s[i + 2]) & 0xC0) == 0x80
        ):
            b1 = ord(s[i + 1])
            b2 = ord(s[i + 2])
            out.append(((b0 & 0x0F) << 12) | ((b1 & 0x3F) << 6) | (b2 & 0x3F))
            i += 3
        elif (
            (b0 & 0xF8) == 0xF0
            and i + 3 < n
            and (ord(s[i + 1]) & 0xC0) == 0x80
            and (ord(s[i + 2]) & 0xC0) == 0x80
            and (ord(s[i + 3]) & 0xC0) == 0x80
        ):
            b1 = ord(s[i + 1])
            b2 = ord(s[i + 2])
            b3 = ord(s[i + 3])
            out.append(
                ((b0 & 0x07) << 18)
                | ((b1 & 0x3F) << 12)
                | ((b2 & 0x3F) << 6)
                | (b3 & 0x3F)
            )
            i += 4
        else:
            out.append(b0)
            i += 1
    return out


class W_LitStr(W_Expr):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        assert isinstance(val, str)
        self.val = val
        bf = 0
        self._packed = (((compute_hash(val) * 1000003) ^ 0x57A5) & 0xFFFFFFFF) | (bf << 32)

    def __repr__(self):
        return repr(self.val)

    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"strVal":%s}\n' % (eid, exporter.quote(self.val)),
        )
        return eid


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

    def to_format(self, constants, marker):
        """A ``Format`` tagging this string literal."""
        return _format.text(LITERAL, self.str())

    def build_str_expr(self):
        Char = Name.simple("Char").const()
        cons = Name.from_str("List.cons").const([W_LEVEL_ZERO]).app(Char)
        expr = Name.from_str("List.nil").const([W_LEVEL_ZERO]).app(Char)
        char_of_nat = Name.from_str("Char.ofNat")
        codepoints = _utf8_codepoints(self.val)
        for i in range(len(codepoints) - 1, -1, -1):
            char_expr = char_of_nat.app(W_LitNat.int(codepoints[i]))
            expr = cons.app(char_expr).app(expr)
        return Name.from_str("String.ofList").app(expr)


    def instantiate(self, expr, depth=0):
        return self

    def subst_levels(self, substs):
        return self

    def subst_levels_lists(self, params, levels):
        return self

    def bind_fvar(self, fvar, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitStr)
        return self.val == other.val


class W_Sort(W_Expr):
    _attrs_ = ['level']
    _immutable_fields_ = ['level']

    def __init__(self, level):
        self.level = level
        lp = _LP_BIT if level.has_param else 0
        canon = _CANON_BIT if level._normal is level else 0
        self._packed = (
            (((level.hash() * 1000003) ^ 0x5071) & 0xFFFFFFFF) | lp | canon
        )

    def __repr__(self):
        # No class name here, as we wouldn't want to see <Sort Type>
        return "<%s>" % (self.str(),)


    def emit_to(self, exporter):
        lid = exporter.level_id(self.level)
        eid = exporter.next_expr_id()
        exporter.stream.write('{"ie":%d,"sort":%d}\n' % (eid, lid))
        return eid

    def to_format(self, constants, marker):
        """A ``Format`` for this Sort, tagged as a sort."""
        return _format.text(SORT, self.str())

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


    def expect_sort(self, env):
        return self.level

    def subst_levels(self, substs):
        new_level = self.level.subst_levels(substs)
        if new_level is self.level:
            return self
        return new_level.sort()

    def syntactic_eq(self, other):
        assert isinstance(other, W_Sort)
        return syntactic_eq(self.level, other.level)


PROP = W_LEVEL_ZERO.sort()
TYPE = W_LEVEL_ZERO.succ().sort()


# Takes the level params from 'const', and substitutes them into 'target'
@unroll_safe
def apply_const_level_params(const, target, env):
    decl = get_decl(env.declarations, const.name)
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
    _attrs_ = ['name', 'levels']
    _immutable_fields_ = ['name', 'levels']

    def __init__(self, name, levels):
        self.name = name
        lp = 0
        canon = _CANON_BIT
        h = name.hash()
        for each in levels:
            assert isinstance(each, W_Level), "%s is not a W_Level" % (each,)
            if each.has_param:
                lp = _LP_BIT
            if each._normal is not each:
                canon = 0
            h = (h * 1000003) ^ each.hash()
        self.levels = levels
        self._packed = (((h * 1000003) ^ 0xC057) & 0xFFFFFFFF) | lp | canon

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

    def def_eq(self, other):
        """
        Whether this is the same constant as ``other`` at definitionally
        equal universe levels.
        """
        assert isinstance(other, W_Const)
        if not self.name.syntactic_eq(other.name):
            return False
        if len(self.levels) != len(other.levels):
            return False
        for i, level in enumerate(self.levels):
            if not level.eq(other.levels[i]):
                return False
        return True


    def to_format(self, constants, marker):
        """
        A ``Format`` for this constant reference.

        Universe levels are omitted, matching Lean's ``pp.universes=false``
        default; declaration *headers* still show their level params (they
        render via ``name_with_levels_format`` directly).
        """
        return name_with_levels_format(self.name, [], constants)

    def str(self):
        return name_with_levels(self.name, self.levels)

    def syntactic_eq(self, other):
        assert isinstance(other, W_Const)
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


    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    @unroll_safe
    def subst_levels(self, substs):
        levels = self.levels
        if not levels:
            return self
        new_levels = None
        for i in range(len(levels)):
            new_level = levels[i].subst_levels(substs)
            if new_level is not levels[i]:
                if new_levels is None:
                    new_levels = list(levels)
                new_levels[i] = new_level
        if new_levels is None:
            return self
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
_NAT_REC_NAME = _NAT_NAME.child("rec")

_BOOL_TRUE = Name.simple("Bool").child("true").const()
_BOOL_FALSE = Name.simple("Bool").child("false").const()

_BIG_ZERO = rbigint.fromint(0)
# Max exponent for Nat.pow / Nat.shiftLeft to prevent excessive computation
_REDUCE_POW_MAX_EXP = rbigint.fromint(1 << 24)


class W_LitNat(W_Expr):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        self.val = val
        bf = 0
        self._packed = (((val.hash() * 1000003) ^ 0x4A75) & 0xFFFFFFFF) | (bf << 32)

    def __repr__(self):
        return "<LitNat %s>" % (self.val.str(),)

    @staticmethod
    def char(char):
        return _mk_w_litnat(rbigint.fromint(ord(char)))

    @staticmethod
    def int(i):
        return _mk_w_litnat(rbigint.fromint(i))

    @staticmethod
    def long(i):
        return _mk_w_litnat(rbigint.fromlong(i))


    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"natVal":%s}\n'
            % (eid, exporter.quote(self.val.str())),
        )
        return eid

    def str(self):
        return self.val.str()

    def to_format(self, constants, marker):
        """A ``Format`` tagging this nat literal."""
        return _format.text(LITERAL, self.str())

    def instantiate(self, expr, depth=0):
        return self

    def subst_levels(self, substs):
        return self

    def subst_levels_lists(self, params, levels):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitNat)
        return self.val.eq(other.val)

    def one_step_constructor(self):
        """
        Expose one Nat constructor: ``Nat.zero`` if the value is zero,
        otherwise ``Nat.succ (W_LitNat (val - 1))``.

        Used by iota reduction so the inductive step sees a concrete
        constructor without materialising the full Nat.succ chain.
        """
        if self.val.eq(rbigint.fromint(0)):
            return NAT_ZERO
        return NAT_SUCC.app(_mk_w_litnat(self.val.sub(rbigint.fromint(1))))

    def bind_fvar(self, fvar, depth):
        return self

    def incr_free_bvars(self, count, depth):
        return self


def is_nat_binop(name):
    """Whether ``name`` is one of the kernel's native binary Nat ops."""
    return (
        name_eq(name, _NAT_ADD)
        or name_eq(name, _NAT_SUB)
        or name_eq(name, _NAT_MUL)
        or name_eq(name, _NAT_POW)
        or name_eq(name, _NAT_GCD)
        or name_eq(name, _NAT_MOD)
        or name_eq(name, _NAT_DIV)
        or name_eq(name, _NAT_BEQ)
        or name_eq(name, _NAT_BLE)
        or name_eq(name, _NAT_LAND)
        or name_eq(name, _NAT_LOR)
        or name_eq(name, _NAT_XOR)
        or name_eq(name, _NAT_SHIFT_LEFT)
        or name_eq(name, _NAT_SHIFT_RIGHT)
    )


def nat_binop_value(name, v1, v2):
    """
    The native result of the binary Nat op ``name`` on the literal
    values ``v1`` and ``v2``: a ``W_LitNat``, a ``Bool`` constant for
    the predicates, or ``None`` when the op declines (a power with an
    exponent past the cap).
    """
    # Use name_eq (which is @elidable) so that with a promoted name the JIT
    # folds every comparison to a compile-time constant.
    if name_eq(name, _NAT_ADD):
        return _mk_w_litnat(v1.add(v2))
    if name_eq(name, _NAT_SUB):
        if v1.lt(v2):
            return _mk_w_litnat(rbigint.fromint(0))
        return _mk_w_litnat(v1.sub(v2))
    if name_eq(name, _NAT_MUL):
        return _mk_w_litnat(v1.mul(v2))
    if name_eq(name, _NAT_POW):
        if v2.gt(_REDUCE_POW_MAX_EXP):
            return None
        return _mk_w_litnat(v1.pow(v2))
    if name_eq(name, _NAT_GCD):
        return _mk_w_litnat(v1.gcd(v2))
    if name_eq(name, _NAT_MOD):
        if v2.eq(rbigint.fromint(0)):
            return _mk_w_litnat(v1)
        return _mk_w_litnat(v1.mod(v2))
    if name_eq(name, _NAT_DIV):
        if v2.eq(rbigint.fromint(0)):
            return _mk_w_litnat(rbigint.fromint(0))
        return _mk_w_litnat(v1.div(v2))
    if name_eq(name, _NAT_BEQ):
        if v1.eq(v2):
            return _BOOL_TRUE
        return _BOOL_FALSE
    if name_eq(name, _NAT_BLE):
        if v1.le(v2):
            return _BOOL_TRUE
        return _BOOL_FALSE
    if name_eq(name, _NAT_LAND):
        return _mk_w_litnat(v1.and_(v2))
    if name_eq(name, _NAT_LOR):
        return _mk_w_litnat(v1.or_(v2))
    if name_eq(name, _NAT_XOR):
        return _mk_w_litnat(v1.xor(v2))
    if name_eq(name, _NAT_SHIFT_LEFT):
        if v1.eq(_BIG_ZERO):
            return _mk_w_litnat(_BIG_ZERO)
        if v2.gt(_REDUCE_POW_MAX_EXP):
            return None
        return _mk_w_litnat(v1.lshift(v2.toint()))
    if name_eq(name, _NAT_SHIFT_RIGHT):
        if v1.eq(_BIG_ZERO):
            return _mk_w_litnat(_BIG_ZERO)
        try:
            shift = v2.toint()
        except OverflowError:
            return _mk_w_litnat(_BIG_ZERO)
        return _mk_w_litnat(v1.rshift(shift))
    return None


class W_Proj(W_Expr):
    _attrs_ = ['struct_name', 'field_index', 'struct_expr']
    _immutable_fields_ = ['struct_name', 'field_index', 'struct_expr']

    def __init__(self, struct_name, field_index, struct_expr):
        self.struct_name = struct_name
        self.field_index = field_index
        self.struct_expr = struct_expr
        sp = struct_expr._packed
        h = (struct_name.hash() * 1000003) ^ field_index
        h = (h * 1000003) ^ (sp & 0xFFFFFFFF)
        self._packed = (
            (((h * 1000003) ^ 0x9709) & 0xFFFFFFFF)
            | (sp & _NON_STYLE_UPPER_MASK)
        )


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

    def _field_name(self, constants):
        """The name of the projected field, or its numeric index as a string."""
        decl = constants.get(self.struct_name, None)
        if decl is not None:
            name = decl.w_kind.field_name(self.field_index)
            if name is not None:
                return name
        return "%d" % self.field_index

    def to_format(self, constants, marker):
        # When the struct_expr is the marked expression, widen the span
        # to cover the whole projection (struct_expr + "." + field_name)
        # rather than just the struct_expr alone.
        mark_whole = (
            marker.mark is not None
            and not marker.found
            and marker.mark is self.struct_expr
        )
        field_name = self._field_name(constants)
        needs_parens = isinstance(self.struct_expr, W_App)
        if mark_whole:
            marker.found = True
            inner = _sub(_NO_MARK, self.struct_expr, constants)
        else:
            inner = _sub(marker, self.struct_expr, constants)
        parts = []
        if needs_parens:
            parts.append(_format.text(PUNCT, "("))
        parts.append(inner)
        if needs_parens:
            parts.append(_format.text(PUNCT, ")"))
        parts.append(_format.text(PUNCT, "."))
        parts.append(_format.text(DECL_NAME, field_name))
        result = _format.concat(parts)
        if mark_whole:
            result = _format.tag(_format.MARK_TAG, result)
        return result


    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return self.with_expr(self.struct_expr.incr_free_bvars(count, depth))

    def bind_fvar(self, fvar, depth):
        if not self.has_fvar():
            return self
        new_expr = self.struct_expr.bind_fvar(fvar, depth)
        if new_expr is self.struct_expr:
            return self
        return self.with_expr(new_expr)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        return self.with_expr(self.struct_expr.instantiate(expr, depth))

    def subst_levels(self, substs):
        if not self.has_level_param():
            return self
        new_expr = self.struct_expr.subst_levels(substs)
        if new_expr is self.struct_expr:
            return self
        return self.with_expr(new_expr)

    def with_expr(self, expr):
        return self.struct_name.proj(self.field_index, expr)


    def syntactic_eq(self, other):
        assert isinstance(other, W_Proj)
        return (
            self.struct_name.syntactic_eq(other.struct_name)
            and self.field_index == other.field_index
            and syntactic_eq(self.struct_expr, other.struct_expr)
        )


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
            stack.append(current.body.instantiate(current.get_binder().fvar()))
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
    _attrs_ = ['name', 'type', 'body', '_binder']
    _immutable_fields_ = ['name', 'type', 'body']

    # Subclasses set this to a distinct tag so structurally-equal
    # lambdas and foralls don't collide in the content hash.
    _hash_tag = 0

    @always_inline
    def __init__(self, binder, body):
        if not we_are_translated():
            assert body is not None
            assert isinstance(binder, Binder)
        self._init_flat(
            binder.name, binder.type, body, binder._pos_style & 3, binder,
        )

    @always_inline
    def _init_flat(self, name, btype, body, style, binder):
        self._cache = 0
        self.name = name
        self.type = btype
        self.body = body
        self._binder = binder
        tp = btype._packed
        bp = body._packed
        body_range = ((bp >> 33) & _LOOSE_MASK) - 1
        if body_range < 0:
            body_range = 0
        binder_range = (tp >> 33) & _LOOSE_MASK
        loose = binder_range if binder_range > body_range else body_range
        flags = (tp | bp) & ((1 << 32) | _LP_BIT)
        # Content hash: mix binder's name + type + body.
        h = (name.hash() * 1000003) ^ (tp & 0xFFFFFFFF)
        h = (h * 1000003) ^ (bp & 0xFFFFFFFF)
        self._packed = (
            (((h * 1000003) ^ self._hash_tag) & 0xFFFFFFFF)
            | (loose << 33)
            | ((style & 3) << _STYLE_SHIFT)
            | flags
        )

    @always_inline
    def binder_style(self):
        return (self._packed >> _STYLE_SHIFT) & 3

    def is_default_binder(self):
        return self.binder_style() == _BINDER_DEFAULT

    def is_instance_binder(self):
        return self.binder_style() == _BINDER_INSTANCE

    def get_binder(self):
        b = self._binder
        if b is None:
            b = Binder(self.name, self.type, style=self.binder_style())
            self._binder = b
        return b

    @not_rpython
    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return (
            self.binder_style() == other.binder_style()
            and self.name == other.name
            and self.type == other.type
            and self.body == other.body
        )

    def contains_const(self, name):
        return (self.type.contains_const(name)
                or self.body.contains_const(name))

    def collect_consts_into(self, out, seen):
        self.type.collect_consts_into(out, seen)
        self.body.collect_consts_into(out, seen)

    # Subclasses (W_Lambda, W_ForAll) set this to their lean4export tag
    # and `_ie_first_tag` to whether `"ie"` precedes the discriminator
    # alphabetically (true for `"lam"` since `'i' < 'l'`, false for
    # `"forallE"` since `'f' < 'i'`).
    _export_tag = ""
    _ie_first_tag = False

    def emit_to(self, exporter):
        bnid = exporter.name_id(self.name)
        tid = exporter.expr_id(self.type)
        bid = exporter.expr_id(self.body)
        eid = exporter.next_expr_id()
        bi = _BINDER_INFO_NAMES[self.binder_style()]
        if self._ie_first_tag:
            exporter.stream.write(
                '{"ie":%d,"%s":{"binderInfo":"%s","body":%d,"name":%d,"type":%d}}\n'
                % (eid, self._export_tag, bi, bid, bnid, tid),
            )
        else:
            exporter.stream.write(
                '{"%s":{"binderInfo":"%s","body":%d,"name":%d,"type":%d},"ie":%d}\n'
                % (self._export_tag, bi, bid, bnid, tid, eid),
            )
        return eid


class W_ForAll(W_FunBase):
    _attrs_ = []

    _export_tag = "forallE"
    _ie_first_tag = False  # `'f' < 'i'`
    _hash_tag = 0xF0A1

    def _rebuild(self, new_type, new_body):
        b = self._binder
        if b is not None:
            new_b = b if new_type is self.type else b.with_type(new_type)
            return _mk_w_forall(new_b, new_body)
        return _mk_w_forall_flat(self.name, self.binder_style(), new_type, new_body)

    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        new_type = self.type.instantiate(expr, depth)
        new_body = self.body.instantiate(expr, depth + 1)
        if new_type is self.type and new_body is self.body:
            return self
        return self._rebuild(new_type, new_body)

    def syntactic_eq(self, other):
        assert isinstance(other, W_ForAll)
        return (
            self.binder_style() == other.binder_style()
            and syntactic_eq(self.name, other.name)
            and syntactic_eq(self.type, other.type)
            and syntactic_eq(self.body, other.body)
        )

    def bind_fvar(self, fvar, depth):
        if not self.has_fvar():
            return self
        new_type = self.type.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        if new_type is self.type and new_body is self.body:
            return self
        return self._rebuild(new_type, new_body)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return self._rebuild(
            self.type.incr_free_bvars(count, depth),
            self.body.incr_free_bvars(count, depth + 1),
        )

    def subst_levels(self, levels):
        if not self.has_level_param():
            return self
        new_type = self.type.subst_levels(levels)
        new_body = self.body.subst_levels(levels)
        if new_type is self.type and new_body is self.body:
            return self
        return self._rebuild(new_type, new_body)

    def to_format(self, constants, marker):
        """
        Render either as an arrow (``x → y``) or else really using ``∀ _, _``.

        ForAll represents two concepts which implementation-wise are
        "the "same", but which are differentiated when pretty printing.
        Those are:

            * universally quantified propositions, i.e. "true" foralls
            * dependent function types

        We try to follow Lean's real pretty printer for deciding when to
        render which.  Consecutive ``∀`` binders merge under a single ``∀``
        (with same-kind, same-type runs grouped, e.g. ``∀ (a b : Nat)``),
        matching Lean.  Either form breaks after the ``,``/``→`` and indents
        its right-hand side when it does not fit on a line.
        """
        is_forall, rhs = _forall_quantifier_step(self, constants)
        if is_forall:
            # Collect the maximal run of binders that each render as ∀.
            binders = [self.get_binder()]
            current = rhs
            while isinstance(current, W_ForAll):
                next_is_forall, next_rhs = _forall_quantifier_step(
                    current, constants,
                )
                if not next_is_forall:
                    break
                binders.append(current.get_binder())
                current = next_rhs
            body = current
            # One `fill` over `∀ ppSpace binder ... , ppSpace term`, mirroring
            # Lean's `forall` parser under the category `fill <| nest 2`. Each
            # binder group is itself a `fill` (its names/type wrap minimally —
            # see `_forall_binder_group_docs`) but is measured flattened by the
            # outer fill, so binders pack as many per line as fit, a binder too
            # wide for the line pushes `∀` onto its own line, and the body
            # joins the last binder line unless it too must wrap. Everything
            # nests by 2.
            parts = [_format.text(KEYWORD, "∀")]
            for group_doc in _forall_binder_group_docs(
                binders, constants, marker,
            ):
                parts.append(_format.LINE)
                parts.append(group_doc)
            parts.append(_format.text(PUNCT, ","))
            parts.append(_format.LINE)
            parts.append(_sub(marker, body, constants))
            return _format.fill(_format.nest(2, _format.concat(parts)))
        else:
            if self.is_default_binder() and not self.body.loose_bvar_range() > 0:
                wrap = isinstance(self.type, W_ForAll)
                inner = _sub(marker, self.type, constants)
                if wrap:
                    lhs = _format.concat([
                        _format.text(PUNCT, "("),
                        inner,
                        _format.text(PUNCT, ")"),
                    ])
                else:
                    lhs = inner
            elif (
                self.is_instance_binder()
                and not self.body.loose_bvar_range() > 0
                and self.name.has_macro_scopes()
            ):
                lhs = _format.concat([
                    _format.text(PUNCT, "["),
                    _sub(marker, self.type, constants),
                    _format.text(PUNCT, "]"),
                ])
            else:
                lhs = _sub(marker, self.get_binder(), constants)
            head = _format.concat([lhs, _format.text(OPERATOR, " →")])
            body = rhs

        return _format.group(_format.concat([
            head,
            _format.nest(2, _format.append(
                _format.LINE, _sub(marker, body, constants),
            )),
        ]))


def group_to_str(group):
    assert not group[-1].is_instance()

    names = " ".join([each.name.user_name().str() for each in group])
    if group[-1].is_default():
        return names

    return "%s%s%s" % (group[-1].left_bracket(), names, group[-1].right_bracket())


def _binder_group_format(group, constants):
    if group[-1].is_default():
        # Default binders carry no brackets; soft-break between names so a
        # long binder list fill-wraps (as Lean does).
        parts = []
        for i, binder in enumerate(group):
            if i > 0:
                parts.append(_format.LINE)
            parts.append(
                _format.text(BINDER_NAME, binder.name.user_name().str()),
            )
        return _format.concat(parts)
    parts = [_format.text(PUNCT, group[-1].left_bracket())]
    for i, binder in enumerate(group):
        if i > 0:
            parts.append(_format.text(PLAIN, " "))
        parts.append(_format.text(BINDER_NAME, binder.name.user_name().str()))
    parts.append(_format.text(PUNCT, group[-1].right_bracket()))
    return _format.concat(parts)


def _forall_quantifier_step(fa, constants):
    """
    Decide whether ``fa`` (a ``W_ForAll``) renders as a ``∀`` quantifier
    rather than an arrow, returning ``(is_forall, rhs)`` where ``rhs`` is the
    body with the binder instantiated to its free variable.

    Mirrors Lean: a ``∀`` is used when the result is a proposition and the
    binding is a genuine quantification (its variable is used, or its domain
    is not itself a proposition).
    """
    lhs_type = fa.type
    if isinstance(lhs_type, W_Const):
        # Tolerate names `constants` doesn't have (a partially registered
        # environment, e.g. mid-`ffi check`): rendering must never raise,
        # it just loses the ∀-vs-→ refinement.
        decl = constants.get(lhs_type.name, None)
        if decl is not None:
            lhs_type = decl.type
    elif isinstance(lhs_type, W_FVar):
        lhs_type = lhs_type.binder.type
    rhs = fa.body.instantiate(fa.get_binder().fvar())
    is_forall = (
        (not _is_prop_type(lhs_type, constants)
         and _is_prop_type(rhs, constants))
        or (fa.body.loose_bvar_range() > 0 and _is_prop_type(rhs, constants))
    )
    return is_forall, rhs


def _forall_binder_group_docs(binders, constants, marker):
    """
    A list of ``Format``s, one per ``∀`` binder group, grouped as Lean
    groups them: runs of adjacent binders with the same binder kind
    (brackets) and a syntactically equal type collapse into one
    ``(a b c : T)``.  The caller joins them with soft breaks.
    """
    docs = []
    i = 0
    n = len(binders)
    while i < n:
        b = binders[i]
        bstyle = b.style()
        j = i + 1
        while (j < n
               and binders[j].style() == bstyle
               and syntactic_eq(binders[j].type, b.type)):
            j += 1
        # Inside the brackets the names soft-break between each other and the
        # type breaks onto its own line after the `:`, all in a `fill` nested
        # by 2 — so a binder wider than the line wraps minimally, exactly as
        # Lean's does:
        #   (aaa bbb ccc
        #       ddd :
        #       Nat)
        inner = []
        for k in range(i, j):
            if inner:
                inner.append(_format.LINE)
            inner.append(
                _format.text(BINDER_NAME, binders[k].name.user_name().str()),
            )
        inner.append(_format.text(PUNCT, " :"))
        inner.append(_format.LINE)
        inner.append(_sub(marker, b.type, constants))
        docs.append(_format.concat([
            _format.text(PUNCT, b.left_bracket()),
            _format.fill(_format.nest(2, _format.concat(inner))),
            _format.text(PUNCT, b.right_bracket()),
        ]))
        i = j
    return docs


class W_Lambda(W_FunBase):
    _attrs_ = []

    _export_tag = "lam"
    _ie_first_tag = True  # `'i' < 'l'`
    _hash_tag = 0x1A3B

    def _binders_and_body(self, constants, marker):
        """
        Collect this lambda's flattened binder groups and its (instantiated)
        body, shared by the standalone and spliced renderings.

        Returns ``(binder_doc, body)`` where ``binder_doc`` is the soft-break
        joined binder list (a ``Format``) and ``body`` is the body expression.
        """
        binders = []
        binder_used = []
        current = self
        while isinstance(current, W_Lambda):
            binders.append(current.get_binder())
            binder_used.append(current.body.loose_bvar_range() > 0)
            current = current.body

        # One Format per emitted binder group / instance binder; joined with
        # soft breaks below so a long binder list fill-wraps (as Lean does).
        binder_docs = []
        current_group, last_style = [], binders[0].style()

        for i, binder in enumerate(binders):
            bstyle = binder.style()
            if binder.is_instance():
                if current_group:
                    binder_docs.append(
                        _binder_group_format(current_group, constants),
                    )
                    current_group = []
                if binder_used[i]:
                    binder_docs.append(binder.to_format(constants, marker))
                else:
                    binder_docs.append(_format.concat([
                        _format.text(PUNCT, "["),
                        _sub(marker, binder.type, constants),
                        _format.text(PUNCT, "]"),
                    ]))
                last_style = -1
            elif bstyle != last_style and current_group:
                binder_docs.append(
                    _binder_group_format(current_group, constants),
                )
                current_group, last_style = [binder], bstyle
            else:
                current_group.append(binder)
                last_style = bstyle
        if current_group:
            binder_docs.append(_binder_group_format(current_group, constants))

        binder_doc = _format.NIL
        for i, doc in enumerate(binder_docs):
            if i > 0:
                binder_doc = _format.append(binder_doc, _format.LINE)
            binder_doc = _format.append(binder_doc, doc)

        body = current
        for binder in reversed(binders):
            body = body.instantiate(binder.fvar())

        return binder_doc, body

    def to_format(self, constants, marker):
        binder_doc, body = self._binders_and_body(constants, marker)
        # The binder list and the body break independently (matching Lean):
        # the binders fill-wrap (continuation indented past `fun `), and the
        # body breaks after `↦` onto an indented line of its own.
        return _format.concat([
            _format.text(KEYWORD, "fun"),
            _format.text(PLAIN, " "),
            _format.fill(_format.nest(4, binder_doc)),
            _format.text(OPERATOR, " ↦"),
            _format.group(_format.nest(2, _format.append(
                _format.LINE, _sub(marker, body, constants),
            ))),
        ])

    def splice_format(self, constants, marker):
        """
        Render this lambda for *splicing* into an enclosing ``fill`` (e.g. as
        the final argument of an application), matching Lean's
        ``ppAllowUngrouped`` on ``fun``: no surrounding group, so the body's
        line break belongs to the enclosing fill rather than a group of its
        own.  The caller supplies the base indentation (a ``nest 2``), so the
        binders nest a further 2 and the body sits at the caller's level.
        """
        binder_doc, body = self._binders_and_body(constants, marker)
        return _format.concat([
            _format.text(KEYWORD, "fun"),
            _format.text(PLAIN, " "),
            _format.fill(_format.nest(2, binder_doc)),
            _format.text(OPERATOR, " ↦"),
            _format.LINE,
            _sub(marker, body, constants),
        ])

    def _rebuild(self, new_type, new_body):
        b = self._binder
        if b is not None:
            new_b = b if new_type is self.type else b.with_type(new_type)
            return _mk_w_lambda(new_b, new_body)
        return _mk_w_lambda_flat(self.name, self.binder_style(), new_type, new_body)

    def syntactic_eq(self, other):
        assert isinstance(other, W_Lambda)
        return (
            self.binder_style() == other.binder_style()
            and syntactic_eq(self.name, other.name)
            and syntactic_eq(self.type, other.type)
            and syntactic_eq(self.body, other.body)
        )

    def bind_fvar(self, fvar, depth):
        if not self.has_fvar():
            return self
        new_type = self.type.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        if new_type is self.type and new_body is self.body:
            return self
        return self._rebuild(new_type, new_body)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        new_type = self.type.instantiate(expr, depth)
        new_body = self.body.instantiate(expr, depth + 1)
        if new_type is self.type and new_body is self.body:
            return self
        return self._rebuild(new_type, new_body)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return self._rebuild(
            self.type.incr_free_bvars(count, depth),
            self.body.incr_free_bvars(count, depth + 1),
        )

    def subst_levels(self, substs):
        if not self.has_level_param():
            return self
        new_type = self.type.subst_levels(substs)
        new_body = self.body.subst_levels(substs)
        if new_type is self.type and new_body is self.body:
            return self
        return self._rebuild(new_type, new_body)


class W_Let(W_Expr):
    _attrs_ = ['name', 'type', 'value', 'body']
    _immutable_fields_ = ['name', 'type', 'value', 'body']

    def __init__(self, name, type, value, body):
        self.name = name
        self.type = type
        self.value = value
        self.body = body
        body_range = body.loose_bvar_range() - 1
        if body_range < 0:
            body_range = 0
        r = type.loose_bvar_range()
        vr = value.loose_bvar_range()
        if vr > r:
            r = vr
        if body_range > r:
            r = body_range
        fvar = type.has_fvar() or value.has_fvar() or body.has_fvar()
        bf = (r << 1) | (1 if fvar else 0)
        lp = (type._packed | value._packed | body._packed) & _LP_BIT
        h = (name.hash() * 1000003) ^ type.hash()
        h = (h * 1000003) ^ value.hash()
        h = (h * 1000003) ^ body.hash()
        self._packed = (((h * 1000003) ^ 0x1ED7) & 0xFFFFFFFF) | (bf << 32) | lp

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

    def to_format(self, constants, marker):
        fvar = self.name.binder(type=self.type).fvar()
        body = self.body.instantiate(fvar)
        # The binder type is omitted, matching Lean's `pp.letVarTypes=false`
        # default (`let x := v`). The value breaks onto its own indented line
        # when it does not fit; the newline before the body is always
        # mandatory, since the body would otherwise run into the binding.
        return _format.concat([
            _format.text(KEYWORD, "let"),
            _format.text(PLAIN, " "),
            _format.text(BINDER_NAME, self.name.str()),
            _format.text(OPERATOR, " :="),
            _format.group(_format.nest(2, _format.append(
                _format.LINE, _sub(marker, self.value, constants),
            ))),
            _format.text(PLAIN, "\n"),
            _sub(marker, body, constants),
        ])


    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        return self.name.let(
            type=self.type.instantiate(expr, depth),
            value=self.value.instantiate(expr, depth),
            body=self.body.instantiate(expr, depth + 1),
        )

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return self.name.let(
            type=self.type.incr_free_bvars(count, depth),
            value=self.value.incr_free_bvars(count, depth),
            body=self.body.incr_free_bvars(count, depth + 1),
        )

    def bind_fvar(self, fvar, depth):
        if not self.has_fvar():
            return self
        new_type = self.type.bind_fvar(fvar, depth)
        new_value = self.value.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        if (new_type is self.type
                and new_value is self.value
                and new_body is self.body):
            return self
        return self.name.let(
            type=new_type, value=new_value, body=new_body,
        )

    def syntactic_eq(self, other):
        assert isinstance(other, W_Let)
        return (
            syntactic_eq(self.name, other.name)
            and syntactic_eq(self.type, other.type)
            and syntactic_eq(self.value, other.value)
            and syntactic_eq(self.body, other.body)
        )


    def subst_levels(self, substs):
        if not self.has_level_param():
            return self
        new_type = self.type.subst_levels(substs)
        new_value = self.value.subst_levels(substs)
        new_body = self.body.subst_levels(substs)
        if (new_type is self.type
                and new_value is self.value
                and new_body is self.body):
            return self
        return self.name.let(
            type=new_type, value=new_value, body=new_body,
        )


class W_App(W_Expr):
    _attrs_ = ['fn', 'arg']
    _immutable_fields_ = ['fn', 'arg']

    @always_inline
    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg
        fp = fn._packed
        ap = arg._packed
        fn_range = (fp >> 33) & _LOOSE_MASK
        arg_range = (ap >> 33) & _LOOSE_MASK
        loose = fn_range if fn_range > arg_range else arg_range
        flags = (fp | ap) & ((1 << 32) | _LP_BIT)
        h = ((fp & 0xFFFFFFFF) * 1000003) ^ (ap & 0xFFFFFFFF)
        self._packed = (((h * 1000003) ^ 0xAB30) & 0xFFFFFFFF) | (loose << 33) | flags


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

    def __repr__(self):
        current, args = self.unapp()
        args.reverse()
        return "<W_App fn={!r} args={!r}>".format(current, args)


    def to_format(self, constants, marker):
        current, args = self.unapp()

        explicit_mask = None
        head_fmt = None
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
                        mask.append(decl_type.is_default_binder())
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
                    head_fmt = _format.text(DECL_NAME, current.name.str())

        if head_fmt is None:
            wrap_fn = isinstance(current, W_Lambda)
            inner = _sub(marker, current, constants)
            if wrap_fn:
                head_fmt = _format.concat([
                    _format.text(PUNCT, "("),
                    inner,
                    _format.text(PUNCT, ")"),
                ])
            else:
                head_fmt = inner

        parts = [head_fmt]
        n = len(args)
        for idx in range(n - 1, -1, -1):
            arg = args[idx]
            if explicit_mask is not None:
                mask_idx = n - 1 - idx
                if not explicit_mask[mask_idx]:
                    continue
            # A trailing lambda is spliced unparenthesized into this fill,
            # matching Lean's `ppAllowUngrouped` on `fun`: `f fun x ↦ y` keeps
            # `f fun x ↦` together and breaks only the lambda body.
            if idx == 0 and isinstance(arg, W_Lambda):
                parts.append(_format.append(
                    _format.LINE, arg.splice_format(constants, marker),
                ))
                continue
            needs_parens = (
                (idx == 0 and (isinstance(arg, W_App) or isinstance(arg, W_ForAll)))
                or (idx > 0 and (isinstance(arg, W_FunBase) or isinstance(arg, W_App)))
            )
            arg_fmt = _sub(marker, arg, constants)
            if needs_parens:
                arg_fmt = _format.concat([
                    _format.text(PUNCT, "("),
                    arg_fmt,
                    _format.text(PUNCT, ")"),
                ])
            # A soft break before each argument: arguments wrap and indent
            # under the function when the whole application does not fit.
            parts.append(_format.append(_format.LINE, arg_fmt))

        # `fill`, matching Lean's category formatter (`fill <| indent <| …`):
        # as many arguments as fit go on each line, the rest wrap, indented.
        return _format.fill(_format.nest(2, _format.concat(parts)))


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

    _QUOT_LIFT = Name.from_str("Quot.lift")
    _QUOT_MK = Name.from_str("Quot.mk")


    def bind_fvar(self, fvar, depth):
        if not self.has_fvar():
            return self
        new_fn = self.fn.bind_fvar(fvar, depth)
        new_arg = self.arg.bind_fvar(fvar, depth)
        if new_fn is self.fn and new_arg is self.arg:
            return self
        return new_fn.app(new_arg)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        new_fn = self.fn.instantiate(expr, depth)
        new_arg = self.arg.instantiate(expr, depth)
        if new_fn is self.fn and new_arg is self.arg:
            return self
        return new_fn.app(new_arg)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return self.fn.incr_free_bvars(count, depth).app(self.arg.incr_free_bvars(count, depth),
        )

    def subst_levels(self, substs):
        if not self.has_level_param():
            return self
        new_fn = self.fn.subst_levels(substs)
        new_arg = self.arg.subst_levels(substs)
        if new_fn is self.fn and new_arg is self.arg:
            return self
        return new_fn.app(new_arg)


class W_RecRule(_Item):
    _attrs_ = ['ctor_name', 'num_fields', 'rhs', '_simple_minor', '_rec_fields']
    _immutable_fields_ = ['ctor_name', 'num_fields', 'rhs']

    def __init__(self, ctor_name, num_fields, rhs):
        self.ctor_name = ctor_name
        self.num_fields = num_fields
        self.rhs = rhs
        #: Cached 0-based minor index when `rhs` has the standard shape
        #: `λ params... motives... minors... fields... =>
        #:    minor_i f0..f{nf-1} (rec params... motives... minors... f_{r0})...`,
        #: -2 = unchecked, -1 = general.
        self._simple_minor = -2
        #: List of 0-based recursive field indices for standard non-indexed
        #: recursive rules (e.g. `[1]` for `List.cons`, `[0]` for `Nat.succ`),
        #: or `None` when non-recursive / general.
        self._rec_fields = None

    def simple_minor(self, rec_decl, num_params, num_motives, num_minors, num_indices):
        m = self._simple_minor
        if m != -2:
            return m
        m = self._compute_simple_minor(
            rec_decl, num_params, num_motives, num_minors, num_indices,
        )
        self._simple_minor = m
        return m

    @dont_inline
    def _compute_simple_minor(
        self, rec_decl, num_params, num_motives, num_minors, num_indices,
    ):
        nf = self.num_fields
        total = num_params + num_motives + num_minors
        expected = total + nf
        cur = self.rhs
        k = 0
        while k < expected:
            if not isinstance(cur, W_Lambda):
                return -1
            cur = cur.body
            k += 1
        rev_args = []
        while isinstance(cur, W_App):
            rev_args.append(cur.arg)
            cur = cur.fn
        if not isinstance(cur, W_BVar):
            return -1
        minor_bvar = cur.id
        if minor_bvar < nf or minor_bvar >= nf + num_minors:
            return -1
        n_app = len(rev_args)
        if n_app < nf:
            return -1
        k = 0
        while k < nf:
            arg = rev_args[n_app - 1 - k]
            if not isinstance(arg, W_BVar) or arg.id != nf - 1 - k:
                return -1
            k += 1
        sminor = (nf + num_minors - 1) - minor_bvar
        if n_app == nf:
            self._rec_fields = None
            return sminor
        if num_indices != 0:
            return -1
        dlvls = rec_decl.levels
        nlvls = len(dlvls)
        rec_fields = []
        idx = n_app - nf - 1
        while idx >= 0:
            rarg = rev_args[idx]
            if not isinstance(rarg, W_App):
                return -1
            rfield = rarg.arg
            if not isinstance(rfield, W_BVar):
                return -1
            fbvar = rfield.id
            if fbvar < 0 or fbvar >= nf:
                return -1
            rcur = rarg.fn
            t = 0
            while t < total:
                if not isinstance(rcur, W_App):
                    return -1
                ra = rcur.arg
                if not isinstance(ra, W_BVar) or ra.id != nf + t:
                    return -1
                rcur = rcur.fn
                t += 1
            if not isinstance(rcur, W_Const):
                return -1
            if rcur.name is not rec_decl.name:
                return -1
            rlvls = rcur.levels
            if len(rlvls) != nlvls:
                return -1
            u = 0
            while u < nlvls:
                if rlvls[u] is not dlvls[u].as_level_param():
                    return -1
                u += 1
            rec_fields.append(nf - 1 - fbvar)
            idx -= 1
        self._rec_fields = rec_fields
        return sminor


#: How much of an inductive block is already in scope during a check.
STAGE_ALL = 0
STAGE_PRE_BLOCK = 1
STAGE_IND_ONLY = 2

#: Bit 62 marks a computed prop-argument bitmask; bits `0..61` indicate that
#: argument `k` of a declaration's type lives in `Prop`.
_PROP_MASK_DONE = 1 << 62

_PM_SORT_UNKNOWN = 0
_PM_SORT_PROP = 1
_PM_SORT_NON_PROP = 2
_PM_SORT_LEVEL = 3

class _PropMaskPlanTable(object):
    """Runtime table of level-dependent `_PropMaskPlan`s indexed by
    `(-_prop_mask) - 2` so `W_Declaration` avoids carrying an extra GC
    pointer slot for the ~95% of declarations whose prop mask is
    level-independent.

    Held on an instance with a runtime-allocated list rather than a
    module-level `[]` literal so RPython's flowspace cannot constant-fold
    `len(...)` to 0 at translation time.
    """

    _attrs_ = ['plans']

    def __init__(self):
        self.plans = None

    def add(self, plan):
        plans = self.plans
        if plans is None:
            plans = []
            self.plans = plans
        idx = len(plans)
        plans.append(plan)
        return idx

    def get(self, idx):
        plans = self.plans
        assert plans is not None
        return plans[idx]


_PROP_MASK_PLANS = _PropMaskPlanTable()

#: Reusable scratch arrays for non-reentrant `W_Declaration.init_prop_mask`,
#: avoiding per-declaration list allocations.
_PM_BINDER_ARITY = [0] * 62
_PM_BINDER_SORT = [0] * 62
_PM_BINDER_LVL = [None] * 62


class _PropMaskPlan(object):
    """Level-parameter-dependent prop-argument bitmask plan for a
    `W_Declaration`. Bits in `base_mask` (with `_PROP_MASK_DONE` set) are
    unconditionally `Prop`; each entry `(bits[i], param_idxs[i], levels[i])`
    adds `1 << bits[i]` when the instantiated universe level normalizes to
    zero (`param_idxs[i] >= 0` indexes `e_levels` directly without
    substitution)."""

    _attrs_ = ['base_mask', 'bits', 'param_idxs', 'levels']
    _immutable_fields_ = ['base_mask', 'bits', 'param_idxs', 'levels']

    def __init__(self, base_mask, bits, param_idxs, levels):
        self.base_mask = base_mask
        self.bits = bits
        self.param_idxs = param_idxs
        self.levels = levels

    def eval(self, decl_levels, e_levels):
        mask = self.base_mask
        bits = self.bits
        pidxs = self.param_idxs
        lvls = self.levels
        i = 0
        n = len(bits)
        while i < n:
            pi = pidxs[i]
            if pi >= 0:
                slvl = e_levels[pi]
            else:
                slvl = lvls[i].subst_levels_lists(decl_levels, e_levels)
            if (isinstance(slvl, W_LevelZero)
                    or isinstance(slvl.normalize(), W_LevelZero)):
                mask |= (1 << bits[i])
            i += 1
        return mask


def _pm_level_sort_class(lvl):
    if isinstance(lvl, W_LevelZero):
        return _PM_SORT_PROP
    if lvl.is_not_zero():
        return _PM_SORT_NON_PROP
    if isinstance(lvl.normalize(), W_LevelZero):
        return _PM_SORT_PROP
    return _PM_SORT_LEVEL


def _pm_decl_ret_sort(decl):
    cur = decl.type
    m = 0
    while isinstance(cur, W_ForAll):
        cur = cur.body
        m += 1
    if isinstance(cur, W_Sort):
        return m, cur.level
    return -1, None


def _pm_unwrap_id_wrapper(e, declarations):
    """Unwrap transparent identity wrappers such as `outParam A`,
    `semiOutParam A`, `optParam A v`, and `autoParam A t`."""
    depth = 0
    while isinstance(e, W_App) and depth < 4:
        fn = e.fn
        if isinstance(fn, W_Const):
            hd = find_decl(declarations, fn.name)
            if hd is not None:
                wk = hd.w_kind
                if isinstance(wk, W_Definition):
                    val = wk.value
                    if isinstance(val, W_Lambda):
                        body = val.body
                        if isinstance(body, W_BVar) and body.id == 0:
                            e = e.arg
                            depth += 1
                            continue
        elif isinstance(fn, W_App):
            fn2 = fn.fn
            if isinstance(fn2, W_Const):
                hd = find_decl(declarations, fn2.name)
                if hd is not None:
                    wk = hd.w_kind
                    if isinstance(wk, W_Definition):
                        val = wk.value
                        if isinstance(val, W_Lambda):
                            b1 = val.body
                            if isinstance(b1, W_Lambda):
                                b2 = b1.body
                                if isinstance(b2, W_BVar) and b2.id == 1:
                                    e = fn.arg
                                    depth += 1
                                    continue
        break
    return e


def _pm_is_opaque_type_head(wk):
    if (isinstance(wk, W_Inductive)
            or isinstance(wk, W_Constructor)
            or isinstance(wk, W_Axiom)
            or isinstance(wk, W_Opaque)):
        return True
    if isinstance(wk, W_Quotient) and wk.kind == W_Quotient.KIND_TYPE:
        return True
    return False


def _pm_const_tail_safe(const_e, nargs, declarations, depth):
    hd = find_decl(declarations, const_e.name)
    if hd is None:
        return False
    wk = hd.w_kind
    if _pm_is_opaque_type_head(wk):
        return True
    if depth <= 0 or not isinstance(wk, W_Definition):
        return False
    val = wk.value
    m = 0
    while isinstance(val, W_Lambda):
        val = val.body
        m += 1
    if nargs < m:
        return False
    if isinstance(val, W_Sort):
        return nargs == m
    vhead = val
    vnargs = 0
    while isinstance(vhead, W_App):
        vhead = vhead.fn
        vnargs += 1
    if isinstance(vhead, W_Const):
        return _pm_const_tail_safe(
            vhead, vnargs + (nargs - m), declarations, depth - 1,
        )
    return False


def _pm_tail_has_no_prop_args(cur, declarations, depth):
    """Whether ``cur`` (the trailing return type after all syntactic
    `W_ForAll`s) cannot WHNF to a `W_ForAll` with any `Prop`-typed argument."""
    if isinstance(cur, W_Sort):
        return True
    head = cur
    nargs = 0
    while isinstance(head, W_App):
        head = head.fn
        nargs += 1
    if isinstance(head, W_BVar):
        return True
    if not isinstance(head, W_Const):
        return False
    hd = find_decl(declarations, head.name)
    if hd is None:
        return False
    wk = hd.w_kind
    if _pm_is_opaque_type_head(wk):
        return True
    if depth <= 0 or not isinstance(wk, W_Definition):
        return False
    val = wk.value
    m = 0
    while isinstance(val, W_Lambda):
        val = val.body
        m += 1
    if nargs < m:
        return False
    if isinstance(val, W_Sort):
        return nargs == m
    vhead = val
    vnargs = 0
    while isinstance(vhead, W_App):
        vhead = vhead.fn
        vnargs += 1
    if isinstance(vhead, W_Const):
        return _pm_const_tail_safe(
            vhead, vnargs + (nargs - m), declarations, depth - 1,
        )
    # Handle `Set`-like aliases (`def Set (α : Type u) := α → Prop`) whose
    # sole unfolded binder domain is guaranteed non-Prop and ends in a Sort.
    if nargs == m and isinstance(val, W_ForAll) and isinstance(val.body, W_Sort):
        vdom = val.type
        if isinstance(vdom, W_BVar):
            pidx = m - 1 - vdom.id
            if 0 <= pidx < m:
                tcur = hd.type
                ti = 0
                while ti < pidx and isinstance(tcur, W_ForAll):
                    tcur = tcur.body
                    ti += 1
                if isinstance(tcur, W_ForAll):
                    pdom = _pm_unwrap_id_wrapper(tcur.type, declarations)
                    if isinstance(pdom, W_Sort) and pdom.level.is_not_zero():
                        return True
    return False


class W_Declaration(_Item):
    _attrs_ = [
        'name', 'type', 'w_kind', 'levels', 'safety', 'index', 'group',
        '_prop_mask',
    ]
    _immutable_fields_ = ['name', 'type', 'w_kind', 'levels', 'safety']

    def __init__(self, name, type, w_kind, levels, safety=SAFETY_SAFE):
        self.name = name
        self.type = type
        self.w_kind = w_kind
        for each in levels:
            assert isinstance(each, Name), "%s is not a level name" % (each,)
        self.levels = levels
        #: One of the `SAFETY_*` constants: `DefinitionVal.safety` for a
        #: definition, `isUnsafe` (unsafe or safe) for every other kind.
        self.safety = safety
        #: Position in declaration order, or -1 when the order is unknown.
        #: A declaration may use only constants declared before it, so
        #: nothing can rest on itself or on something not yet checked.
        self.index = -1
        #: Members of one inductive block, or of one unsafe or partial
        #: mutual block, share a group and may use each other regardless
        #: of `index`. -1 when the declaration belongs to no block.
        self.group = -1
        #: Cached prop-argument bitmask across store resets:
        #:   0   = uncomputed
        #:   >0  = permanent level-independent `_PROP_MASK_DONE | mask`
        #:   -1  = requires dynamic computation
        #:   <=-2 = level-dependent static plan at `_PROP_MASK_PLANS[(-m) - 2]`
        self._prop_mask = 0

    @dont_inline
    def init_prop_mask(self, declarations):
        """Statically analyze `self.type` once to cache which argument
        positions (0..61) live in `Prop`, avoiding `TermStore` instantiation
        and type inference in `Machine._compute_prop_mask`."""
        cur = self.type
        mask = 0
        cond_bits = None
        cond_pidxs = None
        cond_lvls = None
        binder_arity = _PM_BINDER_ARITY
        binder_sort = _PM_BINDER_SORT
        binder_lvl = _PM_BINDER_LVL
        lvl_dirty = False
        ok = True
        k = 0
        while isinstance(cur, W_ForAll) and k < 62:
            dom = _pm_unwrap_id_wrapper(cur.type, declarations)
            inner = dom
            p = 0
            while isinstance(inner, W_ForAll):
                inner = _pm_unwrap_id_wrapper(inner.body, declarations)
                p += 1
            if isinstance(inner, W_Sort):
                sc = _pm_level_sort_class(inner.level)
                binder_arity[k] = p
                binder_sort[k] = sc
                if sc == _PM_SORT_LEVEL:
                    binder_lvl[k] = inner.level
                    lvl_dirty = True
                cls = _PM_SORT_NON_PROP
                lvl = None
            else:
                binder_arity[k] = -1
                binder_sort[k] = _PM_SORT_UNKNOWN
                head = inner
                nargs = 0
                while isinstance(head, W_App):
                    head = head.fn
                    nargs += 1
                if isinstance(head, W_BVar):
                    bid = head.id
                    if bid >= p:
                        j = k - 1 - (bid - p)
                        if 0 <= j < k and binder_arity[j] == nargs:
                            cls = binder_sort[j]
                            lvl = binder_lvl[j]
                        else:
                            ok = False
                            break
                    else:
                        ok = False
                        break
                elif isinstance(head, W_Const):
                    hd = find_decl(declarations, head.name)
                    if hd is None:
                        ok = False
                        break
                    m, rlvl = _pm_decl_ret_sort(hd)
                    if m < 0 or nargs != m:
                        ok = False
                        break
                    assert rlvl is not None
                    cls = _pm_level_sort_class(rlvl)
                    lvl = None
                    if cls == _PM_SORT_LEVEL:
                        if len(head.levels) != len(hd.levels):
                            ok = False
                            break
                        slvl = rlvl.subst_levels_lists(hd.levels, head.levels)
                        cls = _pm_level_sort_class(slvl)
                        if cls == _PM_SORT_LEVEL:
                            lvl = slvl
                else:
                    ok = False
                    break
            if cls == _PM_SORT_UNKNOWN:
                ok = False
                break
            if cls == _PM_SORT_PROP:
                mask |= (1 << k)
            elif cls == _PM_SORT_LEVEL:
                assert lvl is not None
                if cond_bits is None:
                    cond_bits = []
                    cond_pidxs = []
                    cond_lvls = []
                pidx = -1
                if isinstance(lvl, W_LevelParam):
                    dlevels = self.levels
                    pi = 0
                    nl = len(dlevels)
                    while pi < nl:
                        if dlevels[pi].syntactic_eq(lvl.name):
                            pidx = pi
                            break
                        pi += 1
                cond_bits.append(k)
                cond_pidxs.append(pidx)
                cond_lvls.append(W_LEVEL_ZERO if pidx >= 0 else lvl)
            cur = cur.body
            k += 1
        if lvl_dirty:
            ci = 0
            while ci < k:
                binder_lvl[ci] = None
                ci += 1
        if not ok:
            self._prop_mask = -1
            return -1
        if k < 62:
            tail = _pm_unwrap_id_wrapper(cur, declarations)
            if not _pm_tail_has_no_prop_args(tail, declarations, 3):
                self._prop_mask = -1
                return -1
        base = _PROP_MASK_DONE | mask
        if cond_bits is None:
            self._prop_mask = base
            return base
        idx = _PROP_MASK_PLANS.add(
            _PropMaskPlan(base, cond_bits, cond_pidxs, cond_lvls),
        )
        dm = -(idx + 2)
        self._prop_mask = dm
        return dm

    @not_rpython
    def __eq__(self, other):
        # Where a declaration sits (`index`, `group`) is a property of
        # the environment it was registered in, not of the declaration.
        if self.__class__ is not other.__class__:
            return NotImplemented
        return (
            self.name == other.name
            and self.type == other.type
            and self.w_kind == other.w_kind
            and self.levels == other.levels
            and self.safety == other.safety
        )

    def is_unsafe(self):
        return self.safety == SAFETY_UNSAFE

    def group_key(self):
        """
        The name identifying this declaration's block, or ``None`` when
        it may only use what precedes it.
        """
        return self.w_kind.group_key(self.name, self.safety)

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
            levels.append(param.as_level_param())
        return self.name.const(levels=levels)

    def to_format(self, constants, marker):
        return self.w_kind.decl_format(
            self.name, self.levels, self.type, constants, marker,
        )

    def tokens(self, constants, mark=None, span_holder=None):
        """
        Produce a token stream for syntax-highlighted output.

        When ``mark`` is provided, it identifies an expression whose token
        span should be recorded into ``span_holder[0]`` as a
        ``(start_idx, end_idx)`` tuple.
        """
        return _tokens_from_format(
            self.to_format(constants, _marker_for(mark)), span_holder,
        )

    def type_check(self, tc):
        from rpylean.exceptions import LooseBoundVariable

        if self.type.loose_bvar_range() > 0:
            raise LooseBoundVariable(self.type.loose_bvar_range() - 1)
        try:
            error = self.w_kind.type_check(self.type, tc)
        except W_CheckError as error:
            error.name = self.name
            error.declaration = self
            return error
        if error is not None:
            error.name = self.name
            error.declaration = self
        return error


class W_DeclarationKind(_Item):
    _attrs_ = []

    def group_key(self, name, safety):
        """
        The name identifying the block a declaration of this kind with
        the given name and safety belongs to (see `W_Declaration.group`),
        or ``None`` when it belongs to none.
        """
        return None

    # Returns the value associated with this declaration kind.
    # This is the def value for a Definition, and `None` for things like Inductive
    def get_delta_reduce_target(self):
        return None

    def drop_checked_value(self):
        """
        Release any value expression that is dead once this declaration
        has been type-checked, so its (often large) sub-tree can be
        reclaimed mid-run. No-op by default; only kinds that are never
        delta-unfolded — whose value the checker therefore never touches
        again — override it (see ``W_Theorem``). A no-op for definitions,
        whose value must survive for delta-reduction.
        """

    def is_constructor(self):
        """Polymorphic predicate: `W_Constructor` overrides to True."""
        return False

    def allows_warm_cache(self):
        """Whether checking a declaration of this kind may reuse a warm
        `Machine` across consecutive declarations (the declaration only calls
        `check_value` and never modifies inductive-block `stage`)."""
        return False

    def field_name(self, index):
        """The name of the field at ``index``, or None."""
        return None

    def register_exporter_index(self, exporter, name):
        """Hook called once per registered decl before `dump_all`.

        Inductives populate ``ctors_of`` / ``parent_inductive`` lookups
        here; recursors populate ``recs_of``. Other kinds don't need
        anything indexed.
        """

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


class _ProjFieldRule(object):
    """Static projection-chain shortcut for a `DirectCB` field
    `cb.args[num_params + fidx]` whose beta/delta expansion on `req_extra`
    applied arguments reduces directly to a pure chain of kernel projections
    `Proj(S_r, i_r, ... Proj(S_1, i_1, target) ...)` (stored innermost-first)
    applied to the remaining trailing arguments starting at `tail_start`.

    Covers Mathlib `FunLike` / `SetLike` / `EquivLike` coercions (e.g.
    `LinearMap.instFunLike`, `ContinuousLinearMap.funLike`,
    `ContinuousMap.instFunLike`, `LinearIsometryEquiv.instEquivLike`,
    `Submodule.setLike`) and Lean 4 heterogeneous operator bridges
    (`instHAdd`, `instHMul`, `instHSub`, `instHSMul`, `instHPow`,
    `EquivLike.toFunLike`)."""

    _attrs_ = [
        'req_extra', 'target_bvar', 'target_extra', 'tail_start',
        'struct_names', 'field_indices',
    ]
    _immutable_fields_ = [
        'req_extra', 'target_bvar', 'target_extra', 'tail_start',
        'struct_names', 'field_indices',
    ]

    def __init__(self, req_extra, target_bvar, target_extra, tail_start,
                 struct_names, field_indices):
        self.req_extra = req_extra
        self.target_bvar = target_bvar
        self.target_extra = target_extra
        self.tail_start = tail_start
        self.struct_names = struct_names
        self.field_indices = field_indices


_NO_PROJ_RULE = _ProjFieldRule(-1, -1, -1, 0, [], [])


def _match_proj_wrapper(decl):
    """If ``decl`` is a transparent `W_Definition` of the form
    `λ x_0 ... x_{m-1} => Proj(S, idx, BVar(b))` (with `0 <= b < m`),
    return `(m, b, S, idx)`; otherwise return `(-1, -1, None, -1)`."""
    wk = decl.w_kind
    if not isinstance(wk, W_Definition):
        return -1, -1, None, -1
    target = wk.get_delta_reduce_target()
    if target is None:
        return -1, -1, None, -1
    m = 0
    cur = target
    while isinstance(cur, W_Lambda):
        cur = cur.body
        m += 1
    if m <= 0 or not isinstance(cur, W_Proj):
        return -1, -1, None, -1
    inner = cur.struct_expr
    if not isinstance(inner, W_BVar):
        return -1, -1, None, -1
    bid = inner.id
    if bid < 0 or bid >= m:
        return -1, -1, None, -1
    return m, bid, cur.struct_name, cur.field_index


def _peel_proj_chain(expr, declarations, allow_eta_short, max_depth):
    """Walk ``expr`` outside-in peeling `W_Proj` nodes and saturated (or
    `DFunLike.coe`-style) projection-wrapper applications.

    Returns `(end_expr, eta_short, names_innermost, indices_innermost)` where
    `names_innermost` / `indices_innermost` are empty on failure."""
    names_rev = []
    indices_rev = []
    cur = expr
    eta_short = False
    steps = 0
    while steps < 16:
        steps += 1
        if isinstance(cur, W_Proj):
            names_rev.append(cur.struct_name)
            indices_rev.append(cur.field_index)
            cur = cur.struct_expr
            continue
        if isinstance(cur, W_App):
            rev_args = []
            node = cur
            while isinstance(node, W_App):
                rev_args.append(node.arg)
                node = node.fn
            if not isinstance(node, W_Const):
                break
            g_decl = find_decl(declarations, node.name)
            if g_decl is None or len(node.levels) != len(g_decl.levels):
                break
            mg, bg, sname, fidx = _match_proj_wrapper(g_decl)
            if mg < 0 or sname is None:
                break
            na = len(rev_args)
            if na == mg:
                names_rev.append(sname)
                indices_rev.append(fidx)
                cur = rev_args[bg]
                continue
            if na == mg + 1 and max_depth > 0:
                # e.g. `DFunLike.coe α β (LinearMap.instFunLike ...) x`
                inst_ast = rev_args[1 + bg]
                in_node = inst_ast
                in_na = 0
                while isinstance(in_node, W_App):
                    in_node = in_node.fn
                    in_na += 1
                if not isinstance(in_node, W_Const):
                    break
                h_decl = find_decl(declarations, in_node.name)
                if h_decl is None or len(in_node.levels) != len(h_decl.levels):
                    break
                h_wk = h_decl.w_kind
                if not isinstance(h_wk, W_Definition):
                    break
                h_cb = h_wk._ctor_body
                if h_cb is None:
                    h_cb = h_wk.init_ctor_body(declarations)
                if (h_cb.m < 0
                        or h_cb.delegate_const is not None
                        or h_cb.let_vals is not None
                        or in_na < h_cb.m):
                    break
                sub = h_cb.proj_field_rule(fidx, declarations, max_depth - 1)
                if (sub is None
                        or sub.req_extra != 1
                        or sub.target_extra != 0
                        or sub.tail_start != 1):
                    break
                j = len(sub.struct_names) - 1
                while j >= 0:
                    names_rev.append(sub.struct_names[j])
                    indices_rev.append(sub.field_indices[j])
                    j -= 1
                cur = rev_args[0]
                continue
            if (allow_eta_short
                    and len(names_rev) == 0
                    and na == mg - 1
                    and bg == 0):
                # e.g. `ContinuousMap.instFunLike.field[0] = ContinuousMap.toFun α β tα tβ`
                names_rev.append(sname)
                indices_rev.append(fidx)
                eta_short = True
                break
        break
    n = len(names_rev)
    if n == 0:
        return cur, False, [], []
    names = [names_rev[n - 1 - i] for i in range(n)]
    indices = [indices_rev[n - 1 - i] for i in range(n)]
    return cur, eta_short, names, indices


class _PeelResult(object):
    """Cached static result of peeling a projection chain `(f0, f1, ...)` on a
    `_CtorBody` (direct or delegating)."""

    _attrs_ = ['raw_field', 'cur_nlets', 'popped', 'bvar_id', 'arg_idx', 'inner_mask']
    _immutable_fields_ = [
        'raw_field', 'cur_nlets', 'popped', 'bvar_id', 'arg_idx', 'inner_mask',
    ]

    def __init__(self, raw_field, cur_nlets, popped, bvar_id, arg_idx, inner_mask):
        self.raw_field = raw_field
        self.cur_nlets = cur_nlets
        self.popped = popped
        self.bvar_id = bvar_id
        self.arg_idx = arg_idx
        self.inner_mask = inner_mask


_NO_PEEL = _PeelResult(None, 0, 0, -1, -1, -2)


@always_inline
def pack_proj_chain_key(fidxs, pbase, ptop):
    """Pack up to 4 innermost projection indices `fidxs[ptop-1 .. ptop-d]` into
    a positive 28-bit integer key whose low 3 bits hold ``d`` (1..4), or 0."""
    d = ptop - pbase
    if d <= 0:
        return 0
    if d > 4:
        d = 4
    key = d
    shift = 3
    i = 0
    while i < d:
        f = fidxs[ptop - 1 - i]
        if f < 0 or f >= 64:
            if i == 0:
                return 0
            return (key & ~7) | i
        key |= f << shift
        shift += 6
        i += 1
    return key


class _CtorBody(object):
    """Pre-stripped constructor body for a `W_Definition` of the form
    `λ... => let... => Ctor p_0 ... p_{np-1} f_0 ...` (direct:
    ``delegate_const is None``) or a saturated wrapper
    `λ... => let... => Inner a_0 ... a_{k-1}` whose target ``Inner`` itself
    has a valid `_CtorBody` (delegating: ``delegate_const is not None``)."""

    _attrs_ = [
        'm', 'num_params', 'let_vals', 'args', 'uses_lets',
        'delegate_const', 'delegate_decl', 'field_masks', 'proj_rules',
        'peel_cache',
    ]
    _immutable_fields_ = [
        'm', 'num_params', 'let_vals', 'args', 'uses_lets',
        'delegate_const', 'delegate_decl',
    ]

    def __init__(self, m, num_params, let_vals, args, uses_lets,
                 delegate_const=None, delegate_decl=None):
        self.m = m
        self.num_params = num_params
        self.let_vals = let_vals
        self.args = args
        self.uses_lets = uses_lets
        self.delegate_const = delegate_const
        self.delegate_decl = delegate_decl
        self.field_masks = None
        self.proj_rules = None
        self.peel_cache = None

    def proj_field_rule(self, fidx, declarations, max_depth=4):
        """Return a `_ProjFieldRule` if this direct `_CtorBody`'s field
        ``fidx`` statically collapses to a pure projection chain, else None."""
        if fidx < 0 or self.delegate_const is not None or self.let_vals is not None:
            return None
        pr = self.proj_rules
        if pr is not None and fidx < len(pr):
            r = pr[fidx]
            if r is not None:
                return r if r.req_extra >= 0 else None
        if pr is None:
            pr = [None] * (fidx + 1)
            self.proj_rules = pr
        elif fidx >= len(pr):
            pr.extend([None] * (fidx + 1 - len(pr)))
        # Install negative sentinel before recursing so cycles terminate.
        pr[fidx] = _NO_PROJ_RULE
        rule = self._compute_proj_field_rule(fidx, declarations, max_depth)
        if rule is not None:
            pr[fidx] = rule
        return rule

    @dont_inline
    def _compute_proj_field_rule(self, fidx, declarations, max_depth):
        idx = self.num_params + fidx
        if idx >= len(self.args):
            return None
        raw = self.args[idx]
        k = 0
        cur = raw
        while isinstance(cur, W_Lambda):
            cur = cur.body
            k += 1
        # Case 1: direct projection chain (k == 0 or k == 1).
        if k <= 1:
            end, eta_short, names, indices = _peel_proj_chain(
                cur, declarations, k == 0, max_depth,
            )
            if len(names) > 0:
                if eta_short:
                    return _ProjFieldRule(1, -1, 0, 1, names, indices)
                if isinstance(end, W_BVar):
                    bid = end.id
                    if k == 0 and 0 <= bid < self.m:
                        return _ProjFieldRule(0, bid, -1, 0, names, indices)
                    if k == 1 and bid == 0:
                        return _ProjFieldRule(1, -1, 0, 1, names, indices)
        # Case 2: k >= 1 lambdas whose trailing arguments pass through to a
        # projection chain on a constructor-wrapper BVar (e.g. `instHAdd`,
        # `instHMul`, `instHSub`, `instHPow`) or on the first lambda arg.
        if k >= 1:
            base_expr = cur
            stripped = 0
            while stripped < k and isinstance(base_expr, W_App):
                arg = base_expr.arg
                if not isinstance(arg, W_BVar) or arg.id != stripped:
                    break
                base_expr = base_expr.fn
                stripped += 1
            if stripped == k:
                end, eta_short, names, indices = _peel_proj_chain(
                    base_expr, declarations, False, max_depth,
                )
                if len(names) > 0 and not eta_short and isinstance(end, W_BVar):
                    bid = end.id
                    if k <= bid < k + self.m:
                        return _ProjFieldRule(
                            k, bid - k, -1, 0, names, indices,
                        )
            elif stripped == k - 1 and stripped > 0:
                end, eta_short, names, indices = _peel_proj_chain(
                    base_expr, declarations, False, max_depth,
                )
                if len(names) > 0 and not eta_short and isinstance(end, W_BVar):
                    if end.id == stripped:
                        return _ProjFieldRule(k, -1, 0, 1, names, indices)
        return None

    def field_mask(self, fidx):
        """Bitmask of this definition's ``m`` lambda BVars (``0 .. m-1``,
        shifted past ``len(let_vals)`` if any) needed to compute structure
        field ``fidx``, or ``-1`` if all arguments must be materialized, or
        ``-2`` if ``fidx`` is out of range."""
        if fidx < 0:
            return -2
        fm = self.field_masks
        if fm is not None and fidx < len(fm):
            v = fm[fidx]
            if v != -3:
                return v
        res = self._compute_field_mask(fidx)
        if fm is None:
            fm = [-3] * (fidx + 1)
            self.field_masks = fm
        elif fidx >= len(fm):
            fm.extend([-3] * (fidx + 1 - len(fm)))
        fm[fidx] = res
        return res

    def _resolve_let_bvar(self, expr):
        """If ``expr`` is a `W_BVar` pointing (possibly through `let_vals`) to
        one of this `_CtorBody`'s ``m`` lambda arguments, return its lambda
        BVar index ``0 <= bid < self.m``; otherwise return ``-1``."""
        let_vals = self.let_vals
        cur_nlets = 0 if let_vals is None else len(let_vals)
        cur = expr
        while isinstance(cur, W_BVar):
            bid = cur.id
            if cur_nlets <= bid < cur_nlets + self.m:
                return bid - cur_nlets
            if 0 <= bid < cur_nlets:
                assert let_vals is not None
                li = cur_nlets - 1 - bid
                cur = let_vals[li]
                cur_nlets = li
                continue
            return -1
        return -1

    def bvar_field(self, fidx):
        """When this `_CtorBody` selects a single lambda argument ``BVar(bid)``
        for structure field ``fidx`` (chaining through any `let_vals` and
        delegating `_CtorBody`s), return ``bid`` (``0 <= bid < self.m``);
        otherwise return ``-1``."""
        if fidx < 0:
            return -1
        if self.delegate_const is None:
            idx = self.num_params + fidx
            if idx >= len(self.args):
                return -1
            return self._resolve_let_bvar(self.args[idx])
        inner_decl = self.delegate_decl
        assert inner_decl is not None
        inner_kind = inner_decl.w_kind
        assert isinstance(inner_kind, W_Definition)
        inner_cb = inner_kind._ctor_body
        assert inner_cb is not None
        ibid = inner_cb.bvar_field(fidx)
        if ibid < 0:
            return -1
        return self._resolve_let_bvar(self.args[inner_cb.m - 1 - ibid])

    def _peel_ast_expr(self, expr, cur_nlets, fidxs, pbase, rem, decls, depth=6):
        """Follow ``let_vals`` bindings and pending outer projection indices
        `fidxs[pbase .. rem)` on an AST expression ``expr`` in this
        `_CtorBody`'s scope (with ``cur_nlets`` active lets below ``self.m``
        lambda arguments).

        Returns ``(expr, cur_nlets, popped_extra)`` where ``popped_extra`` is
        the number of additional projection layers consumed beyond the
        innermost one (``0 <= popped_extra <= rem - pbase``)."""
        let_vals = self.let_vals
        popped_extra = 0
        while True:
            while cur_nlets > 0 and isinstance(expr, W_BVar):
                bid = expr.id
                if 0 <= bid < cur_nlets:
                    assert let_vals is not None
                    li = cur_nlets - 1 - bid
                    expr = let_vals[li]
                    cur_nlets = li
                else:
                    break
            if rem <= pbase or not isinstance(expr, W_App):
                break
            node = expr
            n_app = 0
            while isinstance(node, W_App):
                node = node.fn
                n_app += 1
            if not isinstance(node, W_Const):
                break
            c2_decl = find_decl(decls, node.name)
            if c2_decl is None:
                break
            c2_kind = c2_decl.w_kind
            if isinstance(c2_kind, W_Constructor):
                idx2 = c2_kind.num_params + fidxs[rem - 1]
                if idx2 >= n_app:
                    break
                steps = n_app - 1 - idx2
                cur_app = expr
                while steps > 0:
                    assert isinstance(cur_app, W_App)
                    cur_app = cur_app.fn
                    steps -= 1
                assert isinstance(cur_app, W_App)
                expr = cur_app.arg
                rem -= 1
                popped_extra += 1
                continue
            if isinstance(c2_kind, W_Definition):
                if len(node.levels) != len(c2_decl.levels):
                    break
                sp = c2_kind.simple_proj()
                if sp >= 0 and (sp & (1 << 30)) == 0:
                    sm = (sp >> 10) & 0x3FF
                    sb = sp & 0x3FF
                    if n_app == sm:
                        steps = sb
                        cur_app = expr
                        while steps > 0:
                            assert isinstance(cur_app, W_App)
                            cur_app = cur_app.fn
                            steps -= 1
                        assert isinstance(cur_app, W_App)
                        expr = cur_app.arg
                        continue
                cb2 = c2_kind._ctor_body
                if cb2 is None:
                    cb2 = c2_kind.init_ctor_body(decls)
                m2 = cb2.m
                if m2 < 0 or n_app < m2:
                    break
                if depth > 0 and (cb2.delegate_const is None or n_app == m2):
                    bid2, pop2 = cb2.bvar_field_chain(
                        fidxs, pbase, rem, decls, depth - 1,
                    )
                    if bid2 >= 0:
                        steps = n_app - m2 + bid2
                        cur_app = expr
                        while steps > 0:
                            assert isinstance(cur_app, W_App)
                            cur_app = cur_app.fn
                            steps -= 1
                        assert isinstance(cur_app, W_App)
                        expr = cur_app.arg
                        rem -= pop2
                        popped_extra += pop2
                        continue
                if cb2.delegate_const is None and cb2.let_vals is None and n_app > m2:
                    idx2 = cb2.num_params + fidxs[rem - 1]
                    nargs2 = len(cb2.args)
                    if nargs2 <= idx2 < nargs2 + (n_app - m2):
                        arg_idx = m2 + (idx2 - nargs2)
                        steps = n_app - 1 - arg_idx
                        cur_app = expr
                        while steps > 0:
                            assert isinstance(cur_app, W_App)
                            cur_app = cur_app.fn
                            steps -= 1
                        assert isinstance(cur_app, W_App)
                        expr = cur_app.arg
                        rem -= 1
                        popped_extra += 1
                        continue
            break
        return expr, cur_nlets, popped_extra

    def bvar_field_chain(self, fidxs, pbase, ptop, decls, depth=6):
        """When applying the projection chain `fidxs[pbase .. ptop)` (innermost
        first at `ptop - 1`) to this `_CtorBody` statically selects one of its
        lambda arguments ``BVar(bid)`` (chaining through `let_vals`, delegating
        `_CtorBody`s, and inline nested constructors / `_CtorBody`s), return
        ``(bid, popped)`` with ``1 <= popped <= ptop - pbase``; else ``(-1, 0)``."""
        if ptop <= pbase:
            return -1, 0
        if ptop - pbase == 1:
            bid = self.bvar_field(fidxs[ptop - 1])
            if bid >= 0:
                return bid, 1
            return -1, 0
        if depth <= 0:
            return -1, 0
        let_vals = self.let_vals
        nlets = 0 if let_vals is None else len(let_vals)
        if self.delegate_const is None:
            fidx = fidxs[ptop - 1]
            if fidx < 0:
                return -1, 0
            idx = self.num_params + fidx
            if idx >= len(self.args):
                return -1, 0
            expr, cur_nlets, extra = self._peel_ast_expr(
                self.args[idx], nlets, fidxs, pbase, ptop - 1, decls, depth - 1,
            )
            if isinstance(expr, W_BVar):
                bid = expr.id
                if cur_nlets <= bid < cur_nlets + self.m:
                    return bid - cur_nlets, 1 + extra
            return -1, 0
        inner_decl = self.delegate_decl
        assert inner_decl is not None
        inner_kind = inner_decl.w_kind
        assert isinstance(inner_kind, W_Definition)
        inner_cb = inner_kind._ctor_body
        assert inner_cb is not None
        ibid, ipop = inner_cb.bvar_field_chain(
            fidxs, pbase, ptop, decls, depth - 1,
        )
        if ibid < 0:
            return -1, 0
        expr, cur_nlets, extra = self._peel_ast_expr(
            self.args[inner_cb.m - 1 - ibid], nlets,
            fidxs, pbase, ptop - ipop, decls, depth - 1,
        )
        if isinstance(expr, W_BVar):
            bid = expr.id
            if cur_nlets <= bid < cur_nlets + self.m:
                return bid - cur_nlets, ipop + extra
        return -1, 0

    def _expr_mask_at_nlets(self, expr, cur_nlets):
        """Return the bitmask of this `_CtorBody`'s ``m`` lambda arguments
        referenced by ``expr`` at ``cur_nlets`` active let bindings (or ``-1``)."""
        if cur_nlets == 0:
            return _expr_bvar_mask(expr, self.m, 0, _MaskMemo())
        let_masks = self._compute_let_masks()
        if let_masks is None:
            return -1
        em = _expr_bvar_mask(expr, self.m + cur_nlets, 0, _MaskMemo())
        if em < 0:
            return -1
        rm = em >> cur_nlets
        b = 0
        while b < cur_nlets:
            if (em & (1 << b)) != 0:
                pm = let_masks[cur_nlets - 1 - b]
                if pm < 0:
                    return -1
                rm |= pm
            b += 1
        return rm

    def field_mask_chain(self, fidxs, pbase, ptop, decls, depth=6):
        """Tight bitmask of this `_CtorBody`'s ``m`` lambda arguments needed to
        evaluate the pending projection chain `fidxs[pbase .. ptop)`."""
        if ptop <= pbase:
            return -2
        fidx = fidxs[ptop - 1]
        if ptop - pbase == 1 or depth <= 0:
            return self.field_mask(fidx)
        if fidx < 0:
            return -2
        let_vals = self.let_vals
        nlets = 0 if let_vals is None else len(let_vals)
        if self.delegate_const is None:
            idx = self.num_params + fidx
            if idx >= len(self.args):
                return -2
            expr, cur_nlets, extra = self._peel_ast_expr(
                self.args[idx], nlets, fidxs, pbase, ptop - 1, decls, depth - 1,
            )
            if extra == 0:
                return self.field_mask(fidx)
            return self._expr_mask_at_nlets(expr, cur_nlets)
        inner_decl = self.delegate_decl
        assert inner_decl is not None
        inner_kind = inner_decl.w_kind
        assert isinstance(inner_kind, W_Definition)
        inner_cb = inner_kind._ctor_body
        assert inner_cb is not None
        ibid, ipop = inner_cb.bvar_field_chain(
            fidxs, pbase, ptop, decls, depth - 1,
        )
        if ibid >= 0:
            expr, cur_nlets, extra = self._peel_ast_expr(
                self.args[inner_cb.m - 1 - ibid], nlets,
                fidxs, pbase, ptop - ipop, decls, depth - 1,
            )
            return self._expr_mask_at_nlets(expr, cur_nlets)
        inner_mask = inner_cb.field_mask_chain(
            fidxs, pbase, ptop, decls, depth - 1,
        )
        if inner_mask < 0:
            return inner_mask
        inner_m = inner_cb.m
        if inner_m > 62:
            return -1
        out_mask = 0
        uses = self.uses_lets
        let_masks = None
        seen = _MaskMemo()
        seen_lets = None
        bid = 0
        while bid < inner_m:
            if (inner_mask & (1 << bid)) != 0:
                arg_idx = inner_m - 1 - bid
                if nlets > 0:
                    assert uses is not None
                    if uses[arg_idx] != 0:
                        if let_masks is None:
                            let_masks = self._compute_let_masks()
                            if let_masks is None:
                                return -1
                            seen_lets = _MaskMemo()
                        assert seen_lets is not None
                        em = _expr_bvar_mask(
                            self.args[arg_idx], self.m + nlets, 0, seen_lets,
                        )
                        if em < 0:
                            return -1
                        rm = em >> nlets
                        b = 0
                        while b < nlets:
                            if (em & (1 << b)) != 0:
                                pm = let_masks[nlets - 1 - b]
                                if pm < 0:
                                    return -1
                                rm |= pm
                            b += 1
                        out_mask |= rm
                        bid += 1
                        continue
                bm = _expr_bvar_mask(self.args[arg_idx], self.m, nlets, seen)
                if bm < 0:
                    return -1
                out_mask |= bm
            bid += 1
        return out_mask

    @dont_inline
    def get_peel_result(self, ckey, fidxs, pbase, ptop, decls):
        """Return the cached `_PeelResult` for packed chain ``ckey`` on this
        `_CtorBody` (computing and caching it on first sight)."""
        pc = self.peel_cache
        if pc is not None:
            res = pc.get(ckey, None)
            if res is not None:
                return res
        else:
            pc = {}
            self.peel_cache = pc
        res = self._compute_peel_result(fidxs, pbase, ptop, decls)
        pc[ckey] = res
        return res

    def _compute_peel_result(self, fidxs, pbase, ptop, decls):
        let_vals = self.let_vals
        nlets = 0 if let_vals is None else len(let_vals)
        if self.delegate_const is None:
            fidx = fidxs[ptop - 1]
            idx = self.num_params + fidx
            if fidx < 0 or idx >= len(self.args):
                return _NO_PEEL
            raw_field, cur_nlets, extra = self._peel_ast_expr(
                self.args[idx], nlets, fidxs, pbase, ptop - 1, decls,
            )
            bvar_id = -1
            if isinstance(raw_field, W_BVar):
                bid = raw_field.id
                if cur_nlets <= bid < cur_nlets + self.m:
                    bvar_id = bid - cur_nlets
            return _PeelResult(raw_field, cur_nlets, 1 + extra, bvar_id, idx, -2)
        inner_decl = self.delegate_decl
        assert inner_decl is not None
        inner_kind = inner_decl.w_kind
        assert isinstance(inner_kind, W_Definition)
        inner_cb = inner_kind._ctor_body
        assert inner_cb is not None
        inner_m = inner_cb.m
        ibid, ipop = inner_cb.bvar_field_chain(fidxs, pbase, ptop, decls)
        if ibid >= 0:
            arg_idx = inner_m - 1 - ibid
            raw_field, cur_nlets, extra = self._peel_ast_expr(
                self.args[arg_idx], nlets, fidxs, pbase, ptop - ipop, decls,
            )
            bvar_id = -1
            if isinstance(raw_field, W_BVar):
                bid = raw_field.id
                if cur_nlets <= bid < cur_nlets + self.m:
                    bvar_id = bid - cur_nlets
            return _PeelResult(raw_field, cur_nlets, ipop + extra, bvar_id, arg_idx, -2)
        inner_mask = inner_cb.field_mask_chain(fidxs, pbase, ptop, decls)
        if inner_mask < 0:
            return _NO_PEEL
        if inner_m <= 62:
            if inner_mask == ((1 << inner_m) - 1):
                return _NO_PEEL
            used_cnt = 0
            tmp_m = inner_mask
            while tmp_m != 0:
                tmp_m &= tmp_m - 1
                used_cnt += 1
            if used_cnt > 8 and used_cnt * 2 > inner_m:
                return _NO_PEEL
        return _PeelResult(None, 0, 0, -1, -1, inner_mask)

    def _compute_let_masks(self):
        """For each `let_vals[li]`, return the transitive bitmask of this
        `_CtorBody`'s ``m`` lambda arguments it depends on (or ``-1``)."""
        let_vals = self.let_vals
        assert let_vals is not None
        nlets = len(let_vals)
        m = self.m
        if m + nlets > 62:
            return None
        let_masks = [0] * nlets
        li = 0
        while li < nlets:
            lm = _expr_bvar_mask(let_vals[li], m + li, 0, _MaskMemo())
            if lm < 0:
                let_masks[li] = -1
            else:
                rm = lm >> li
                b = 0
                while b < li:
                    if (lm & (1 << b)) != 0:
                        pm = let_masks[li - 1 - b]
                        if pm < 0:
                            rm = -1
                            break
                        rm |= pm
                    b += 1
                let_masks[li] = rm
            li += 1
        return let_masks

    def _compute_field_mask(self, fidx):
        let_vals = self.let_vals
        nlets = 0 if let_vals is None else len(let_vals)
        if self.delegate_const is None:
            idx = self.num_params + fidx
            if idx >= len(self.args):
                return -2
            if nlets == 0:
                return _expr_bvar_mask(self.args[idx], self.m, 0, _MaskMemo())
            uses = self.uses_lets
            assert uses is not None
            if uses[idx] == 0:
                return _expr_bvar_mask(self.args[idx], self.m, nlets, _MaskMemo())
            let_masks = self._compute_let_masks()
            if let_masks is None:
                return -1
            em = _expr_bvar_mask(self.args[idx], self.m + nlets, 0, _MaskMemo())
            if em < 0:
                return -1
            rm = em >> nlets
            b = 0
            while b < nlets:
                if (em & (1 << b)) != 0:
                    pm = let_masks[nlets - 1 - b]
                    if pm < 0:
                        return -1
                    rm |= pm
                b += 1
            return rm
        inner_decl = self.delegate_decl
        assert inner_decl is not None
        inner_kind = inner_decl.w_kind
        assert isinstance(inner_kind, W_Definition)
        inner_cb = inner_kind._ctor_body
        assert inner_cb is not None
        inner_mask = inner_cb.field_mask(fidx)
        if inner_mask < 0:
            return inner_mask
        inner_m = inner_cb.m
        if inner_m > 62:
            return -1
        out_mask = 0
        uses = self.uses_lets
        let_masks = None
        seen = _MaskMemo()
        seen_lets = None
        bid = 0
        while bid < inner_m:
            if (inner_mask & (1 << bid)) != 0:
                arg_idx = inner_m - 1 - bid
                if nlets > 0:
                    assert uses is not None
                    if uses[arg_idx] != 0:
                        if let_masks is None:
                            let_masks = self._compute_let_masks()
                            if let_masks is None:
                                return -1
                            seen_lets = _MaskMemo()
                        assert seen_lets is not None
                        em = _expr_bvar_mask(
                            self.args[arg_idx], self.m + nlets, 0, seen_lets,
                        )
                        if em < 0:
                            return -1
                        rm = em >> nlets
                        b = 0
                        while b < nlets:
                            if (em & (1 << b)) != 0:
                                pm = let_masks[nlets - 1 - b]
                                if pm < 0:
                                    return -1
                                rm |= pm
                            b += 1
                        out_mask |= rm
                        bid += 1
                        continue
                bm = _expr_bvar_mask(self.args[arg_idx], self.m, nlets, seen)
                if bm < 0:
                    return -1
                out_mask |= bm
            bid += 1
        return out_mask


def _compute_uses_lets_masks(let_vals, args):
    """Precompute for each `args[i]` an 8-bit bitmask of which `let_vals[li]`
    (bit ``li``) it transitively depends on."""
    nlets = len(let_vals)
    # Transitive let-dependency mask of each let_vals[li] (bits 0..li-1).
    let_deps = [0] * nlets
    li = 1
    while li < nlets:
        lm = _expr_bvar_mask(let_vals[li], li, 0, _MaskMemo())
        if lm < 0:
            let_deps[li] = (1 << li) - 1
        else:
            d = 0
            b = 0
            while b < li:
                if (lm & (1 << b)) != 0:
                    prev = li - 1 - b
                    d |= (1 << prev) | let_deps[prev]
                b += 1
            let_deps[li] = d
        li += 1
    seen = _MaskMemo()
    out = []
    i = 0
    nargs = len(args)
    while i < nargs:
        bm = _expr_bvar_mask(args[i], nlets, 0, seen)
        if bm < 0:
            out.append((1 << nlets) - 1)
        elif bm == 0:
            out.append(0)
        else:
            d = 0
            b = 0
            while b < nlets:
                if (bm & (1 << b)) != 0:
                    prev = nlets - 1 - b
                    d |= (1 << prev) | let_deps[prev]
                b += 1
            out.append(d)
        i += 1
    return out


_NO_CTOR_BODY = _CtorBody(-1, 0, None, [], None)


class _CasesBody(object):
    """Pre-analysed recursor-wrapper body for a `W_Definition` (such as
    `Foo.casesOn`, non-recursive `Foo.recOn`, or a single-scrutinee `match_1`
    wrapper) whose value peels via ``m`` leading lambdas to a fully-applied
    recursor `Rec ... major` (or another `_CasesBody`) with `major = BVar(major_bvar)`
    and minor premises passing `BVar(minor_bvars[r])` directly or via a
    casesOn lambda wrapper discarding induction hypotheses."""

    _attrs_ = ['m', 'major_bvar', 'rec_decl', 'minor_bvars']
    _immutable_fields_ = ['m', 'major_bvar', 'rec_decl', 'minor_bvars']

    def __init__(self, m, major_bvar, rec_decl, minor_bvars):
        self.m = m
        self.major_bvar = major_bvar
        self.rec_decl = rec_decl
        self.minor_bvars = minor_bvars


_NO_CASES_BODY = _CasesBody(-1, 0, None, None)


class W_Definition(W_DeclarationKind):
    _attrs_ = [
        'value', 'hint', 'all', '_ctor_body', '_cases_body',
        '_simple_proj', '_simple_proj_name',
    ]
    _immutable_fields_ = ['value', 'hint', 'all']

    def __init__(self, value, hint, all=None):
        self.value = value
        self.hint = hint
        #: The members of this definition's mutual block (`DefinitionVal.
        #: all`), or ``None`` when it stands alone.
        self.all = all
        self._ctor_body = None
        self._cases_body = None
        self._simple_proj = -2
        self._simple_proj_name = None

    def simple_proj(self):
        """Cached encoding for simple argument-picker (`λ... => BVar(b)`) or
        projection-wrapper (`λ... => Proj(S, fidx, BVar(b))`) definitions.
        Returns ``-1`` otherwise."""
        v = self._simple_proj
        if v != -2:
            return v
        return self._init_simple_proj()

    @dont_inline
    def _init_simple_proj(self):
        target = self.get_delta_reduce_target()
        if target is None:
            self._simple_proj = -1
            return -1
        m = 0
        cur = target
        while isinstance(cur, W_Lambda):
            cur = cur.body
            m += 1
        if 0 < m < 1024:
            if isinstance(cur, W_BVar):
                bid = cur.id
                if 0 <= bid < m:
                    v = (m << 10) | bid
                    self._simple_proj = v
                    return v
            elif isinstance(cur, W_Proj):
                inner = cur.struct_expr
                fidx = cur.field_index
                if isinstance(inner, W_BVar) and 0 <= fidx < 1024:
                    bid = inner.id
                    if 0 <= bid < m:
                        v = (1 << 30) | (fidx << 20) | (m << 10) | bid
                        self._simple_proj = v
                        self._simple_proj_name = cur.struct_name
                        return v
        self._simple_proj = -1
        return -1

    @dont_inline
    def init_cases_body(self, declarations, max_depth=2):
        """Inspect `self.value` once and cache a `_CasesBody` when it peels via
        leading lambdas to a fully-applied `W_Recursor` (or another `_CasesBody`
        definition) whose major premise is a lambda `BVar` and at least one
        constructor minor premise maps cleanly to a lambda `BVar` without using
        induction hypotheses."""
        target = self.get_delta_reduce_target()
        if target is None:
            self._cases_body = _NO_CASES_BODY
            return _NO_CASES_BODY
        cur = target
        m = 0
        while isinstance(cur, W_Lambda):
            cur = cur.body
            m += 1
        if m < 2 or not isinstance(cur, W_App):
            self._cases_body = _NO_CASES_BODY
            return _NO_CASES_BODY
        rev_args = []
        node = cur
        while isinstance(node, W_App):
            rev_args.append(node.arg)
            node = node.fn
        if not isinstance(node, W_Const):
            self._cases_body = _NO_CASES_BODY
            return _NO_CASES_BODY
        target_decl = find_decl(declarations, node.name)
        if target_decl is None:
            self._cases_body = _NO_CASES_BODY
            return _NO_CASES_BODY
        target_kind = target_decl.w_kind
        n_app = len(rev_args)
        if isinstance(target_kind, W_Recursor):
            skip = (
                target_kind.num_params
                + target_kind.num_motives
                + target_kind.num_minors
                + target_kind.num_indices
            )
            if n_app != skip + 1 or target_kind.num_minors <= 0:
                self._cases_body = _NO_CASES_BODY
                return _NO_CASES_BODY
            major_arg = rev_args[0]
            if not isinstance(major_arg, W_BVar):
                self._cases_body = _NO_CASES_BODY
                return _NO_CASES_BODY
            major_bvar = major_arg.id
            if major_bvar < 0 or major_bvar >= m:
                self._cases_body = _NO_CASES_BODY
                return _NO_CASES_BODY
            minor_bvars = [-1] * target_kind.num_minors
            any_ok = False
            for rule in target_kind.rules:
                sminor = rule.simple_minor(
                    target_decl,
                    target_kind.num_params,
                    target_kind.num_motives,
                    target_kind.num_minors,
                    target_kind.num_indices,
                )
                if sminor < 0 or sminor >= target_kind.num_minors:
                    continue
                pos = target_kind.num_params + target_kind.num_motives + sminor
                marg = rev_args[n_app - 1 - pos]
                nf = rule.num_fields
                nr = 0 if rule._rec_fields is None else len(rule._rec_fields)
                if nr == 0 and isinstance(marg, W_BVar):
                    bid = marg.id
                    if 0 <= bid < m:
                        minor_bvars[sminor] = bid
                        any_ok = True
                    continue
                k = 0
                wcur = marg
                while isinstance(wcur, W_Lambda):
                    wcur = wcur.body
                    k += 1
                if k == 0 or k != nf + nr:
                    continue
                wrev = []
                wnode = wcur
                while isinstance(wnode, W_App):
                    wrev.append(wnode.arg)
                    wnode = wnode.fn
                if len(wrev) != nf or not isinstance(wnode, W_BVar):
                    continue
                hbid = wnode.id
                if hbid < k or hbid >= k + m:
                    continue
                ok = True
                i = 0
                while i < nf:
                    fa = wrev[nf - 1 - i]
                    if not isinstance(fa, W_BVar) or fa.id != k - 1 - i:
                        ok = False
                        break
                    i += 1
                if ok:
                    minor_bvars[sminor] = hbid - k
                    any_ok = True
            if any_ok:
                cb = _CasesBody(m, major_bvar, target_decl, minor_bvars)
                self._cases_body = cb
                return cb
            self._cases_body = _NO_CASES_BODY
            return _NO_CASES_BODY
        if max_depth > 0 and isinstance(target_kind, W_Definition):
            self._cases_body = _NO_CASES_BODY
            inner = target_kind._cases_body
            if inner is None:
                inner = target_kind.init_cases_body(declarations, max_depth - 1)
            if inner.m >= 0 and n_app == inner.m:
                major_arg = rev_args[inner.major_bvar]
                if isinstance(major_arg, W_BVar):
                    outer_major = major_arg.id
                    if 0 <= outer_major < m:
                        in_minors = inner.minor_bvars
                        assert in_minors is not None
                        nmin = len(in_minors)
                        out_minors = [-1] * nmin
                        any_ok = False
                        r = 0
                        while r < nmin:
                            imb = in_minors[r]
                            if imb >= 0:
                                ma = rev_args[imb]
                                if isinstance(ma, W_BVar):
                                    ob = ma.id
                                    if 0 <= ob < m:
                                        out_minors[r] = ob
                                        any_ok = True
                            r += 1
                        if any_ok:
                            cb = _CasesBody(m, outer_major, inner.rec_decl, out_minors)
                            self._cases_body = cb
                            return cb
        self._cases_body = _NO_CASES_BODY
        return _NO_CASES_BODY

    @dont_inline
    def init_ctor_body(self, declarations, max_depth=6):
        """Inspect `self.value` once and cache a `_CtorBody` when it peels via
        leading lambdas (and up to 8 leading lets) to a constructor application
        or to a saturated application of another `_CtorBody` definition."""
        target = self.get_delta_reduce_target()
        if target is None:
            self._ctor_body = _NO_CTOR_BODY
            return _NO_CTOR_BODY
        cur = target
        m = 0
        while isinstance(cur, W_Lambda):
            cur = cur.body
            m += 1
        let_vals = None
        while isinstance(cur, W_Let):
            if let_vals is None:
                let_vals = []
            elif len(let_vals) >= 8:
                self._ctor_body = _NO_CTOR_BODY
                return _NO_CTOR_BODY
            let_vals.append(cur.value)
            cur = cur.body
        if not isinstance(cur, W_App):
            self._ctor_body = _NO_CTOR_BODY
            return _NO_CTOR_BODY
        rev_args = []
        node = cur
        while isinstance(node, W_App):
            rev_args.append(node.arg)
            node = node.fn
        if not isinstance(node, W_Const):
            self._ctor_body = _NO_CTOR_BODY
            return _NO_CTOR_BODY
        target_decl = find_decl(declarations, node.name)
        if target_decl is None:
            self._ctor_body = _NO_CTOR_BODY
            return _NO_CTOR_BODY
        target_kind = target_decl.w_kind
        if isinstance(target_kind, W_Constructor):
            args = []
            i = len(rev_args) - 1
            while i >= 0:
                args.append(rev_args[i])
                i -= 1
            uses_lets = (
                _compute_uses_lets_masks(let_vals, args)
                if let_vals is not None
                else None
            )
            cb = _CtorBody(m, target_kind.num_params, let_vals, args, uses_lets)
            self._ctor_body = cb
            return cb
        if (max_depth > 0
                and isinstance(target_kind, W_Definition)
                and len(node.levels) == len(target_decl.levels)):
            # Install negative sentinel before recursing so self/mutual cycles
            # terminate immediately.
            self._ctor_body = _NO_CTOR_BODY
            inner_cb = target_kind._ctor_body
            if inner_cb is None:
                inner_cb = target_kind.init_ctor_body(declarations, max_depth - 1)
            if inner_cb.m >= 0 and len(rev_args) == inner_cb.m:
                args = []
                i = len(rev_args) - 1
                while i >= 0:
                    args.append(rev_args[i])
                    i -= 1
                uses_lets = (
                    _compute_uses_lets_masks(let_vals, args)
                    if let_vals is not None
                    else None
                )
                cb = _CtorBody(m, 0, let_vals, args, uses_lets, node, target_decl)
                self._ctor_body = cb
                return cb
        self._ctor_body = _NO_CTOR_BODY
        return _NO_CTOR_BODY

    def group_key(self, name, safety):
        # An unsafe definition enters the environment before its value is
        # checked, so it may use itself and its mutual block; a partial
        # one may use only a mutual block it shares.
        if safety == SAFETY_UNSAFE:
            return name if self.all is None else self.all[0]
        if safety == SAFETY_PARTIAL and self.all is not None:
            return self.all[0]
        return None

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_def(decl, self.value, self.hint)

    def type_check(self, type, tc):
        return tc.machine.check_value(type, self.value, False)

    def decl_format(self, name, levels, type, constants, marker):
        return _decl_with_value_format(
            "def", name, levels, type, self.value, constants, marker,
        )

    def get_delta_reduce_target(self):
        return self.value

    def allows_warm_cache(self):
        return True


class W_Opaque(W_DeclarationKind):
    """
    An Opaque definition.

    Like a definition with hint 'opaque', except the kernel will never unfold
    it — so just like `W_Theorem`, its value is dead once checked and can be
    dropped via `drop_checked_value`.
    """

    _attrs_ = ['value']
    _immutable_fields_ = ['value?']

    def __init__(self, value):
        self.value = value

    def drop_checked_value(self):
        self.value = None

    def dump_to(self, exporter, decl):
        value = self.value
        assert value is not None
        exporter.begin_decl(decl)
        exporter.dump_deps(value)
        exporter.emit_opaque(decl, value)

    def type_check(self, type, tc):
        value = self.value
        assert value is not None
        return tc.machine.check_value(type, value, False)

    def allows_warm_cache(self):
        return True

    def decl_format(self, name, levels, type, constants, marker):
        value = self.value
        assert value is not None
        return _decl_with_value_format(
            "def", name, levels, type, value, constants, marker,
        )


class W_Theorem(W_DeclarationKind):
    # `value` is `None` once `drop_checked_value` has run: a theorem is
    # never delta-unfolded, so nothing reads its proof term after its own
    # check, and `None` (impossible for a real expr) is a value the reader
    # sites below must — and do — prove absent before use. It is also
    # quasi-immutable (`?`): set once, read only during this theorem's
    # check, then dropped.
    _attrs_ = ['value']
    _immutable_fields_ = ['value?']

    def __init__(self, value):
        self.value = value

    def drop_checked_value(self):
        # The proof term is dead now: a theorem is never a delta-reduce
        # target, so no later declaration's check can reach it. Drop the
        # reference so its sub-tree becomes collectable. `None` — not a
        # stand-in expr — so that any read after the drop is a loud crash
        # (or the assertions below), never a silently-wrong expression.
        self.value = None

    def dump_to(self, exporter, decl):
        value = self.value
        assert value is not None
        exporter.begin_decl(decl)
        exporter.dump_deps(value)
        exporter.emit_thm(decl, value)

    def type_check(self, type, tc):
        value = self.value
        assert value is not None
        return tc.machine.check_value(type, value, True)

    def allows_warm_cache(self):
        return True

    def decl_format(self, name, levels, type, constants, marker):
        value = self.value
        assert value is not None
        return _decl_with_value_format(
            "theorem", name, levels, type, value, constants, marker,
        )


class W_Axiom(W_DeclarationKind):
    _attrs_ = []

    def decl_format(self, name, levels, type, constants, marker):
        return _decl_signature_format(
            "axiom", name, levels, type, constants, marker,
        )

    def type_check(self, type, tc):
        type_type = type.infer(tc)
        if not isinstance(type_type.whnf(tc), W_Sort):
            return W_NotASort(tc, type, inferred_type=type_type, name=None)


_QUOT_NAME = Name.simple("Quot")
_QUOT_MK_NAME = _QUOT_NAME.child("mk")
_QUOT_LIFT_NAME = _QUOT_NAME.child("lift")
_QUOT_IND_NAME = _QUOT_NAME.child("ind")
_EQ_NAME = Name.simple("Eq")


def _pi(binders, body):
    result = body
    i = len(binders) - 1
    while i >= 0:
        result = _mk_w_forall(binders[i], result)
        i -= 1
    return result


def _decl_visible(current, target):
    """Whether ``target`` is in scope when checking ``current`` (same block
    or declared at or before ``current`` in an ordered stream)."""
    if current is None or current.index < 0:
        return True
    if current.group >= 0 and target.group == current.group:
        return True
    return target.index <= current.index


def _check_eq_for_quot(tc):
    """Verify ``Eq`` and its single constructor match Lean's prelude ``Eq``,
    as required by Lean's kernel before introducing ``Quot.lift``."""
    eq_decl = find_decl(tc.declarations, _EQ_NAME)
    if eq_decl is None:
        return "missing inductive `Eq`"
    eq_ind = eq_decl.w_kind
    if not isinstance(eq_ind, W_Inductive):
        return "missing inductive `Eq`"
    if len(eq_decl.levels) != 1:
        return "`Eq` must have 1 universe parameter"
    eq_u = eq_decl.levels[0].as_level_param()
    tc.check_reference(_EQ_NAME.const([eq_u]), eq_decl)
    if len(eq_ind.ctor_names) != 1:
        return "`Eq` must have 1 constructor"
    alpha = Name.simple("α")
    anon = Name.ANONYMOUS
    expected_eq_type = _pi(
        [
            alpha.implicit_binder(eq_u.sort()),
            anon.binder(_mk_w_bvar(0)),
            anon.binder(_mk_w_bvar(1)),
        ],
        PROP,
    )
    if not tc.def_eq(eq_decl.type, expected_eq_type):
        return "`Eq` does not have the expected type"
    eq_refl = find_decl(tc.declarations, eq_ind.ctor_names[0])
    if (
        eq_refl is None
        or not isinstance(eq_refl.w_kind, W_Constructor)
        or (
            tc.decl is not None
            and tc.decl.index >= 0
            and eq_refl.index >= tc.decl.index
        )
    ):
        return "missing constructor for `Eq`"
    if len(eq_refl.levels) != 1:
        return "`Eq` constructor must have 1 universe parameter"
    refl_u = eq_refl.levels[0].as_level_param()
    a = Name.simple("a")
    eq_refl_ret = _mk_app(
        _mk_app(_mk_app(_EQ_NAME.const([refl_u]), _mk_w_bvar(1)), _mk_w_bvar(0)),
        _mk_w_bvar(0),
    )
    expected_refl_type = _pi(
        [
            alpha.implicit_binder(refl_u.sort()),
            a.binder(_mk_w_bvar(0)),
        ],
        eq_refl_ret,
    )
    if not tc.def_eq(eq_refl.type, expected_refl_type):
        return "`Eq` constructor does not have the expected type"
    return None


class W_Quotient(W_DeclarationKind):
    """
    A Quot kernel axiom. Lean's `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`
    are kernel-builtin constants; the kernel treats them specially for
    `Quot.lift` reduction. ``kind`` distinguishes which of the four.
    """

    _attrs_ = ['kind']
    _immutable_fields_ = ['kind']

    KIND_TYPE = 0  # `Quot`
    KIND_CTOR = 1  # `Quot.mk`
    KIND_LIFT = 2  # `Quot.lift`
    KIND_IND = 3   # `Quot.ind`

    def __init__(self, kind):
        # `kind` is one of the `KIND_*` constants above; the integer values
        # match Lean's `QuotKind` ctor tags so the FFI walker can pass the
        # raw byte through.
        self.kind = kind

    def kind_str(self):
        if self.kind == W_Quotient.KIND_TYPE:
            return "type"
        if self.kind == W_Quotient.KIND_CTOR:
            return "ctor"
        if self.kind == W_Quotient.KIND_LIFT:
            return "lift"
        if self.kind == W_Quotient.KIND_IND:
            return "ind"
        raise ValueError("unknown quot kind: %d" % self.kind)

    @staticmethod
    def kind_from_str(s):
        if s == "type":
            return W_Quotient.KIND_TYPE
        if s == "ctor":
            return W_Quotient.KIND_CTOR
        if s == "lift":
            return W_Quotient.KIND_LIFT
        if s == "ind":
            return W_Quotient.KIND_IND
        raise ValueError("unknown quot kind: %s" % s)

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.emit_quot(decl, self.kind_str())

    def type_check(self, type, tc):
        type_type = type.infer(tc)
        if not isinstance(type_type.whnf(tc), W_Sort):
            return W_NotASort(tc, type, inferred_type=type_type, name=None)
        decl = tc.decl
        if decl is None:
            return None
        kind = self.kind
        if kind == W_Quotient.KIND_TYPE:
            expected_name = _QUOT_NAME
            expected_nlevels = 1
        elif kind == W_Quotient.KIND_CTOR:
            expected_name = _QUOT_MK_NAME
            expected_nlevels = 1
        elif kind == W_Quotient.KIND_LIFT:
            expected_name = _QUOT_LIFT_NAME
            expected_nlevels = 2
        elif kind == W_Quotient.KIND_IND:
            expected_name = _QUOT_IND_NAME
            expected_nlevels = 1
        else:
            return W_InvalidQuotient(tc, "unknown quotient kind", type)

        if not name_eq(decl.name, expected_name):
            return W_InvalidQuotient(
                tc, "quotient kind does not match declaration name", type,
            )
        if len(decl.levels) != expected_nlevels:
            return W_InvalidQuotient(
                tc, "unexpected number of universe parameters", type,
            )

        u = decl.levels[0].as_level_param()
        sort_u = u.sort()
        alpha = Name.simple("α")
        r = Name.simple("r")
        a = Name.simple("a")
        anon = Name.ANONYMOUS
        # r : α → α → Prop (under binder α)
        r_type = _pi(
            [anon.binder(_mk_w_bvar(0)), anon.binder(_mk_w_bvar(1))],
            PROP,
        )

        if kind == W_Quotient.KIND_TYPE:
            # Quot.{u} : ∀ {α : Sort u} (r : α → α → Prop), Sort u
            expected = _pi(
                [alpha.implicit_binder(sort_u), r.binder(r_type)],
                sort_u,
            )
        else:
            quot_decl = find_decl(tc.declarations, _QUOT_NAME)
            if quot_decl is None:
                return W_InvalidQuotient(
                    tc, "missing quotient type declaration `Quot`", type,
                )
            quot_wk = quot_decl.w_kind
            if (
                not isinstance(quot_wk, W_Quotient)
                or quot_wk.kind != W_Quotient.KIND_TYPE
            ):
                return W_InvalidQuotient(
                    tc, "missing quotient type declaration `Quot`", type,
                )
            quot_u = _QUOT_NAME.const([u])
            tc.check_reference(quot_u, quot_decl)
            if kind == W_Quotient.KIND_CTOR:
                # Quot.mk.{u} : ∀ {α : Sort u} (r : α → α → Prop) (a : α), @Quot.{u} α r
                expected = _pi(
                    [
                        alpha.implicit_binder(sort_u),
                        r.binder(r_type),
                        a.binder(_mk_w_bvar(1)),
                    ],
                    _mk_app(_mk_app(quot_u, _mk_w_bvar(2)), _mk_w_bvar(1)),
                )
            elif kind == W_Quotient.KIND_LIFT:
                eq_err = _check_eq_for_quot(tc)
                if eq_err is not None:
                    return W_InvalidQuotient(tc, eq_err, type)
                v = decl.levels[1].as_level_param()
                sort_v = v.sort()
                beta = Name.simple("β")
                f = Name.simple("f")
                b = Name.simple("b")
                # f : α → β (under α, r, β)
                f_type = _pi([anon.binder(_mk_w_bvar(2))], _mk_w_bvar(1))
                # ∀ (a b : α), r a b → @Eq.{v} β (f a) (f b) (under α, r, β, f)
                eq_v = _EQ_NAME.const([v])
                r_a_b = _mk_app(_mk_app(_mk_w_bvar(4), _mk_w_bvar(1)), _mk_w_bvar(0))
                fa = _mk_app(_mk_w_bvar(3), _mk_w_bvar(2))
                fb = _mk_app(_mk_w_bvar(3), _mk_w_bvar(1))
                eq_fa_fb = _mk_app(_mk_app(_mk_app(eq_v, _mk_w_bvar(4)), fa), fb)
                sanity = _pi(
                    [
                        a.binder(_mk_w_bvar(3)),
                        b.binder(_mk_w_bvar(4)),
                        anon.binder(r_a_b),
                    ],
                    eq_fa_fb,
                )
                quot_a_r = _mk_app(_mk_app(quot_u, _mk_w_bvar(4)), _mk_w_bvar(3))
                # Quot.lift.{u, v} : ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v}
                #   (f : α → β), (∀ a b, r a b → f a = f b) → @Quot.{u} α r → β
                expected = _pi(
                    [
                        alpha.implicit_binder(sort_u),
                        r.implicit_binder(r_type),
                        beta.implicit_binder(sort_v),
                        f.binder(f_type),
                        anon.binder(sanity),
                        anon.binder(quot_a_r),
                    ],
                    _mk_w_bvar(3),
                )
            else:
                # KIND_IND
                mk_decl = find_decl(tc.declarations, _QUOT_MK_NAME)
                if mk_decl is None:
                    return W_InvalidQuotient(
                        tc, "missing quotient constructor `Quot.mk`", type,
                    )
                mk_wk = mk_decl.w_kind
                if (
                    not isinstance(mk_wk, W_Quotient)
                    or mk_wk.kind != W_Quotient.KIND_CTOR
                ):
                    return W_InvalidQuotient(
                        tc, "missing quotient constructor `Quot.mk`", type,
                    )
                quot_mk_u = _QUOT_MK_NAME.const([u])
                tc.check_reference(quot_mk_u, mk_decl)
                beta = Name.simple("β")
                q = Name.simple("q")
                # β : @Quot.{u} α r → Prop (under α, r)
                beta_type = _pi(
                    [anon.binder(_mk_app(_mk_app(quot_u, _mk_w_bvar(1)), _mk_w_bvar(0)))],
                    PROP,
                )
                # ∀ (a : α), β (@Quot.mk.{u} α r a) (under α, r, β)
                quot_mk_a = _mk_app(
                    _mk_app(_mk_app(quot_mk_u, _mk_w_bvar(3)), _mk_w_bvar(2)),
                    _mk_w_bvar(0),
                )
                mk_hyp = _pi(
                    [a.binder(_mk_w_bvar(2))],
                    _mk_app(_mk_w_bvar(1), quot_mk_a),
                )
                quot_a_r = _mk_app(_mk_app(quot_u, _mk_w_bvar(3)), _mk_w_bvar(2))
                # Quot.ind.{u} : ∀ {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop},
                #   (∀ a, β (@Quot.mk.{u} α r a)) → ∀ (q : @Quot.{u} α r), β q
                expected = _pi(
                    [
                        alpha.implicit_binder(sort_u),
                        r.implicit_binder(r_type),
                        beta.implicit_binder(beta_type),
                        anon.binder(mk_hyp),
                        q.binder(quot_a_r),
                    ],
                    _mk_app(_mk_w_bvar(2), _mk_w_bvar(0)),
                )

        if not tc.def_eq(type, expected):
            return W_InvalidQuotient(
                tc, "quotient type does not match Lean's specification", type,
            )

    def decl_format(self, name, levels, type, constants, marker):
        # rpylean displays quot decls as ordinary axioms.
        return _decl_signature_format(
            "axiom", name, levels, type, constants, marker,
        )


def _expr_has_bvar_lt(e, k, depth):
    """Whether ``e`` contains a bound variable referring to indices
    ``[depth, depth + k)`` (used to test whether a structure field type
    depends on earlier fields)."""
    if k <= 0 or e.loose_bvar_range() <= depth:
        return False
    if depth > 256:
        return True
    if isinstance(e, W_BVar):
        return depth <= e.id < depth + k
    if isinstance(e, W_App):
        return (
            _expr_has_bvar_lt(e.fn, k, depth)
            or _expr_has_bvar_lt(e.arg, k, depth)
        )
    if isinstance(e, W_FunBase):
        return (
            _expr_has_bvar_lt(e.type, k, depth)
            or _expr_has_bvar_lt(e.body, k, depth + 1)
        )
    if isinstance(e, W_Let):
        return (
            _expr_has_bvar_lt(e.type, k, depth)
            or _expr_has_bvar_lt(e.value, k, depth)
            or _expr_has_bvar_lt(e.body, k, depth + 1)
        )
    if isinstance(e, W_Proj):
        return _expr_has_bvar_lt(e.struct_expr, k, depth)
    return False


class _CowFlag(object):
    """Process-wide toggle disabling intrusive `W_Expr._cache` writes during
    multi-process fork checking so workers never dirty shared parent pages."""

    _attrs_ = ['enabled']

    def __init__(self):
        self.enabled = False


_COW_FLAG = _CowFlag()


def _mask_key_eq(a, b):
    return a[0] is b[0] and a[1] == b[1]


def _mask_key_hash(k):
    return k[0].hash() ^ (k[1] * 1000003)


class _MaskMemo(object):
    """Intrusive `W_Expr._cache` memo for `_expr_bvar_mask`: avoids Python
    dict / `(e, depth)` tuple / GC identity-hash shadow allocations on the
    99.9% single-depth path, falling back to a dict only on multi-depth
    DAG collisions, COW-parallel mode, or cache-generation exhaustion."""

    _attrs_ = ['base_gen', 'gens', 'vals', 'overflow']

    def __init__(self):
        g0 = 0 if _COW_FLAG.enabled else _next_cache_gen()
        self.base_gen = g0
        self.gens = [g0]
        self.vals = []
        self.overflow = None

    def gen_for_depth(self, depth):
        gens = self.gens
        while depth >= len(gens):
            gens.append(0)
        g = gens[depth]
        if g == 0:
            g = _next_cache_gen()
            gens[depth] = g
        return g


def _expr_bvar_mask(e, limit, depth, seen):
    """Bitmask of bound-variable indices ``b`` in ``[0, limit)`` occurring
    free in ``e`` at binder depth ``depth``. Memoized intrusively on
    `W_Expr._cache` via ``seen`` so shared DAGs run in O(nodes) with zero
    GC shadow allocations."""
    if limit <= 0 or e.loose_bvar_range() <= depth:
        return 0
    if limit > 62 or depth > 128:
        return -1
    if isinstance(e, W_BVar):
        b = e.id - depth
        if 0 <= b < limit:
            return 1 << b
        return 0
    dgen = seen.gen_for_depth(depth) if seen.base_gen > 0 else -1
    if dgen > 0:
        c = e._cache
        cg = c >> 32
        if cg == dgen:
            return seen.vals[c & 0xFFFFFFFF]
        if cg >= seen.base_gen and seen.overflow is not None:
            cached = seen.overflow.get((e, depth), -2)
            if cached != -2:
                return cached
    elif seen.overflow is not None:
        cached = seen.overflow.get((e, depth), -2)
        if cached != -2:
            return cached
    total = len(seen.vals) + (len(seen.overflow) if seen.overflow is not None else 0)
    if total >= 4096:
        return -1
    if isinstance(e, W_App):
        m1 = _expr_bvar_mask(e.fn, limit, depth, seen)
        if m1 < 0:
            res = -1
        else:
            m2 = _expr_bvar_mask(e.arg, limit, depth, seen)
            res = -1 if m2 < 0 else (m1 | m2)
    elif isinstance(e, W_FunBase):
        m1 = _expr_bvar_mask(e.type, limit, depth, seen)
        if m1 < 0:
            res = -1
        else:
            m2 = _expr_bvar_mask(e.body, limit, depth + 1, seen)
            res = -1 if m2 < 0 else (m1 | m2)
    elif isinstance(e, W_Let):
        m1 = _expr_bvar_mask(e.type, limit, depth, seen)
        if m1 < 0:
            res = -1
        else:
            m2 = _expr_bvar_mask(e.value, limit, depth, seen)
            if m2 < 0:
                res = -1
            else:
                m3 = _expr_bvar_mask(e.body, limit, depth + 1, seen)
                res = -1 if m3 < 0 else (m1 | m2 | m3)
    elif isinstance(e, W_Proj):
        res = _expr_bvar_mask(e.struct_expr, limit, depth, seen)
    else:
        res = 0
    if dgen > 0:
        cg = e._cache >> 32
        if cg < seen.base_gen:
            idx = len(seen.vals)
            seen.vals.append(res)
            e._cache = (dgen << 32) | idx
        elif cg != dgen:
            ov = seen.overflow
            if ov is None:
                ov = seen.overflow = r_dict(_mask_key_eq, _mask_key_hash)
            ov[(e, depth)] = res
    else:
        ov = seen.overflow
        if ov is None:
            ov = seen.overflow = r_dict(_mask_key_eq, _mask_key_hash)
        ov[(e, depth)] = res
    return res


class W_Inductive(W_DeclarationKind):
    _attrs_ = [
        'name', 'all', 'constructors', 'recursors',
        'num_nested', 'num_params', 'num_indices',
        'is_reflexive', 'is_recursive', 'ctor_names',
        '_proj_ctor', '_proj_fields', '_proj_field_uses_earlier',
    ]

    def group_key(self, name, safety):
        return self.all[0] if self.all else None
    # `constructors` is appended to by the parser when registering
    # mutual-inductive blocks; everything else is set-once at construction.
    _immutable_fields_ = [
        'name', 'all', 'recursors',
        'num_nested', 'num_params', 'num_indices',
        'is_reflexive', 'is_recursive', 'ctor_names',
    ]

    def __init__(
        self,
        name,
        all,
        constructors,
        recursors,
        num_nested,
        num_params,
        num_indices,
        is_reflexive,
        is_recursive,
        ctor_names=None,
    ):
        #: This inductive's own name. NOT `all[0]`: in a mutual block
        #: every member shares the same `all` list, so constructor
        #: validation keyed on `all[0]` would reject every member but
        #: the first.
        self.name = name
        #: All inductives in this mutual block (just `[self]` for a
        #: non-mutual inductive). Matches Lean's `InductiveVal.all`.
        self.all = all
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
        self._proj_ctor = None
        self._proj_fields = None
        self._proj_field_uses_earlier = None

    @dont_inline
    def init_proj_cache(self, ctor_decl):
        """Cache the sole constructor and pre-stripped field domain types
        for fast projection type inference."""
        self._proj_ctor = ctor_decl
        cur = ctor_decl.type
        np = self.num_params
        ok = True
        k = 0
        while k < np:
            if not isinstance(cur, W_ForAll):
                ok = False
                break
            cur = cur.body
            k += 1
        fields = []
        uses = []
        if ok:
            fi = 0
            while isinstance(cur, W_ForAll):
                ft = cur.type
                fields.append(ft)
                uses.append(_expr_has_bvar_lt(ft, fi, 0))
                cur = cur.body
                fi += 1
        self._proj_fields = fields
        self._proj_field_uses_earlier = uses

    def is_non_recursive_structure(self):
        """
        Whether this inductive is a *structure* whose recursor admits
        struct-eta reduction on a stuck major: exactly one constructor,
        no indices, and not (mutually) recursive.
        """
        return (
            len(self.ctor_names) == 1
            and self.num_indices == 0
            and not self.is_recursive
        )

    def constructor_decls(self, declarations):
        """
        The constructor `W_Declaration`s, in `ctor_names` order.

        `self.constructors` is complete whenever the parser registered
        this inductive (blocks register types and ctors together), but
        the FFI walk hands constructors out as separate constants in
        hash order — so when the walked list is short, derive it from
        the authoritative `ctor_names` via `get_decl`, which
        demand-loads under `ffi check`.
        """
        constructors = self.constructors
        if len(constructors) == len(self.ctor_names):
            return constructors
        constructors = [
            get_decl(declarations, each) for each in self.ctor_names
        ]
        self.constructors = constructors
        return constructors

    def register_exporter_index(self, exporter, name):
        exporter.register_inductive_ctors(name, self.ctor_names)

    def dump_to(self, exporter, decl):
        # Mark every mutual-block member visited up front so dep walks
        # cycling back through any of them short-circuit before the
        # block emit completes.
        for n in self.all:
            exporter.mark_emitted(n)
        ctor_pairs = []   # [(induct_name, ctor_decl)]
        rec_decls = []
        for n in self.all:
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
        for n in self.all:
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

    def type_check(self, type, tc):
        from rpylean._inductive import W_InvalidInductive, recursors_of

        if not self.all:
            return W_InvalidInductive(tc.env, "inductive block is empty")
        in_block = False
        for name in self.all:
            if name.syntactic_eq(self.name):
                in_block = True
                break
        if not in_block:
            return W_InvalidInductive(
                tc.env,
                "%s is not listed in its own block" % self.name.str(),
            )
        first = find_decl(tc.declarations, self.all[0])
        if first is None or not _decl_visible(tc.decl, first):
            return W_InvalidInductive(
                tc.env,
                "%s is not declared" % self.all[0].str(),
            )
        recursors_of(first, tc)

    def decl_format(self, name, levels, type, constants, marker):
        parts = [_decl_signature_format(
            "inductive", name, levels, type, constants, marker,
        )]
        for each in self.constructors:
            each_kind = each.w_kind
            assert isinstance(each_kind, W_Constructor)
            # Each constructor goes on its own line.
            parts.append(_format.text(PLAIN, "\n"))
            parts.append(each_kind.constructor_format(
                each.name, each.type, self, constants, marker,
            ))
        return _format.concat(parts)


class W_Constructor(W_DeclarationKind):
    _attrs_ = ['induct', 'num_params', 'num_fields', 'cidx']
    _immutable_fields_ = ['induct', 'num_params', 'num_fields', 'cidx']

    def __init__(self, num_params, num_fields, cidx=0, induct=Name.ANONYMOUS):
        self.induct = induct
        self.num_params = num_params
        self.num_fields = num_fields
        #: This constructor's index within its parent inductive's
        #: source-order ctor list. From `ConstructorVal.cidx`.
        self.cidx = cidx

    def is_constructor(self):
        return True

    def dump_to(self, exporter, decl):
        induct_name = exporter.parent_inductive(decl.name)
        if induct_name is not None and induct_name in exporter.decls:
            exporter.dump_constant(exporter.decls[induct_name])
            return
        # Unattached ctor (parent inductive wasn't registered) — emit
        # as an axiom so the output stays self-contained.
        exporter.begin_decl(decl)
        exporter.emit_axiom(decl)

    def type_check(self, type, tc):
        # A constructor's type, arity, universe levels and positivity
        # are checked as part of its inductive's block; here verify it
        # really belongs to one, so an unattached constructor cannot
        # slip through unchecked.
        ind_decl = find_decl(tc.declarations, self.induct)
        if ind_decl is None or not _decl_visible(tc.decl, ind_decl):
            return W_InvalidConstructorResult(tc.env, type)
        ind_kind = ind_decl.w_kind
        if not isinstance(ind_kind, W_Inductive):
            return W_InvalidConstructorResult(tc.env, type)
        for name in ind_kind.ctor_names:
            if name.syntactic_eq(tc.decl.name):
                return None
        return W_InvalidConstructorResult(tc.env, type)

    def decl_format(self, name, levels, type, constants, marker):
        return _decl_signature_format(
            "constructor", name, levels, type, constants, marker,
        )

    def constructor_format(
        self, constructor_name, type, inductive, constants, marker,
    ):
        # Constructor names are always a single-part child of their
        # inductive's name in Lean (e.g., `List.cons` inside `List`),
        # so display just the leaf part. Fall back to the full name
        # if the invariant doesn't hold.
        if constructor_name.parent.syntactic_eq(inductive.name):
            short = constructor_name._part_str()
        else:
            short = constructor_name.str()
        parts = [_format.text(PUNCT, "| "), _format.text(DECL_NAME, short)]
        if type not in [each.const() for each in inductive.all]:
            parts.append(_format.text(PUNCT, " : "))
            parts.append(_sub(marker, type, constants))
        return _format.concat(parts)


class W_Recursor(W_DeclarationKind):
    _attrs_ = [
        'k', 'num_params', 'num_indices', 'num_motives', 'num_minors',
        '_rules_by_ctor', 'all', 'rules',
    ]

    def group_key(self, name, safety):
        return self.all[0] if self.all else None
    _immutable_fields_ = [
        'k', 'num_params', 'num_indices', 'num_motives', 'num_minors',
        'all', 'rules',
    ]

    def __init__(
        self,
        all,
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
        # Lazy {ctor_name → W_RecRule} index, populated on first
        # `rule_for_ctor` call so iota lookup is O(1) instead of a
        # linear scan over `rules`.
        self._rules_by_ctor = None
        #: The inductives this recursor targets (just `[parent]` for a
        #: non-mutual recursor like `Foo.rec` → `[Foo]`). Matches
        #: Lean's `RecursorVal.all`.
        self.all = all
        self.rules = rules

    def major_induct_name(self, rec_type):
        """
        The name of this recursor's major-premise inductive, read off
        the recursor's type: skip the params/motives/minors/indices
        binders, then take the head constant of the major's domain.
        Mirrors lean4's ``recursor_val::get_major_induct``
        (declaration.cpp). ``None`` if the type isn't the expected pi
        chain (malformed exports).

        For an ordinary recursor this is `all[0]`; for the split
        recursors of a nested block it's the nested container (e.g.
        `Lean.Syntax.rec_1`'s major is an `Array Lean.Syntax`).
        """
        n = (
            self.num_params
            + self.num_motives
            + self.num_minors
            + self.num_indices
        )
        t = rec_type
        for _ in range(n):
            if not isinstance(t, W_ForAll):
                return None
            t = t.body
        if not isinstance(t, W_ForAll):
            return None
        head = t.type.head()
        if not isinstance(head, W_Const):
            return None
        return head.name

    def rule_for_ctor(self, ctor_name):
        """The rec rule matching ``ctor_name``, or None if no rule does.

        Populates an internal ctor-name-keyed index on first call so
        subsequent lookups during iota reduction are O(1).
        """
        if self._rules_by_ctor is None:
            index = name_dict()
            for r in self.rules:
                index[r.ctor_name] = r
            self._rules_by_ctor = index
        return self._rules_by_ctor.get(ctor_name, None)

    def register_exporter_index(self, exporter, name):
        for induct in self.all:
            exporter.register_inductive_recursor(induct, name)

    def dump_to(self, exporter, decl):
        # Each mutual-block inductive's `dump_to` emits the whole
        # group (types + ctors + recs). Recursors come back via that
        # path; the standalone recursor visit just routes there.
        for ind in self.all:
            if ind in exporter.decls:
                exporter.dump_constant(exporter.decls[ind])

    def type_check(self, type, tc):
        from rpylean._inductive import alpha_eq, recursors_of

        env = tc.env
        if not self.all:
            return W_InvalidRecursorRule(
                env, "recursor targets no inductive types",
            )
        try:
            first = get_decl(env.declarations, self.all[0])
        except UnknownDeclaration:
            return W_InvalidRecursorRule(
                env,
                "recursor refers to %s which is not declared"
                % self.all[0].str(),
            )
        if not _decl_visible(tc.decl, first):
            return W_InvalidRecursorRule(
                env,
                "recursor refers to %s which is not declared"
                % self.all[0].str(),
            )
        first_kind = first.w_kind
        if not isinstance(first_kind, W_Inductive):
            return W_InvalidRecursorRule(
                env,
                "recursor refers to %s which is not an inductive"
                % self.all[0].str(),
            )
        if tc.decl.safety != first.safety:
            return W_InvalidRecursorRule(
                env, "recursor and inductive differ in safety",
            )
        if len(first_kind.all) != len(self.all):
            return W_InvalidRecursorRule(
                env, "recursor and inductive disagree on their block",
            )
        for i in range(len(self.all)):
            if not self.all[i].syntactic_eq(first_kind.all[i]):
                return W_InvalidRecursorRule(
                    env, "recursor and inductive disagree on their block",
                )

        spec = None
        for each in recursors_of(first, tc):
            if each.name.syntactic_eq(tc.decl.name):
                spec = each
                break
        if spec is None:
            return W_InvalidRecursorRule(
                env,
                "recursor %s is not a name the kernel generates for %s"
                % (tc.decl.name.str(), self.all[0].str()),
            )

        levels = tc.decl.levels
        expected_type = spec.type
        substs = None
        offset = 0
        if spec.elim_name is not None:
            offset = 1
            if len(levels) != len(first.levels) + 1:
                return W_InvalidRecursorRule(
                    env,
                    "recursor does not take a universe to eliminate into",
                )
            elim = levels[0]
            for each in first.levels:
                if each.syntactic_eq(elim):
                    return W_InvalidRecursorRule(
                        env, "recursor repeats a universe parameter",
                    )
            if not elim.syntactic_eq(spec.elim_name):
                substs = {spec.elim_name: elim.as_level_param()}
                expected_type = expected_type.subst_levels(substs)
        elif len(levels) != len(first.levels):
            return W_InvalidRecursorRule(
                env, "recursor may only eliminate into Prop",
            )
        for i in range(len(first.levels)):
            if not levels[i + offset].syntactic_eq(first.levels[i]):
                return W_InvalidRecursorRule(
                    env,
                    "recursor and inductive differ in universe parameters",
                )

        if (
            self.num_params != spec.num_params
            or self.num_indices != spec.num_indices
            or self.num_motives != spec.num_motives
            or self.num_minors != spec.num_minors
        ):
            return W_InvalidRecursorRule(
                env,
                "recursor should have %d param(s), %d index(es), "
                "%d motive(s) and %d minor(s)" % (
                    spec.num_params, spec.num_indices,
                    spec.num_motives, spec.num_minors,
                ),
            )
        if self.k != spec.k:
            return W_InvalidRecursorRule(
                env, "recursor is wrong about supporting K-like reduction",
            )
        if not alpha_eq(type, expected_type):
            sort = type.infer(tc).whnf(tc)
            if not isinstance(sort, W_Sort) or not tc.def_eq(
                type, expected_type,
            ):
                return W_InvalidRecursorRule(
                    env,
                    "recursor type is not the one its inductive gives rise to",
                )
        if len(self.rules) != len(spec.rules):
            return W_InvalidRecursorRule(
                env,
                "recursor has %d rule(s) but should have %d"
                % (len(self.rules), len(spec.rules)),
            )
        for i in range(len(self.rules)):
            rule = self.rules[i]
            expected = spec.rules[i]
            if not rule.ctor_name.syntactic_eq(expected.ctor_name):
                return W_InvalidRecursorRule(
                    env,
                    "rule #%d is for %s but should be for %s" % (
                        i + 1,
                        rule.ctor_name.str(),
                        expected.ctor_name.str(),
                    ),
                )
            if rule.num_fields != expected.num_fields:
                return W_InvalidRecursorRule(
                    env,
                    "rule for %s claims %d fields but the ctor has %d" % (
                        rule.ctor_name.str(),
                        rule.num_fields,
                        expected.num_fields,
                    ),
                )
            rhs = expected.rhs
            if substs is not None:
                rhs = rhs.subst_levels(substs)
            if not alpha_eq(rule.rhs, rhs):
                rhs_type = rule.rhs.infer(tc)
                if not tc.def_eq(rhs_type, rhs.infer(tc)) or not tc.def_eq(
                    rule.rhs, rhs,
                ):
                    return W_InvalidRecursorRule(
                        env,
                        "rule for %s is not the one its inductive gives "
                        "rise to" % rule.ctor_name.str(),
                    )

    def decl_format(self, name, levels, type, constants, marker):
        return _decl_signature_format(
            "recursor", name, levels, type, constants, marker,
        )


def syntactic_eq(expr1, expr2):
    """
    Check if two expressions are syntactically equal.
    """
    if expr1 is expr2:
        return True
    if expr1.__class__ is not expr2.__class__:
        return False
    return expr1.syntactic_eq(expr2)


class Telescope(object):
    _attrs_ = ['_binders']

    def __init__(self, *binders):
        assert len(binders) > 0
        self._binders = list(binders)

    @unroll_safe
    def forall(self, body):
        forall = _mk_w_forall(self._binders[-1], body)
        for binder in reversed(self._binders[:-1]):
            forall = _mk_w_forall(binder, forall)
        return forall

    @unroll_safe
    def fun(self, body):
        fun = _mk_w_lambda(self._binders[-1], body)
        for binder in reversed(self._binders[:-1]):
            fun = _mk_w_lambda(binder, fun)
        return fun


def forall(*binders):
    return Telescope(*binders).forall


def fun(*binders):
    return Telescope(*binders).fun
