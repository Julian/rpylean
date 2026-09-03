from rpython.rlib.jit import (
    dont_look_inside, elidable, promote, unroll_safe,
)
from rpython.rlib.objectmodel import (
    always_inline, compute_hash, newlist_hint,
    not_rpython, specialize,
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


class W_HeartbeatError(W_CheckError):
    """
    The heartbeat limit was exceeded while checking a declaration.
    """

    _attrs_ = ['heartbeats', 'max_heartbeat']

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


@elidable
def name_eq(name, other):
    # FIXME: this duplicates Name.syntactic_eq, but if we remove it and use
    #        that directly, RPython seems unable to be convinced that name and
    #        other are always Names no matter how much I assert.
    #
    return name.syntactic_eq(other)


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
        return a.syntactic_eq(b)

    def _hash(name):
        return name.hash()

    return r_dict(_eq, _hash)


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

_INTERN_STR_NAME = {}      # int -> list[StrName]
_INTERN_NUM_NAME = {}      # int -> list[NumName]
# The expression tables map each content hash to a single node — on a
# collision the newest node simply takes the slot. Losing the displaced
# node only costs sharing (a future structurally-equal request allocates
# anew); nothing relies on interned-expression identity for correctness.
# One-node slots keep the table at a dict entry per node where chained
# buckets cost a `list` + backing array apiece — tens of millions of
# entries on Mathlib-sized exports. The name/level tables stay chained:
# they are small, and keeping every name canonical preserves the `is`
# fast paths and per-instance caches (`_level_cache`) at full strength.
_INTERN_W_APP = {}         # int -> W_App
_INTERN_W_CONST = {}       # int -> W_Const
_INTERN_W_PROJ = {}        # int -> W_Proj
_INTERN_W_LET = {}         # int -> W_Let
_INTERN_W_SORT = {}        # int -> list[W_Sort]
_INTERN_LEVEL_SUCC = {}    # int -> list[W_LevelSucc]
_INTERN_LEVEL_MAX = {}     # int -> list[W_LevelMax]
_INTERN_LEVEL_IMAX = {}    # int -> list[W_LevelIMax]
_INTERN_LEVEL_PARAM = {}   # int -> list[W_LevelParam]
# NOT hash-consed (see comments by their `_mk_*` factories):
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
    uid = _EXPR_UID.count
    _EXPR_UID.count = uid + 1
    return uid


def intern_stats():
    """
    Entry counts of the persistent intern tables, for leak hunting: the
    tables only ever grow, so a count climbing in step with declarations
    checked (rather than with parsing) means reduction products are
    being interned persistently somewhere.
    """
    return len(_INTERN_W_APP), len(_INTERN_W_PROJ), len(_INTERN_W_CONST)


def _mk_str_name(parent, suffix):
    assert isinstance(parent, Name)
    h = _mix2(parent.hash(), compute_hash(suffix))
    bucket = _INTERN_STR_NAME.get(h, None)
    if bucket is None:
        e = StrName(parent, suffix)
        _INTERN_STR_NAME[h] = [e]
        return e
    for existing in bucket:
        if existing.parent is parent and existing.suffix == suffix:
            return existing
    e = StrName(parent, suffix)
    bucket.append(e)
    return e


def _mk_num_name(parent, idx):
    assert isinstance(parent, Name)
    # `idx.hash()` here is rbigint's content hash — cheap, no string alloc.
    h = _mix2(parent.hash(), idx.hash())
    bucket = _INTERN_NUM_NAME.get(h, None)
    if bucket is None:
        e = NumName(parent, idx)
        _INTERN_NUM_NAME[h] = [e]
        return e
    for existing in bucket:
        if existing.parent is parent and existing.idx.eq(idx):
            return existing
    e = NumName(parent, idx)
    bucket.append(e)
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
    h = h & _HASH_MASK
    existing = _INTERN_W_CONST.get(h, None)
    if existing is not None and existing.name is name:
        if len(existing.levels) == len(levels):
            match = True
            for i in range(len(levels)):
                if existing.levels[i] is not levels[i]:
                    match = False
                    break
            if match:
                return existing
    e = W_Const(name=name, levels=levels)
    _INTERN_W_CONST[h] = e
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
    return Binder(name=name, type=type, left="(", right=")")


def _mk_binder_implicit(name, type):
    return Binder(name=name, type=type, left="{", right="}")


def _mk_binder_instance(name, type):
    return Binder(name=name, type=type, left="[", right="]")


def _mk_binder_strict_implicit(name, type):
    return Binder(name=name, type=type, left="\xe2\xa6\x83", right="\xe2\xa6\x84")


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

@elidable
def _mk_app(fn, arg):
    """
    Allocate a `W_App(fn, arg)` against the persistent intern table.
    """
    assert isinstance(fn, W_Expr)
    assert isinstance(arg, W_Expr)
    h = _mix2(fn.hash(), arg.hash())
    existing = _INTERN_W_APP.get(h, None)
    if existing is not None and existing.fn is fn and existing.arg is arg:
        return existing
    e = W_App(fn, arg)
    _INTERN_W_APP[h] = e
    return e


def _mk_w_lambda(binder, body):
    return W_Lambda(binder, body)


def _mk_w_forall(binder, body):
    return W_ForAll(binder, body)


@elidable
def _mk_w_proj(struct_name, field_index, struct_expr):
    assert isinstance(struct_name, Name)
    assert isinstance(struct_expr, W_Expr)
    h = _mix3(struct_name.hash(), field_index, struct_expr.hash())
    existing = _INTERN_W_PROJ.get(h, None)
    if (existing is not None
            and existing.struct_name is struct_name
            and existing.field_index == field_index
            and existing.struct_expr is struct_expr):
        return existing
    e = W_Proj(struct_name, field_index, struct_expr)
    _INTERN_W_PROJ[h] = e
    return e


def _mk_w_let(name, type, value, body):
    assert isinstance(name, Name)
    assert isinstance(type, W_Expr)
    assert isinstance(value, W_Expr)
    assert isinstance(body, W_Expr)
    h = _mix4(name.hash(), type.hash(), value.hash(), body.hash())
    existing = _INTERN_W_LET.get(h, None)
    if (existing is not None
            and existing.name is name and existing.type is type
            and existing.value is value and existing.body is body):
        return existing
    e = W_Let(name=name, type=type, value=value, body=body)
    _INTERN_W_LET[h] = e
    return e


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
        '_level_cache', 'parent', '_hash', 'is_internal', 'is_private',
        '_decl_dict', '_decl_cached',
    ]
    _immutable_fields_ = ['parent', '_hash', 'is_internal', 'is_private']

    def __init__(self):
        # Lazy cache for `as_level_param()`; populated on first call.
        # Subclasses set their own `parent` / `_hash` / `is_internal` /
        # `is_private` fields after calling this.
        self._level_cache = None
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

    def syntactic_eq(self, other):
        """
        Lean's ``Name.beq``: structural equality, walked iteratively
        leaf-to-root so deep names don't blow the C stack on translated
        builds.
        """
        a = self
        b = other
        while True:
            if a is b:
                return True
            if a.is_anonymous() or b.is_anonymous():
                return a.is_anonymous() and b.is_anonymous()
            if isinstance(a, NumName):
                if not isinstance(b, NumName):
                    return False
                if not a.idx.eq(b.idx):
                    return False
            else:
                assert isinstance(a, StrName)
                if not isinstance(b, StrName):
                    return False
                if a.suffix != b.suffix:
                    return False
            a = a.parent
            b = b.parent

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

    @unroll_safe
    def const(self, levels=None):
        """
        Construct a constant expression for this name.
        """
        return _mk_w_const(self, [] if levels is None else levels)

    def declaration(self, type, w_kind, levels=None, safety=SAFETY_SAFE):
        """
        Make a declaration with this name.
        """
        return W_Declaration(
            name=self,
            type=type,
            levels=[] if levels is None else levels,
            w_kind=w_kind,
            safety=safety,
        )

    def constructor(self, type, num_params=0, num_fields=0, cidx=0,
                    levels=None, is_unsafe=False):
        """
        Make a constructor declaration with this name.
        """
        constructor = W_Constructor(
            num_params=num_params,
            num_fields=num_fields,
            cidx=cidx,
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

    def __init__(self, parent, suffix):
        Name.__init__(self)
        self.parent = parent
        self.suffix = suffix
        self._hash = (
            (parent.hash() * 1000003) ^ compute_hash(suffix)
        ) & 0xFFFFFFFF
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
    ``idx`` is an ``rbigint`` since Lean's ``Nat`` is unbounded.
    """

    _attrs_ = ['idx']
    _immutable_fields_ = ['idx']

    def __init__(self, parent, idx):
        Name.__init__(self)
        self.parent = parent
        self.idx = idx
        # XOR with a marker bit so a `Name.num n` and a `Name.str (str n)`
        # don't collide in the hash table; `syntactic_eq` also distinguishes
        # via subclass identity.
        h = compute_hash(idx.str()) ^ 0x5A5A5A5A
        self._hash = ((parent.hash() * 1000003) ^ h) & 0xFFFFFFFF
        # Lean's `isInternal` / private-name checks: num parts don't
        # trigger themselves but they don't block parent propagation.
        self.is_internal = parent.is_internal
        self.is_private = parent.is_private

    def has_macro_scopes(self):
        # Lean: `.num n _ => hasMacroScopes n`
        return self.parent.has_macro_scopes()

    def _part_str(self):
        return self.idx.str()


def names(*many):
    """
    Create a bunch of names at once.
    """
    return [Name.from_str(each) for each in many]


#: The anonymous name.
Name.ANONYMOUS = _AnonymousName()


class Binder(_Item):
    """
    A binder within a Lambda or ForAll.

    Only `type` is really functionally important, the other attributes are
    strictly for pretty printing.
    """

    _attrs_ = ['name', 'type', 'left', 'right', '_position', '_fvar', '_hash']
    _immutable_fields_ = ['name', 'type', 'left', 'right', '_hash']

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

    def __init__(self, name, type, left, right):
        self.name = name
        self.type = type
        self.left = left
        self.right = right
        #: The binding position this binder stands at, which a binder
        #: rebuilt from it (with a substituted type, say) shares, and
        #: which its free variable carries as its id.
        self._position = next(W_FVar._counter)
        self._fvar = None
        h = name.hash() ^ type.hash()
        h = (h * 1000003) ^ compute_hash(left)
        h = (h * 1000003) ^ compute_hash(right)
        self._hash = h & 0xFFFFFFFF

    def hash(self):
        return self._hash

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

    def to_format(self, constants, marker):
        return _format.concat([
            _format.text(PUNCT, self.left),
            _format.text(BINDER_NAME, self.name.user_name().str()),
            _format.text(PUNCT, " : "),
            _sub(marker, self.type, constants),
            _format.text(PUNCT, self.right),
        ])

    def tokens(self, constants, mark=None, span_holder=None):
        return _tokens_from_format(
            self.to_format(constants, _marker_for(mark)), span_holder,
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

        Returns the same FVar each time so that identity comparisons
        work across inference and rendering.
        """
        fvar = self._fvar
        if fvar is None:
            fvar = W_FVar(self, self._position)
            self._fvar = fvar
        return fvar

    def bind_fvar(self, fvar, depth):
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
            self.left == other.left
            and syntactic_eq(self.name, other.name)
            and syntactic_eq(self.type, other.type)
        )

    def with_type(self, type):
        """
        Create a new binder of the same name and kind but with a new type.
        """
        if self.left == "(":
            binder = _mk_binder_default(self.name, type)
        elif self.left == "{":
            binder = _mk_binder_implicit(self.name, type)
        elif self.left == "[":
            binder = _mk_binder_instance(self.name, type)
        else:
            binder = _mk_binder_strict_implicit(self.name, type)
        binder._position = self._position
        return binder


def leq(fn):
    def leq(self, other, balance=0):
        if self is other or syntactic_eq(self, other):
            return balance >= 0
        return fn(self, other, balance)

    return leq


# Based on https://github.com/gebner/trepplein/blob/c704ffe81941779dacf9efa20a75bf22832f98a9/src/main/scala/trepplein/level.scala#L100
class W_Level(_Item):
    _attrs_ = ['_hash', '_normal']
    _immutable_fields_ = ['_hash']

    #: The normal form, once computed (levels are immutable and
    #: interned, so it never changes).
    _normal = None

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
        return _mk_w_sort(self)

    def succ(self):
        """
        Return the level which is successor to this one.
        """
        return _mk_level_succ(self)

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
        self._hash = ((parent.hash() * 1000003) ^ 0x53C7) & 0xFFFFFFFF

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
        base, k = self.to_offset()
        return base.normalize_at(k)

    def norm_kind(self):
        return 1

    def is_not_zero(self):
        return True

    def pretty_parts(self):
        text, balance = self.parent.pretty_parts()
        return text, balance + 1

    def subst_levels(self, substs):
        new_parent = self.parent.subst_levels(substs)
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
        h = (lhs.hash() * 1000003) ^ rhs.hash()
        self._hash = ((h * 1000003) ^ 0x6D4A) & 0xFFFFFFFF

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
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
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
        h = (lhs.hash() * 1000003) ^ rhs.hash()
        self._hash = ((h * 1000003) ^ 0x694D) & 0xFFFFFFFF

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
        new_lhs = self.lhs.subst_levels(substs)
        new_rhs = self.rhs.subst_levels(substs)
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
        self._hash = ((name.hash() * 1000003) ^ 0x5041) & 0xFFFFFFFF

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


class W_Expr(_Item):
    # Three per-node immutable scalars are packed into one `_packed` word:
    #
    #   bits  0-31 : the content `hash()` (already masked to 32 bits)
    #   bit     32 : `has_fvar` (does any free variable occur)
    #   bits 33-63 : `loose_bvar_range` (largest loose de-Bruijn index + 1)
    #
    # Each was its own machine word before (`_hash`, plus a `_bvar_fvar`
    # that already folded the latter two). They are all small — a term's
    # bvar depth is tiny and the hash is 32-bit — so one word holds them
    # with `loose_bvar_range` never reaching bit 63 (it stays positive,
    # so the `>> 33` unpack needs no mask). Tens of millions of nodes are
    # live on a Mathlib-sized heap, so collapsing three words to one is a
    # direct cut to the parsed-heap footprint and thus to GC
    # survivor-tracing time. `Name` / `W_Level` keep their own separate
    # `_hash` field — only `W_Expr` is packed.
    #
    # Accessors are `@always_inline` (not `@elidable`): they sit on hot
    # paths — `loose_bvar_range() <= depth` in substitution, `hash()` in
    # every node's construction — and the default binary runs the JIT
    # off, so they must inline to a bare shift/mask rather than stay a
    # call for a tracer to fold. `_packed` is immutable, so the unpack is
    # still JIT-foldable.
    _attrs_ = ['_packed', '_uid']
    _immutable_fields_ = ['_packed', '_uid']

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
        return self._packed >> 33

    @always_inline
    def has_fvar(self):
        """Whether any free variable (`W_FVar`) occurs in this term."""
        return ((self._packed >> 32) & 1) != 0


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
                return expr.binder.name.user_name().str()
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
        self._uid = _next_uid()
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


class W_FVar(W_Expr):
    """An FVar which refers to its binder by identity."""

    _attrs_ = ['id', 'binder']
    _immutable_fields_ = ['id', 'binder']

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


class W_LitStr(W_Expr):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        assert isinstance(val, str)
        self.val = val
        bf = 0
        self._uid = _next_uid()
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
        for i in range(len(self.val) - 1, -1, -1):
            char_expr = Name.from_str("Char.ofNat").app(W_LitNat.char(self.val[i]))
            expr = cons.app(char_expr).app(expr)
        return Name.from_str("String.ofList").app(expr)


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
    _attrs_ = ['level']
    _immutable_fields_ = ['level']

    def __init__(self, level):
        self.level = level
        bf = 0
        self._uid = _next_uid()
        self._packed = (((level.hash() * 1000003) ^ 0x5071) & 0xFFFFFFFF) | (bf << 32)

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
    _attrs_ = [
        'name', 'levels',
        '_infer_cache_env', '_infer_cache_result',
        '_delta_cache_env', '_delta_cache_result',
    ]
    _immutable_fields_ = ['name', 'levels']

    def __init__(self, name, levels):
        self.name = name
        for each in levels:
            assert isinstance(each, W_Level), "%s is not a W_Level" % (each,)
        self.levels = levels
        bf = 0
        # Inline caches, tagged with the env — hash-consing shares this
        # instance across `Environment`s and both the inferred type
        # and the delta-unfolded value depend on the env's declarations.
        # `_infer_cache_*` caches `apply_const_level_params(self, decl.type)`,
        # `_delta_cache_*` caches the same applied to `decl.value`. Both
        # walks were unconditionally re-running before — `subst_levels`
        # showed up as ~10% leaf time in profiles because every shared
        # `W_Const` reference repeated the full structural rewrite.
        self._infer_cache_env = None
        self._infer_cache_result = None
        self._delta_cache_env = None
        self._delta_cache_result = None
        h = name.hash()
        for lvl in levels:
            h = (h * 1000003) ^ lvl.hash()
        self._uid = _next_uid()
        self._packed = (((h * 1000003) ^ 0xC057) & 0xFFFFFFFF) | (bf << 32)

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

# Max exponent for Nat.pow to prevent excessive computation
_REDUCE_POW_MAX_EXP = rbigint.fromint(1 << 24)


class W_LitNat(W_Expr):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        self.val = val
        bf = 0
        self._uid = _next_uid()
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
        return _mk_w_litnat(v1.lshift(v2.toint()))
    if name_eq(name, _NAT_SHIFT_RIGHT):
        return _mk_w_litnat(v1.rshift(v2.toint()))
    return None


class W_Proj(W_Expr):
    _attrs_ = [
        'struct_name', 'field_index', 'struct_expr',
        '_struct_whnf_env', '_struct_whnf',
    ]
    _immutable_fields_ = ['struct_name', 'field_index', 'struct_expr']

    def __init__(self, struct_name, field_index, struct_expr):
        self.struct_name = struct_name
        self.field_index = field_index
        self.struct_expr = struct_expr
        # Inline cache of `struct_expr.whnf(env)` for the `env` it was
        # computed under. Lives in its own mutable slot so `struct_expr`
        # stays set-once (interning of `W_Proj` requires it). The env
        # tag is needed because hash-consing shares the same `W_Proj`
        # across `Environment`s and `whnf` is env-dependent.
        self._struct_whnf_env = None
        self._struct_whnf = None
        bf = (
            (struct_expr.loose_bvar_range() << 1)
            | (1 if struct_expr.has_fvar() else 0)
        )
        h = (struct_name.hash() * 1000003) ^ field_index
        h = (h * 1000003) ^ struct_expr.hash()
        self._uid = _next_uid()
        self._packed = (((h * 1000003) ^ 0x9709) & 0xFFFFFFFF) | (bf << 32)


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
        new_expr = self.struct_expr.bind_fvar(fvar, depth)
        if new_expr is self.struct_expr:
            return self
        return self.with_expr(new_expr)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        return self.with_expr(self.struct_expr.instantiate(expr, depth))

    def subst_levels(self, substs):
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
    _attrs_ = ['binder', 'body']
    _immutable_fields_ = ['binder', 'body']

    # Subclasses set this to a distinct tag so structurally-equal
    # lambdas and foralls don't collide in the content hash.
    _hash_tag = 0

    def __init__(self, binder, body):
        assert body is not None
        assert isinstance(binder, Binder)
        self.binder = binder
        self.body = body
        body_range = body.loose_bvar_range() - 1
        if body_range < 0:
            body_range = 0
        binder_range = binder.type.loose_bvar_range()
        if binder_range > body_range:
            loose = binder_range
        else:
            loose = body_range
        fvar = binder.type.has_fvar() or body.has_fvar()
        bf = (loose << 1) | (1 if fvar else 0)
        # Content hash: mix binder's name + type + binder-info + body.
        h = (binder.name.hash() * 1000003) ^ binder.type.hash()
        h = (h * 1000003) ^ body.hash()
        self._uid = _next_uid()
        self._packed = (((h * 1000003) ^ self._hash_tag) & 0xFFFFFFFF) | (bf << 32)


    def contains_const(self, name):
        return (self.binder.type.contains_const(name)
                or self.body.contains_const(name))

    def collect_consts_into(self, out, seen):
        self.binder.type.collect_consts_into(out, seen)
        self.body.collect_consts_into(out, seen)

    # Subclasses (W_Lambda, W_ForAll) set this to their lean4export tag
    # and `_ie_first_tag` to whether `"ie"` precedes the discriminator
    # alphabetically (true for `"lam"` since `'i' < 'l'`, false for
    # `"forallE"` since `'f' < 'i'`).
    _export_tag = ""
    _ie_first_tag = False

    def emit_to(self, exporter):
        bnid = exporter.name_id(self.binder.name)
        tid = exporter.expr_id(self.binder.type)
        bid = exporter.expr_id(self.body)
        eid = exporter.next_expr_id()
        bi = self.binder.export_info_name()
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


class W_ForAll(W_FunBase):
    _attrs_ = []

    _export_tag = "forallE"
    _ie_first_tag = False  # `'f' < 'i'`
    _hash_tag = 0xF0A1


    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        new_binder = self.binder.instantiate(expr, depth)
        new_body = self.body.instantiate(expr, depth + 1)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_forall(new_binder, new_body)

    def syntactic_eq(self, other):
        assert isinstance(other, W_ForAll)
        return syntactic_eq(self.binder, other.binder) and syntactic_eq(
            self.body, other.body
        )

    def bind_fvar(self, fvar, depth):
        new_binder = self.binder.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_forall(new_binder, new_body)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return _mk_w_forall(self.binder.incr_free_bvars(count, depth),
            self.body.incr_free_bvars(count, depth + 1),
        )

    def subst_levels(self, levels):
        new_binder = self.binder.subst_levels(levels)
        new_body = self.body.subst_levels(levels)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_forall(new_binder, new_body)

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
            binders = [self.binder]
            current = rhs
            while isinstance(current, W_ForAll):
                next_is_forall, next_rhs = _forall_quantifier_step(
                    current, constants,
                )
                if not next_is_forall:
                    break
                binders.append(current.binder)
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
            if self.binder.is_default() and not self.body.loose_bvar_range() > 0:
                wrap = isinstance(self.binder.type, W_ForAll)
                inner = _sub(marker, self.binder.type, constants)
                if wrap:
                    lhs = _format.concat([
                        _format.text(PUNCT, "("),
                        inner,
                        _format.text(PUNCT, ")"),
                    ])
                else:
                    lhs = inner
            elif (
                self.binder.is_instance()
                and not self.body.loose_bvar_range() > 0
                and self.binder.name.has_macro_scopes()
            ):
                lhs = _format.concat([
                    _format.text(PUNCT, "["),
                    _sub(marker, self.binder.type, constants),
                    _format.text(PUNCT, "]"),
                ])
            else:
                lhs = _sub(marker, self.binder, constants)
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

    return "%s%s%s" % (group[-1].left, names, group[-1].right)


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
    parts = [_format.text(PUNCT, group[-1].left)]
    for i, binder in enumerate(group):
        if i > 0:
            parts.append(_format.text(PLAIN, " "))
        parts.append(_format.text(BINDER_NAME, binder.name.user_name().str()))
    parts.append(_format.text(PUNCT, group[-1].right))
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
    lhs_type = fa.binder.type
    if isinstance(lhs_type, W_Const):
        # Tolerate names `constants` doesn't have (a partially registered
        # environment, e.g. mid-`ffi check`): rendering must never raise,
        # it just loses the ∀-vs-→ refinement.
        decl = constants.get(lhs_type.name, None)
        if decl is not None:
            lhs_type = decl.type
    elif isinstance(lhs_type, W_FVar):
        lhs_type = lhs_type.binder.type
    rhs = fa.body.instantiate(fa.binder.fvar())
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
        j = i + 1
        while (j < n
               and binders[j].left == b.left
               and binders[j].right == b.right
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
            _format.text(PUNCT, b.left),
            _format.fill(_format.nest(2, _format.concat(inner))),
            _format.text(PUNCT, b.right),
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
            binders.append(current.binder)
            binder_used.append(current.body.loose_bvar_range() > 0)
            current = current.body

        # One Format per emitted binder group / instance binder; joined with
        # soft breaks below so a long binder list fill-wraps (as Lean does).
        binder_docs = []
        current_group, last_style = [], binders[0].left

        for i, binder in enumerate(binders):
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
                last_style = None
            elif binder.left != last_style and current_group:
                binder_docs.append(
                    _binder_group_format(current_group, constants),
                )
                current_group, last_style = [binder], binder.left
            else:
                current_group.append(binder)
                last_style = binder.left
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

    def syntactic_eq(self, other):
        assert isinstance(other, W_Lambda)
        return syntactic_eq(self.binder, other.binder) and syntactic_eq(
            self.body, other.body
        )

    def bind_fvar(self, fvar, depth):
        new_binder = self.binder.bind_fvar(fvar, depth)
        new_body = self.body.bind_fvar(fvar, depth + 1)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_lambda(new_binder, new_body)

    def instantiate(self, expr, depth=0):
        if self.loose_bvar_range() <= depth:
            return self
        new_binder = self.binder.instantiate(expr, depth)
        new_body = self.body.instantiate(expr, depth + 1)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_lambda(new_binder, new_body)

    def incr_free_bvars(self, count, depth):
        if self.loose_bvar_range() <= depth:
            return self
        return _mk_w_lambda(self.binder.incr_free_bvars(count, depth),
            self.body.incr_free_bvars(count, depth + 1),
        )


    def subst_levels(self, substs):
        new_binder = self.binder.subst_levels(substs)
        new_body = self.body.subst_levels(substs)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_lambda(new_binder, new_body)


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
        h = (name.hash() * 1000003) ^ type.hash()
        h = (h * 1000003) ^ value.hash()
        h = (h * 1000003) ^ body.hash()
        self._uid = _next_uid()
        self._packed = (((h * 1000003) ^ 0x1ED7) & 0xFFFFFFFF) | (bf << 32)

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

    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg
        fn_range = fn.loose_bvar_range()
        arg_range = arg.loose_bvar_range()
        if fn_range > arg_range:
            loose = fn_range
        else:
            loose = arg_range
        fvar = fn.has_fvar() or arg.has_fvar()
        bf = (loose << 1) | (1 if fvar else 0)
        h = (fn.hash() * 1000003) ^ arg.hash()
        self._uid = _next_uid()
        self._packed = (((h * 1000003) ^ 0xAB30) & 0xFFFFFFFF) | (bf << 32)


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
        new_fn = self.fn.subst_levels(substs)
        new_arg = self.arg.subst_levels(substs)
        if new_fn is self.fn and new_arg is self.arg:
            return self
        return new_fn.app(new_arg)


class W_RecRule(_Item):
    _attrs_ = ['ctor_name', 'num_fields', 'rhs']
    _immutable_fields_ = ['ctor_name', 'num_fields', 'rhs']

    def __init__(self, ctor_name, num_fields, rhs):
        self.ctor_name = ctor_name
        self.num_fields = num_fields
        self.rhs = rhs


class W_Declaration(_Item):
    _attrs_ = [
        'name', 'type', 'w_kind', 'levels', 'safety', 'index', 'group',
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


class W_Definition(W_DeclarationKind):
    _attrs_ = ['value', 'hint', 'all']
    _immutable_fields_ = ['value', 'hint', 'all']

    def __init__(self, value, hint, all=None):
        self.value = value
        self.hint = hint
        #: The members of this definition's mutual block (`DefinitionVal.
        #: all`), or ``None`` when it stands alone.
        self.all = all

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


class W_Opaque(W_Definition):
    """
    An Opaque definition.

    This is like a definition with hint 'opaque', but even
    stronger (we will never unfold it).
    """

    _attrs_ = []

    def __init__(self, value):
        self.value = value
        self.hint = HINT_OPAQUE
        self.all = None

    def group_key(self, name, safety):
        return None

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_opaque(decl, self.value)

    def get_delta_reduce_target(self):
        return None


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

    def decl_format(self, name, levels, type, constants, marker):
        # rpylean displays quot decls as ordinary axioms.
        return _decl_signature_format(
            "axiom", name, levels, type, constants, marker,
        )


class W_Inductive(W_DeclarationKind):
    _attrs_ = [
        'name', 'all', 'constructors', 'recursors',
        'num_nested', 'num_params', 'num_indices',
        'is_reflexive', 'is_recursive', 'ctor_names',
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
        target = type
        for _ in range(self.num_params + self.num_indices):
            if not isinstance(target, W_ForAll):
                # The remaining arity can hide behind a definition —
                # e.g. `Presieve.ofArrows : … → Presieve X`, where
                # `Presieve X` unfolds to a pi ending in a Sort and
                # the export counts its binders among the indices.
                target = target.whnf(tc)
            if not isinstance(target, W_ForAll):
                return W_NotASort(tc, type, inferred_type=target, name=None)
            # The peeled binder is bvar(0) of the body — depth 0, not
            # the loop index (an index-i substitution targets bvar(i)
            # at the body's top level, which never exists, silently
            # leaving every binder after the first loose).
            target = target.body.instantiate(target.binder.fvar(), 0)
        target_sort = target.whnf(tc)
        if not isinstance(target_sort, W_Sort):
            return W_NotASort(
                tc, type, inferred_type=target.infer(tc), name=None,
            )
        for ctor in self.constructor_decls(tc.declarations):
            error = self._check_constructor(ctor, target_sort.level, tc)
            if error is not None:
                return error

    def _check_constructor(self, ctor, inductive_level, env):
        """
        Verify a constructor is valid for this inductive.

        Checks the result type, index arguments, universe levels,
        and strict positivity of field types.
        """
        ctor_kind = ctor.w_kind
        assert isinstance(ctor_kind, W_Constructor)
        num_params = ctor_kind.num_params
        assert num_params >= 0
        ind_name = self.name
        error = W_InvalidConstructorResult(env, ctor.type, name=ctor.name)
        all_fvars, ctor_type = ctor.type.open_all_binders()
        if len(all_fvars) < num_params:
            return error
        param_fvars = all_fvars[:num_params]
        remaining_fvars = all_fvars[num_params:]
        if len(remaining_fvars) != ctor_kind.num_fields:
            return W_ConstructorFieldCountMismatch(
                env, ctor.type,
                declared=ctor_kind.num_fields,
                actual=len(remaining_fvars),
                name=ctor.name,
            )
        # ctor_type is now the result type, e.g. Ind p1 p2 ... idx1 idx2 ...
        head, rev_args = ctor_type.unapp()
        if not head.is_named(ind_name):
            return error
        assert isinstance(head, W_Const)
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
        # Index args must not contain any inductive of this block.
        for i in range(num_params, len(rev_args)):
            if self._contains_any_inductive(rev_args[i]):
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
        Whether *expr* contains an application of an inductive in this
        block whose index arguments themselves contain a block member.

        Mutual blocks share their parameter telescope, so
        ``self.num_params`` is the params/indices boundary for every
        member's application.
        """
        head, rev_args = expr.unapp()
        head_in_block = False
        for member in self.all:
            if head.is_named(member):
                head_in_block = True
                break
        if head_in_block:
            # Check index args (those after the params) for occurrences.
            rev_args.reverse()
            for i in range(self.num_params, len(rev_args)):
                if self._contains_any_inductive(rev_args[i]):
                    return True
            # Recurse into all args for nested invalid occurrences.
            for i in range(len(rev_args)):
                if self._has_invalid_index_occurrence(rev_args[i]):
                    return True
            return False
        return expr._any_subexpr_invalid_index(self)

    def _contains_any_inductive(self, expr):
        """Whether *expr* mentions any of the inductives in this block."""
        for name in self.all:
            if expr.contains_const(name):
                return True
        return False

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
    _attrs_ = ['num_params', 'num_fields', 'cidx']
    _immutable_fields_ = ['num_params', 'num_fields', 'cidx']

    def __init__(self, num_params, num_fields, cidx=0):
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
        # TODO - implement type checking
        # This includes checking that num_params and num_fields match the declared ctype
        pass

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
        head = t.binder.type.head()
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
        env = tc.env
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
        # Skip validation entirely if the parent inductive isn't in
        # scope and can't be demand-loaded — under the standard
        # (parser-based) flow inductives are registered in their block
        # before their recursors, and under `ffi check` `get_decl`
        # demand-loads them, so the skip only fires for genuinely
        # incomplete environments.
        all_ctors = []
        first_kind = None
        for ind_name in self.all:
            try:
                ind_decl = get_decl(env.declarations, ind_name)
            except UnknownDeclaration:
                return None
            ind_kind = ind_decl.w_kind
            if not isinstance(ind_kind, W_Inductive):
                return W_InvalidRecursorRule(
                    env,
                    "recursor refers to %s which is not an inductive"
                    % ind_name.str(),
                )
            if first_kind is None:
                first_kind = ind_kind
            for ctor in ind_kind.constructor_decls(env.declarations):
                all_ctors.append(ctor)
        if first_kind is None:
            return W_InvalidRecursorRule(
                env, "recursor targets no inductive types",
            )
        error = self._check_name(env, tc.decl.name, first_kind)
        if error is not None:
            return error
        # The kernel constructs one motive per type in the block —
        # the mutual members (`all`) plus the auxiliary types nested
        # occurrences are eliminated into (`num_nested`). A recursor
        # claiming any other count is one the kernel never generates;
        # in particular `num_motives = 0` would dodge every count-gated
        # check below.
        if self.num_motives != len(self.all) + first_kind.num_nested:
            return W_InvalidRecursorRule(
                env,
                "recursor has %d motive(s) but its block has %d type(s)"
                % (
                    self.num_motives,
                    len(self.all) + first_kind.num_nested,
                ),
            )
        error = self._check_type_shape(env, type, first_kind)
        if error is not None:
            return error
        # Split recursors (one per motive in a mutual or nested-inductive
        # block) only have rules for ctors whose return matches *their*
        # motive's type — so `len(rules) != len(ctors_of(all))` is fine
        # for them. Only enforce the count for single-motive recursors.
        if self.num_motives == 1 and len(self.rules) != len(all_ctors):
            return W_InvalidRecursorRule(
                env,
                "recursor has %d rule(s) but its inductive%s has %d "
                "constructor(s)" % (
                    len(self.rules),
                    "s" if len(self.all) > 1 else "",
                    len(all_ctors),
                ),
            )
        # ctor_name → ctor decl, for looking up `num_fields` per rule.
        # For *nested* inductives the recursor's rules may reference
        # ctors of other types woven into the mutual block (e.g.
        # `Lean.Syntax.rec_*` has rules for `Array.mk` and `List.nil`
        # / `List.cons`); fall back to the global env when the ctor
        # isn't one of the immediate inductives'.
        ctor_by_name = name_dict()
        for ctor in all_ctors:
            ctor_by_name[ctor.name] = ctor
        for rule_idx, rule in enumerate(self.rules):
            ctor = ctor_by_name.get(rule.ctor_name, None)
            if ctor is None:
                try:
                    env_decl = get_decl(env.declarations, rule.ctor_name)
                except UnknownDeclaration:
                    env_decl = None
                if env_decl is None or not env_decl.w_kind.is_constructor():
                    return W_InvalidRecursorRule(
                        env,
                        "rule's ctor %s is not a constructor"
                        % rule.ctor_name.str(),
                    )
                ctor = env_decl
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
            # the constructors' source-declaration order. For split
            # mutual / nested recursors (num_motives > 1) the minors
            # are interleaved across the whole block, so `rule_idx`
            # isn't the right global minor offset and this check would
            # false-reject; skip it there.
            if self.num_motives == 1:
                error = self._check_rule_rhs_head(env, rule, rule_idx)
                if error is not None:
                    return error

    def _check_name(self, env, name, first_kind):
        """
        Verify this recursor's name is one the kernel could have
        generated for its inductive block. The kernel constructs
        recursors (names included) from the inductive types alone:
        ``mk_rec_name(member)`` (`<member>.rec`) for each block
        member, plus ``mk_rec_name(all[0]).append_after(k)``
        (`<all[0]>.rec_<k>`) for ``1 <= k <= num_nested`` — the
        auxiliary recursors `mk_aux_rec_name_map` (lean4
        inductive.cpp) renames when restoring eliminated nested
        occurrences. A recursor under any other name — e.g. arena's
        `misnamed_rec.not_rec` — is a declaration the kernel would
        never produce.
        """
        if isinstance(name, StrName):
            suffix = name.suffix
            if suffix == "rec":
                for ind_name in self.all:
                    if name.parent.syntactic_eq(ind_name):
                        return None
            elif (
                suffix.startswith("rec_")
                and len(suffix) <= 13
                and suffix[4] != "0"
                and name.parent.syntactic_eq(self.all[0])
            ):
                k = 0
                for i in range(4, len(suffix)):
                    ch = suffix[i]
                    if ch < "0" or ch > "9":
                        k = 0
                        break
                    k = k * 10 + (ord(ch) - ord("0"))
                if 1 <= k <= first_kind.num_nested:
                    return None
        return W_InvalidRecursorRule(
            env,
            "recursor %s is not a name the kernel generates for %s"
            % (name.str(), self.all[0].str()),
        )

    def _check_type_shape(self, env, type, first_kind):
        """
        Verify this recursor's declared type has the one shape the
        kernel ever generates:

            Π params… motives… minors… indices… (major : I …) ⇒
                motive_i indices… major

        — a syntactic Pi telescope of exactly
        ``num_params + num_motives + num_minors + num_indices`` binders,
        then the major premise, whose domain is headed by an inductive
        constant (a member of ``all``, or the nested container for the
        split recursors of a nested block), with a result headed by one
        of the motive binders.

        Purely structural — binder *types* aren't derived and compared
        here — but it pins the declared type to the recursor telescope,
        so a recursor whose type is an arbitrary proposition (e.g.
        `BogusRecursor.rec : False`) is rejected no matter how
        plausible its counts and rules look: a telescope ending in an
        application of its own motive binder cannot be a closed
        statement.
        """
        t = type
        n = (
            self.num_params
            + self.num_motives
            + self.num_minors
            + self.num_indices
        )
        for _ in range(n):
            if not isinstance(t, W_ForAll):
                return W_InvalidRecursorRule(
                    env,
                    "recursor type has fewer than %d binders "
                    "(expected one each for params, motives, minors "
                    "and indices)" % (n,),
                )
            t = t.body
        if not isinstance(t, W_ForAll):
            return W_InvalidRecursorRule(
                env, "recursor type has no major premise binder",
            )
        major_head = t.binder.type.head()
        if not isinstance(major_head, W_Const):
            return W_InvalidRecursorRule(
                env,
                "recursor major premise is not headed by an inductive",
            )
        if first_kind.num_nested == 0:
            ok = False
            for ind_name in self.all:
                if major_head.name.syntactic_eq(ind_name):
                    ok = True
                    break
            if not ok:
                return W_InvalidRecursorRule(
                    env,
                    "recursor major premise type %s is not one of the "
                    "recursor's inductives" % (major_head.name.str(),),
                )
        else:
            major_decl = find_decl(env.declarations, major_head.name)
            if major_decl is None or not isinstance(
                major_decl.w_kind, W_Inductive,
            ):
                return W_InvalidRecursorRule(
                    env,
                    "recursor major premise type %s is not an inductive"
                    % (major_head.name.str(),),
                )
        result_head = t.body.head()
        # Under params…motives…minors…indices…major, the motive
        # binders sit at de Bruijn indices
        # [num_indices + num_minors + 1, … + num_motives].
        lo = self.num_indices + self.num_minors + 1
        if not isinstance(result_head, W_BVar) or not (
            lo <= result_head.id < lo + self.num_motives
        ):
            return W_InvalidRecursorRule(
                env,
                "recursor result is not an application of a motive",
            )
        return None

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
