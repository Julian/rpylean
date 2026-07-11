from rpython.rlib.jit import (
    JitDriver, dont_look_inside, elidable, promote, unroll_safe,
)
from rpython.rlib.objectmodel import (
    compute_hash, compute_identity_hash, newlist_hint, not_rpython, specialize,
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


def _whnf_printable_location(expr_class):
    """
    Return a human-readable description of the current WHNF trace.

    Called by the JIT to label traces in PYPYLOG output.
    """
    return "whnf: %s" % expr_class.__name__


# JIT driver for the WHNF reduction loop - the core hot path of type checking.
# greens: expr_class determines which reduction rule applies
# reds: the mutable state during reduction
# is_recursive=True: WHNF can re-enter itself via subterm reduction (e.g.
# `W_App._whnf_core` calling `expr.whnf(env)` on the function head, or
# iota reduction going through def_eq → whnf again). Without the hint the
# JIT bails on these mutually-recursive entries before specialising.
whnf_jitdriver = JitDriver(
    greens=["expr_class"],
    reds=["made_progress", "expr", "env"],
    name="whnf",
    get_printable_location=_whnf_printable_location,
    is_recursive=True,
)


# JIT driver for the Nat.succ chain walker. The loop is uniform —
# every iteration unpeels one `Nat.succ` and recurses; the JIT
# specialises on the (empty) green key and inlines the WHNF call.
to_nat_val_jitdriver = JitDriver(
    greens=[],
    reds=["succs", "expr", "env"],
    name="to_nat_val",
    is_recursive=True,
)


def _inst_printable_location(cls):
    return "instantiate: %s" % cls.__name__


# JIT driver for `_instantiate`'s per-kind dispatch (W_App / W_Lambda /
# W_ForAll). Each kind has its own helper (`_inst_app` / `_inst_lambda` /
# `_inst_forall`) that may recurse into `_instantiate` for sub-terms;
# `is_recursive=True` lets the JIT compile per-kind traces that can
# tail-call themselves.
#
# History: a previous driver attached to the older work-stack version
# (5-way polymorphic dispatch) caused a ~25% regression and 79+
# bridges (see `_iter_instantiate`'s docstring). The current direct-
# recursion split is a 3-way dispatch, which should be a friendlier
# trace shape — but worth measuring before assuming it pays off.
inst_jitdriver = JitDriver(
    greens=["cls"],
    reds=["depth", "tc", "cur", "sub"],
    name="instantiate",
    get_printable_location=_inst_printable_location,
    is_recursive=True,
)


def _app_args_printable_location():
    return "app_args"


# JIT driver for `W_App.def_eq`'s args-spine comparison loop. The loop
# body is uniform (`def_eq(self_args[i], other_args[i])`) so greens
# are empty; reds carry the loop index and the two arg lists plus
# the bound `env.def_eq` to call. Each iteration enters the
# `def_eq_jitdriver` via that bound method, so this driver only needs
# to compile the outer loop's dispatch — congruence over deep app
# spines (the `assemble*` family in `init.ndjson` is the motivating
# case) flows through here.
app_args_jitdriver = JitDriver(
    greens=[],
    reds=["i", "self_args", "other_args", "tc"],
    name="app_args",
    get_printable_location=_app_args_printable_location,
)


def get_decl(declarations, name):
    """
    Look up a declaration by name.

    This is a hot path during type checking — called for every constant.
    We promote both arguments here and dispatch to the `@elidable` inner
    so every call site benefits from JIT-time folding, not only the ones
    that happen to promote on their own.
    """
    try:
        return _get_decl(promote(declarations), promote(name))
    except KeyError:
        return _demand_decl(declarations, name)


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

    ``mark`` is the expression (by identity) to locate when building a
    ``Format``; ``found`` records whether the (first) occurrence has been
    wrapped already.  Hash-consing means the same interned sub-expression
    can appear at many syntactic positions, so we wrap only the first one
    seen in source order -- the caret then lands where a reader would look
    for it.  A ``mark`` of ``None`` matches nothing.
    """

    _attrs_ = ['mark', 'found']

    def __init__(self, mark):
        self.mark = mark
        self.found = False


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
    if marker.mark is not None and not marker.found and marker.mark is expr:
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
    # Marked @elidable so the JIT can fold calls to this function at
    # trace-compile time when both arguments are promoted.  This collapses
    # all 14 sequential nat-op comparisons in _try_reduce_nat into constants.
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
#   * W_Lambda / W_ForAll — their binders can't be interned (below), so
#     they only participate in the per-decl arenas (`_mk_w_lambda_in` /
#     `_mk_w_forall_in`).
#   * Binder — `_fvar` is *per-binding-position* mutable state that
#     interning would silently share across distinct positions.


class _ExprCaches(object):
    """
    The mutable inline-cache slots of a `W_App` / `W_FunBase`, hung off
    the node's single `_caches` slot and allocated on the first cache
    write. The overwhelming majority of parsed nodes are never reduced
    — inlining these slots on every node costs multiple words apiece
    across tens of millions of nodes, which is most of the parsed heap.

    `inst_*` is the 1-entry instantiate cache (env-independent);
    `infer_*` / `whnf_*` / `closure_*` are env-tagged (hash-consing
    shares nodes across `Environment`s). `closure_*` is only used by
    `W_FunBase`; `whnf_*` only by `W_App` — sharing one class keeps
    both nodes at a single extra slot without a second allocation path.
    """

    _attrs_ = [
        'inst_expr', 'inst_depth', 'inst_result',
        'infer_env', 'infer_result',
        'whnf_env', 'whnf_result',
        'closure_env', 'closure_result',
    ]

    def __init__(self):
        self.inst_expr = None
        self.inst_depth = -1
        self.inst_result = None
        self.infer_env = None
        self.infer_result = None
        self.whnf_env = None
        self.whnf_result = None
        self.closure_env = None
        self.closure_result = None


class _CacheWriteRegistry(object):
    """
    Every node whose per-instance inline caches were populated since
    the last `reset_decl_caches()` call. The inline caches are keyed
    on per-declaration identities (the `TypeChecker`, a closure env, a
    substitute), so after a decl's check returns they can never hit
    again — but their `*_result` references would pin entire reduction
    towers on nodes that outlive the decl (parsed / interned ones).
    Write sites register the node here on the first write into an
    empty slot; the checker resets every registered node between
    decls.

    The registered nodes live in a rebindable `items` slot (rather
    than a bare module-level list) because RPython's list shrinking
    only decrements the length: the backing array keeps stale
    references in the vacated slots, which would itself pin every
    node ever registered. Dropping the whole list frees the backing
    array too.
    """

    def __init__(self):
        self.items = []


_DECL_CACHE_WRITES = _CacheWriteRegistry()


def _note_cache_write(expr):
    _DECL_CACHE_WRITES.items.append(expr)


def reset_decl_caches():
    """
    Reset the inline caches of every node registered since the last
    call. Called by the checker after each declaration so dead caches
    don't pin that decl's reduction output for the rest of the run.
    """
    items = _DECL_CACHE_WRITES.items
    for i in range(len(items)):
        items[i]._reset_caches()
    _DECL_CACHE_WRITES.items = []


def intern_stats():
    """
    Entry counts of the persistent intern tables, plus the pending
    cache-write registry length, for leak hunting: the tables only
    ever grow, so a count climbing in step with declarations checked
    (rather than with parsing) means reduction products are being
    interned persistently somewhere; the registry should be near zero
    at any declaration boundary — a climbing value means
    `reset_decl_caches` isn't draining it.
    """
    return (
        len(_INTERN_W_APP),
        len(_INTERN_W_PROJ),
        len(_INTERN_W_CONST),
        len(_DECL_CACHE_WRITES.items),
    )


def _mk_str_name(parent, suffix):
    assert isinstance(parent, Name)
    h = _mix2(parent._hash, compute_hash(suffix))
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
    h = _mix2(parent._hash, idx.hash())
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


def _mk_level_succ(parent):
    assert isinstance(parent, W_Level)
    h = _mix1(parent._hash)
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


def _mk_level_max(lhs, rhs):
    assert isinstance(lhs, W_Level)
    assert isinstance(rhs, W_Level)
    h = _mix2(lhs._hash, rhs._hash)
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
    h = _mix2(lhs._hash, rhs._hash)
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
    h = _mix1(name._hash)
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
    h = _mix1(level._hash)
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
    h = name._hash
    for lvl in levels:
        assert isinstance(lvl, W_Level)
        h = (h * 1000003) ^ lvl._hash
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
# W_Lambda / W_ForAll have no *persistent* intern table: their binders
# carry a mutable `_fvar` slot used by `binder.fvar()` to hand out a
# stable FVar for that *binding occurrence*, so binders themselves
# can't be interned (see the comment by `_mk_binder_default`). They DO
# participate in the per-decl arenas (`_mk_w_lambda_in` /
# `_mk_w_forall_in`), keyed on the identity of the binder's components
# and of the body — see `_binder_key_hash` for the key shape and why
# it leaves the `_fvar` sharing story unchanged.

@elidable
def _mk_app(fn, arg):
    """
    Allocate a `W_App(fn, arg)` against the persistent intern table.
    Used at every reduction-time `_mk_app_in` site, so it is on the
    hottest path.
    """
    assert isinstance(fn, W_Expr)
    assert isinstance(arg, W_Expr)
    h = _mix2(fn._hash, arg._hash)
    existing = _INTERN_W_APP.get(h, None)
    if existing is not None and existing.fn is fn and existing.arg is arg:
        return existing
    e = W_App(fn, arg)
    _INTERN_W_APP[h] = e
    return e


@elidable
def _mk_app_in(tc, fn, arg):
    """
    Allocate a `W_App(fn, arg)` for a reduction-time call site,
    against the per-decl arena on `tc`.

    The arena gives us hash-consing across iterations within one
    declaration (so `Nat.brecOn`-style sub-W_Apps reconstructed each
    step are shared and re-hit the WHNF cache) without polluting the
    persistent table — the arena dict is dropped when the TC goes
    out of scope, so reduction-produced W_Apps don't accumulate over
    the run. Mirrors nanoda_lib's two-tier dag scheme
    (`util.rs:218-227`, `alloc_expr` at `util.rs:394`).

    There is deliberately no fallback probe of the persistent
    parse-time table: it serves a 5.7% hit rate against two extra
    dict probes (content-hash) per arena miss — a reduction-built
    node that coincides with a parsed one is simply allocated anew
    and shared via the arena from then on.

    `tc` may also be a bare `Environment` (tests / REPL / cold paths
    outside a check); its `_intern_w_app` slot is `None` and we route
    directly to `_mk_app`. A bare `None` (no env at all) takes the
    same fallback.
    """
    if tc is None:
        return _mk_app(fn, arg)
    arena = tc._intern_w_app
    if arena is None:
        return _mk_app(fn, arg)
    assert isinstance(fn, W_Expr)
    assert isinstance(arg, W_Expr)
    # The arena's equality is identity (`existing.fn is fn`), so its
    # key must mix *identity* hashes, not content hashes: W_Lambda /
    # W_ForAll aren't interned, so big proof terms carry thousands of
    # structurally-equal-but-distinct lambda subtrees — under a
    # content-hash key those all collide into one bucket and every
    # allocation degenerates to a linear scan of it (98% of wall time
    # on Vector.pmap_pmap).
    hi = _mix2(compute_identity_hash(fn), compute_identity_hash(arg))
    existing = arena.get(hi, None)
    if existing is not None and existing.fn is fn and existing.arg is arg:
        tc.tracer.arena_app_hit()
        return existing
    tc.tracer.arena_app_miss()
    e = W_App(fn, arg)
    arena[hi] = e
    return e


def _mk_w_lambda(binder, body):
    return W_Lambda(binder, body)


def _mk_w_forall(binder, body):
    return W_ForAll(binder, body)


def _binder_key_hash(binder, body):
    """
    Arena key for a lambda/forall node: identity of the binder's
    *components* (name, type, style) plus identity of the body — NOT
    identity of the binder object itself. `binder.instantiate` /
    `with_type` allocate a fresh `Binder` whenever the binder type is
    touched by substitution, so a binder-identity key would miss every
    rebuild of such a spine, and each miss mints a fresh `_fvar` for
    what is semantically the same binding occurrence.

    Keying on the components is safe for the `_fvar` slot: each
    distinct key keeps the binder of its first-seen node, so two
    *different* interned lambdas never share a binder object that
    wasn't already shared — the merge only drops never-used duplicate
    binders.
    """
    h = _mix2(
        compute_identity_hash(binder.name),
        compute_identity_hash(binder.type),
    )
    return _mix3(h, compute_hash(binder.left), compute_identity_hash(body))


def _binder_key_eq(existing, binder, body):
    eb = existing.binder
    return (
        existing.body is body
        and eb.name is binder.name
        and eb.type is binder.type
        and eb.left == binder.left
    )


@elidable
def _mk_w_lambda_in(tc, binder, body):
    """
    Allocate a `W_Lambda(binder, body)` for a reduction-time call
    site, against the per-decl arena on `tc`.

    Keyed per `_binder_key_hash` — see also the hash-consing comment
    block above `_mk_app`. Sharing the rebuilt lambda node is what
    lets the identity-keyed inline caches (`_whnf_cache_*`,
    `_infer_cache_*`, `_inst_cache_*`) on the apps *above* it hit:
    without it every instantiation that rebuilds a lambda spine cuts
    the sharing chain and the whole tower re-reduces from scratch.

    There is no persistent fallback — lambdas have no persistent
    intern table.
    """
    if tc is None:
        return W_Lambda(binder, body)
    arena = tc._intern_w_lambda
    if arena is None:
        return W_Lambda(binder, body)
    assert isinstance(binder, Binder)
    assert isinstance(body, W_Expr)
    hi = _binder_key_hash(binder, body)
    existing = arena.get(hi, None)
    if existing is not None and _binder_key_eq(existing, binder, body):
        tc.tracer.arena_lambda_hit()
        return existing
    tc.tracer.arena_lambda_miss()
    e = W_Lambda(binder, body)
    arena[hi] = e
    return e


@elidable
def _mk_w_forall_in(tc, binder, body):
    """
    Reduction-path companion to `_mk_w_forall`. Same per-decl arena
    scheme as `_mk_w_lambda_in`.
    """
    if tc is None:
        return W_ForAll(binder, body)
    arena = tc._intern_w_forall
    if arena is None:
        return W_ForAll(binder, body)
    assert isinstance(binder, Binder)
    assert isinstance(body, W_Expr)
    hi = _binder_key_hash(binder, body)
    existing = arena.get(hi, None)
    if existing is not None and _binder_key_eq(existing, binder, body):
        tc.tracer.arena_forall_hit()
        return existing
    tc.tracer.arena_forall_miss()
    e = W_ForAll(binder, body)
    arena[hi] = e
    return e


@elidable
def _mk_w_proj(struct_name, field_index, struct_expr):
    assert isinstance(struct_name, Name)
    assert isinstance(struct_expr, W_Expr)
    h = _mix3(struct_name._hash, field_index, struct_expr._hash)
    existing = _INTERN_W_PROJ.get(h, None)
    if (existing is not None
            and existing.struct_name is struct_name
            and existing.field_index == field_index
            and existing.struct_expr is struct_expr):
        return existing
    e = W_Proj(struct_name, field_index, struct_expr)
    _INTERN_W_PROJ[h] = e
    return e


@elidable
def _mk_w_proj_in(tc, struct_name, field_index, struct_expr):
    """
    Reduction-path companion to `_mk_w_proj`. Same per-decl arena
    scheme as `_mk_app_in` (and likewise no persistent fallback
    probe).
    """
    if tc is None:
        return _mk_w_proj(struct_name, field_index, struct_expr)
    arena = tc._intern_w_proj
    if arena is None:
        return _mk_w_proj(struct_name, field_index, struct_expr)
    assert isinstance(struct_name, Name)
    assert isinstance(struct_expr, W_Expr)
    # Identity-keyed like `_mk_app_in`'s arena — see the comment there.
    hi = _mix3(
        compute_identity_hash(struct_name),
        field_index,
        compute_identity_hash(struct_expr),
    )
    existing = arena.get(hi, None)
    if (existing is not None
            and existing.struct_name is struct_name
            and existing.field_index == field_index
            and existing.struct_expr is struct_expr):
        tc.tracer.arena_proj_hit()
        return existing
    tc.tracer.arena_proj_miss()
    e = W_Proj(struct_name, field_index, struct_expr)
    arena[hi] = e
    return e


def _mk_w_let(name, type, value, body):
    assert isinstance(name, Name)
    assert isinstance(type, W_Expr)
    assert isinstance(value, W_Expr)
    assert isinstance(body, W_Expr)
    h = _mix4(name._hash, type._hash, value._hash, body._hash)
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

    _attrs_ = ['_level_cache', 'parent', '_hash', 'is_internal', 'is_private']
    _immutable_fields_ = ['parent', '_hash', 'is_internal', 'is_private']

    def __init__(self):
        # Lazy cache for `as_level_param()`; populated on first call.
        # Subclasses set their own `parent` / `_hash` / `is_internal` /
        # `is_private` fields after calling this.
        self._level_cache = None

    @staticmethod
    def simple(part):
        """A name with one (string) part."""
        return Name.ANONYMOUS.child(part)

    @staticmethod
    def from_str(s):
        """Construct a name by splitting a string on ``.`` (all str parts)."""
        name = Name.ANONYMOUS
        for p in s.split("."):
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

    def app_in(self, tc, *args):
        """
        Apply this name to the given argument(s), allocating in tc's arena.
        """
        return self.const().app_in(tc, *args)

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

    def declaration(self, type, w_kind, levels=None, is_unsafe=False):
        """
        Make a declaration with this name.
        """
        return W_Declaration(
            name=self,
            type=type,
            levels=[] if levels is None else levels,
            w_kind=w_kind,
            is_unsafe=is_unsafe,
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

    def definition(self, type, value, hint=1, levels=None, is_unsafe=False):
        """
        Make a definition of the given type and value with this name.
        """
        definition = W_Definition(value=value, hint=hint)
        return self.declaration(type=type, w_kind=definition, levels=levels,
                                is_unsafe=is_unsafe)

    def opaque(self, type, value, levels=None, is_unsafe=False):
        """
        Make an opaque declaration with this name.
        """
        opaque = W_Opaque(value=value)
        return self.declaration(type=type, w_kind=opaque, levels=levels,
                                is_unsafe=is_unsafe)

    def axiom(self, type, levels=None, is_unsafe=False):
        """
        Make an axiom with this name.
        """
        return self.declaration(type=type, w_kind=W_Axiom(), levels=levels,
                                is_unsafe=is_unsafe)

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
        return self.declaration(type=type, w_kind=recursor, levels=levels)

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

    def proj_in(self, tc, field_index, struct_expr):
        """
        Reduction-path `.proj(...)` — allocates a fresh `W_Proj` when
        called with a `tc` instead of hash-consing through the
        persistent intern table.
        """
        return _mk_w_proj_in(tc, self, field_index, struct_expr)

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
            (parent._hash * 1000003) ^ compute_hash(suffix)
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
        self._hash = ((parent._hash * 1000003) ^ h) & 0xFFFFFFFF
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

    _attrs_ = ['name', 'type', 'left', 'right', '_fvar', '_hash']
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
            fvar = W_FVar(self)
            self._fvar = fvar
        return fvar

    def bind_fvar(self, tc, fvar, depth):
        new_type = self.type.bind_fvar(tc, fvar, depth)
        if new_type is self.type:
            return self
        return self.with_type(type=new_type)

    def incr_free_bvars(self, tc, expr, depth):
        if self.type.loose_bvar_range <= depth:
            return self
        return self.with_type(type=self.type.incr_free_bvars(tc, expr, depth))

    def instantiate(self, tc, expr, depth=0):
        if self.type.loose_bvar_range <= depth:
            return self
        return self.with_type(type=self.type.instantiate(tc, expr, depth))

    def subst_levels(self, tc, subts):
        new_type = self.type.subst_levels(tc, subts)
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
            return _mk_binder_default(self.name, type)
        if self.left == "{":
            return _mk_binder_implicit(self.name, type)
        if self.left == "[":
            return _mk_binder_instance(self.name, type)
        return _mk_binder_strict_implicit(self.name, type)


def leq(fn):
    def leq(self, other, balance=0):
        if self is other or syntactic_eq(self, other):
            return balance >= 0
        return fn(self, other, balance)

    return leq


# Based on https://github.com/gebner/trepplein/blob/c704ffe81941779dacf9efa20a75bf22832f98a9/src/main/scala/trepplein/level.scala#L100
class W_Level(_Item):
    _attrs_ = ['_hash']
    _immutable_fields_ = ['_hash']

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
        Two levels are equal via antisymmetry.

        I.e. `a == b` if `a.leq(b)` and `b.leq(a)`.
        """
        return self.leq(other) and other.leq(self)

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
        if isinstance(other, W_LevelIMax):
            if self.leq(other.lhs) or self.leq(other.rhs):
                return other
        elif isinstance(other, W_LevelMax):
            if self.leq(other.lhs) or self.leq(other.rhs):
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
        if isinstance(other, W_LevelSucc):
            return self.max(other)
        if isinstance(other, W_LevelMax) and (
            isinstance(other.lhs, W_LevelSucc) or isinstance(other.rhs, W_LevelSucc)
        ):
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

    def pretty_parts(self):
        return "", 0

    def subst_levels(self, tc, substs):
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

    def pretty_parts(self):
        text, balance = self.parent.pretty_parts()
        return text, balance + 1

    def subst_levels(self, tc, substs):
        new_parent = self.parent.subst_levels(tc, substs)
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

    def subst_levels(self, tc, substs):
        new_lhs = self.lhs.subst_levels(tc, substs)
        new_rhs = self.rhs.subst_levels(tc, substs)
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
        return self.rhs.imax_leq(self, other, balance)

    def gt(self, other, balance):
        return self.rhs.imax_gt(self, other, balance)

    def pretty_parts(self):
        lhs, _ = self.lhs.pretty_parts()
        rhs, _ = self.rhs.pretty_parts()
        return "(imax %s %s)" % (lhs, rhs), 0

    def subst_levels(self, tc, substs):
        new_lhs = self.lhs.subst_levels(tc, substs)
        new_rhs = self.rhs.subst_levels(tc, substs)
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
            return balance >= 0
        if isinstance(other, W_LevelParam):
            return balance >= 0 and syntactic_eq(self.name, other.name)
        return False

    def pretty_parts(self):
        return self.name.str(), 0

    def syntactic_eq(self, other):
        assert isinstance(other, W_LevelParam)
        return syntactic_eq(self.name, other.name)

    def is_named(self, name):
        return self.name.syntactic_eq(name)

    def subst_levels(self, tc, substs):
        return substs.get(self.name, self)

    def imax_leq(self, imax, other, balance):
        """Check imax ≤ other by case-splitting on this param."""
        subst_zero = {self.name: W_LEVEL_ZERO}
        subst_succ = {self.name: self.succ()}
        return (
            imax.subst_levels(None, subst_zero).leq(
                other.subst_levels(None, subst_zero), balance,
            )
            and imax.subst_levels(None, subst_succ).leq(
                other.subst_levels(None, subst_succ), balance,
            )
        )

    def imax_gt(self, imax, other, balance):
        """Check other ≤ imax by case-splitting on this param."""
        subst_zero = {self.name: W_LEVEL_ZERO}
        subst_succ = {self.name: self.succ()}
        return (
            other.subst_levels(None, subst_zero).leq(
                imax.subst_levels(None, subst_zero), balance,
            )
            and other.subst_levels(None, subst_succ).leq(
                imax.subst_levels(None, subst_succ), balance,
            )
        )


class W_Expr(_Item):
    _attrs_ = ['_hash', 'loose_bvar_range', 'has_fvar']
    _immutable_fields_ = ['_hash', 'loose_bvar_range', 'has_fvar']

    @elidable
    def hash(self):
        """
        A content hash. Subclasses set ``self._hash`` eagerly in
        ``__init__``, mixing the hashes of their sub-expressions /
        levels / names — so this is O(1) and JIT-foldable. Used by
        the exporter's content-keyed dedup to match `lean4export`'s
        `HashMap Expr Nat`.
        """
        return self._hash

    def _reset_caches(self):
        """
        Drop every per-instance inline cache on this node.

        The inline caches (`_whnf_cache_*` / `_infer_cache_*` /
        `_delta_cache_*` / `_closure_cache_*` / `_inst_cache_*`) are
        keyed on per-declaration identities — the `TypeChecker`, a
        reduction-produced closure env, or a reduction-produced
        substitute — so once the decl's check returns they can never
        hit again, but the dangling `*_result` references pin whole
        reduction towers on nodes that outlive the decl (parsed /
        interned ones). The `TypeChecker` records every node whose
        caches it populated and resets them here when it's torn down.
        """

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

    def open_all_binders(self, tc):
        """
        Open all leading forall binders, instantiating each with a fresh fvar.

        Returns ``(fvars, body)``.
        """
        fvars = []
        expr = self
        while isinstance(expr, W_ForAll):
            fvar = expr.binder.fvar()
            fvars.append(fvar)
            expr = expr.body.instantiate(tc, fvar, 0)
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

        Allocates against the persistent parser-time intern table; use
        `.app_in(tc, arg)` from reduction paths so the allocation lands
        in the per-decl arena and is reclaimed when the TC ends.
        """
        expr = _mk_app(self, arg)
        if not more:
            return expr
        return expr.app(*more)

    @unroll_safe
    def app_in(self, tc, arg, *more):
        """
        `.app(...)` for a reduction-time call site. With a `tc`,
        allocates a fresh `W_App` (no hash-consing) so the result
        isn't pinned in any intern dict for the lifetime of the
        check. Without a `tc` (parser / test paths), routes to the
        persistent intern table.
        """
        expr = _mk_app_in(tc, self, arg)
        if not more:
            return expr
        return expr.app_in(tc, *more)

    @unroll_safe
    def closure(self, env):
        """
        Wrap this expression in a closure that defers ``env``'s substitution.
        """
        if not env:
            return self
        if self.loose_bvar_range == 0:
            return self
        return W_Closure(env, self)

    def _whnf_under_closure(self, tc, closure_env):
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

        `_whnf_core` steps never delta-reduce; when they bottom out,
        the head constant is unfolded one definition layer here and
        the loop continues — lean4's `whnf` loop over `whnf_core` +
        `unfold_definition` (type_checker.cpp:644).
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
            env.tick_wall_time()
            next = expr._whnf_core(env)
            if next is None:
                # Native nat reduction sits between whnf_core and
                # delta — lean4's whnf loop ordering (whnf_core →
                # reduce_nat → unfold_definition, type_checker.cpp:
                # 644). It must NOT live inside `_whnf_core`: probing
                # a binary nat op WHNFs its arguments, which is full
                # evaluation, and whnf_core callers (def_eq's lazy
                # delta) must never evaluate.
                if isinstance(expr, W_App):
                    next = _try_reduce_nat(expr, env)
                if next is None:
                    next = expr.try_unfold_head(env)
                    if next is None:
                        return (expr, made_progress)
            expr = next
            made_progress = True

    def whnf_core(self, env):
        """
        Reduce to weak head normal form *without* delta-unfolding the
        head: beta / iota / proj / quot / zeta only. Mirrors lean4's
        `whnf_core` (type_checker.cpp:401). Lazy delta uses this
        between single unfold steps so heads can be compared at every
        definition layer.
        """
        expr = self
        while True:
            # A full-WHNF inline cache entry mapping the expr to
            # *itself* means it's in WHNF proper, which is also
            # whnf_core-normal — the common case on def_eq's entry
            # path, where most operands are already normal.
            if isinstance(expr, W_App):
                c = expr._caches
                if (c is not None and c.whnf_env is env
                        and c.whnf_result is expr):
                    return expr
            env.tracer.whnf_step(expr, env.declarations)
            env.tick_wall_time()
            next = expr._whnf_core(env)
            if next is None:
                return expr
            expr = next

    def try_unfold_head(self, env):
        """
        Delta-unfold this expression's head constant by exactly one
        definition layer, re-applying any spine args. Returns ``None``
        when the head isn't an unfoldable constant — lean4's
        `unfold_definition` / `unfold_definition_core`
        (type_checker.cpp:488).
        """
        head, args = self.unapp()
        if not isinstance(head, W_Const):
            return None
        if find_decl(env.declarations, head.name) is None:
            return None
        val = head.try_delta_reduce(env)
        if val is None:
            return None
        result = val
        i = len(args) - 1
        while i >= 0:
            result = result.app_in(env, args[i])
            i -= 1
        return result

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
        self.loose_bvar_range = id + 1
        self.has_fvar = False
        self._hash = ((id * 1000003) ^ 0xB7A8) & 0xFFFFFFFF

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

    def bind_fvar(self, tc, fvar, depth):
        return self

    def instantiate(self, tc, expr, depth=0):
        if self.id == depth:
            incr = expr.incr_free_bvars(tc, depth, 0)
            return incr
        elif self.id > depth:
            # This variable is not bound here (e.g. 'fun x => BVar(1)')
            # Instantiation has removed the outermost binder, so we need to decrement this
            # TODO - should we take in a context instead of relying on 'bvar.id'?
            return _mk_w_bvar(self.id - 1)
        return self

    def incr_free_bvars(self, tc, count, depth):
        if self.id >= depth:
            return _mk_w_bvar(self.id + count)
        return self

    def subst_levels(self, tc, substs):
        return self

    @unroll_safe
    def closure(self, env):
        if not env:
            return self
        if self.id < len(env):
            return env[self.id]
        return _mk_w_bvar(self.id - len(env))

    def _whnf_under_closure(self, tc, closure_env):
        if self.id < len(closure_env):
            return closure_env[self.id]
        return _mk_w_bvar(self.id - len(closure_env))


class W_FVar(W_Expr):
    """An FVar which refers to its binder by identity."""

    _attrs_ = ['id', 'binder']
    _immutable_fields_ = ['id', 'binder']

    _counter = count()

    def __init__(self, binder):
        self.id = next(self._counter)
        assert isinstance(binder, Binder)
        self.binder = binder
        self.loose_bvar_range = 0
        self.has_fvar = True
        # FVars are unique by id, so hashing on id alone is fine.
        self._hash = ((self.id * 1000003) ^ 0xF7A8) & 0xFFFFFFFF

    def __repr__(self):
        return "<FVar id={} binder={!r}>".format(self.id, self.binder)

    def def_eq(self, other, tc):
        assert isinstance(other, W_FVar)
        return self.id == other.id

    def str(self):
        return self.binder.name.user_name().str()

    def to_format(self, constants, marker):
        return _format.text(BINDER_NAME, self.str())

    def incr_free_bvars(self, tc, count, depth):
        return self

    def instantiate(self, tc, expr, depth=0):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_FVar)
        return self.id == other.id and syntactic_eq(self.binder, other.binder)

    def infer(self, env):
        """
        A free variable's type comes from the binder's type which it replaced.
        """
        return self.binder.type

    def bind_fvar(self, tc, fvar, depth):
        if self.id == fvar.id:
            return _mk_w_bvar(depth)
        return self


class W_LitStr(W_Expr):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        assert isinstance(val, str)
        self.val = val
        self.loose_bvar_range = 0
        self.has_fvar = False
        self._hash = ((compute_hash(val) * 1000003) ^ 0x57A5) & 0xFFFFFFFF

    def __repr__(self):
        return repr(self.val)

    def emit_to(self, exporter):
        eid = exporter.next_expr_id()
        exporter.stream.write(
            '{"ie":%d,"strVal":%s}\n' % (eid, exporter.quote(self.val)),
        )
        return eid

    def def_eq(self, other, tc):
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

    def to_format(self, constants, marker):
        """A ``Format`` tagging this string literal."""
        return _format.text(LITERAL, self.str())

    def build_str_expr(self, env):
        if len(self.val) > 5:
            print("Building large str expr for %s" % self.val[:10])
        Char = Name.simple("Char").const()
        cons = Name.from_str("List.cons").const([W_LEVEL_ZERO]).app_in(env, Char)
        expr = Name.from_str("List.nil").const([W_LEVEL_ZERO]).app_in(env, Char)
        for i in range(len(self.val) - 1, -1, -1):
            char_expr = Name.from_str("Char.ofNat").app_in(env, W_LitNat.char(self.val[i]))
            expr = cons.app_in(env, char_expr).app_in(env, expr)
        return Name.from_str("String.ofList").app_in(env, expr)

    def infer(self, env):
        """
        String literals infer as the constant named String.
        """
        return STRING

    def instantiate(self, tc, expr, depth=0):
        return self

    def subst_levels(self, tc, substs):
        return self

    def bind_fvar(self, tc, fvar, depth):
        return self

    def incr_free_bvars(self, tc, count, depth):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitStr)
        return self.val == other.val


class W_Sort(W_Expr):
    _attrs_ = ['level']
    _immutable_fields_ = ['level']

    def __init__(self, level):
        self.level = level
        self.loose_bvar_range = 0
        self.has_fvar = False
        self._hash = ((level.hash() * 1000003) ^ 0x5071) & 0xFFFFFFFF

    def __repr__(self):
        # No class name here, as we wouldn't want to see <Sort Type>
        return "<%s>" % (self.str(),)

    def def_eq(self, other, tc):
        assert isinstance(other, W_Sort)
        return self.level.eq(other.level)

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

    def incr_free_bvars(self, tc, count, depth):
        return self

    def bind_fvar(self, tc, fvar, depth):
        return self

    def instantiate(self, tc, expr, depth=0):
        return self

    def infer(self, env):
        return self.level.succ().sort()

    def expect_sort(self, env):
        return self.level

    def subst_levels(self, tc, substs):
        new_level = self.level.subst_levels(tc, substs)
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
    return target.subst_levels(env, substs)


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
        self.loose_bvar_range = 0
        self.has_fvar = False
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
        self._hash = ((h * 1000003) ^ 0xC057) & 0xFFFFFFFF

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

    def def_eq(self, other, tc):
        assert isinstance(other, W_Const)
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

    def bind_fvar(self, tc, fvar, depth):
        return self

    def instantiate(self, tc, expr, depth=0):
        return self

    def incr_free_bvars(self, tc, count, depth):
        return self

    def _whnf_core(self, env):
        # No delta here: `_whnf_core` is beta / iota / proj / quot /
        # zeta only, mirroring lean4's `whnf_core`
        # (type_checker.cpp:401). Delta-unfolding the head is the
        # *outer* `whnf` loop's job (one layer per iteration, via
        # `try_unfold_head`), so that `whnf_core`-level callers —
        # lazy delta in particular — can compare heads after each
        # definition layer instead of bulldozing to a normal form.
        return None

    def try_delta_reduce(self, env, only_abbrev=False):
        # Promote for the same reason as _whnf_core: lets the JIT fold
        # get_decl (and the second call inside apply_const_level_params)
        # to compile-time constants when this constant is hot.
        name = promote(self.name)
        declarations = promote(env.declarations)
        decl = get_decl(declarations, name)
        # TODO - use hint to decide whether to delta reduce or not
        val = decl.w_kind.get_delta_reduce_target()
        if not isinstance(decl.w_kind, W_Definition):
            return None

        if val is None:
            return None

        env.tracer.delta(name)
        if self._delta_cache_env is env:
            return self._delta_cache_result
        result = apply_const_level_params(self, val, env)
        if self._delta_cache_env is None:
            _note_cache_write(self)
        self._delta_cache_env = env
        self._delta_cache_result = result
        return result

    def infer(self, env):
        if self._infer_cache_env is env:
            return self._infer_cache_result
        decl = get_decl(env.declarations, self.name)
        params = decl.levels
        if not params:
            result = decl.type
        else:
            result = apply_const_level_params(self, decl.type, env)
        if self._infer_cache_env is None:
            _note_cache_write(self)
        self._infer_cache_env = env
        self._infer_cache_result = result
        return result

    def _reset_caches(self):
        self._infer_cache_env = None
        self._infer_cache_result = None
        self._delta_cache_env = None
        self._delta_cache_result = None

    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    @unroll_safe
    def subst_levels(self, tc, substs):
        levels = self.levels
        if not levels:
            return self
        new_levels = None
        for i in range(len(levels)):
            new_level = levels[i].subst_levels(tc, substs)
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


def _to_nat_val(expr, env):
    """
    If expr (already WHNF'd) is a nat literal, Nat.zero, or a chain of
    Nat.succ applications on a nat value, return its rbigint value.
    Otherwise return None.

    Iterative to avoid stack overflow on large Nat.succ chains.
    """
    succs = 0
    while True:
        to_nat_val_jitdriver.jit_merge_point(
            succs=succs, expr=expr, env=env,
        )
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


def _is_nat_zero_const(expr):
    """
    Whether ``expr`` is the syntactic form of ``Nat.zero``: either the
    ``Nat.zero`` constant or a ``W_LitNat`` with value zero.

    Caller is responsible for any needed WHNF; this never reduces.
    """
    if isinstance(expr, W_LitNat):
        return expr.val.eq(rbigint.fromint(0))
    if isinstance(expr, W_Const):
        return expr.name.syntactic_eq(NAT_ZERO.name)
    return False


def _nat_succ_pred(expr):
    """
    If ``expr`` is the syntactic form of ``Nat.succ pred``, return
    ``pred``; otherwise return None.

    Caller is responsible for any needed WHNF.
    """
    if isinstance(expr, W_LitNat):
        if not expr.val.eq(rbigint.fromint(0)):
            return _mk_w_litnat(expr.val.sub(rbigint.fromint(1)))
        return None
    if isinstance(expr, W_App):
        head = expr.fn
        if isinstance(head, W_Const) and head.name.syntactic_eq(
            _NAT_SUCC_NAME,
        ):
            return expr.arg
    return None


class W_LitNat(W_Expr):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        self.val = val
        self.loose_bvar_range = 0
        self.has_fvar = False
        self._hash = ((val.hash() * 1000003) ^ 0x4A75) & 0xFFFFFFFF

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

    def def_eq(self, other, tc):
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

    def to_format(self, constants, marker):
        """A ``Format`` tagging this nat literal."""
        return _format.text(LITERAL, self.str())

    def instantiate(self, tc, expr, depth=0):
        return self

    def subst_levels(self, tc, substs):
        return self

    def syntactic_eq(self, other):
        assert isinstance(other, W_LitNat)
        return self.val.eq(other.val)

    def one_step_constructor(self, tc):
        """
        Expose one Nat constructor: ``Nat.zero`` if the value is zero,
        otherwise ``Nat.succ (W_LitNat (val - 1))``.

        Used by iota reduction so the inductive step sees a concrete
        constructor without materialising the full Nat.succ chain.
        """
        if self.val.eq(rbigint.fromint(0)):
            return NAT_ZERO
        return NAT_SUCC.app_in(tc, _mk_w_litnat(self.val.sub(rbigint.fromint(1))))

    def bind_fvar(self, tc, fvar, depth):
        return self

    def incr_free_bvars(self, tc, count, depth):
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
        # which would then need re-expanding in iota reduction.
        return None

    if nargs != 2:
        return None

    result = _dispatch_nat_op(name, args, env)
    if result is not None:
        env.tracer.nat_reduce(name)
    return result


def _dispatch_nat_op(name, args, env):
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
    return _mk_w_litnat(v1.add(v2))


def _reduce_bin_nat_op_sub(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v1.lt(v2):
        return _mk_w_litnat(rbigint.fromint(0))
    return _mk_w_litnat(v1.sub(v2))


def _reduce_bin_nat_op_mul(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return _mk_w_litnat(v1.mul(v2))


def _reduce_nat_pow(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v2.gt(_REDUCE_POW_MAX_EXP):
        return None
    return _mk_w_litnat(v1.pow(v2))


def _reduce_bin_nat_op_gcd(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return _mk_w_litnat(v1.gcd(v2))


def _reduce_bin_nat_op_mod(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v2.eq(rbigint.fromint(0)):
        return _mk_w_litnat(v1)
    return _mk_w_litnat(v1.mod(v2))


def _reduce_bin_nat_op_div(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    if v2.eq(rbigint.fromint(0)):
        return _mk_w_litnat(rbigint.fromint(0))
    return _mk_w_litnat(v1.div(v2))


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
    return _mk_w_litnat(v1.and_(v2))


def _reduce_bin_nat_op_lor(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return _mk_w_litnat(v1.or_(v2))


def _reduce_bin_nat_op_xor(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return _mk_w_litnat(v1.xor(v2))


def _reduce_bin_nat_op_shiftleft(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return _mk_w_litnat(v1.lshift(v2.toint()))


def _reduce_bin_nat_op_shiftright(args, env):
    v1, v2 = _get_bin_nat_args(args, env)
    if v1 is None:
        return None
    return _mk_w_litnat(v1.rshift(v2.toint()))


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
        self.loose_bvar_range = struct_expr.loose_bvar_range
        self.has_fvar = struct_expr.has_fvar
        h = (struct_name.hash() * 1000003) ^ field_index
        h = (h * 1000003) ^ struct_expr.hash()
        self._hash = ((h * 1000003) ^ 0x9709) & 0xFFFFFFFF

    def _reset_caches(self):
        self._struct_whnf_env = None
        self._struct_whnf = None

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

    def def_eq(self, other, tc):
        assert isinstance(other, W_Proj)
        return (
            self.struct_name.syntactic_eq(other.struct_name)
            and self.field_index == other.field_index
            and tc.def_eq(self.struct_expr, other.struct_expr)
        )

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

    def _whnf_core(self, env):
        if self._struct_whnf_env is env:
            reduced_struct = self._struct_whnf
        else:
            reduced_struct = self.struct_expr.whnf(env)
            # String literals carry their constructor form implicitly.
            # To project a field out of one, materialize the constructor
            # app and whnf again so the field-extract below sees the
            # spine.
            if isinstance(reduced_struct, W_LitStr):
                reduced_struct = reduced_struct.build_str_expr(env).whnf(env)
            if self._struct_whnf_env is None:
                _note_cache_write(self)
            self._struct_whnf_env = env
            self._struct_whnf = reduced_struct

        # Try to perform projection reduction (structural iota reduction).
        # If the struct expression reduces to a constructor application,
        # extract the field at the appropriate index.
        head, ctor_args = reduced_struct.unapp()

        if isinstance(head, W_Const):
            decl = get_decl(env.declarations, head.name)
            kind = decl.w_kind
            if isinstance(kind, W_Constructor):
                ctor_args.reverse()
                # Constructor args = params ++ fields
                # The field we want is at index num_params + field_index
                idx = kind.num_params + self.field_index
                if idx < len(ctor_args):
                    return ctor_args[idx]

        return None

    def incr_free_bvars(self, tc, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return self.with_expr(tc, self.struct_expr.incr_free_bvars(tc, count, depth))

    def bind_fvar(self, tc, fvar, depth):
        new_expr = self.struct_expr.bind_fvar(tc, fvar, depth)
        if new_expr is self.struct_expr:
            return self
        return self.with_expr(tc, new_expr)

    def instantiate(self, tc, expr, depth=0):
        if self.loose_bvar_range <= depth:
            return self
        return self.with_expr(tc, self.struct_expr.instantiate(tc, expr, depth))

    def subst_levels(self, tc, substs):
        new_expr = self.struct_expr.subst_levels(tc, substs)
        if new_expr is self.struct_expr:
            return self
        return self.with_expr(tc, new_expr)

    def with_expr(self, tc, expr):
        return self.struct_name.proj_in(tc, self.field_index, expr)

    def _whnf_under_closure(self, tc, closure_env):
        return self.with_expr(tc, self.struct_expr.closure(closure_env))

    def syntactic_eq(self, other):
        assert isinstance(other, W_Proj)
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
        except UnknownDeclaration:
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
        struct_kind = struct_type.w_kind
        assert isinstance(struct_kind, W_Inductive)
        if len(struct_kind.ctor_names) != 1:
            raise InvalidProjection.not_a_structure(
                self.struct_name, self.field_index,
                len(struct_kind.ctor_names), self.struct_expr,
            )

        ind_type_whnf = apply_const_level_params(
            struct_expr_type, struct_type.type, env
        ).whnf(env)
        is_prop_type = isinstance(ind_type_whnf, W_Sort) and ind_type_whnf.level.eq(
            W_LEVEL_ZERO
        )

        ctor_decl = struct_kind.constructor_decls(env.declarations)[0]
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
            new_type = ctor_type.body.instantiate(env, app.arg)
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
                proj = self.struct_name.proj_in(env, i, self.struct_expr)
                ctor_type = ctor_type.body.instantiate(env, proj)
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
            stack.append(current.body.instantiate(None, current.binder.fvar()))
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
                            val = val.subst_levels(None, substs)
                        # Beta-reduce by applying each arg to the lambda body.
                        for arg in args:
                            if isinstance(val, W_Lambda):
                                val = val.body.instantiate(None, arg)
                            else:
                                break
                        stack.append(val)
                    else:
                        # Axiom or other non-definition: use type-level reasoning.
                        # The return type after applying all args tells us the sort.
                        decl_type = decl.type
                        for arg in args:
                            if isinstance(decl_type, W_ForAll):
                                decl_type = decl_type.body.instantiate(None, arg)
                            else:
                                break
                        stack.append(decl_type)
    return False


# Used to abstract over W_ForAll and W_Lambda (which are often handled the same way)
class W_FunBase(W_Expr):
    _attrs_ = ['binder', 'body', 'finished_reduce', '_caches']
    _immutable_fields_ = ['binder', 'body']

    # Subclasses set this to a distinct tag so structurally-equal
    # lambdas and foralls don't collide in the content hash.
    _hash_tag = 0

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
        self.has_fvar = binder.type.has_fvar or body.has_fvar
        # Instantiate / infer / closure caches, allocated on first
        # write — see `_ExprCaches`. The closure cache is critical for
        # DAG-shared lambdas: when ``λ`` appears N times under the
        # same env (e.g. wrap2 lam lam) all N calls return the same
        # ``W_Closure``, preserving the inferred-type cache across
        # references and avoiding exponential blowup.
        self._caches = None
        # Content hash: mix binder's name + type + binder-info + body.
        h = (binder.name.hash() * 1000003) ^ binder.type.hash()
        h = (h * 1000003) ^ body.hash()
        self._hash = ((h * 1000003) ^ self._hash_tag) & 0xFFFFFFFF

    def _ensure_caches(self):
        c = self._caches
        if c is None:
            c = _ExprCaches()
            self._caches = c
        return c

    @unroll_safe
    def closure(self, env):
        if not env:
            return self
        if self.loose_bvar_range == 0:
            return self
        c = self._caches
        if c is not None and c.closure_env is env:
            return c.closure_result
        result = W_Closure(env, self)
        c = self._ensure_caches()
        if c.closure_env is None:
            _note_cache_write(self)
        c.closure_env = env
        c.closure_result = result
        return result

    def _reset_caches(self):
        self._caches = None

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
        return self.body.instantiate(env, self.binder.fvar()).whnf(env).is_strictly_positive(
            inductive, env,
        )

    def def_eq(self, other, tc):
        """
        Compare binders and bodies without regard for bound variable names.

        (This is alpha equivalence.)
        """
        assert isinstance(other, W_FunBase)
        if not tc.def_eq(self.binder.type, other.binder.type):
            return False

        fvar = self.binder.fvar()
        body = self.body.instantiate(tc, fvar)
        other_body = other.body.instantiate(tc, fvar)

        return tc.def_eq(body, other_body)

    def _whnf_under_closure(self, tc, closure_env):
        # Closure-of-lambda (or -ForAll) is itself a value in WHNF.
        return None


class W_ForAll(W_FunBase):
    _attrs_ = []

    _export_tag = "forallE"
    _ie_first_tag = False  # `'f' < 'i'`
    _hash_tag = 0xF0A1

    def infer(self, env):
        return _iter_infer(env, self)

    def _infer_recursive(self, env):
        binder_sort = self.binder.type.infer(env).whnf(env).expect_sort(env)
        body_sort = (
            self.body.instantiate(env, self.binder.fvar())
            .infer(env)
            .whnf(env)
            .expect_sort(env)
        )
        return binder_sort.imax(body_sort).sort()

    def expect_sort(self, env):
        return self.infer(env).whnf(env).expect_sort(env)

    def instantiate(self, tc, expr, depth=0):
        return _iter_instantiate(tc, self, expr, depth)

    def syntactic_eq(self, other):
        assert isinstance(other, W_ForAll)
        return syntactic_eq(self.binder, other.binder) and syntactic_eq(
            self.body, other.body
        )

    def bind_fvar(self, tc, fvar, depth):
        new_binder = self.binder.bind_fvar(tc, fvar, depth)
        new_body = self.body.bind_fvar(tc, fvar, depth + 1)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_forall_in(tc, new_binder, new_body)

    def incr_free_bvars(self, tc, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return _mk_w_forall_in(
            tc,
            self.binder.incr_free_bvars(tc, count, depth),
            self.body.incr_free_bvars(tc, count, depth + 1),
        )

    def subst_levels(self, tc, levels):
        new_binder = self.binder.subst_levels(tc, levels)
        new_body = self.body.subst_levels(tc, levels)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_forall_in(tc, new_binder, new_body)

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
            if self.binder.is_default() and not self.body.loose_bvar_range > 0:
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
                and not self.body.loose_bvar_range > 0
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
    rhs = fa.body.instantiate(None, fa.binder.fvar())
    is_forall = (
        (not _is_prop_type(lhs_type, constants)
         and _is_prop_type(rhs, constants))
        or (fa.body.loose_bvar_range > 0 and _is_prop_type(rhs, constants))
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
            binder_used.append(current.body.loose_bvar_range > 0)
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
            body = body.instantiate(None, binder.fvar())

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

    def bind_fvar(self, tc, fvar, depth):
        new_binder = self.binder.bind_fvar(tc, fvar, depth)
        new_body = self.body.bind_fvar(tc, fvar, depth + 1)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_lambda_in(tc, new_binder, new_body)

    def instantiate(self, tc, expr, depth=0):
        return _iter_instantiate(tc, self, expr, depth)

    def incr_free_bvars(self, tc, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return _mk_w_lambda_in(
            tc,
            self.binder.incr_free_bvars(tc, count, depth),
            self.body.incr_free_bvars(tc, count, depth + 1),
        )

    def infer(self, env):
        return _iter_infer(env, self)

    def subst_levels(self, tc, substs):
        new_binder = self.binder.subst_levels(tc, substs)
        new_body = self.body.subst_levels(tc, substs)
        if new_binder is self.binder and new_body is self.body:
            return self
        return _mk_w_lambda_in(tc, new_binder, new_body)


class W_Let(W_Expr):
    _attrs_ = ['name', 'type', 'value', 'body']
    _immutable_fields_ = ['name', 'type', 'value', 'body']

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
        self.has_fvar = type.has_fvar or value.has_fvar or body.has_fvar
        h = (name.hash() * 1000003) ^ type.hash()
        h = (h * 1000003) ^ value.hash()
        h = (h * 1000003) ^ body.hash()
        self._hash = ((h * 1000003) ^ 0x1ED7) & 0xFFFFFFFF

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
        body = self.body.instantiate(None, fvar)
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
        body_type = self.body.instantiate(env, self.value)
        return body_type.infer(env)

    def instantiate(self, tc, expr, depth=0):
        if self.loose_bvar_range <= depth:
            return self
        return self.name.let(
            type=self.type.instantiate(tc, expr, depth),
            value=self.value.instantiate(tc, expr, depth),
            body=self.body.instantiate(tc, expr, depth + 1),
        )

    def incr_free_bvars(self, tc, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return self.name.let(
            type=self.type.incr_free_bvars(tc, count, depth),
            value=self.value.incr_free_bvars(tc, count, depth),
            body=self.body.incr_free_bvars(tc, count, depth + 1),
        )

    def bind_fvar(self, tc, fvar, depth):
        new_type = self.type.bind_fvar(tc, fvar, depth)
        new_value = self.value.bind_fvar(tc, fvar, depth)
        new_body = self.body.bind_fvar(tc, fvar, depth + 1)
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

    def _whnf_core(self, env):
        return self.body.instantiate(env, self.value)

    def subst_levels(self, tc, substs):
        new_type = self.type.subst_levels(tc, substs)
        new_value = self.value.subst_levels(tc, substs)
        new_body = self.body.subst_levels(tc, substs)
        if (new_type is self.type
                and new_value is self.value
                and new_body is self.body):
            return self
        return self.name.let(
            type=new_type, value=new_value, body=new_body,
        )

    def _whnf_under_closure(self, tc, closure_env):
        # let x := val in body  ⇒  body[x ↦ val], all under closure_env.
        return self.body.closure([self.value]).closure(closure_env)


class W_App(W_Expr):
    _attrs_ = ['fn', 'arg', '_caches']
    _immutable_fields_ = ['fn', 'arg']

    def __init__(self, fn, arg):
        self.fn = fn
        self.arg = arg
        fn_range = fn.loose_bvar_range
        arg_range = arg.loose_bvar_range
        if fn_range > arg_range:
            self.loose_bvar_range = fn_range
        else:
            self.loose_bvar_range = arg_range
        self.has_fvar = fn.has_fvar or arg.has_fvar
        # Instantiate / infer / whnf caches, allocated on first write —
        # see `_ExprCaches`.
        self._caches = None
        h = (fn.hash() * 1000003) ^ arg.hash()
        self._hash = ((h * 1000003) ^ 0xAB30) & 0xFFFFFFFF

    def _ensure_caches(self):
        c = self._caches
        if c is None:
            c = _ExprCaches()
            self._caches = c
        return c

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

    def def_eq(self, other, tc):
        assert isinstance(other, W_App)
        self_fn = self.fn
        if isinstance(self_fn, W_Closure):
            self_fn_body = self_fn.body
            if isinstance(self_fn_body, W_Lambda):
                new_env = [self.arg] + list(self_fn.env)
                if tc.def_eq(self_fn_body.body.closure(new_env), other):
                    return True
        elif isinstance(self_fn, W_FunBase):
            if tc.def_eq(self_fn.body.instantiate(tc, self.arg), other):
                return True
        other_fn = other.fn
        if isinstance(other_fn, W_Closure):
            other_fn_body = other_fn.body
            if isinstance(other_fn_body, W_Lambda):
                new_env = [other.arg] + list(other_fn.env)
                if tc.def_eq(self, other_fn_body.body.closure(new_env)):
                    return True
        elif isinstance(other_fn, W_FunBase):
            if tc.def_eq(self, other_fn.body.instantiate(tc, other.arg)):
                return True
        # Iterative spine walk to avoid stack overflow on deep W_App trees.
        # Collect args from both sides while both fns are W_App, then
        # compare heads and args pairwise via def_eq.
        self_args = newlist_hint(4)
        other_args = newlist_hint(4)
        lhs = self
        rhs = other
        while isinstance(lhs, W_App) and isinstance(rhs, W_App):
            self_args.append(lhs.arg)
            other_args.append(rhs.arg)
            lhs = lhs.fn
            rhs = rhs.fn
        if not tc.def_eq(lhs, rhs):
            return False
        if len(self_args) != len(other_args):
            return False
        i = len(self_args) - 1
        while i >= 0:
            app_args_jitdriver.jit_merge_point(
                i=i,
                self_args=self_args,
                other_args=other_args,
                tc=tc,
            )
            if not tc.def_eq(self_args[i], other_args[i]):
                return False
            i -= 1
        return True

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
                    decl_type = decl_type.subst_levels(None, substs)
                for j in range(n - 1, -1, -1):
                    if isinstance(decl_type, W_ForAll):
                        mask.append(decl_type.binder.is_default())
                        decl_type = decl_type.body.instantiate(None, args[j])
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

    def infer(self, env):
        return _iter_infer(env, self)

    def whnf(self, env):
        c = self._caches
        if c is not None and c.whnf_env is env:
            env.tracer.whnf_cache_hit()
            return c.whnf_result
        env.tracer.whnf_cache_miss()
        (expr, _progress) = self.whnf_with_progress(env)
        c = self._ensure_caches()
        if c.whnf_env is None:
            _note_cache_write(self)
        c.whnf_env = env
        c.whnf_result = expr
        return expr

    def _reset_caches(self):
        self._caches = None

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
        return f.app_in(env, a)

    def _whnf_core_no_iota(self, env):
        """W_App._whnf_core minus the iota/struct-eta/quot-lift steps.

        Used inside the iterative iota driver to drive WHNF of a major
        premise without triggering recursive `try_iota_reduce` calls.
        """
        fn_next = self.fn._whnf_core(env)
        if fn_next is not None:
            return fn_next.app_in(env, self.arg)
        fn = self.fn
        if isinstance(fn, W_Closure):
            inner = fn.body
            if isinstance(inner, W_Lambda):
                new_env = [self.arg] + list(fn.env)
                env.tracer.beta()
                return inner.body.closure(new_env)
            fn = fn.force(env)
        if isinstance(fn, W_FunBase):
            env.tracer.beta()
            return fn.body.instantiate(env, self.arg)
        return None

    def try_iota_reduce(self, env):
        target, args = self.unapp()

        if not isinstance(target, W_Const):
            return False, self

        decl = get_decl(env.declarations, target.name)
        rec_kind = decl.w_kind
        if not isinstance(rec_kind, W_Recursor):
            return False, self

        skip_count = (
            rec_kind.num_params
            + rec_kind.num_indices
            + rec_kind.num_minors
            + rec_kind.num_motives
        )
        major_idx = len(args) - 1 - skip_count

        # Not enough arguments in our current app - we cannot reduce, since we need to know the major premise
        # to pick the recursor rule to apply
        if major_idx < 0:
            return False, self

        # Fast path: `Nat.rec motive zero succ (W_LitNat N)`. The
        # standard iota path applies `rec_rule.rhs` to four args
        # (motive, zero, succ, pred) and lets the outer whnf loop
        # beta away the four-lambda rule body — four betas per step.
        # We construct the same one-step iota result directly here,
        # skipping those four betas. The chain stays lazy: consumers
        # only descend as far as they need, and each successive step
        # also hits this path. On `Nat.brecOn`-shaped recursions in
        # init.ndjson the rule-unwrap betas account for ~22% of all
        # betas in the workload.
        nat_rec_step = self._maybe_iota_nat_rec_step(
            env, target, args, major_idx,
        )
        if nat_rec_step is not None:
            env.tracer.iota(target.name)
            return True, nat_rec_step

        major_premise = _whnf_iota_chain(env, args[major_idx])

        # TODO - when checking the declaration, verify that all of the requirements for k-like reduction
        # are met: https://ammkrn.github.io/type_checking_in_lean4/type_checking/reduction.html?highlight=k-li#k-like-reduction
        if rec_kind.k == 1:
            # Verify that our major premise type is correct (by checking the whole expression)
            # before we get rid of it
            self.infer(env)

            # Full whnf, not just `.head()`: the major is typically an
            # opened binder's fvar whose type may sit under a closure
            # or behind a definition unfolding to the inductive —
            # lean4's to_cnstr_when_K does `whnf(infer_type(e))`.
            old_ty = major_premise.infer(env).whnf(env)
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
                env.tracer.klike_bail_head()
                return False, self

            # Mutual-inductive blocks legitimately have `len(all) > 1`;
            # k-like reduction can only operate on a single-inductive
            # context. Same bail-out reasoning.
            if len(rec_kind.all) != 1:
                env.tracer.klike_bail_mutual()
                return False, self
            inductive_decl = get_decl(env.declarations, rec_kind.all[0])
            ind_kind = inductive_decl.w_kind
            assert isinstance(ind_kind, W_Inductive)

            # K-like reduction only makes sense for a single-ctor
            # inductive.
            if len(ind_kind.ctor_names) != 1:
                env.tracer.klike_bail_ctors()
                return False, self
            ctor_decl = ind_kind.constructor_decls(env.declarations)[0]
            ctor_kind = ctor_decl.w_kind
            assert isinstance(ctor_kind, W_Constructor)

            new_args = list(args)
            new_args.reverse()
            num_ctor_params = ctor_kind.num_params

            major_premise_ctor = ctor_decl.name.const(old_ty_base.levels)
            assert num_ctor_params >= 0
            for arg in new_args[0:num_ctor_params]:
                major_premise_ctor = major_premise_ctor.app_in(env, arg)

            new_ty = major_premise_ctor.infer(env)
            if not env.def_eq(old_ty, new_ty):
                env.tracer.klike_bail_defeq()
                return False, self
            env.tracer.klike_fired()
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
            major_premise = major_premise.one_step_constructor(env)
        else:
            # A stuck major of non-recursive-structure type reduces by
            # eta-expanding it to `C.mk params… major.0 … major.n`
            # first, so the ctor's rule can fire — lean4's
            # `to_cnstr_when_structure` (inductive.h), applied to the
            # recursor's *major* inductive (`get_major_induct`), which
            # for the split recursors of a nested block differs from
            # `all[0]` (e.g. `CedarType.rec_1`'s major is a
            # `Cedar.Data.Map`, whose single `Map.mk` rule fires).
            expanded = self._to_cnstr_when_structure(
                env, decl.type, rec_kind, major_premise,
            )
            if expanded is not None:
                major_premise = expanded

        # If the inductive type has parameters, we need to extract them from the major premise
        # (e.g. the 'p' in 'Decidable.isFalse p')
        # and add then as arguments to the recursor rule application (before the motive)
        major_premise_ctor, all_ctor_args = major_premise.unapp()

        if not isinstance(major_premise_ctor, W_Const):
            return False, self

        all_ctor_args.reverse()
        rec_rule = rec_kind.rule_for_ctor(major_premise_ctor.name)
        if rec_rule is not None:
            # Construct an application of the recursor rule, using all
            # of the parameters except the major premise (which is
            # implied by the rule we matched for the ctor — e.g.
            # `Bool.false`).
            new_app = rec_rule.rhs
            # The rec rule's value uses the inductive's level
            # parameters, so substitute the recursor call's levels in.
            new_app = apply_const_level_params(target, new_app, env)

            new_args = list(args)
            new_args.reverse()

            total_args = (
                rec_kind.num_params
                + rec_kind.num_motives
                + rec_kind.num_minors
            )
            assert total_args >= 0
            for arg in new_args[:total_args]:
                new_app = new_app.app_in(env, arg)

            # For nested-inductive recursors the ctor whose iota we're
            # firing can belong to a *different* inductive than the
            # recursor's (e.g. `Lean.Syntax.rec_*` has a rule for
            # `Array.mk`, whose parent has its own param count). Slice
            # the ctor's args using the *ctor's* num_params, not the
            # recursor's. For non-nested cases the two coincide.
            ctor_decl = find_decl(env.declarations, rec_rule.ctor_name)
            if ctor_decl is None or not ctor_decl.w_kind.is_constructor():
                return False, self
            ctor_kind = ctor_decl.w_kind
            assert isinstance(ctor_kind, W_Constructor)
            ctor_start = ctor_kind.num_params
            ctor_end = ctor_kind.num_params + rec_rule.num_fields
            assert ctor_start >= 0
            assert ctor_end >= 0

            for ctor_field in all_ctor_args[ctor_start:ctor_end]:
                new_app = new_app.app_in(env, ctor_field)

            i = major_idx - 1
            while i >= 0:
                new_app = new_app.app_in(env, args[i])
                i -= 1

            env.tracer.iota(target.name)
            return True, new_app

        return False, self

    def _to_cnstr_when_structure(self, env, rec_type, rec_kind, major):
        """
        Lean's ``to_cnstr_when_structure`` (inductive.h): if ``major``
        is not a constructor application and its type is a non-Prop
        non-recursive structure ``C params…``, return
        ``C.mk params… major.0 … major.n`` (`expand_eta_struct`);
        otherwise ``None``.

        The structure consulted is the recursor's major-premise
        inductive (``recursor_val::get_major_induct``), read off the
        recursor's own type.
        """
        induct_name = rec_kind.major_induct_name(rec_type)
        if induct_name is None:
            return None
        ind_decl = find_decl(env.declarations, induct_name)
        if ind_decl is None:
            return None
        ind_kind = ind_decl.w_kind
        if not isinstance(ind_kind, W_Inductive):
            return None
        if not ind_kind.is_non_recursive_structure():
            return None
        major_head, _ = major.unapp()
        if isinstance(major_head, W_Const):
            head_decl = find_decl(env.declarations, major_head.name)
            if head_decl is not None and head_decl.w_kind.is_constructor():
                return None
        e_type = major.infer(env).whnf(env)
        type_head, rev_type_args = e_type.unapp()
        if not isinstance(type_head, W_Const):
            return None
        if not type_head.name.syntactic_eq(induct_name):
            return None
        ctor_decl = ind_kind.constructor_decls(env.declarations)[0]
        ctor_kind = ctor_decl.w_kind
        assert isinstance(ctor_kind, W_Constructor)
        rev_type_args.reverse()
        num_params = ctor_kind.num_params
        assert num_params >= 0
        if len(rev_type_args) < num_params:
            return None
        result = ctor_decl.name.const(type_head.levels)
        for i in range(num_params):
            result = result.app_in(env, rev_type_args[i])
        for i in range(ctor_kind.num_fields):
            result = result.app_in(
                env, induct_name.proj_in(env, i, major),
            )
        return result

    def _maybe_iota_nat_rec_step(self, tc, target, args, major_idx):
        """One-step iota for `Nat.rec motive zero succ (W_LitNat N)`.

        Returns the same expression the standard iota path would produce
        after fully beta-reducing `rec_rule.rhs` against the four args
        — namely:

            N == 0   →   zero_case
            N >  0   →   succ_case (W_LitNat N-1) (Nat.rec motive zero succ (W_LitNat N-1))

        — but built directly as a small `W_App` tree rather than via an
        app spine the outer whnf loop has to peel one beta at a time.
        Returns None when this isn't applicable (not `Nat.rec`, major
        isn't a literal, or trailing args sit after the major).
        """
        if not target.name.syntactic_eq(_NAT_REC_NAME):
            return None
        if major_idx != 0:
            # Trailing args after the major aren't handled here — fall
            # through so the standard iota path peels them as usual.
            return None
        major = args[0]
        if not isinstance(major, W_LitNat):
            return None
        # args is outermost-first from `unapp`, so for the fully-applied
        # `Nat.rec motive zero succ N` we have args = [N, succ, zero, motive].
        succ_case = args[1]
        zero_case = args[2]
        motive = args[3]
        if major.val.eq(rbigint.fromint(0)):
            return zero_case
        pred = _mk_w_litnat(major.val.sub(rbigint.fromint(1)))
        rec_at_pred = target.app_in(tc, motive).app_in(tc, zero_case).app_in(tc, succ_case).app_in(tc, pred)
        return succ_case.app_in(tc, pred).app_in(tc, rec_at_pred)

    # https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#weak-head-normalisation
    def _whnf_core(self, env):
        # No native nat probe here: probing a binary nat op WHNFs its
        # arguments — full evaluation — and whnf_core must never
        # evaluate. The probe lives in the evaluating loops
        # (`whnf_with_progress`, `_whnf_iota_chain`) and, fvar-gated,
        # in `_try_lazy_delta`, mirroring lean4 (reduce_nat is called
        # from `whnf` at type_checker.cpp:670 and from
        # `lazy_delta_reduction` at :979, never from `whnf_core`).

        # Reduce the head by a single step rather than calling
        # whnf_with_progress (which spawns its own JIT-driver loop).
        # Returning a new App here lets the *outer* whnf_with_progress
        # loop iterate over the entire reduction chain — every step
        # goes through the same W_App merge-point, giving the RPython
        # JIT enough iterations to compile a useful trace.
        fn_next = self.fn._whnf_core(env)
        if fn_next is not None:
            return fn_next.app_in(env, self.arg)

        # self.fn is now in WHNF.
        fn = self.fn

        # Beta reduction. If `fn` is a closure around a lambda
        # (`_whnf_under_closure` treats those as already-WHNF), do
        # the beta step *inside* the closure: extend the closure
        # environment with the arg instead of materializing the whole
        # substitution via `force`.
        if isinstance(fn, W_Closure):
            inner = fn.body
            if isinstance(inner, W_Lambda):
                new_env = [self.arg] + list(fn.env)
                env.tracer.beta()
                return inner.body.closure(new_env)
            fn = fn.force(env)
        if isinstance(fn, W_FunBase):
            env.tracer.beta()
            # No curried-call closure batching here: `W_Closure` is
            # identity-hashed, so wrapping the hot brecOn matcher
            # minors (3-binder lambdas) in fresh closures defeats the
            # W_App interning that keeps reconstructed recursor
            # sub-terms shared — every below-tower layer became a
            # fresh subtree and the per-decl arena never deduped it.
            return fn.body.instantiate(env, self.arg)

        # Handle recursor in head position. A stuck major of
        # structure type is eta-expanded inside (`_to_cnstr_when_
        # structure`), which unsticks reductions like
        # `Prod.casesOn STUCK (fun l r => mk l r)` — the `Prod.mk`
        # rule fires against `Prod.mk STUCK.fst STUCK.snd`.
        iota_progress, reduced = self.try_iota_reduce(env)
        if iota_progress:
            return reduced

        # Quot.lift reduction: Quot.lift {α} {r} {β} f h (Quot.mk {α} r a) ≡ f a
        reduced = self.try_quot_lift_reduce(env)
        if reduced is not None:
            return reduced

        return None

    def bind_fvar(self, tc, fvar, depth):
        new_fn = self.fn.bind_fvar(tc, fvar, depth)
        new_arg = self.arg.bind_fvar(tc, fvar, depth)
        if new_fn is self.fn and new_arg is self.arg:
            return self
        return new_fn.app_in(tc, new_arg)

    def instantiate(self, tc, expr, depth=0):
        return _iter_instantiate(tc, self, expr, depth)

    def incr_free_bvars(self, tc, count, depth):
        if self.loose_bvar_range <= depth:
            return self
        return self.fn.incr_free_bvars(tc, count, depth).app_in(
            tc, self.arg.incr_free_bvars(tc, count, depth),
        )

    def subst_levels(self, tc, substs):
        new_fn = self.fn.subst_levels(tc, substs)
        new_arg = self.arg.subst_levels(tc, substs)
        if new_fn is self.fn and new_arg is self.arg:
            return self
        return new_fn.app_in(tc, new_arg)

    def _whnf_under_closure(self, tc, closure_env):
        return self.fn.closure(closure_env).app_in(tc, self.arg.closure(closure_env))


def _whnf_iota_chain(env, expr):
    """
    WHNF ``expr``, walking through chains of nested recursor-iota
    applications iteratively via an explicit work stack.

    Each frame is a ``W_App`` we're trying to iota-reduce. Descending
    happens by pushing the frame and continuing with its major
    premise. When the deepest expression is reduced as far as
    non-iota steps allow, we walk the stack back up applying iota at
    each level — pre-populating the ``_whnf_cache_result`` of each
    frame's major so a re-entry through `try_iota_reduce` (which
    routes its `args[major_idx].whnf(env)` back into us) short-
    circuits on the cache check below.
    """
    if isinstance(expr, W_App):
        c = expr._caches
        if c is not None and c.whnf_env is env:
            return c.whnf_result
    elif isinstance(expr, W_Closure):
        if expr._whnf_cache_env is env:
            return expr._whnf_cache_result

    chain = []
    cur = expr

    while True:
        # Reduce `cur` as far as possible without firing iota itself
        # (so we don't recurse through `try_iota_reduce`). Major
        # premises are evaluated with full-whnf semantics: native nat
        # reduction and delta (`try_unfold_head`, one layer at a time)
        # both apply here, like lean4's `reduce_recursor` calling the
        # evaluating `whnf` on the major.
        while True:
            if isinstance(cur, W_App):
                next_ = cur._whnf_core_no_iota(env)
                if next_ is None:
                    next_ = _try_reduce_nat(cur, env)
                if next_ is None:
                    # Quot.lift is not a recursor, so a stuck
                    # `Quot.lift f h (Quot.mk r a)` never becomes a
                    # chain frame — without firing it here the whole
                    # major chain above it dead-ends (Finset/Multiset
                    # computations inside recursor majors reduce
                    # through `Quot` constantly, e.g. every
                    # `Polynomial.natDegree (0 : Polynomial R) ≡ 0`
                    # obligation in Mathlib). Struct-eta stays out:
                    # struct recursors do become frames, and the
                    # walk-up handles them once their major is
                    # exhausted.
                    next_ = cur.try_quot_lift_reduce(env)
            else:
                next_ = cur._whnf_core(env)
            if next_ is None:
                next_ = cur.try_unfold_head(env)
                if next_ is None:
                    break
            cur = next_

        # If `cur` is a recursor application, descend into its major.
        descended = False
        if isinstance(cur, W_App):
            target, args = cur.unapp()
            if isinstance(target, W_Const):
                decl = find_decl(env.declarations, target.name)
                if decl is not None:
                    rec = decl.w_kind
                    if isinstance(rec, W_Recursor):
                        skip = (
                            rec.num_params
                            + rec.num_indices
                            + rec.num_minors
                            + rec.num_motives
                        )
                        major_idx = len(args) - 1 - skip
                        if major_idx >= 0:
                            chain.append((cur, args, major_idx))
                            cur = args[major_idx]
                            descended = True
        if descended:
            continue

        # No further descent. Walk back up applying iota.
        if not chain:
            return cur

        parent, p_args, p_mi = chain.pop()
        major_arg = p_args[p_mi]
        # Cache the descent's result as the major's WHNF so the
        # `args[major_idx].whnf(env)` call inside `try_iota_reduce`
        # returns immediately instead of recursing.
        if isinstance(major_arg, W_App):
            c = major_arg._ensure_caches()
            if c.whnf_env is None:
                _note_cache_write(major_arg)
            c.whnf_env = env
            c.whnf_result = cur
        elif isinstance(major_arg, W_Closure):
            if major_arg._whnf_cache_env is None:
                _note_cache_write(major_arg)
            major_arg._whnf_cache_env = env
            major_arg._whnf_cache_result = cur

        progress, reduced = parent.try_iota_reduce(env)
        if not progress:
            # Iota didn't fire at this level (struct-eta on a stuck
            # major happens inside it). Quot-lift can still unstick it
            # — same fallback order as `_whnf_core`.
            reduced = parent.try_quot_lift_reduce(env)
            if reduced is None:
                # Leave `parent` un-reduced and propagate it up; any
                # frame above us has `parent` as part of its
                # major-chain, so they can't iota either.
                cur = parent
                while chain:
                    higher, _, _ = chain.pop()
                    cur = higher
                return cur
        cur = reduced


class W_Closure(W_Expr):
    """
    A deferred substitution: ``body`` evaluated under ``env``.

    Represents the result of substituting ``[bvar(0) ↦ env[0],
    bvar(1) ↦ env[1], ...]`` into ``body``, with bvars at indices
    ``>= len(env)`` shifted down by ``len(env)``. Each entry of
    ``env`` lives in the closure's outer scope (i.e. the scope
    containing the closure itself).
    """

    _attrs_ = [
        'env', 'body',
        '_whnf_cache_env', '_whnf_cache_result',
        '_infer_cache_env', '_infer_cache_result',
    ]
    _immutable_fields_ = ['env', 'body']

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
        fvar = body.has_fvar
        if not fvar:
            for v in env:
                if v.has_fvar:
                    fvar = True
                    break
        self.has_fvar = fvar
        # Inline whnf/infer caches, env-tagged for hash-consing safety.
        self._whnf_cache_env = None
        self._whnf_cache_result = None
        self._infer_cache_env = None
        self._infer_cache_result = None
        # Closures shouldn't reach the exporter (they're produced during
        # reduction, not by the walker), but give them an identity-based
        # hash so the RPython annotator sees `_hash` set on every W_Expr.
        self._hash = compute_identity_hash(self)

    def whnf(self, env):
        if self._whnf_cache_env is env:
            env.tracer.whnf_cache_hit()
            return self._whnf_cache_result
        env.tracer.whnf_cache_miss()
        (expr, _progress) = self.whnf_with_progress(env)
        if self._whnf_cache_env is None:
            _note_cache_write(self)
        self._whnf_cache_env = env
        self._whnf_cache_result = expr
        return expr

    def _reset_caches(self):
        self._whnf_cache_env = None
        self._whnf_cache_result = None
        self._infer_cache_env = None
        self._infer_cache_result = None

    def _whnf_core(self, env):
        return self.body._whnf_under_closure(env, self.env)

    def _whnf_under_closure(self, tc, closure_env):
        # Nested closure: peel inner first, then re-wrap.
        inner_step = self.body._whnf_under_closure(tc, self.env)
        if inner_step is None:
            return None
        return inner_step.closure(closure_env)

    def force(self, tc):
        """
        Materialize the closure-free form by performing the deferred
        substitution eagerly.

        ``tc`` routes the substitution-produced `W_App`s into the
        per-decl arena (when called from reduction paths). Cold-path
        callers without a TC pass `None`; those allocations route to
        the persistent intern. Without this threading, reduction-time
        force()s would dump every materialised `W_App` into the
        persistent table, recreating the leak the per-decl arena was
        meant to bound.
        """
        # Multi-arg substitute: one walk of `self.body` substituting
        # every `env[i]` for bvar `i` at once. Replaces the N sequential
        # `instantiate` calls of the previous loop — for closures
        # accumulated across a curried-Lambda peel, this is the savings
        # nanoda_lib gets from `inst(body, &substs)` (tc.rs:786) versus
        # what would otherwise be N body walks. The previous outermost-
        # first ordering was only needed for the sequential case; with
        # parallel substitution the rel-mapping in `_instantiate_multi`
        # handles every bvar in its own pass.
        return _instantiate_multi(tc, self.body, self.env, 0)

    def syntactic_eq(self, other):
        return syntactic_eq(self.force(None), other)

    def infer(self, env):
        return self.force(env).infer(env)

    def instantiate(self, tc, expr, depth=0):
        return self.force(tc).instantiate(tc, expr, depth)

    def bind_fvar(self, tc, fvar, depth):
        return self.force(tc).bind_fvar(tc, fvar, depth)

    def incr_free_bvars(self, tc, count, depth):
        return self.force(tc).incr_free_bvars(tc, count, depth)

    def subst_levels(self, tc, substs):
        return self.force(tc).subst_levels(tc, substs)

    def def_eq(self, other, tc):
        # Re-dispatch through tc.def_eq so the forced LHS gets WHNF'd
        # against ``other`` (which may itself still be a closure).
        return tc.def_eq(self.force(tc), other)

    def to_format(self, constants, marker):
        return self.force(None).to_format(constants, marker)

    def expect_sort(self, env):
        return self.force(env).expect_sort(env)

    def contains_const(self, name):
        return self.force(None).contains_const(name)

    def _any_subexpr_invalid_index(self, inductive):
        return self.force(None)._any_subexpr_invalid_index(inductive)

    def is_strictly_positive(self, inductive, env):
        return self.force(env).is_strictly_positive(inductive, env)


class W_RecRule(_Item):
    _attrs_ = ['ctor_name', 'num_fields', 'rhs']
    _immutable_fields_ = ['ctor_name', 'num_fields', 'rhs']

    def __init__(self, ctor_name, num_fields, rhs):
        self.ctor_name = ctor_name
        self.num_fields = num_fields
        self.rhs = rhs


class W_Declaration(_Item):
    _attrs_ = ['name', 'type', 'w_kind', 'levels', 'is_unsafe']
    _immutable_fields_ = ['name', 'type', 'w_kind', 'levels', 'is_unsafe']

    def __init__(self, name, type, w_kind, levels, is_unsafe=False):
        self.name = name
        self.type = type
        self.w_kind = w_kind
        for each in levels:
            assert isinstance(each, Name), "%s is not a level name" % (each,)
        self.levels = levels
        #: Mirrors Lean's `ConstantInfo.isUnsafe` (or `DefinitionVal.safety
        #: == .unsafe`). `lean4export` skips unsafe constants unless
        #: `--export-unsafe` is passed; we follow the same convention
        #: by default.
        self.is_unsafe = is_unsafe

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

    # Returns the value associated with this declaration kind.
    # This is the def value for a Definition, and `None` for things like Inductive
    def get_delta_reduce_target(self):
        return None

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
    _attrs_ = ['value', 'hint']
    _immutable_fields_ = ['value', 'hint']

    def __init__(self, value, hint):
        self.value = value
        self.hint = hint

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_def(decl, self.value, self.hint)

    def type_check(self, type, tc):
        type_type = type.infer(tc)
        if not isinstance(type_type.whnf(tc), W_Sort):
            return W_NotASort(tc, type, inferred_type=type_type, name=None)
        val_type = self.value.infer(tc)
        if not tc.def_eq(type, val_type):
            return W_TypeError(tc, self.value, type, inferred_type=val_type)

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

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_opaque(decl, self.value)

    def get_delta_reduce_target(self):
        return None


class W_Theorem(W_DeclarationKind):
    _attrs_ = ['value']
    _immutable_fields_ = ['value']

    def __init__(self, value):
        self.value = value

    def dump_to(self, exporter, decl):
        exporter.begin_decl(decl)
        exporter.dump_deps(self.value)
        exporter.emit_thm(decl, self.value)

    def type_check(self, type, tc):
        type_type = type.infer(tc)
        type_type_whnf = type_type.whnf(tc)
        if not isinstance(type_type_whnf, W_Sort):
            return W_NotASort(tc, type, inferred_type=type_type, name=None)
        if not type_type_whnf.level.eq(W_LEVEL_ZERO):
            return W_NotAProp(tc, type, inferred_sort=type_type_whnf, name=None)
        val_type = self.value.infer(tc)
        if not tc.def_eq(type, val_type):
            return W_TypeError(tc, self.value, type, inferred_type=val_type)

    def decl_format(self, name, levels, type, constants, marker):
        return _decl_with_value_format(
            "theorem", name, levels, type, self.value, constants, marker,
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
            target = target.body.instantiate(tc, target.binder.fvar(), 0)
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
        all_fvars, ctor_type = ctor.type.open_all_binders(env)
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
    if isinstance(expr1, W_Closure):
        expr1 = expr1.force(None)
    if isinstance(expr2, W_Closure):
        expr2 = expr2.force(None)
    if expr1.__class__ is not expr2.__class__:
        return False
    return expr1.syntactic_eq(expr2)


def _iter_instantiate(tc, root, expr, depth):
    """
    Substitute ``expr`` for the bvar at ``depth`` in ``root``.

    Recursive — splits per-kind into `_inst_app` / `_inst_lambda` /
    `_inst_forall` so each call site has a single static type and the
    JIT can trace each path independently (the older explicit-work-stack
    version had a 5-way polymorphic dispatch that defeated tracing —
    79+ bridges, ~25% regression with a JIT driver attached). The
    per-instance 1-entry inline cache (`_inst_cache_*` on `W_App` /
    `W_FunBase`) breaks the 2^N work that DAG-shared subexpressions
    would otherwise cause.

    The original work-stack version existed to keep `app-lam`
    alternations from blowing the C stack on extreme depths; we now
    rely on RPython's `stack_check___` guard (already ~3% of profile
    time, so the cost is paid regardless) to abort cleanly if a
    pathological term outruns the host stack.

    `tc` may be a `TypeChecker` (per-decl arena routing for any new
    `W_App`s built by `_inst_app`) or `None` (parser/test path; allocates
    against the persistent table).
    """
    return _instantiate(tc, root, expr, depth)


def _instantiate(tc, cur, sub, depth):
    if cur.loose_bvar_range <= depth:
        return cur
    cls = cur.__class__
    # Merge point after the no-op early-out, so the trace doesn't
    # specialise on a path that exits immediately.
    inst_jitdriver.jit_merge_point(
        cls=cls,
        tc=tc,
        cur=cur,
        sub=sub,
        depth=depth,
    )
    if cls is W_App:
        assert isinstance(cur, W_App)
        return _inst_app(tc, cur, sub, depth)
    if cls is W_Lambda:
        assert isinstance(cur, W_Lambda)
        return _inst_lambda(tc, cur, sub, depth)
    if cls is W_ForAll:
        assert isinstance(cur, W_ForAll)
        return _inst_forall(tc, cur, sub, depth)
    return cur.instantiate(tc, sub, depth)


@unroll_safe
def _inst_app(tc, app, sub, depth):
    c = app._caches
    if c is not None and c.inst_expr is sub and c.inst_depth == depth:
        return c.inst_result
    fn = app.fn
    arg = app.arg
    new_fn = fn
    new_arg = arg
    if fn.loose_bvar_range > depth:
        new_fn = _instantiate(tc, fn, sub, depth)
    if arg.loose_bvar_range > depth:
        new_arg = _instantiate(tc, arg, sub, depth)
    # If neither side moved, reuse the existing app — avoids a fresh
    # `_mk_app_in` lookup per `_inst_app` call. For brecOn-style hot
    # loops the substitute frequently doesn't reach this sub-app even
    # though its `loose_bvar_range` admitted descent.
    if new_fn is fn and new_arg is arg:
        result = app
    else:
        result = new_fn.app_in(tc, new_arg)
    c = app._ensure_caches()
    if c.inst_expr is None:
        _note_cache_write(app)
    c.inst_expr = sub
    c.inst_depth = depth
    c.inst_result = result
    return result


@unroll_safe
def _inst_lambda(tc, fun, sub, depth):
    c = fun._caches
    if c is not None and c.inst_expr is sub and c.inst_depth == depth:
        return c.inst_result
    new_binder = fun.binder.instantiate(tc, sub, depth)
    new_body = _instantiate(tc, fun.body, sub, depth + 1)
    if new_binder is fun.binder and new_body is fun.body:
        result = fun
    else:
        result = _mk_w_lambda_in(tc, new_binder, new_body)
    c = fun._ensure_caches()
    if c.inst_expr is None:
        _note_cache_write(fun)
    c.inst_expr = sub
    c.inst_depth = depth
    c.inst_result = result
    return result


@unroll_safe
def _inst_forall(tc, fun, sub, depth):
    c = fun._caches
    if c is not None and c.inst_expr is sub and c.inst_depth == depth:
        return c.inst_result
    new_binder = fun.binder.instantiate(tc, sub, depth)
    new_body = _instantiate(tc, fun.body, sub, depth + 1)
    if new_binder is fun.binder and new_body is fun.body:
        result = fun
    else:
        result = _mk_w_forall_in(tc, new_binder, new_body)
    c = fun._ensure_caches()
    if c.inst_expr is None:
        _note_cache_write(fun)
    c.inst_expr = sub
    c.inst_depth = depth
    c.inst_result = result
    return result


def _instantiate_multi(tc, cur, substs, depth):
    """
    Substitute multiple expressions simultaneously for bvars in `cur`.

    `substs[i]` is the substitute for bvar `i` (at depth 0); when called
    with `depth > 0`, the mapping is bvar `depth + i` → `substs[i]`. A
    bvar at or above `depth + len(substs)` is decremented by `len(substs)`
    to account for the removed binders.

    This is the multi-arg analog of `_instantiate`: substituting N values
    in one walk rather than calling `_instantiate` N times costs O(|body|)
    instead of O(N·|body|). Mirrors nanoda_lib's `inst_aux` (expr.rs:170)
    used in its `whnf_no_unfolding` multi-Lambda peel (tc.rs:780-789) and
    its `Let`/`Var` handlers.
    """
    if cur.loose_bvar_range <= depth:
        return cur
    cls = cur.__class__
    if cls is W_BVar:
        assert isinstance(cur, W_BVar)
        if cur.id < depth:
            return cur
        rel = cur.id - depth
        n = len(substs)
        if rel < n:
            return substs[rel].incr_free_bvars(tc, depth, 0)
        return _mk_w_bvar(cur.id - n)
    if cls is W_App:
        assert isinstance(cur, W_App)
        new_fn = _instantiate_multi(tc, cur.fn, substs, depth)
        new_arg = _instantiate_multi(tc, cur.arg, substs, depth)
        if new_fn is cur.fn and new_arg is cur.arg:
            return cur
        return new_fn.app_in(tc, new_arg)
    if cls is W_Lambda:
        assert isinstance(cur, W_Lambda)
        new_binder = cur.binder
        if cur.binder.type.loose_bvar_range > depth:
            new_type = _instantiate_multi(tc, cur.binder.type, substs, depth)
            if new_type is not cur.binder.type:
                new_binder = cur.binder.with_type(type=new_type)
        new_body = _instantiate_multi(tc, cur.body, substs, depth + 1)
        if new_binder is cur.binder and new_body is cur.body:
            return cur
        return _mk_w_lambda_in(tc, new_binder, new_body)
    if cls is W_ForAll:
        assert isinstance(cur, W_ForAll)
        new_binder = cur.binder
        if cur.binder.type.loose_bvar_range > depth:
            new_type = _instantiate_multi(tc, cur.binder.type, substs, depth)
            if new_type is not cur.binder.type:
                new_binder = cur.binder.with_type(type=new_type)
        new_body = _instantiate_multi(tc, cur.body, substs, depth + 1)
        if new_binder is cur.binder and new_body is cur.body:
            return cur
        return _mk_w_forall_in(tc, new_binder, new_body)
    if cls is W_Proj:
        assert isinstance(cur, W_Proj)
        new_struct = _instantiate_multi(tc, cur.struct_expr, substs, depth)
        if new_struct is cur.struct_expr:
            return cur
        return cur.struct_name.proj_in(tc, cur.field_index, new_struct)
    if cls is W_Let:
        assert isinstance(cur, W_Let)
        new_type = _instantiate_multi(tc, cur.type, substs, depth)
        new_value = _instantiate_multi(tc, cur.value, substs, depth)
        new_body = _instantiate_multi(tc, cur.body, substs, depth + 1)
        if (new_type is cur.type
                and new_value is cur.value
                and new_body is cur.body):
            return cur
        return _mk_w_let(cur.name, new_type, new_value, new_body)
    # W_Closure / other: fall back to a sequence of single-arg
    # `instantiate` calls. Closures aren't expected to be substituted
    # into during a force — they'd have been peeled earlier — but the
    # fallback keeps semantics correct if one slips through.
    result = cur
    k = len(substs) - 1
    while k >= 0:
        result = result.instantiate(tc, substs[k], depth + k)
        k -= 1
    return result


# Iterative infer driver. The work stack carries items of the following
# kinds; pushes use LIFO ordering so the bottom of the stack runs last.
class _InferWork(object):
    _attrs_ = []


class _InferVisit(_InferWork):
    _attrs_ = ['expr']

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

    _attrs_ = ['head', 'args', 'j']

    def __init__(self, head, args, j):
        self.head = head
        self.args = args
        self.j = j

    def arg(self):
        return self.args[self.j]

    def spine_so_far(self, tc):
        spine = self.head
        i = len(self.args) - 1
        while i > self.j:
            spine = spine.app_in(tc, self.args[i])
            i -= 1
        return spine


class _InferBindLambda(_InferWork):
    _attrs_ = ['binder', 'fvar']

    def __init__(self, binder, fvar):
        self.binder = binder
        self.fvar = fvar


class _InferBindForAll(_InferWork):
    _attrs_ = ['binder_sort']

    def __init__(self, binder_sort):
        self.binder_sort = binder_sort


class _InferStore(_InferWork):
    _attrs_ = ['expr']

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

    A recursive split into ``_infer_app`` / ``_infer_lambda`` /
    ``_infer_forall`` / ``_infer_closure`` (the same shape we use for
    ``_instantiate``) was tried; it overflows the host stack on
    ``app-lam.ndjson`` because every lambda level recurses *twice*
    (through ``_infer_lambda`` then ``_infer_closure``-on-body), so
    a 4000-level term needs ~8000 C frames.

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
            if cls is W_App:
                assert isinstance(cur, W_App)
                c = cur._caches
                if c is not None and c.infer_env is env:
                    values.append(c.infer_result)
                    continue
            elif cls is W_Lambda or cls is W_ForAll:
                assert isinstance(cur, W_FunBase)
                c = cur._caches
                if c is not None and c.infer_env is env:
                    values.append(c.infer_result)
                    continue
            elif cls is W_Closure:
                assert isinstance(cur, W_Closure)
                if cur._infer_cache_env is env:
                    values.append(cur._infer_cache_result)
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
                    new_app = inner.fn.closure(closure_env).app_in(
                        env, inner.arg.closure(closure_env),
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
                fn_type = fn_type.force(env)
            arg = item.arg()
            if not isinstance(fn_type, W_ForAll):
                raise W_NotAFunction(
                    env, item.spine_so_far(env), inferred_type=fn_type_base,
                )
            # In `infer_only` mode the argument's type is trusted (the
            # term is already known well-typed); only the declaration's
            # own type and value, checked in the default mode, validate
            # each argument against its function's domain. Mirrors
            # lean4's `infer_app`, which runs `is_def_eq(a_type, d_type)`
            # only when `infer_only` is false (type_checker.cpp).
            if not env.infer_only:
                if not env.def_eq(fn_type.binder.type, arg_type):
                    raise W_TypeError(
                        env, arg, fn_type.binder.type,
                        inferred_type=arg_type,
                    )
            values.append(fn_type.body.instantiate(env, arg))
        elif isinstance(item, _InferBindLambda):
            body_type = values.pop()
            body_type = body_type.bind_fvar(env, item.fvar, 0)
            values.append(forall(item.binder)(body_type))
        elif isinstance(item, _InferBindForAll):
            body_sort = values.pop().whnf(env).expect_sort(env)
            values.append(item.binder_sort.imax(body_sort).sort())
        else:
            assert isinstance(item, _InferStore)
            target = item.expr
            result = values[len(values) - 1]
            if isinstance(target, W_App):
                c = target._ensure_caches()
                if c.infer_env is None:
                    _note_cache_write(target)
                c.infer_env = env
                c.infer_result = result
            elif isinstance(target, W_FunBase):
                c = target._ensure_caches()
                if c.infer_env is None:
                    _note_cache_write(target)
                c.infer_env = env
                c.infer_result = result
            elif isinstance(target, W_Closure):
                if target._infer_cache_env is None:
                    _note_cache_write(target)
                target._infer_cache_env = env
                target._infer_cache_result = result
            elif isinstance(target, W_Const):
                if target._infer_cache_env is None:
                    _note_cache_write(target)
                target._infer_cache_env = env
                target._infer_cache_result = result
    return values[0]


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
