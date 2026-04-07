from __future__ import print_function

from rpylean._tokens import (
    DECL_NAME,
    Diagnostic,
    ERROR,
    FORMAT_PLAIN,
    LITERAL,
    MESSAGE,
    NO_SPAN,
    PLAIN,
    PUNCT,
)


class ExportError(Exception):
    """
    Something is wrong with the export file.
    """

    def __str__(self):
        return FORMAT_PLAIN(self.tokens())

    def tokens(self):
        """
        Return a token list describing this error.  Must be overridden.
        """
        raise NotImplementedError

    def at(self, source_pos):
        """
        Pair this error with a source position.
        """
        return ErrorAtSource(self, source_pos)


class ErrorAtSource(Exception):
    """
    An ExportError paired with a source position.
    """

    def __init__(self, error, source_pos):
        self.error = error
        self.source_pos = source_pos


class IndexGapError(ExportError):
    """
    An index in the export is not the next sequential value expected.
    """

    def __init__(self, kind, expected, got):
        self.kind = kind
        self.expected = expected
        self.got = got

    def tokens(self):
        return [
            ERROR.emit(
                "expected %s index %d, got %d" % (self.kind, self.expected, self.got)
            ),
        ]


class AlreadyDeclared(ExportError):
    """
    A declaration already exists in the environment.
    """

    def __init__(self, name, constants):
        self.name = name
        reason = [ERROR.emit("already declared as ")] + (
            constants[name].tokens(constants)
        )
        self.reason = reason

    def tokens(self):
        return [
            ERROR.emit("Invalid declaration "),
            DECL_NAME.emit(self.name.str()),
            PLAIN.emit(": "),
        ] + self.reason


class DuplicateLevels(ExportError):
    """
    A declaration has duplicate level parameters.
    """

    def __init__(self, name, levels, duplicate):
        self.name = name
        self.levels = levels
        self.duplicate = duplicate

    def tokens(self):
        level_strs = ", ".join([l.str() for l in self.levels])
        return [
            ERROR.emit("Invalid declaration "),
            DECL_NAME.emit(
                "%s.{%s}" % (self.name.str(), level_strs),
            ),
            PLAIN.emit(": "),
            ERROR.emit("duplicate level parameter "),
            DECL_NAME.emit(self.duplicate.str()),
        ]


class ReflexiveKError(ExportError):
    """
    A reflexive inductive type has a bad recursor.

    Reflexive inductive types cannot support K-like reduction, which
    requires a single constructor with 0 arguments.
    """

    def __init__(self, name, rec_name):
        self.name = name
        self.rec_name = rec_name

    def tokens(self):
        return [
            ERROR.emit("Invalid declaration "),
            DECL_NAME.emit(self.name.str()),
            PLAIN.emit(": "),
            ERROR.emit("declaration is reflexive but recursor "),
            DECL_NAME.emit(self.rec_name.str()),
            ERROR.emit(" claims to support k-like reduction"),
        ]


class UnknownQuotient(ExportError):
    """
    An unknown quotient declaration was found.

    Only a specific set of Quot declarations are expected and known compatible
    with Lean's type theory.
    """

    def __init__(self, name, type):
        self.name = name
        self.type = type

    def tokens(self):
        return [
            ERROR.emit("Unknown quotient declaration: "),
            DECL_NAME.emit(self.name.str()),
        ]


class W_Error(Exception):
    """
    An exception which might happen at (rpylean) runtime.
    """

    def __str__(self):
        """
        Show our runtime message when we're raised in Python-land.
        """
        return FORMAT_PLAIN(self.tokens())

    def tokens(self):
        """
        Return a token list describing this error.  Must be overridden.
        """
        raise NotImplementedError

    def write_to(self, writer):
        """Write this error to a TokenWriter."""
        writer.writeline(self.tokens())

    def diagnostic_in(self, declaration, declarations):
        """A ``Diagnostic`` for this error within the given declaration."""
        tokens = [DECL_NAME.emit(declaration.name.str()), PLAIN.emit(" : ")]
        tokens += declaration.type.tokens(declarations)
        message = [PLAIN.emit("\n")] + self.tokens()
        return Diagnostic(tokens, NO_SPAN, message)


class W_InvalidDeclaration(W_Error):
    """
    A type-checking error attributed to a specific declaration.
    """

    def __init__(self, declaration, inner, declarations):
        self.declaration = declaration
        self.inner = inner
        self.declarations = declarations

    def as_diagnostic(self):
        """Return this error as a ``Diagnostic`` with declaration context."""
        return self.inner.diagnostic_in(self.declaration, self.declarations)

    def tokens(self):
        return self.as_diagnostic().tokens + self.as_diagnostic().message

    def write_to(self, writer):
        """Write this error as a diagnostic with declaration context."""
        writer.writeline_diagnostic(self.as_diagnostic())


class InvalidProjection(W_Error):
    """
    A projection expression is invalid.
    """

    def __init__(self, struct_name, field_index, expr, suffix_tokens):
        self.struct_name = struct_name
        self.field_index = field_index
        self.expr = expr
        self._suffix = suffix_tokens

    def tokens(self):
        return [
            ERROR.emit("invalid projection "),
            DECL_NAME.emit(self.struct_name.str()),
            PUNCT.emit("."),
            LITERAL.emit("%d" % self.field_index),
            ERROR.emit(": "),
        ] + self._suffix

    def diagnostic_in(self, declaration, declarations):
        if self.expr is not None:
            span_holder = [NO_SPAN]
            tokens = declaration.tokens(
                declarations, mark=self.expr, span_holder=span_holder,
            )
            if span_holder[0] != NO_SPAN:
                message = [MESSAGE.emit("\n")] + self._suffix
                return Diagnostic(tokens, span_holder[0], message)
            # Exact subexpression not found (e.g. nested lambdas);
            # fall back to marking the whole declaration value.
            value = declaration.w_kind.get_delta_reduce_target()
            if value is not None:
                span_holder = [NO_SPAN]
                tokens = declaration.tokens(
                    declarations, mark=value, span_holder=span_holder,
                )
                if span_holder[0] != NO_SPAN:
                    message = [MESSAGE.emit("\n")] + self.tokens()
                    return Diagnostic(tokens, span_holder[0], message)
        return W_Error.diagnostic_in(self, declaration, declarations)

    @staticmethod
    def not_a_structure(struct_name, field_index, num_constructors, expr):
        """The projection target is not a single-constructor inductive."""
        n = num_constructors
        return InvalidProjection(
            struct_name,
            field_index,
            expr,
            [
                DECL_NAME.emit(struct_name.str()),
                ERROR.emit(
                    " is not a structure (it has %d constructor%s)"
                    % (n, "s" if n != 1 else "")
                ),
            ],
        )

    @staticmethod
    def unknown_structure(struct_name, field_index, expr):
        """The projection names a structure not in the environment."""
        return InvalidProjection(
            struct_name,
            field_index,
            expr,
            [
                ERROR.emit("unknown structure "),
                DECL_NAME.emit(struct_name.str()),
            ],
        )

    @staticmethod
    def out_of_bounds(struct_name, field_index, num_fields, expr):
        """The field index exceeds the number of fields in the structure."""
        if num_fields == 0:
            info = "no fields"
        elif num_fields == 1:
            info = "only 1 field"
        else:
            info = "only %d fields" % num_fields
        return InvalidProjection(
            struct_name,
            field_index,
            expr,
            [ERROR.emit("%s has %s" % (struct_name.str(), info))],
        )

    @staticmethod
    def non_prop_field(struct_name, field_index, expr):
        """The field is not propositional but the structure is Prop-valued."""
        return InvalidProjection(
            struct_name,
            field_index,
            expr,
            [
                ERROR.emit(
                    "cannot project a non-propositional field"
                    " from a propositional structure"
                )
            ],
        )

    def _suffix_tokens(self):
        return self._suffix


class HeartbeatExceeded(W_Error):
    """
    The maximum number of def_eq steps was exceeded for a declaration.
    """

    def __init__(self, declaration, heartbeats, max_heartbeat):
        self.declaration = declaration
        self.heartbeats = heartbeats
        self.max_heartbeat = max_heartbeat

    def tokens(self):
        return [
            PLAIN.emit("in "),
            DECL_NAME.emit(self.declaration.name.str()),
            ERROR.emit(
                "\nheartbeat limit exceeded (%s def_eq calls, limit %s)"
                % (self.heartbeats, self.max_heartbeat)
            ),
        ]
