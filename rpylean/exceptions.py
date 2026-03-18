from __future__ import print_function

from rpylean._tokens import DECL_NAME, ERROR, FORMAT_PLAIN, PLAIN


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

    def __init__(self, name, duplicate):
        self.name = name
        self.duplicate = duplicate

    def tokens(self):
        return [
            ERROR.emit("Invalid declaration "),
            DECL_NAME.emit(self.name.str()),
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


class W_InvalidDeclaration(W_Error):
    """
    A type-checking error attributed to a specific declaration.
    """

    def __init__(self, declaration, inner):
        self.declaration = declaration
        self.inner = inner

    def tokens(self):
        return [
            ERROR.emit("Invalid declaration "),
            DECL_NAME.emit(self.declaration.name.str()),
            PLAIN.emit(": "),
        ] + self.inner.tokens()


class NotAStructure(W_Error):
    """
    A proj expression targets a type that is not a single-constructor inductive.
    """

    def __init__(self, struct_decl):
        self.struct_decl = struct_decl

    def tokens(self):
        n = len(self.struct_decl.w_kind.constructors)
        return [
            DECL_NAME.emit(self.struct_decl.name.str()),
            ERROR.emit(
                " is not a structure: it has %d constructor%s"
                % (n, "s" if n != 1 else "")
            ),
        ]


class UnknownStructure(W_Error):
    """
    A proj expression names a structure type that is not in the environment.
    """

    def __init__(self, name):
        self.name = name

    def tokens(self):
        return [
            ERROR.emit("unknown structure: "),
            DECL_NAME.emit(self.name.str()),
        ]


class InvalidProjection(W_Error):
    """
    An attempt was made to project a structure field that does not exist.
    """

    def __init__(self, structure, field_index, num_fields):
        self.structure = structure
        self.field_index = field_index
        self.num_fields = num_fields

    def tokens(self):
        if self.num_fields == 0:
            info = "no fields"
        elif self.num_fields == 1:
            info = "only 1 field"
        else:
            info = "only %d fields" % self.num_fields
        return [
            ERROR.emit("index %d is not valid for " % self.field_index),
            DECL_NAME.emit(self.structure.name.str()),
            ERROR.emit(", which has %s" % info),
        ]


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
