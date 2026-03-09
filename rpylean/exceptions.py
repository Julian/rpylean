from __future__ import print_function

from rpylean._tokens import DECL_NAME, ERROR, FORMAT_PLAIN, PLAIN


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


class _InvalidDeclaration(W_Error):
    """
    A declaration is invalid.
    """

    def __init__(self, name, reason=[]):
        self.name = name
        self.reason = reason

    def tokens(self):
        return [
            ERROR.emit("Invalid declaration "),
            DECL_NAME.emit(self.name.str()),
            PLAIN.emit(": "),
        ] + self.reason


class AlreadyDeclared(_InvalidDeclaration):
    """
    A declaration already exists in the environment.
    """

    def __init__(self, name, constants):
        reason = [ERROR.emit("already declared as ")] + (
            constants[name].tokens(constants)
        )
        _InvalidDeclaration.__init__(self, name, reason)


class DuplicateLevels(_InvalidDeclaration):
    """
    A declaration has duplicate level parameters.
    """

    def __init__(self, name, duplicate):
        reason = [
            ERROR.emit("duplicate level parameter "),
            DECL_NAME.emit(duplicate.str()),
        ]
        _InvalidDeclaration.__init__(self, name, reason)


class ReflexiveKError(_InvalidDeclaration):
    """
    A reflexive inductive type has a bad recursor.

    Reflexive inductive types cannot support K-like reduction, which
    requires a single constructor with 0 arguments.
    """

    def __init__(self, name, rec_name):
        reason = [
            ERROR.emit("declaration is reflexive but recursor "),
            DECL_NAME.emit(rec_name.str()),
            ERROR.emit(" claims to support k-like reduction"),
        ]
        _InvalidDeclaration.__init__(self, name, reason)


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


class UnknownQuotient(W_Error):
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
