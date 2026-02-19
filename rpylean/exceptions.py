class W_Error(Exception):
    """
    An exception which might happen at (rpylean) runtime.
    """

    def __str__(self):
        """
        Show our runtime message when we're raised in Python-land.
        """
        return self.str()

    def str(self):
        """
        Override me in actual exceptions.
        """
        return "Unexpected error!"


class InvalidDeclaration(W_Error):
    """
    A declaration is invalid.
    """

    def __init__(self, name, reason):
        self.name = name
        self.reason = reason

    def str(self):
        return "Invalid declaration %s: %s" % (
            self.name.str(),
            self.reason,
        )


class AlreadyDeclared(InvalidDeclaration):
    """
    A declaration already exists in the environment.
    """

    def __init__(self, name, constants):
        reason = "%s is already declared as %s" % (
            name.str(),
            constants[name].pretty(constants),
        )
        InvalidDeclaration.__init__(self, name, reason)
        self.constants = constants


class DuplicateLevels(InvalidDeclaration):
    """
    A declaration has duplicate level parameters.
    """

    def __init__(self, name, duplicate):
        reason = "%s has duplicate level parameter %s" % (
            name.str(),
            duplicate,
        )
        InvalidDeclaration.__init__(self, name, reason)
        self.duplicate = duplicate


class ReflexiveKError(InvalidDeclaration):
    """
    A reflexive inductive type has a bad recursor.

    Reflexive inductive types cannot support K-like reduction, which
    requires a single constructor with 0 arguments.
    """

    def __init__(self, name, rec_name):
        reason = (
            "%s is reflexive "
            "but recursor %s claims to support k-like reduction"
        ) % (name.str(), rec_name.str())
        InvalidDeclaration.__init__(self, name, reason)
        self.rec_name = rec_name


class InvalidProjection(W_Error):
    """
    An attempt was made to project a structure field that does not exist.
    """

    def __init__(self, structure, field_index, num_fields):
        self.structure = structure
        self.field_index = field_index
        self.num_fields = num_fields

    def str(self):
        if self.num_fields == 0:
            info = "no fields"
        elif self.num_fields == 1:
            info = "only 1 field"
        else:
            info = "only %d fields" % self.num_fields
        return "index %d is not valid for %s, which has %s" % (
            self.field_index,
            self.structure.name.str(),
            info,
        )


class UnknownQuotient(W_Error):
    """
    An unknown quotient declaration was found.

    Only a specific set of Quot declarations are expected and known compatible
    with Lean's type theory.
    """

    def __init__(self, name, type):
        self.name = name
        self.type = type

    def str(self):
        return "Unknown quotient declaration: %s" % (self.name.str(),)


class HeartbeatExceeded(W_Error):
    """
    The maximum number of def_eq steps was exceeded for a declaration.
    """

    def __init__(self, declaration, heartbeats, max_heartbeat):
        self.declaration = declaration
        self.heartbeats = heartbeats
        self.max_heartbeat = max_heartbeat

    def str(self):
        return "in %s:\nheartbeat limit exceeded (%s def_eq calls, limit %s)" % (
            self.declaration.name.str(),
            self.heartbeats,
            self.max_heartbeat,
        )
