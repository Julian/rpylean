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
    def __init__(self, declaration, reason):
        self.declaration = declaration
        self.reason = reason

    def str(self):
        return "Invalid declaration %s: %s" % (
            self.declaration.name.str(),
            self.reason,
        )


class AlreadyDeclared(InvalidDeclaration):
    """
    A declaration already exists in the environment.
    """
    def __init__(self, declaration, constants):
        reason = "%s is already declared as %s" % (
            declaration.name.str(),
            constants[declaration.name].pretty(constants),
        )
        InvalidDeclaration.__init__(self, declaration, reason)
        self.constants = constants


class DuplicateLevels(InvalidDeclaration):
    """
    A declaration has duplicate level parameters.
    """
    def __init__(self, declaration, duplicate):
        reason = "%s has duplicate level parameter %s" % (
            declaration.name.str(),
            duplicate,
        )
        InvalidDeclaration.__init__(self, declaration, reason)
        self.duplicate = duplicate


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
