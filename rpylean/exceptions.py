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


class InvalidDeclaration(Exception):
    """
    A declaration is invalid.
    """
    def __init__(self, declaration, reason):
        self.declaration = declaration
        self.reason = reason

    def str(self):
        return "Invalid declaration %s: %s" % (
            self.declaration.name.pretty(),
            self.reason,
        )


class AlreadyDeclared(InvalidDeclaration):
    """
    A declaration already exists in the environment.
    """
    def __init__(self, declaration, existing):
        reason = "%s is already declared as %s" % (
            declaration.name.pretty(),
            existing.pretty(),
        )
        InvalidDeclaration.__init__(self, declaration, reason)
        self.existing = existing


class DuplicateLevels(InvalidDeclaration):
    """
    A declaration has duplicate level parameters.
    """
    def __init__(self, declaration, duplicate):
        reason = "%s has duplicate level parameter %s" % (
            declaration.name.pretty(),
            duplicate,
        )
        InvalidDeclaration.__init__(self, declaration, reason)
        self.duplicate = duplicate
