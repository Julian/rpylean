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


class W_TypeError(W_Error):
    """
    A term does not type check.
    """
    def __init__(self, term, expected_type):  # TODO: inferred_type
        self.term = term
        self.expected_type = expected_type

    def str(self):
        return "%s is not of type %s" % (
            self.term.pretty(),
            self.expected_type.pretty(),
        )


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
    def __init__(self, declaration, existing):
        reason = "%s is already declared as %s" % (
            declaration.name.str(),
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
            declaration.name.str(),
            duplicate,
        )
        InvalidDeclaration.__init__(self, declaration, reason)
        self.duplicate = duplicate
