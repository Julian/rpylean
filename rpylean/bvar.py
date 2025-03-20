# Keeps track of our current 'BVar -> type' mapping as we
# traverse through lambda/forall expressions.
class BVarContext:
    def __init__(self):
        self.bvars = []

    # Produces a context manager that pushes/pops a BVarData corresponding
    # to the given 'W_FunBase' expression. This is used as:
    # ```
    # with bvar_context.in_binder(expr):
    #     bvar_context.lookup(some_bvar_expr)
    # 
    # ```
    # Inside of the 'with' block, 'bvar_context.lookup' work correctly.
    # Note that since 'Bvar 0' refers to the closest binder, failing to
    # use 'in_binder' can cause the wrong BVarData to be looked up,
    # and will not necessarily fail.
    def in_binder(self, expr):
        bvar_data = BVarData(expr.binder_name, expr.binder_type)
        return BVarContextManager(self, bvar_data)

    def lookup(self, bvar):
        # BVar ids start at the closest binder and move outwards
        # A BVar id of 0 corresponds to the binder we just pushed,
        # which is at the end of the list.

        # We may try to lookup a non-existing BVar when pretty-printing
        # an expression from the table, since we won't have gone
        # through the parent lambda/forall expressions.
        if bvar.id >= len(self.bvars):
            return None
        return self.bvars[len(self.bvars) - 1 - bvar.id]

class BVarContextManager:
    def __init__(self, context, bvar_data):
        self.context = context
        self.bvar_data = bvar_data

    def __enter__(self):
        self.context.bvars.append(self.bvar_data)

    def __exit__(self, exc_type, exc_value, traceback):
        out = self.context.bvars.pop()
        if not out is self.bvar_data:
            raise Exception("BVarContextManager: popped unexpected BVarData")

class BVarData:
    def __init__(self, name, type):
        self.name = name
        self.type = type