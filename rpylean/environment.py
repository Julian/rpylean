from __future__ import print_function

import os
from sys import stderr
from time import clock
from traceback import print_exc

from rpython.rlib import rgc
from rpython.rlib.objectmodel import not_rpython, we_are_translated

from rpylean import _gcstats
from rpylean._rlib import r_dict_eq
from rpylean._tracer import StreamTracer, Tracer  # noqa: F401 (re-exported)
from rpylean.exceptions import (
    AlreadyDeclared,
    DuplicateLevels,
    MemoryExceeded,
    UndeclaredLevelParam,
    W_Error,
    W_InvalidDeclaration,
    WallTimeExceeded,
)
from rpylean.machine import acquire, release
from rpylean.objects import (
    STAGE_ALL,
    STAGE_IND_ONLY,
    STAGE_PRE_BLOCK,
    Name,
    W_CheckError,
    W_Constructor,
    W_Inductive,
    W_MemoryError,
    W_NotYetDeclared,
    W_UnsafeReference,
    W_WallTimeError,
    name_dict,
)


def _check_duplicate_levels(name, levels):
    nl = len(levels)
    if nl == 2:
        if levels[0] is levels[1]:
            raise DuplicateLevels(name, levels, levels[1])
    elif nl == 3:
        l0, l1, l2 = levels[0], levels[1], levels[2]
        if l0 is l1:
            raise DuplicateLevels(name, levels, l1)
        if l0 is l2 or l1 is l2:
            raise DuplicateLevels(name, levels, l2)
    elif nl > 3:
        seen = {}
        for level in levels:
            if level in seen:
                raise DuplicateLevels(name, levels, level)
            seen[level] = True


def _link_inductive_groups(env, declarations):
    """
    Place each inductive's constructors and recursors in its block when
    constructed programmatically via `Environment.having` (where members
    are passed as separate declarations without an explicit `group=`).
    """
    groups = env._groups
    if groups is None:
        groups = name_dict()
        env._groups = groups
    for each in declarations:
        kind = each.w_kind
        if isinstance(kind, W_Inductive):
            groups[each.name] = each.group
            for member in kind.constructors:
                member.group = each.group
            for member in kind.recursors:
                member.group = each.group
    for each in declarations:
        kind = each.w_kind
        if isinstance(kind, W_Constructor):
            group = groups.get(kind.induct, -1)
            if group >= 0:
                each.group = group


class TypeChecker(object):
    """
    The checker for one declaration: the machine reducing, inferring
    and comparing that declaration's terms, plus the per-declaration
    limits (wall time, memory) and the reference rules its position
    and safety impose.
    """

    _attrs_ = [
        'env', 'decl', 'machine',
        'declarations', 'tracer',
        'max_wall_time', 'max_memory', 'has_limits', 'def_eq_hooked', 'start_time', 'start_peak',
        '_whnf_tick', '_released', '_keep_warm', 'stage', 'allowed_levels',
    ]
    _immutable_fields_ = [
        'env', 'decl', 'machine', 'declarations', 'tracer',
        'max_wall_time', 'max_memory',
        'has_limits', 'def_eq_hooked', 'start_time', 'start_peak',
    ]

    # Mask for the wall-time sampling: `clock()` is read every 1024th
    # tick so the per-tick cost stays a counter bump and a mask test.
    _WALL_TIME_SAMPLE_MASK = 1023

    def __init__(self, env, decl, allow_warm=False):
        self.env = env
        self.decl = decl
        self.declarations = env.declarations
        self.tracer = env.tracer
        self.max_wall_time = env.max_wall_time
        self.max_memory = env.max_memory
        self.has_limits = env.max_wall_time > 0.0 or env.max_memory > 0
        self.def_eq_hooked = self.has_limits or self.tracer.recording
        self.start_time = clock() if env.max_wall_time > 0.0 else 0.0
        self.start_peak = _gcstats.peak_memory() if env.max_memory > 0 else 0
        self._whnf_tick = 0
        self._keep_warm = allow_warm
        self.machine = acquire(self, allow_warm)
        self._released = False
        self.stage = STAGE_ALL
        self.allowed_levels = decl.levels if decl is not None else None

    def check_level(self, level):
        """Verify every universe parameter in ``level`` is declared on the
        declaration currently under check."""
        if not level.has_param:
            return
        allowed = self.allowed_levels
        if allowed is None:
            return
        bad = level.check_params(allowed)
        if bad is not None:
            raise UndeclaredLevelParam(bad)

    def free(self, failed=False):
        """Release the machine once the check is over."""
        if self._released:
            return
        self._released = True
        release(self.machine, failed, self._keep_warm and not failed)

    def tick_wall_time(self):
        """
        Count a reduction step; every 1024th one, check whether
        `max_wall_time` or `max_memory` has been exceeded.
        """
        self._whnf_tick += 1
        if (self._whnf_tick & self._WALL_TIME_SAMPLE_MASK) != 0:
            return
        max_wall_time = self.max_wall_time
        max_memory = self.max_memory
        if max_wall_time <= 0.0 and max_memory <= 0:
            return
        if max_wall_time > 0.0:
            elapsed = clock() - self.start_time
            if elapsed > max_wall_time:
                raise WallTimeExceeded(
                    self.decl, elapsed, max_wall_time,
                )
        if max_memory > 0:
            # Two triggers: live heap above the cap (even a major
            # collection can't shrink below this), or this decl pushing
            # the process-wide footprint high-water mark up by more
            # than the cap (`TOTAL_MEMORY` oscillates with the major
            # collection cycle, so it alone misses footprint spikes —
            # the thing that actually drives the machine into swap).
            live = _gcstats.live_memory()
            if live > max_memory:
                raise MemoryExceeded(
                    self.decl, live, max_memory,
                )
            growth = _gcstats.peak_memory() - self.start_peak
            if growth > max_memory:
                raise MemoryExceeded(
                    self.decl, growth, max_memory,
                )

    def check_reference(self, const, target):
        """
        ``const``, occurring in the declaration under check, names the
        declaration ``target``: verify the declaration may use it.

        It may not use anything declared after it, nor itself, except
        within its own block (and only what is already in scope at the
        current stage of checking an inductive block); and it may not
        use anything less safe than it is.
        """
        current = self.decl
        if current is None:
            return
        if current.group >= 0 and target.group == current.group:
            if self.stage == STAGE_PRE_BLOCK:
                raise W_NotYetDeclared(self, const)
            if (
                self.stage == STAGE_IND_ONLY
                and not isinstance(target.w_kind, W_Inductive)
            ):
                raise W_NotYetDeclared(self, const)
        elif current.index >= 0 and target.index >= current.index:
            raise W_NotYetDeclared(self, const)
        if target.safety > current.safety:
            raise W_UnsafeReference(self, const, target.safety)

    def whnf(self, expr):
        """The weak head normal form of ``expr``."""
        machine = self.machine
        h = machine.store.import_term(expr)
        result = machine.whnf(h)
        if result == h:
            return expr
        return machine.export(result)

    def infer(self, expr):
        """The type of ``expr``, checking it along the way."""
        machine = self.machine
        return machine.export(
            machine.infer(machine.store.import_term(expr), True),
        )

    def def_eq(self, expr1, expr2):
        """Whether ``expr1`` and ``expr2`` are definitionally equal."""
        machine = self.machine
        store = machine.store
        return machine.def_eq(
            store.import_term(expr1), store.import_term(expr2),
        )


class CheckResult(object):
    """
    The outcome of type-checking a single declaration.

    `elapsed` is wall/CPU clock; `gc_elapsed` is the time the runtime
    spent in GC during this check (subtract for "real work" time);
    `bytes_allocated` is the cumulative bytes allocated by the runtime
    during the check (most of which are short-lived and reclaimed by GC);
    `live_memory` is the live heap size at the *end* of the check —
    a sequence of decls whose `live_memory` keeps climbing is
    permanently growing the working set, vs. churning through
    ephemeral allocations that the GC reclaims back to a stable
    plateau.
    `peak_growth` is how much this decl pushed the process-wide peak
    heap up: 0 means the decl fit within previously-seen high-water
    headroom; positive means the run needed *more* memory to clear it.
    """

    _attrs_ = [
        'elapsed', 'gc_elapsed', 'bytes_allocated', 'live_memory',
        'peak_growth', 'error',
    ]

    def __init__(self, elapsed, gc_elapsed, bytes_allocated, live_memory,
                 peak_growth, error):
        self.elapsed = elapsed
        self.gc_elapsed = gc_elapsed
        self.bytes_allocated = bytes_allocated
        self.live_memory = live_memory
        self.peak_growth = peak_growth
        self.error = error


class Environment(object):
    """
    A Lean environment with its declarations.
    """

    _attrs_ = [
        'declarations', 'tracer',
        'max_wall_time', 'max_memory',
        '_code_cache', '_groups',
    ]
    # `declarations` is fully immutable: the reference is set in
    # `__init__` and never reassigned (the dict's *contents* are
    # mutated as decls are parsed, but the reference isn't). The
    # limits change only at run-setup time (CLI options) or at REPL
    # command boundaries — never inside the check loop.
    _immutable_fields_ = [
        'declarations',
        'tracer?',
        'max_wall_time?',
        'max_memory?',
        '_code_cache?',
    ]

    def __init__(self, declarations, tracer=Tracer(None)):
        self.declarations = declarations
        self.tracer = tracer
        self.max_wall_time = 0.0
        self.max_memory = 0
        self._code_cache = None
        # Block name (see `W_Declaration.group_key`) -> group id, created
        # lazily when ordered registration encounters a block member.
        self._groups = None

    @not_rpython
    def __getitem__(self, value):
        name = value if isinstance(value, Name) else Name.from_str(value)
        return self.declarations[name]

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return NotImplemented
        return r_dict_eq(self.declarations, other.declarations)

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        return "<Environment with %s declarations>" % (len(self.declarations),)

    def check_name(self, name):
        """
        Lean's ``environment.check_name``: nothing may already be
        declared under ``name``.
        """
        if name in self.declarations:
            raise AlreadyDeclared(name, self.declarations)

    def register_declaration(self, decl, group=-1, ordered=True):
        """
        Validate and register ``decl`` in this environment.

        When ``ordered`` is True (export streams and `Environment.having`),
        records declaration order (`decl.index`) and block membership
        (`decl.group`), using ``group`` when the caller is registering a
        whole inductive block. Pass ``ordered=False`` when declarations
        arrive out of dependency order (e.g. demand-loaded via FFI).
        """
        env_decls = self.declarations
        dname = decl.name
        cached_dict = dname._decl_dict
        if cached_dict is not None:
            if cached_dict is env_decls or dname in env_decls:
                raise AlreadyDeclared(dname, env_decls)
        elif dname in env_decls:
            raise AlreadyDeclared(dname, env_decls)
        _check_duplicate_levels(dname, decl.levels)
        if ordered:
            self._place(decl, group)
        env_decls[dname] = decl
        dname._decl_dict = env_decls
        dname._decl_cached = decl

    def _place(self, decl, group):
        index = len(self.declarations)
        decl.index = index
        key = decl.group_key()
        if group < 0:
            if key is None:
                return
            if self._groups is None:
                self._groups = name_dict()
            group = self._groups.get(key, -1)
            if group < 0:
                group = index
        if key is not None:
            if self._groups is None:
                self._groups = name_dict()
            if key not in self._groups:
                self._groups[key] = group
        decl.group = group

    @staticmethod
    def having(declarations):
        """
        Construct an environment with the given declarations.
        """
        env = Environment(declarations=name_dict())
        has_inductive = False
        for each in declarations:
            env.register_declaration(each)
            if isinstance(each.w_kind, W_Inductive):
                has_inductive = True
        if has_inductive:
            _link_inductive_groups(env, declarations)
        return env

    def type_check(self, declarations, printer=None):
        """
        Type check each declaration, yielding only the errors.
        """
        measure = printer is not None
        for each in declarations:
            result = self.type_check_one(each, printer=printer, measure=measure)
            if result.error is not None:
                yield result.error

    def check_decl(self, decl):
        """
        Type-check a single declaration without the `CheckResult`
        bookkeeping `type_check_one` does — returns the `W_Error` (or
        ``None`` on success) directly. Convenience for tests and
        scripts that want a one-shot check; production paths should
        use `type_check_one`.
        """
        tc = TypeChecker(self, decl)
        try:
            return decl.type_check(tc)
        finally:
            tc.free()

    def type_check_one(self, decl, printer=None, measure=True):
        """
        Type check a single declaration, returning a `CheckResult`.
        """
        if printer is not None:
            printer.before(self, decl)
        allow_warm = (
            decl.index >= 0
            and decl.group < 0
            and decl.w_kind.allows_warm_cache()
            and not self.tracer.recording
            and self.max_memory == 0
        )
        result = self._run_type_check_one(
            decl, measure or printer is not None, allow_warm,
        )
        if printer is not None:
            printer.after(self, decl, result)
        return result

    def _run_type_check_one(self, decl, measure, allow_warm):
        if measure:
            gc_start = _gcstats.gc_time_seconds()
            bytes_start = _gcstats.bytes_allocated()
            peak_start = _gcstats.peak_memory()
            start = clock()
        else:
            gc_start = 0.0
            bytes_start = 0
            peak_start = 0
            start = 0.0

        tc = TypeChecker(self, decl, allow_warm=allow_warm)
        error = None
        try:
            error = decl.type_check(tc)
        except WallTimeExceeded as err:
            error = W_WallTimeError(
                decl.name,
                err.elapsed,
                err.max_wall_time,
            )
        except MemoryExceeded as err:
            error = W_MemoryError(
                decl.name,
                err.used,
                err.max_memory,
            )
        except W_CheckError as err:
            if err.name is None:
                err.name = decl.name
            error = err
        except W_Error as err:
            error = W_InvalidDeclaration(decl, err, self.declarations)
        except Exception:
            if not we_are_translated():
                print_exc(None, stderr)
                stderr.write("\nwhile checking ")
                stderr.write(decl.name.str())
                stderr.write("\n\n")
                if os.environ.get("RPYLEAN_PDB"):
                    import pdb
                    pdb.post_mortem()
            tc.free(True)
            raise
        finally:
            if measure:
                elapsed = clock() - start
                gc_elapsed = _gcstats.gc_time_seconds() - gc_start
                bytes_allocated = _gcstats.bytes_allocated() - bytes_start
            else:
                elapsed = 0.0
                gc_elapsed = 0.0
                bytes_allocated = 0
            recheck = tc.machine.recheck_on_error
            tc.free(error is not None)
        if (error is not None and recheck
                and not isinstance(error, W_WallTimeError)
                and not isinstance(error, W_MemoryError)):
            # Re-check on a clean cold machine so error diagnostics keep exact
            # binder names and original W_Expr highlight spans.
            return self._run_type_check_one(decl, measure, False)
        if isinstance(error, W_MemoryError):
            # The decl blew the memory cap: collect now so the next
            # decl starts from a shrunken heap instead of riding the
            # high-water mark into swap.
            rgc.collect()
        if measure:
            live_memory = _gcstats.live_memory()
            peak_growth = _gcstats.peak_memory() - peak_start
        else:
            live_memory = 0
            peak_growth = 0
        return CheckResult(
            elapsed, gc_elapsed, bytes_allocated, live_memory,
            peak_growth, error,
        )

    def all(self):
        """
        All declarations in the environment.
        """
        return _AllDeclarations(self.declarations)

    def only(self, names):
        """
        Yield declarations whose name is in the given collection.
        """
        if not names:
            return self.all()
        return _NamedDeclarations(self.declarations, names)

    def public(self):
        """
        All public declarations in the environment.
        """
        return self.all().public()

    def def_eq(self, expr1, expr2):
        """
        Definitional equality, with a transient `TypeChecker`.

        Each call gets its own checker, outside any declaration, so
        nothing accumulates across calls: for tests and REPL paths that
        need a single comparison. A declaration's check constructs one
        checker and uses it throughout, so its memos are scoped to the
        declaration.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.def_eq(expr1, expr2)
        finally:
            tc.free()

    def infer(self, expr):
        """
        Type inference, with a transient `TypeChecker`. See `def_eq`.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.infer(expr)
        finally:
            tc.free()

    def whnf(self, expr):
        """
        Weak head normal form, with a transient `TypeChecker`. See
        `def_eq`.
        """
        tc = TypeChecker(self, None)
        try:
            return tc.whnf(expr)
        finally:
            tc.free()


#: The empty environment.
Environment.EMPTY = Environment.having([])


class _Declarations(object):
    _attrs_ = []

    def __iter__(self):
        return self

    def public(self):
        return _PublicDeclarations(self)


class _AllDeclarations(_Declarations):
    _attrs_ = ['declarations', 'iter']

    def __init__(self, declarations):
        self.declarations = declarations
        self.iter = iter(self.declarations.itervalues())

    def next(self):
        return next(self.iter)


class _NamedDeclarations(_Declarations):
    _attrs_ = ['declarations', 'names', 'iter']

    def __init__(self, declarations, names):
        self.declarations = declarations
        self.names = names
        self.iter = iter(self.names)

    def next(self):
        name = next(self.iter)
        assert name in self.declarations, name.str()
        return self.declarations[name]


class _PublicDeclarations(_Declarations):
    _attrs_ = ['iter']

    def __init__(self, iterator):
        self.iter = iterator

    def next(self):
        for declaration in self.iter:
            if declaration.name.is_private:
                continue
            return declaration
        raise StopIteration
