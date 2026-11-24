"""
The recursors an inductive block gives rise to.

A recursor is not taken on an export's word: its type, its universe of
elimination, its rules and whether it admits K-like reduction all
follow from the inductive types and their constructors alone, and a
recursor which differs from what they determine can prove `False`.
This module constructs, from a block's types and constructors, the
recursors the block must have, for a declared recursor to be compared
against.

A nested occurrence of the block (`List T` within a constructor of
`T`) makes the applied container a further member of the block, with
the container's constructors, instantiated, as that member's
constructors. Members found this way get the recursors `T.rec_1`,
`T.rec_2`, … in order of discovery.
"""

from rpython.rlib.objectmodel import r_dict

from rpylean.objects import (
    Binder,
    Name,
    STAGE_ALL,
    STAGE_IND_ONLY,
    STAGE_PRE_BLOCK,
    W_App,
    W_BVar,
    W_CheckError,
    W_Const,
    W_Constructor,
    W_ConstructorFieldCountMismatch,
    W_ForAll,
    W_FVar,
    W_FunBase,
    W_Inductive,
    W_InvalidConstructorResult,
    W_Lambda,
    W_Let,
    W_NonPositiveOccurrence,
    W_NotASort,
    W_Proj,
    W_RecRule,
    W_Sort,
    W_UniverseTooHigh,
    W_LEVEL_ZERO,
    MESSAGE,
    _COW_FLAG,
    _error_diagnostic,
    _mk_w_bvar,
    _mk_w_forall,
    _mk_w_lambda,
    _next_cache_gen,
    _decl_visible,
    get_decl,
    find_decl,
    name_dict,
    syntactic_eq,
)


class W_InvalidInductive(W_CheckError):
    """
    An inductive block is one no recursor can be constructed for.
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
            "Invalid inductive ", message, declarations,
        )


_OPT_PARAM = Name.simple("optParam")
_AUTO_PARAM = Name.simple("autoParam")
_OUT_PARAM = Name.simple("outParam")
_SEMI_OUT_PARAM = Name.simple("semiOutParam")


def _consume_type_annotations(type):
    """``type`` without any `optParam`, `autoParam` or `outParam` at its head."""
    while isinstance(type, W_App):
        fn = type.fn
        if isinstance(fn, W_App):
            head = fn.fn
            if isinstance(head, W_Const) and (
                head.name.syntactic_eq(_OPT_PARAM)
                or head.name.syntactic_eq(_AUTO_PARAM)
            ):
                type = fn.arg
                continue
            return type
        if isinstance(fn, W_Const) and (
            fn.name.syntactic_eq(_OUT_PARAM)
            or fn.name.syntactic_eq(_SEMI_OUT_PARAM)
        ):
            type = type.arg
            continue
        return type
    return type


def _local_for(binder):
    """A free variable standing for what ``binder`` binds."""
    type = _consume_type_annotations(binder.type)
    if type is not binder.type:
        binder = binder.with_type(type)
    return binder.fvar()


def _local(name, type):
    return Binder.default(Name.simple(name), type).fvar()


def _expr_is(a, b):
    return a is b


def _expr_id_hash(a):
    return a.hash()


def _expr_depth_eq(a, b):
    return a[0] is b[0] and a[1] == b[1]


def _expr_depth_hash(a):
    return (a[0].hash() * 1000003) ^ a[1]


def _expr_pair_eq(a, b):
    return a[0] is b[0] and a[1] is b[1]


def _expr_pair_hash(a):
    return (a[0].hash() * 1000003) ^ a[1].hash()


class _DepthMemo(object):
    """Intrusive `W_Expr._cache` memo keyed by `(expr, depth)`: avoids `r_dict`,
    2-tuple keys, and GC identity-hash shadow allocations on the common
    single-depth path, falling back to `r_dict` only on multi-depth DAG
    collisions or cache-generation exhaustion."""

    _attrs_ = ['base_gen', 'gens', 'results', 'overflow']

    def __init__(self):
        self.base_gen = 0
        self.gens = []
        self.results = []
        self.overflow = None
        self.reset()

    def reset(self):
        g0 = 0 if _COW_FLAG.enabled else _next_cache_gen()
        self.base_gen = g0
        del self.gens[:]
        self.gens.append(g0)
        del self.results[:]
        self.overflow = None

    def gen(self, depth):
        if self.base_gen <= 0:
            return -1
        gens = self.gens
        while depth >= len(gens):
            gens.append(0)
        g = gens[depth]
        if g == 0:
            g = _next_cache_gen()
            gens[depth] = g
        return g

    def put_overflow(self, expr, depth, res):
        ov = self.overflow
        if ov is None:
            ov = self.overflow = r_dict(_expr_depth_eq, _expr_depth_hash)
        ov[(expr, depth)] = res


def _bind_fvars_prefix(expr, fvar_idx, limit, depth, dgen, memo):
    """DAG-memoized substitution of `fvars[0..limit-1]` with de Bruijn indices
    starting at ``depth`` (innermost `fvars[limit-1]` -> ``depth``)."""
    if limit <= 0 or not expr.has_fvar():
        return expr
    if isinstance(expr, W_FVar):
        k = fvar_idx.get(expr.id, -1)
        if 0 <= k < limit:
            return _mk_w_bvar(depth + limit - 1 - k)
        return expr
    if dgen > 0:
        c = expr._cache
        cg = c >> 32
        if cg == dgen:
            return memo.results[c & 0xFFFFFFFF]
        if cg >= memo.base_gen and memo.overflow is not None:
            cached = memo.overflow.get((expr, depth), None)
            if cached is not None:
                return cached
    elif memo.overflow is not None:
        cached = memo.overflow.get((expr, depth), None)
        if cached is not None:
            return cached
    if isinstance(expr, W_App):
        new_fn = _bind_fvars_prefix(expr.fn, fvar_idx, limit, depth, dgen, memo)
        new_arg = _bind_fvars_prefix(expr.arg, fvar_idx, limit, depth, dgen, memo)
        if new_fn is expr.fn and new_arg is expr.arg:
            res = expr
        else:
            res = new_fn.app(new_arg)
    elif isinstance(expr, W_ForAll):
        new_bt = _bind_fvars_prefix(expr.type, fvar_idx, limit, depth, dgen, memo)
        ndepth = depth + 1
        ndgen = memo.gen(ndepth)
        new_body = _bind_fvars_prefix(
            expr.body, fvar_idx, limit, ndepth, ndgen, memo,
        )
        if new_bt is expr.type and new_body is expr.body:
            res = expr
        else:
            res = expr._rebuild(new_bt, new_body)
    elif isinstance(expr, W_Lambda):
        new_bt = _bind_fvars_prefix(expr.type, fvar_idx, limit, depth, dgen, memo)
        ndepth = depth + 1
        ndgen = memo.gen(ndepth)
        new_body = _bind_fvars_prefix(
            expr.body, fvar_idx, limit, ndepth, ndgen, memo,
        )
        if new_bt is expr.type and new_body is expr.body:
            res = expr
        else:
            res = expr._rebuild(new_bt, new_body)
    elif isinstance(expr, W_Let):
        new_type = _bind_fvars_prefix(expr.type, fvar_idx, limit, depth, dgen, memo)
        new_val = _bind_fvars_prefix(expr.value, fvar_idx, limit, depth, dgen, memo)
        ndepth = depth + 1
        ndgen = memo.gen(ndepth)
        new_body = _bind_fvars_prefix(
            expr.body, fvar_idx, limit, ndepth, ndgen, memo,
        )
        if (new_type is expr.type
                and new_val is expr.value
                and new_body is expr.body):
            res = expr
        else:
            res = expr.name.let(type=new_type, value=new_val, body=new_body)
    elif isinstance(expr, W_Proj):
        new_se = _bind_fvars_prefix(
            expr.struct_expr, fvar_idx, limit, depth, dgen, memo,
        )
        res = expr if new_se is expr.struct_expr else expr.with_expr(new_se)
    else:
        res = expr
    if dgen > 0:
        cg = expr._cache >> 32
        if cg < memo.base_gen:
            idx = len(memo.results)
            memo.results.append(res)
            expr._cache = (dgen << 32) | idx
        elif cg != dgen:
            memo.put_overflow(expr, depth, res)
    else:
        memo.put_overflow(expr, depth, res)
    return res


def _inst_multi_dag_rec(expr, vals, nvals, all_closed, depth, dgen, memo):
    if expr.loose_bvar_range() <= depth:
        return expr
    if isinstance(expr, W_BVar):
        rel = expr.id - depth
        if rel < nvals:
            sub = vals[nvals - 1 - rel]
            if depth > 0 and not all_closed and sub.loose_bvar_range() > 0:
                return sub.incr_free_bvars(depth, 0)
            return sub
        return _mk_w_bvar(expr.id - nvals)
    if dgen > 0:
        c = expr._cache
        cg = c >> 32
        if cg == dgen:
            return memo.results[c & 0xFFFFFFFF]
        if cg >= memo.base_gen and memo.overflow is not None:
            cached = memo.overflow.get((expr, depth), None)
            if cached is not None:
                return cached
    elif memo.overflow is not None:
        cached = memo.overflow.get((expr, depth), None)
        if cached is not None:
            return cached
    if isinstance(expr, W_App):
        new_fn = _inst_multi_dag_rec(
            expr.fn, vals, nvals, all_closed, depth, dgen, memo,
        )
        new_arg = _inst_multi_dag_rec(
            expr.arg, vals, nvals, all_closed, depth, dgen, memo,
        )
        if new_fn is expr.fn and new_arg is expr.arg:
            res = expr
        else:
            res = new_fn.app(new_arg)
    elif isinstance(expr, W_ForAll):
        new_bt = _inst_multi_dag_rec(
            expr.type, vals, nvals, all_closed, depth, dgen, memo,
        )
        ndepth = depth + 1
        ndgen = memo.gen(ndepth)
        new_body = _inst_multi_dag_rec(
            expr.body, vals, nvals, all_closed, ndepth, ndgen, memo,
        )
        if new_bt is expr.type and new_body is expr.body:
            res = expr
        else:
            res = expr._rebuild(new_bt, new_body)
    elif isinstance(expr, W_Lambda):
        new_bt = _inst_multi_dag_rec(
            expr.type, vals, nvals, all_closed, depth, dgen, memo,
        )
        ndepth = depth + 1
        ndgen = memo.gen(ndepth)
        new_body = _inst_multi_dag_rec(
            expr.body, vals, nvals, all_closed, ndepth, ndgen, memo,
        )
        if new_bt is expr.type and new_body is expr.body:
            res = expr
        else:
            res = expr._rebuild(new_bt, new_body)
    elif isinstance(expr, W_Let):
        new_type = _inst_multi_dag_rec(
            expr.type, vals, nvals, all_closed, depth, dgen, memo,
        )
        new_val = _inst_multi_dag_rec(
            expr.value, vals, nvals, all_closed, depth, dgen, memo,
        )
        ndepth = depth + 1
        ndgen = memo.gen(ndepth)
        new_body = _inst_multi_dag_rec(
            expr.body, vals, nvals, all_closed, ndepth, ndgen, memo,
        )
        if (new_type is expr.type
                and new_val is expr.value
                and new_body is expr.body):
            res = expr
        else:
            res = expr.name.let(type=new_type, value=new_val, body=new_body)
    elif isinstance(expr, W_Proj):
        new_se = _inst_multi_dag_rec(
            expr.struct_expr, vals, nvals, all_closed, depth, dgen, memo,
        )
        res = expr if new_se is expr.struct_expr else expr.with_expr(new_se)
    else:
        res = expr
    if dgen > 0:
        cg = expr._cache >> 32
        if cg < memo.base_gen:
            idx = len(memo.results)
            memo.results.append(res)
            expr._cache = (dgen << 32) | idx
        elif cg != dgen:
            memo.put_overflow(expr, depth, res)
    else:
        memo.put_overflow(expr, depth, res)
    return res


def _instantiate_multi_dag(expr, vals):
    """Simultaneously instantiate outer bound variables `BVar(n-1)..BVar(0)`
    with `vals[0..n-1]` (outermost first) in a single DAG pass."""
    nvals = len(vals)
    if nvals == 0 or expr.loose_bvar_range() == 0:
        return expr
    if isinstance(expr, W_BVar):
        if expr.id < nvals:
            return vals[nvals - 1 - expr.id]
        return _mk_w_bvar(expr.id - nvals)
    all_closed = True
    for v in vals:
        if v.loose_bvar_range() > 0:
            all_closed = False
            break
    memo = _DepthMemo()
    return _inst_multi_dag_rec(
        expr, vals, nvals, all_closed, 0, memo.base_gen, memo,
    )


def _instantiate_dag(expr, val):
    if expr.loose_bvar_range() == 0:
        return expr
    return _instantiate_multi_dag(expr, [val])


def _mk_pi(fvars, body):
    n = len(fvars)
    if n == 0:
        return body
    fvar_idx = {}
    for i in range(n):
        fvar = fvars[i]
        assert isinstance(fvar, W_FVar)
        fvar_idx[fvar.id] = i
    memo = _DepthMemo()
    body = _bind_fvars_prefix(body, fvar_idx, n, 0, memo.base_gen, memo)
    i = n - 1
    while i >= 0:
        fvar = fvars[i]
        assert isinstance(fvar, W_FVar)
        binder = fvar.binder
        if i > 0 and binder.type.has_fvar():
            memo.reset()
            new_type = _bind_fvars_prefix(
                binder.type, fvar_idx, i, 0, memo.base_gen, memo,
            )
            if new_type is not binder.type:
                binder = binder.with_type(new_type)
        body = _mk_w_forall(binder, body)
        i -= 1
    return body


def _mk_lambda(fvars, body):
    n = len(fvars)
    if n == 0:
        return body
    fvar_idx = {}
    for i in range(n):
        fvar = fvars[i]
        assert isinstance(fvar, W_FVar)
        fvar_idx[fvar.id] = i
    memo = _DepthMemo()
    body = _bind_fvars_prefix(body, fvar_idx, n, 0, memo.base_gen, memo)
    i = n - 1
    while i >= 0:
        fvar = fvars[i]
        assert isinstance(fvar, W_FVar)
        binder = fvar.binder
        if i > 0 and binder.type.has_fvar():
            memo.reset()
            new_type = _bind_fvars_prefix(
                binder.type, fvar_idx, i, 0, memo.base_gen, memo,
            )
            if new_type is not binder.type:
                binder = binder.with_type(new_type)
        body = _mk_w_lambda(binder, body)
        i -= 1
    return body


def _mk_app(fn, args):
    for each in args:
        fn = fn.app(each)
    return fn


def _args_of(expr):
    """The head and (in order) the arguments of an application."""
    head, args = expr.unapp()
    args.reverse()
    return head, args


def _take(args, n):
    assert n >= 0
    return args[:n]


def _drop(args, n):
    assert n >= 0
    return args[n:]


def _levels_eq(levels, others):
    if len(levels) != len(others):
        return False
    for i in range(len(levels)):
        if not syntactic_eq(levels[i], others[i]):
            return False
    return True


class _AlphaMemo(object):
    """Intrusive `a._cache` memo for `alpha_eq`: stores each left node's first
    proven alpha-equal partner in a flat list, spilling to `r_dict` only if
    the same left node is paired with multiple distinct right nodes."""

    _attrs_ = ['gen', 'partners', 'overflow']

    def __init__(self):
        self.gen = 0 if _COW_FLAG.enabled else _next_cache_gen()
        self.partners = []
        self.overflow = None

    def put_overflow(self, a, b):
        ov = self.overflow
        if ov is None:
            ov = self.overflow = r_dict(_expr_pair_eq, _expr_pair_hash)
        ov[(a, b)] = True


def _alpha_eq_memo(a, b, memo):
    gen = memo.gen
    partners = memo.partners
    keys_a = None
    keys_b = None
    while True:
        if a is b:
            ok = True
            break
        if a.__class__ is not b.__class__:
            return False
        if gen > 0:
            c = a._cache
            if (c >> 32) == gen:
                if partners[c & 0xFFFFFFFF] is b:
                    ok = True
                    break
                if memo.overflow is not None and (a, b) in memo.overflow:
                    ok = True
                    break
        elif memo.overflow is not None and (a, b) in memo.overflow:
            ok = True
            break
        if keys_a is None:
            keys_a = [a]
            keys_b = [b]
        else:
            keys_a.append(a)
            keys_b.append(b)
        if isinstance(a, W_App):
            assert isinstance(b, W_App)
            if not _alpha_eq_memo(a.arg, b.arg, memo):
                return False
            a = a.fn
            b = b.fn
        elif isinstance(a, W_FunBase):
            assert isinstance(b, W_FunBase)
            if not _alpha_eq_memo(a.type, b.type, memo):
                return False
            a = a.body
            b = b.body
        elif isinstance(a, W_Let):
            assert isinstance(b, W_Let)
            if not _alpha_eq_memo(a.type, b.type, memo):
                return False
            if not _alpha_eq_memo(a.value, b.value, memo):
                return False
            a = a.body
            b = b.body
        elif isinstance(a, W_Proj):
            assert isinstance(b, W_Proj)
            if a.field_index != b.field_index:
                return False
            if not a.struct_name.syntactic_eq(b.struct_name):
                return False
            a = a.struct_expr
            b = b.struct_expr
        else:
            ok = syntactic_eq(a, b)
            break
    if ok and keys_a is not None:
        assert keys_b is not None
        i = 0
        nk = len(keys_a)
        while i < nk:
            ka = keys_a[i]
            kb = keys_b[i]
            if gen > 0:
                c = ka._cache
                if (c >> 32) != gen:
                    idx = len(partners)
                    partners.append(kb)
                    ka._cache = (gen << 32) | idx
                elif partners[c & 0xFFFFFFFF] is not kb:
                    memo.put_overflow(ka, kb)
            else:
                memo.put_overflow(ka, kb)
            i += 1
    return ok


def alpha_eq(a, b):
    """Whether two expressions differ at most in how binders are written."""
    if a is b:
        return True
    return _alpha_eq_memo(a, b, _AlphaMemo())


class _Member(object):
    """
    A type of the block: one being declared, applied to the block's
    parameters, or a container some member occurs nested within,
    applied to the arguments it occurs at.
    """

    _attrs_ = [
        'decl', 'kind', 'name', 'levels', 'args', 'rec_name',
        'ctors', 'indices', 'major', 'motive',
    ]

    def __init__(self, decl, levels, args, rec_name):
        kind = decl.w_kind
        assert isinstance(kind, W_Inductive)
        self.decl = decl
        self.kind = kind
        self.name = decl.name
        self.levels = levels
        self.args = args
        self.rec_name = rec_name
        self.ctors = []
        self.indices = []
        self.major = None
        self.motive = None

    def const(self):
        return self.name.const(self.levels)


class _Ctor(object):
    """A constructor of a member, its type instantiated at the member."""

    _attrs_ = [
        'decl', 'name', 'levels', 'type', 'fields',
        'rec_fields', 'rec_xs', 'rec_member', 'rec_indices',
        'result_indices',
    ]

    def __init__(self, decl, levels, type):
        self.decl = decl
        self.name = decl.name
        self.levels = levels
        self.type = type
        self.fields = []
        #: For each recursive field: the field, the variables its type
        #: quantifies over, and the member and indices it lands in.
        self.rec_fields = []
        self.rec_xs = []
        self.rec_member = []
        self.rec_indices = []
        self.result_indices = []


class RecursorSpec(object):
    """A recursor as its inductive block determines it."""

    _attrs_ = [
        'name', 'elim_name', 'type', 'rules', 'k',
        'num_params', 'num_indices', 'num_motives', 'num_minors',
    ]

    def __init__(self, name, elim_name, type, rules, k,
                 num_params, num_indices, num_motives, num_minors):
        self.name = name
        #: The universe parameter eliminated into, or None for a
        #: recursor which eliminates only into `Prop`.
        self.elim_name = elim_name
        self.type = type
        self.rules = rules
        self.k = k
        self.num_params = num_params
        self.num_indices = num_indices
        self.num_motives = num_motives
        self.num_minors = num_minors


_OCC_KNOWN = 1
_OCC_TRUE = 2
_UNIFORM_SEEN = 4
_NESTED_SEEN = 8


class _Block(object):
    _attrs_ = [
        'tc', 'env', 'first', 'first_kind', 'num_params', 'unsafe',
        'level_names', 'levels', 'params', 'members', 'num_declared',
        'result_level', 'elim_name', 'elim_level', '_occ_gen',
    ]

    def __init__(self, first, tc):
        self.tc = tc
        self.env = tc.env
        self.first = first
        kind = first.w_kind
        assert isinstance(kind, W_Inductive)
        self.first_kind = kind
        self.num_params = kind.num_params
        self.unsafe = first.is_unsafe()
        self.level_names = first.levels
        self.levels = [each.as_level_param() for each in first.levels]
        self.params = []
        self.members = []
        self.num_declared = 0
        self.result_level = W_LEVEL_ZERO
        self.elim_name = None
        self.elim_level = W_LEVEL_ZERO
        self._occ_gen = 0 if _COW_FLAG.enabled else _next_cache_gen()

    def fail(self, summary):
        return W_InvalidInductive(self.env, summary)

    # -- the block's members ------------------------------------------

    def is_declared_name(self, name):
        for i in range(self.num_declared):
            if self.members[i].name.syntactic_eq(name):
                return True
        return False

    def _has_occurrence_memo(self, expr, seen):
        if expr in seen:
            return False
        if isinstance(expr, W_Const):
            if self.is_declared_name(expr.name):
                return True
        elif isinstance(expr, W_App):
            if (self._has_occurrence_memo(expr.fn, seen)
                    or self._has_occurrence_memo(expr.arg, seen)):
                return True
        elif isinstance(expr, W_FunBase):
            if (self._has_occurrence_memo(expr.type, seen)
                    or self._has_occurrence_memo(expr.body, seen)):
                return True
        elif isinstance(expr, W_Let):
            if (self._has_occurrence_memo(expr.type, seen)
                    or self._has_occurrence_memo(expr.value, seen)
                    or self._has_occurrence_memo(expr.body, seen)):
                return True
        elif isinstance(expr, W_Proj):
            if self._has_occurrence_memo(expr.struct_expr, seen):
                return True
        seen[expr] = True
        return False

    def _has_occurrence_gen(self, expr, gen):
        c = expr._cache
        if (c >> 32) == gen and (c & _OCC_KNOWN) != 0:
            return (c & _OCC_TRUE) != 0
        found = False
        if isinstance(expr, W_Const):
            found = self.is_declared_name(expr.name)
        elif isinstance(expr, W_App):
            found = (
                self._has_occurrence_gen(expr.fn, gen)
                or self._has_occurrence_gen(expr.arg, gen)
            )
        elif isinstance(expr, W_FunBase):
            found = (
                self._has_occurrence_gen(expr.type, gen)
                or self._has_occurrence_gen(expr.body, gen)
            )
        elif isinstance(expr, W_Let):
            found = (
                self._has_occurrence_gen(expr.type, gen)
                or self._has_occurrence_gen(expr.value, gen)
                or self._has_occurrence_gen(expr.body, gen)
            )
        elif isinstance(expr, W_Proj):
            found = self._has_occurrence_gen(expr.struct_expr, gen)
        old = expr._cache
        bits = (old & (_UNIFORM_SEEN | _NESTED_SEEN)) if (old >> 32) == gen else 0
        expr._cache = (gen << 32) | bits | _OCC_KNOWN | (_OCC_TRUE if found else 0)
        return found

    def has_occurrence(self, expr):
        """Whether ``expr`` mentions a type being declared."""
        gen = self._occ_gen
        if gen > 0:
            return self._has_occurrence_gen(expr, gen)
        return self._has_occurrence_memo(expr, r_dict(_expr_is, _expr_id_hash))

    def collect_members(self):
        declarations = self.tc.declarations
        all = self.first_kind.all
        if not all or not all[0].syntactic_eq(self.first.name):
            raise self.fail("the block does not begin with its first type")
        for name in all:
            decl = get_decl(declarations, name)
            if not _decl_visible(self.first, decl):
                raise self.fail("%s is not declared" % name.str())
            kind = decl.w_kind
            if not isinstance(kind, W_Inductive):
                raise self.fail("%s is not an inductive type" % name.str())
            if decl.safety != self.first.safety:
                raise self.fail(
                    "the types of the block differ in safety",
                )
            if kind.num_params != self.num_params:
                raise self.fail(
                    "the types of the block differ in their number of "
                    "parameters",
                )
            if len(kind.all) != len(all):
                raise self.fail("the types of the block disagree on it")
            for i in range(len(all)):
                if not kind.all[i].syntactic_eq(all[i]):
                    raise self.fail("the types of the block disagree on it")
            if len(decl.levels) != len(self.level_names):
                raise self.fail(
                    "the types of the block differ in universe parameters",
                )
            for i in range(len(decl.levels)):
                if not decl.levels[i].syntactic_eq(self.level_names[i]):
                    raise self.fail(
                        "the types of the block differ in universe "
                        "parameters",
                    )
            self.members.append(
                _Member(decl, self.levels, [], name.child("rec")),
            )
        self.num_declared = len(self.members)

        tc = self.tc
        tc.stage = STAGE_PRE_BLOCK
        prev_levels = tc.allowed_levels
        tc.allowed_levels = self.level_names
        try:
            for i in range(self.num_declared):
                decl_type = self.members[i].decl.type
                if self.first.group < 0 and self.has_occurrence(decl_type):
                    raise self.fail(
                        "the type of an inductive may not mention the "
                        "types being declared",
                    )
                inferred = decl_type.infer(tc)
                if not isinstance(inferred.whnf(tc), W_Sort):
                    raise W_NotASort(
                        tc, decl_type, inferred_type=inferred,
                    )
        finally:
            tc.allowed_levels = prev_levels
            tc.stage = STAGE_ALL

        cur = self.first.type
        pending = []
        for _ in range(self.num_params):
            if not isinstance(cur, W_ForAll):
                if pending:
                    cur = _instantiate_multi_dag(cur, pending)
                    del pending[:]
                cur = cur.whnf(self.tc)
            if not isinstance(cur, W_ForAll):
                raise self.fail("the type has fewer binders than parameters")
            binder = cur.get_binder()
            if pending:
                btype = _instantiate_multi_dag(binder.type, pending)
                if btype is not binder.type:
                    binder = binder.with_type(btype)
            param = _local_for(binder)
            self.params.append(param)
            pending.append(param)
            cur = cur.body
        for i in range(self.num_declared):
            self.members[i].args = self.params

        qhead = 0
        while qhead < len(self.members):
            member = self.members[qhead]
            declared = qhead < self.num_declared
            substs = None
            if not declared:
                substs = {}
                names = member.decl.levels
                for i in range(len(names)):
                    substs[names[i]] = member.levels[i]
            seen_ctors = name_dict()
            for ctor_name in member.kind.ctor_names:
                if declared:
                    if ctor_name in seen_ctors:
                        raise self.fail(
                            "duplicate constructor %s" % ctor_name.str(),
                        )
                    seen_ctors[ctor_name] = True
                ctor_decl = get_decl(declarations, ctor_name)
                if declared and not _decl_visible(self.first, ctor_decl):
                    raise self.fail("%s is not declared" % ctor_name.str())
                ctor_kind = ctor_decl.w_kind
                if not isinstance(ctor_kind, W_Constructor):
                    raise self.fail(
                        "%s is not a constructor" % ctor_name.str(),
                    )
                if declared:
                    if ctor_decl.safety != self.first.safety:
                        raise self.fail(
                            "%s differs in safety from its inductive"
                            % ctor_name.str(),
                        )
                    if (
                        not ctor_kind.induct.is_anonymous()
                        and not ctor_kind.induct.syntactic_eq(member.name)
                    ):
                        raise W_InvalidConstructorResult(
                            self.env, ctor_decl.type,
                        )
                    if ctor_kind.num_params != self.num_params:
                        raise W_InvalidConstructorResult(
                            self.env, ctor_decl.type,
                        )
                    if len(ctor_decl.levels) != len(self.level_names):
                        raise W_InvalidConstructorResult(
                            self.env, ctor_decl.type,
                        )
                    for i in range(len(ctor_decl.levels)):
                        if not ctor_decl.levels[i].syntactic_eq(
                            self.level_names[i]
                        ):
                            raise W_InvalidConstructorResult(
                                self.env, ctor_decl.type,
                            )
                type = ctor_decl.type
                if substs is not None:
                    type = type.subst_levels(substs)
                nargs = len(member.args)
                cur = type
                peeled = 0
                while peeled < nargs and isinstance(cur, W_ForAll):
                    cur = cur.body
                    peeled += 1
                if peeled == nargs:
                    type = (
                        _instantiate_multi_dag(cur, member.args)
                        if nargs > 0 else cur
                    )
                else:
                    type = (
                        _instantiate_multi_dag(cur, member.args[:peeled])
                        if peeled > 0 else cur
                    )
                    for idx_a in range(peeled, nargs):
                        if not isinstance(type, W_ForAll):
                            if declared:
                                raise W_InvalidConstructorResult(
                                    self.env, ctor_decl.type,
                                )
                            raise self.fail(
                                "%s has fewer binders than parameters"
                                % ctor_name.str(),
                            )
                        type = _instantiate_dag(type.body, member.args[idx_a])
                occ_gen = self._occ_gen
                if declared:
                    self.check_uniform_occurrences(
                        type, ctor_decl.type,
                        None if occ_gen > 0 else r_dict(_expr_is, _expr_id_hash),
                    )
                self.find_nested(
                    type,
                    None if occ_gen > 0 else r_dict(_expr_is, _expr_id_hash),
                )
                member.ctors.append(_Ctor(ctor_decl, member.levels, type))
            qhead += 1

    def check_uniform_occurrences(self, expr, ctor_type, seen):
        """
        Every occurrence of a type being declared must be applied to
        the block's universe levels and parameters.
        """
        if seen is None:
            gen = self._occ_gen
            c = expr._cache
            if (c >> 32) == gen:
                if (c & _UNIFORM_SEEN) != 0:
                    return
                expr._cache = c | _UNIFORM_SEEN
            else:
                expr._cache = (gen << 32) | _UNIFORM_SEEN
        else:
            if expr in seen:
                return
            seen[expr] = True
        if isinstance(expr, W_App) or isinstance(expr, W_Const):
            head, args = _args_of(expr)
            if isinstance(head, W_Const) and self.is_declared_name(head.name):
                ok = (
                    len(args) >= self.num_params
                    and _levels_eq(head.levels, self.levels)
                )
                if ok:
                    for i in range(self.num_params):
                        if args[i] is not self.params[i]:
                            ok = False
                            break
                if not ok:
                    raise W_InvalidConstructorResult(self.env, ctor_type)
                for i in range(self.num_params, len(args)):
                    self.check_uniform_occurrences(args[i], ctor_type, seen)
                return
            if not isinstance(head, W_Const):
                self.check_uniform_occurrences(head, ctor_type, seen)
            for each in args:
                self.check_uniform_occurrences(each, ctor_type, seen)
        elif isinstance(expr, W_FunBase):
            self.check_uniform_occurrences(expr.type, ctor_type, seen)
            self.check_uniform_occurrences(expr.body, ctor_type, seen)
        elif isinstance(expr, W_Let):
            self.check_uniform_occurrences(expr.type, ctor_type, seen)
            self.check_uniform_occurrences(expr.value, ctor_type, seen)
            self.check_uniform_occurrences(expr.body, ctor_type, seen)
        elif isinstance(expr, W_Proj):
            self.check_uniform_occurrences(expr.struct_expr, ctor_type, seen)

    def find_nested(self, expr, seen):
        """Add a member for each container the block occurs nested in."""
        if seen is None:
            gen = self._occ_gen
            c = expr._cache
            if (c >> 32) == gen:
                if (c & _NESTED_SEEN) != 0:
                    return
                expr._cache = c | _NESTED_SEEN
            else:
                expr._cache = (gen << 32) | _NESTED_SEEN
        else:
            if expr in seen:
                return
            seen[expr] = True
        if isinstance(expr, W_App):
            if self.add_if_nested(expr):
                return
            self.find_nested(expr.fn, seen)
            self.find_nested(expr.arg, seen)
        elif isinstance(expr, W_FunBase):
            self.find_nested(expr.type, seen)
            self.find_nested(expr.body, seen)
        elif isinstance(expr, W_Let):
            self.find_nested(expr.type, seen)
            self.find_nested(expr.value, seen)
            self.find_nested(expr.body, seen)
        elif isinstance(expr, W_Proj):
            self.find_nested(expr.struct_expr, seen)

    def add_if_nested(self, expr):
        head, args = _args_of(expr)
        if not isinstance(head, W_Const):
            return False
        if self.is_declared_name(head.name):
            return False
        decl = find_decl(self.tc.declarations, head.name)
        if decl is None:
            return False
        if self.first.index >= 0 and decl.index >= self.first.index:
            return False
        kind = decl.w_kind
        if not isinstance(kind, W_Inductive):
            return False
        num_params = kind.num_params
        if num_params > len(args):
            return False
        nested = False
        loose = False
        for i in range(num_params):
            if args[i].loose_bvar_range() > 0:
                loose = True
            if self.has_occurrence(args[i]):
                nested = True
        if not nested:
            return False
        if loose:
            raise self.fail(
                "the parameters %s is nested at mention local variables"
                % head.name.str(),
            )
        container_args = _take(args, num_params)
        if self.find_member(head, container_args) >= 0:
            return True
        if len(head.levels) != len(decl.levels):
            raise self.fail(
                "%s occurs at the wrong number of universe levels"
                % head.name.str(),
            )
        declarations = self.tc.declarations
        for name in kind.all:
            sibling = get_decl(declarations, name)
            if not isinstance(sibling.w_kind, W_Inductive):
                raise self.fail("%s is not an inductive type" % name.str())
            index = len(self.members) - self.num_declared + 1
            rec_name = self.first.name.child("rec_%d" % index)
            self.members.append(
                _Member(sibling, head.levels, container_args, rec_name),
            )
        return True

    def find_member(self, head, args):
        """The index of the member which is ``head`` applied to ``args``."""
        for i in range(len(self.members)):
            member = self.members[i]
            if not member.name.syntactic_eq(head.name):
                continue
            if not _levels_eq(member.levels, head.levels):
                continue
            if len(member.args) != len(args):
                continue
            same = True
            for j in range(len(args)):
                if not alpha_eq(member.args[j], args[j]):
                    same = False
                    break
            if same:
                return i
        return -1

    def valid_app(self, expr):
        """
        The index of the member ``expr`` is a full application of, its
        indices free of the types being declared, or -1.
        """
        head, args = _args_of(expr)
        if not isinstance(head, W_Const):
            return -1
        for i in range(len(self.members)):
            member = self.members[i]
            num_args = len(member.args)
            if len(args) != num_args + len(member.indices):
                continue
            if self.find_member(head, _take(args, num_args)) != i:
                continue
            for j in range(num_args, len(args)):
                if self.has_occurrence(args[j]):
                    return -1
            return i
        return -1

    # -- the types ----------------------------------------------------

    def check_types(self):
        for i in range(len(self.members)):
            member = self.members[i]
            type = member.decl.type
            if i >= self.num_declared:
                substs = {}
                names = member.decl.levels
                for j in range(len(names)):
                    substs[names[j]] = member.levels[j]
                type = type.subst_levels(substs)
            cur = type
            pending = []
            for arg in member.args:
                if not isinstance(cur, W_ForAll):
                    if pending:
                        cur = _instantiate_multi_dag(cur, pending)
                        del pending[:]
                    cur = cur.whnf(self.tc)
                if not isinstance(cur, W_ForAll):
                    raise self.fail(
                        "%s has fewer binders than parameters"
                        % member.name.str(),
                    )
                if 0 < i < self.num_declared:
                    assert isinstance(arg, W_FVar)
                    dom = (
                        _instantiate_multi_dag(cur.type, pending)
                        if pending else cur.type
                    )
                    if not self.tc.def_eq(
                        _consume_type_annotations(dom),
                        arg.binder.type,
                    ):
                        raise self.fail(
                            "the types of the block differ in parameter types",
                        )
                pending.append(arg)
                cur = cur.body
            type = _instantiate_multi_dag(cur, pending) if pending else cur
            type = type.whnf(self.tc)
            while isinstance(type, W_ForAll):
                index = _local_for(type.get_binder())
                member.indices.append(index)
                type = _instantiate_dag(type.body, index).whnf(self.tc)
            if not isinstance(type, W_Sort):
                raise self.fail(
                    "%s is not a family of types" % member.name.str(),
                )
            if len(member.indices) != member.kind.num_indices:
                raise self.fail(
                    "%s has %d indices, not %d" % (
                        member.name.str(),
                        len(member.indices),
                        member.kind.num_indices,
                    ),
                )
            if i == 0:
                self.result_level = type.level
            elif not type.level.eq(self.result_level):
                raise self.fail(
                    "the types of the block live in different universes",
                )
        if len(self.members) - self.num_declared != self.first_kind.num_nested:
            raise self.fail(
                "the block has %d nested occurrences, not %d" % (
                    len(self.members) - self.num_declared,
                    self.first_kind.num_nested,
                ),
            )

    # -- the constructors ---------------------------------------------

    def check_constructors(self):
        tc = self.tc
        recursive = False
        for i in range(len(self.members)):
            member = self.members[i]
            declared = i < self.num_declared
            for ctor in member.ctors:
                ctor_kind = ctor.decl.w_kind
                assert isinstance(ctor_kind, W_Constructor)
                orig = ctor.decl.type
                if declared:
                    for _ in range(len(member.args)):
                        assert isinstance(orig, W_ForAll)
                        orig = orig.body
                cur = ctor.type
                fields = ctor.fields
                number = 0
                while isinstance(cur, W_ForAll):
                    number += 1
                    field_type = (
                        _instantiate_multi_dag(cur.type, fields)
                        if fields else cur.type
                    )
                    orig_field_type = field_type
                    if declared and isinstance(orig, W_ForAll):
                        orig_field_type = orig.type
                        orig = orig.body
                    binder = cur.get_binder()
                    if field_type is not binder.type:
                        binder = binder.with_type(field_type)
                    field = _local_for(binder)
                    fields.append(field)
                    if self.has_occurrence(field_type):
                        recursive = True
                        self.check_field(
                            ctor, field, field_type, orig_field_type,
                            number, declared,
                        )
                    cur = cur.body
                type = _instantiate_multi_dag(cur, fields) if fields else cur
                if declared and len(ctor.fields) != ctor_kind.num_fields:
                    raise W_ConstructorFieldCountMismatch(
                        self.env, ctor.decl.type,
                        declared=ctor_kind.num_fields,
                        actual=len(ctor.fields),
                    )
                if self.valid_app(type) != i:
                    if declared:
                        raise W_InvalidConstructorResult(
                            self.env, ctor.decl.type,
                        )
                    raise self.fail(
                        "%s does not construct %s"
                        % (ctor.name.str(), member.name.str()),
                    )
                if declared:
                    tc.stage = STAGE_IND_ONLY
                    prev_levels = tc.allowed_levels
                    tc.allowed_levels = self.level_names
                    try:
                        inferred = ctor.decl.type.infer(tc)
                        if not isinstance(inferred.whnf(tc), W_Sort):
                            raise W_NotASort(
                                tc, ctor.decl.type,
                                inferred_type=inferred,
                            )
                        if not self.result_level.eq(W_LEVEL_ZERO):
                            for field in ctor.fields:
                                assert isinstance(field, W_FVar)
                                f_sort = field.binder.type.infer(tc).whnf(tc)
                                if not isinstance(f_sort, W_Sort):
                                    raise self.fail(
                                        "a field of %s is not a type"
                                        % ctor.name.str(),
                                    )
                                if not f_sort.level.leq(self.result_level):
                                    raise W_UniverseTooHigh(
                                        self.env, ctor.decl.type,
                                        field.binder.type,
                                        field_level=f_sort.level,
                                        inductive_level=self.result_level,
                                    )
                    finally:
                        tc.allowed_levels = prev_levels
                        tc.stage = STAGE_ALL
                _, args = _args_of(type)
                ctor.result_indices = _drop(args, len(member.args))
        for i in range(self.num_declared):
            if self.members[i].kind.is_recursive != recursive:
                raise self.fail(
                    "%s is wrong about whether it is recursive"
                    % self.members[i].name.str(),
                )

    def check_field(self, ctor, field, type, orig_field_type, number, declared):
        """
        A field mentioning the block must mention it strictly
        positively; a field which ends in a member is a recursive one.
        """
        tc = self.tc
        xs = []
        type = type.whnf(tc)
        while self.has_occurrence(type):
            if isinstance(type, W_ForAll):
                if self.has_occurrence(type.type) and not self.unsafe:
                    if declared:
                        raise W_NonPositiveOccurrence(
                            self.env, orig_field_type, field_number=number,
                        )
                    raise self.fail(
                        "field #%d of %s has a non-positive occurrence of "
                        "the types being declared" % (number, ctor.name.str()),
                    )
                x = _local_for(type.get_binder())
                xs.append(x)
                type = _instantiate_dag(type.body, x).whnf(tc)
                continue
            index = self.valid_app(type)
            if index < 0:
                if self.unsafe:
                    return
                if declared:
                    head, _ = _args_of(type)
                    if (
                        isinstance(head, W_Const)
                        and self.is_declared_name(head.name)
                    ):
                        raise W_InvalidConstructorResult(
                            self.env, ctor.decl.type,
                        )
                    raise W_NonPositiveOccurrence(
                        self.env, orig_field_type, field_number=number,
                    )
                raise self.fail(
                    "field #%d of %s has an invalid occurrence of the "
                    "types being declared" % (number, ctor.name.str()),
                )
            _, args = _args_of(type)
            ctor.rec_fields.append(field)
            ctor.rec_xs.append(xs)
            ctor.rec_member.append(index)
            ctor.rec_indices.append(
                _drop(args, len(self.members[index].args)),
            )
            return

    # -- the universe eliminated into ---------------------------------

    def elim_only_into_prop(self):
        if self.result_level.is_not_zero():
            return False
        if len(self.members) > 1:
            return True
        ctors = self.members[0].ctors
        if len(ctors) > 1:
            return True
        if len(ctors) == 0:
            return False
        ctor = ctors[0]
        tc = self.tc
        for field in ctor.fields:
            assert isinstance(field, W_FVar)
            sort = field.binder.type.infer(tc).whnf(tc)
            if not isinstance(sort, W_Sort):
                raise self.fail(
                    "a field of %s is not a type" % ctor.name.str(),
                )
            if sort.level.eq(W_LEVEL_ZERO):
                continue
            found = False
            for each in ctor.result_indices:
                if each is field:
                    found = True
                    break
            if not found:
                return True
        return False

    def init_elim_level(self):
        if self.elim_only_into_prop():
            return
        name = Name.simple("u")
        i = 1
        while self.is_level_name(name):
            name = Name.simple("u_%d" % i)
            i += 1
        self.elim_name = name
        self.elim_level = name.as_level_param()

    def is_level_name(self, name):
        for each in self.level_names:
            if each.syntactic_eq(name):
                return True
        return False

    def is_k_target(self):
        if len(self.members) != 1:
            return False
        if not self.result_level.eq(W_LEVEL_ZERO):
            return False
        ctors = self.members[0].ctors
        return len(ctors) == 1 and len(ctors[0].fields) == 0

    # -- the recursors ------------------------------------------------

    def recursors(self):
        members = self.members
        elim_sort = self.elim_level.sort()
        for i in range(len(members)):
            member = members[i]
            major_type = _mk_app(
                _mk_app(member.const(), member.args), member.indices,
            )
            member.major = _local("t", major_type)
            motive_type = _mk_pi(
                member.indices + [member.major], elim_sort,
            )
            member.motive = _local("motive", motive_type)

        motives = [each.motive for each in members]
        minors = []
        for member in members:
            for ctor in member.ctors:
                ihs = []
                for j in range(len(ctor.rec_fields)):
                    target = members[ctor.rec_member[j]]
                    xs = ctor.rec_xs[j]
                    ih_type = _mk_pi(xs, _mk_app(
                        target.motive, ctor.rec_indices[j],
                    ).app(_mk_app(ctor.rec_fields[j], xs)))
                    ihs.append(_local("ih", ih_type))
                built = _mk_app(
                    _mk_app(ctor.name.const(ctor.levels), member.args),
                    ctor.fields,
                )
                result = _mk_app(
                    member.motive, ctor.result_indices,
                ).app(built)
                minor_type = _mk_pi(ctor.fields + ihs, result)
                minors.append(_local("minor", minor_type))

        if self.elim_name is None:
            rec_levels = self.levels
        else:
            rec_levels = [self.elim_level] + self.levels

        specs = []
        minor_index = 0
        k = self.is_k_target()
        prefix_binders = self.params + motives + minors
        for member in members:
            type = _mk_app(member.motive, member.indices).app(member.major)
            type = _mk_pi(
                prefix_binders + member.indices + [member.major], type,
            )

            rules = []
            for ctor in member.ctors:
                ihs = []
                for j in range(len(ctor.rec_fields)):
                    target = members[ctor.rec_member[j]]
                    xs = ctor.rec_xs[j]
                    rec = target.rec_name.const(rec_levels)
                    rec = _mk_app(rec, self.params)
                    rec = _mk_app(rec, motives)
                    rec = _mk_app(rec, minors)
                    rec = _mk_app(rec, ctor.rec_indices[j])
                    rec = rec.app(_mk_app(ctor.rec_fields[j], xs))
                    ihs.append(_mk_lambda(xs, rec))
                rhs = _mk_app(_mk_app(minors[minor_index], ctor.fields), ihs)
                rhs = _mk_lambda(prefix_binders + ctor.fields, rhs)
                rules.append(W_RecRule(ctor.name, len(ctor.fields), rhs))
                minor_index += 1

            specs.append(RecursorSpec(
                name=member.rec_name,
                elim_name=self.elim_name,
                type=type,
                rules=rules,
                k=k,
                num_params=self.num_params,
                num_indices=len(member.indices),
                num_motives=len(motives),
                num_minors=len(minors),
            ))
        return specs


def generate(first, tc):
    """
    The recursors of the block whose first type is the declaration
    ``first``, or a `W_InvalidInductive` raised if it can have none.
    """
    block = _Block(first, tc)
    block.collect_members()
    block.check_types()
    block.check_constructors()
    block.init_elim_level()
    return block.recursors()


class _Cache(object):
    """The most recently constructed block's recursors."""

    _attrs_ = ['first', 'specs']

    def __init__(self):
        self.first = None
        self.specs = None


_CACHE = _Cache()


def recursors_of(first, tc):
    """`generate`, remembering the last block it was asked about."""
    cache = _CACHE
    if cache.first is not first:
        specs = generate(first, tc)
        cache.first = first
        cache.specs = specs
    return cache.specs
