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

from rpylean.objects import (
    Binder,
    Name,
    W_App,
    W_CheckError,
    W_Const,
    W_Constructor,
    W_ForAll,
    W_FVar,
    W_FunBase,
    W_Inductive,
    W_Lambda,
    W_Let,
    W_Proj,
    W_RecRule,
    W_Sort,
    W_LEVEL_ZERO,
    MESSAGE,
    _error_diagnostic,
    _mk_w_forall,
    _mk_w_lambda,
    get_decl,
    find_decl,
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


def _mk_pi(fvars, body):
    i = len(fvars) - 1
    while i >= 0:
        fvar = fvars[i]
        assert isinstance(fvar, W_FVar)
        body = _mk_w_forall(fvar.binder, body.bind_fvar(fvar, 0))
        i -= 1
    return body


def _mk_lambda(fvars, body):
    i = len(fvars) - 1
    while i >= 0:
        fvar = fvars[i]
        assert isinstance(fvar, W_FVar)
        body = _mk_w_lambda(fvar.binder, body.bind_fvar(fvar, 0))
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


def alpha_eq(a, b):
    """Whether two expressions differ at most in how binders are written."""
    while True:
        if a is b:
            return True
        if a.__class__ is not b.__class__:
            return False
        if isinstance(a, W_App):
            assert isinstance(b, W_App)
            if not alpha_eq(a.arg, b.arg):
                return False
            a = a.fn
            b = b.fn
        elif isinstance(a, W_FunBase):
            assert isinstance(b, W_FunBase)
            if not alpha_eq(a.binder.type, b.binder.type):
                return False
            a = a.body
            b = b.body
        elif isinstance(a, W_Let):
            assert isinstance(b, W_Let)
            if not alpha_eq(a.type, b.type):
                return False
            if not alpha_eq(a.value, b.value):
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
            return syntactic_eq(a, b)


class _Member(object):
    """
    A type of the block: one being declared, applied to the block's
    parameters, or a container some member occurs nested within,
    applied to the arguments it occurs at.
    """

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

    def __init__(self, name, levels, type):
        self.name = name
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


class _Block(object):
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

    def fail(self, summary):
        return W_InvalidInductive(self.env, summary)

    # -- the block's members ------------------------------------------

    def is_declared_name(self, name):
        for i in range(self.num_declared):
            if self.members[i].name.syntactic_eq(name):
                return True
        return False

    def has_occurrence(self, expr):
        """Whether ``expr`` mentions a type being declared."""
        for i in range(self.num_declared):
            if expr.contains_const(self.members[i].name):
                return True
        return False

    def collect_members(self):
        declarations = self.tc.declarations
        all = self.first_kind.all
        if not all or not all[0].syntactic_eq(self.first.name):
            raise self.fail("the block does not begin with its first type")
        for name in all:
            decl = get_decl(declarations, name)
            kind = decl.w_kind
            if not isinstance(kind, W_Inductive):
                raise self.fail("%s is not an inductive type" % name.str())
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

        type = self.first.type
        for _ in range(self.num_params):
            if not isinstance(type, W_ForAll):
                type = type.whnf(self.tc)
            if not isinstance(type, W_ForAll):
                raise self.fail("the type has fewer binders than parameters")
            param = _local_for(type.binder)
            self.params.append(param)
            type = type.body.instantiate(param, 0)
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
            for ctor_name in member.kind.ctor_names:
                ctor_decl = get_decl(declarations, ctor_name)
                if not isinstance(ctor_decl.w_kind, W_Constructor):
                    raise self.fail(
                        "%s is not a constructor" % ctor_name.str(),
                    )
                type = ctor_decl.type
                if substs is not None:
                    type = type.subst_levels(substs)
                for arg in member.args:
                    if not isinstance(type, W_ForAll):
                        raise self.fail(
                            "%s has fewer binders than parameters"
                            % ctor_name.str(),
                        )
                    type = type.body.instantiate(arg, 0)
                if declared:
                    self.check_uniform_occurrences(type)
                self.find_nested(type)
                member.ctors.append(_Ctor(ctor_name, member.levels, type))
            qhead += 1

    def check_uniform_occurrences(self, expr):
        """
        Every occurrence of a type being declared must be applied to
        the block's universe levels and parameters.
        """
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
                    raise self.fail(
                        "%s occurs applied to other than the parameters and "
                        "universe levels of the block" % head.name.str(),
                    )
                for i in range(self.num_params, len(args)):
                    self.check_uniform_occurrences(args[i])
                return
            if not isinstance(head, W_Const):
                self.check_uniform_occurrences(head)
            for each in args:
                self.check_uniform_occurrences(each)
        elif isinstance(expr, W_FunBase):
            self.check_uniform_occurrences(expr.binder.type)
            self.check_uniform_occurrences(expr.body)
        elif isinstance(expr, W_Let):
            self.check_uniform_occurrences(expr.type)
            self.check_uniform_occurrences(expr.value)
            self.check_uniform_occurrences(expr.body)
        elif isinstance(expr, W_Proj):
            self.check_uniform_occurrences(expr.struct_expr)

    def find_nested(self, expr):
        """Add a member for each container the block occurs nested in."""
        if isinstance(expr, W_App):
            if self.add_if_nested(expr):
                return
            self.find_nested(expr.fn)
            self.find_nested(expr.arg)
        elif isinstance(expr, W_FunBase):
            self.find_nested(expr.binder.type)
            self.find_nested(expr.body)
        elif isinstance(expr, W_Let):
            self.find_nested(expr.type)
            self.find_nested(expr.value)
            self.find_nested(expr.body)
        elif isinstance(expr, W_Proj):
            self.find_nested(expr.struct_expr)

    def add_if_nested(self, expr):
        head, args = _args_of(expr)
        if not isinstance(head, W_Const):
            return False
        if self.is_declared_name(head.name):
            return False
        decl = find_decl(self.tc.declarations, head.name)
        if decl is None:
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
            for arg in member.args:
                if not isinstance(type, W_ForAll):
                    type = type.whnf(self.tc)
                if not isinstance(type, W_ForAll):
                    raise self.fail(
                        "%s has fewer binders than parameters"
                        % member.name.str(),
                    )
                type = type.body.instantiate(arg, 0)
            type = type.whnf(self.tc)
            while isinstance(type, W_ForAll):
                index = _local_for(type.binder)
                member.indices.append(index)
                type = type.body.instantiate(index, 0).whnf(self.tc)
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
        recursive = False
        for i in range(len(self.members)):
            member = self.members[i]
            for ctor in member.ctors:
                type = ctor.type
                number = 0
                while isinstance(type, W_ForAll):
                    number += 1
                    field_type = type.binder.type
                    field = _local_for(type.binder)
                    ctor.fields.append(field)
                    if self.has_occurrence(field_type):
                        recursive = True
                        self.check_field(ctor, field, field_type, number)
                    type = type.body.instantiate(field, 0)
                if self.valid_app(type) != i:
                    raise self.fail(
                        "%s does not construct %s"
                        % (ctor.name.str(), member.name.str()),
                    )
                _, args = _args_of(type)
                ctor.result_indices = _drop(args, len(member.args))
        for i in range(self.num_declared):
            if self.members[i].kind.is_recursive != recursive:
                raise self.fail(
                    "%s is wrong about whether it is recursive"
                    % self.members[i].name.str(),
                )

    def check_field(self, ctor, field, type, number):
        """
        A field mentioning the block must mention it strictly
        positively; a field which ends in a member is a recursive one.
        """
        tc = self.tc
        xs = []
        type = type.whnf(tc)
        while self.has_occurrence(type):
            if isinstance(type, W_ForAll):
                if self.has_occurrence(type.binder.type) and not self.unsafe:
                    raise self.fail(
                        "field #%d of %s has a non-positive occurrence of "
                        "the types being declared" % (number, ctor.name.str()),
                    )
                x = _local_for(type.binder)
                xs.append(x)
                type = type.body.instantiate(x, 0).whnf(tc)
                continue
            index = self.valid_app(type)
            if index < 0:
                if self.unsafe:
                    return
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
                minor_type = _mk_pi(ctor.fields, _mk_pi(ihs, result))
                minors.append(_local("minor", minor_type))

        if self.elim_name is None:
            rec_levels = self.levels
        else:
            rec_levels = [self.elim_level] + self.levels

        specs = []
        minor_index = 0
        k = self.is_k_target()
        for member in members:
            type = _mk_app(member.motive, member.indices).app(member.major)
            type = _mk_pi([member.major], type)
            type = _mk_pi(member.indices, type)
            type = _mk_pi(minors, type)
            type = _mk_pi(motives, type)
            type = _mk_pi(self.params, type)

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
                rhs = _mk_lambda(ctor.fields, rhs)
                rhs = _mk_lambda(minors, rhs)
                rhs = _mk_lambda(motives, rhs)
                rhs = _mk_lambda(self.params, rhs)
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

    def __init__(self):
        self.first = None
        self.specs = None
        self.error = None


_CACHE = _Cache()


def recursors_of(first, tc):
    """`generate`, remembering the last block it was asked about."""
    cache = _CACHE
    if cache.first is not first:
        cache.first = first
        cache.specs = None
        cache.error = None
        try:
            cache.specs = generate(first, tc)
        except W_InvalidInductive as error:
            cache.error = error
    if cache.error is not None:
        raise W_InvalidInductive(cache.error.environment, cache.error.summary)
    return cache.specs
