"""
A call-by-need abstract machine (Krivine / CEK) over persistent immutable
code nodes, designed for RPython's meta-tracing JIT.

Every Lean expression evaluated here is compiled once into an immutable
`CodeNode` graph (persistent across declarations in an `Environment`).
The JIT's green variables are `(rec_edge, code)` — the Lean expression's own
program counter — so hot recursive Lean definitions (`Nat.rec`, `List.rec`,
`brecOn`, `match_1`, `decide +kernel` evaluators) are traced with AST
dispatch, delta lookups, and recursor rule dispatch constant-folded away,
and transient closures / argument nodes / continuations virtualized.

`can_enter_jit` fires only on true recursive recursor back-edges (`Nat.rec`
on `n > 0` and recursive `CRec` rules, landed on the caller's minor premise),
and ordinary declarations never enter this machine unless they compare a
closed compound term against a `Bool` or `Nat` scalar, so non-looping type
checking pays negligible JIT bookkeeping overhead.
"""

from rpython.rlib import jit
from rpython.rlib.objectmodel import compute_identity_hash, r_dict
from rpython.rlib.rarithmetic import LONG_BIT, ovfcheck
from rpython.rlib.rbigint import rbigint

from rpylean.objects import (
    NAT_ZERO,
    W_App,
    W_BVar,
    W_Const,
    W_Constructor,
    W_Definition,
    W_Lambda,
    W_Let,
    W_LitNat,
    W_LitStr,
    W_Proj,
    W_Recursor,
    _BOOL_FALSE,
    _BOOL_TRUE,
    _NAT_ADD,
    _NAT_BEQ,
    _NAT_BLE,
    _NAT_DIV,
    _NAT_GCD,
    _NAT_LAND,
    _NAT_LOR,
    _NAT_MOD,
    _NAT_MUL,
    _NAT_POW,
    _NAT_REC_NAME,
    _NAT_SHIFT_LEFT,
    _NAT_SHIFT_RIGHT,
    _NAT_SUB,
    _NAT_SUCC_NAME,
    _NAT_XOR,
    _REDUCE_POW_MAX_EXP,
    _mk_w_litnat,
    find_decl,
    syntactic_eq,
)


def _expr_is(a, b):
    return a is b


def _expr_id_hash(a):
    return compute_identity_hash(a)


# ---- Bail signal ---------------------------------------------------------

class _EvalBail(Exception):
    """Raised when evaluation encounters a stuck neutral, K-like recursor on
    a non-constructor, or unsupported construct; the caller falls back to
    `Machine`'s general reduction/def_eq."""


# ---- Native Nat op tags --------------------------------------------------

OP_NONE = 0
OP_ADD = 1
OP_SUB = 2
OP_MUL = 3
OP_POW = 4
OP_GCD = 5
OP_MOD = 6
OP_DIV = 7
OP_BEQ = 8
OP_BLE = 9
OP_LAND = 10
OP_LOR = 11
OP_XOR = 12
OP_SHL = 13
OP_SHR = 14


def _nat_op_id(name):
    if name.syntactic_eq(_NAT_ADD):
        return OP_ADD
    if name.syntactic_eq(_NAT_SUB):
        return OP_SUB
    if name.syntactic_eq(_NAT_MUL):
        return OP_MUL
    if name.syntactic_eq(_NAT_POW):
        return OP_POW
    if name.syntactic_eq(_NAT_GCD):
        return OP_GCD
    if name.syntactic_eq(_NAT_MOD):
        return OP_MOD
    if name.syntactic_eq(_NAT_DIV):
        return OP_DIV
    if name.syntactic_eq(_NAT_BEQ):
        return OP_BEQ
    if name.syntactic_eq(_NAT_BLE):
        return OP_BLE
    if name.syntactic_eq(_NAT_LAND):
        return OP_LAND
    if name.syntactic_eq(_NAT_LOR):
        return OP_LOR
    if name.syntactic_eq(_NAT_XOR):
        return OP_XOR
    if name.syntactic_eq(_NAT_SHIFT_LEFT):
        return OP_SHL
    if name.syntactic_eq(_NAT_SHIFT_RIGHT):
        return OP_SHR
    return OP_NONE


# ---- Constructor tags ----------------------------------------------------

CTOR_NORMAL = 0
CTOR_BOOL_TRUE = 1
CTOR_BOOL_FALSE = 2
CTOR_NAT_ZERO = 3
CTOR_NAT_SUCC = 4
CTOR_QUOT_MK = 5


# ---- CodeNode tags -------------------------------------------------------

TAG_VAL = 0
TAG_BVAR = 1
TAG_LAM = 2
TAG_APP = 3
TAG_LET = 4
TAG_PROJ = 5
TAG_CTOR = 6
TAG_DEF = 7
TAG_REC = 8
TAG_QUOT_LIFT = 9
TAG_OPAQUE = 10
TAG_NAT_OP = 11
TAG_FULL_CTOR = 12


# ---- Runtime slots (Values and Thunks) -----------------------------------

class Slot(object):
    """Either an already-evaluated WHNF `Val` or a call-by-need `Thunk`."""

    _attrs_ = []


class Val(Slot):
    """A value in weak head normal form."""

    _attrs_ = []


class VSmallNat(Val):
    """A non-negative Nat fitting in a signed machine word."""

    _attrs_ = ['n']
    _immutable_fields_ = ['n']

    def __init__(self, n):
        self.n = n


_MAX_SMALL_NAT = rbigint.fromint((1 << (LONG_BIT - 3)) - 1)
_BIG_ZERO = rbigint.fromint(0)
_BIG_ONE = rbigint.fromint(1)
_SMALL_NATS = [VSmallNat(i) for i in range(256)]
_NAT_ZERO_VAL = _SMALL_NATS[0]


def mk_small_nat(n):
    return VSmallNat(n)


def mk_const_small_nat(n):
    if 0 <= n < 256:
        return _SMALL_NATS[n]
    return VSmallNat(n)


class VBigNat(Val):
    """A Nat too large for a signed machine word."""

    _attrs_ = ['big']
    _immutable_fields_ = ['big']

    def __init__(self, big):
        self.big = big


def mk_nat_from_bigint(big):
    if big.le(_MAX_SMALL_NAT) and big.ge(_BIG_ZERO):
        return mk_small_nat(big.toint())
    return VBigNat(big)


def mk_const_nat_from_bigint(big):
    if big.le(_MAX_SMALL_NAT) and big.ge(_BIG_ZERO):
        return mk_const_small_nat(big.toint())
    return VBigNat(big)


class VCtor(Val):
    """A saturated constructor application storing only its `num_fields` fields."""

    _attrs_ = ['ctor_node']
    _immutable_fields_ = ['ctor_node']

    def __init__(self, ctor_node):
        self.ctor_node = ctor_node


class VCtor0(VCtor):
    """A saturated constructor with 0 fields (shared singleton per CCtor)."""

    _attrs_ = []


class VCtor1(VCtor):
    """A saturated constructor with 1 field (no array allocation)."""

    _attrs_ = ['f0']
    _immutable_fields_ = ['f0']

    def __init__(self, ctor_node, f0):
        self.ctor_node = ctor_node
        self.f0 = f0


class VCtor2(VCtor):
    """A saturated constructor with 2 fields (no array allocation)."""

    _attrs_ = ['f0', 'f1']
    _immutable_fields_ = ['f0', 'f1']

    def __init__(self, ctor_node, f0, f1):
        self.ctor_node = ctor_node
        self.f0 = f0
        self.f1 = f1


class VCtorN(VCtor):
    """A saturated constructor with 3+ fields."""

    _attrs_ = ['fields']
    _immutable_fields_ = ['fields[*]']

    def __init__(self, ctor_node, fields):
        self.ctor_node = ctor_node
        self.fields = fields


class VPartialCtor(Val):
    """An under-applied constructor waiting for more arguments."""

    _attrs_ = ['ctor_node', 'collected']
    _immutable_fields_ = ['ctor_node', 'collected[*]']

    def __init__(self, ctor_node, collected):
        self.ctor_node = ctor_node
        self.collected = collected


class VClosure(Val):
    """An unapplied lambda closed over its environment."""

    _attrs_ = ['lam_node', 'env']
    _immutable_fields_ = ['lam_node', 'env']

    def __init__(self, lam_node, env):
        self.lam_node = lam_node
        self.env = env


class VAtom(Val):
    """An inert non-reducible value (Sort, ForAll, opaque const, etc.)."""

    _attrs_ = ['node']
    _immutable_fields_ = ['node']

    def __init__(self, node):
        self.node = node


class VLitStr(Val):
    """A string literal, lazily expanded to its kernel `String.ofList`
    constructor value on first projection or recursor match."""

    _attrs_ = ['lit', 'expanded']
    _immutable_fields_ = ['lit']

    def __init__(self, lit):
        self.lit = lit
        self.expanded = None


class Thunk(Slot):
    """A call-by-need suspension, updated in place when first forced."""

    _attrs_ = ['val', 'code', 'env']

    def __init__(self, code, env):
        self.val = None
        self.code = code
        self.env = env


class RecNatThunk(Thunk):
    """Suspended `Nat.rec motive zero_case succ_case pred`."""

    _attrs_ = ['rec_node', 'motive', 'zero_case', 'succ_case', 'pred_slot']
    _immutable_fields_ = [
        'rec_node', 'motive', 'zero_case', 'succ_case', 'pred_slot',
    ]

    def __init__(self, rec_node, motive, zero_case, succ_case, pred_slot):
        self.val = None
        self.code = rec_node
        self.env = None
        self.rec_node = rec_node
        self.motive = motive
        self.zero_case = zero_case
        self.succ_case = succ_case
        self.pred_slot = pred_slot


# ---- Linked de Bruijn environment ----------------------------------------

class Env(object):
    """Compact immutable linked de Bruijn environment (24 bytes, zero guards)."""

    _attrs_ = ['slot', 'prev']
    _immutable_fields_ = ['slot', 'prev']

    def __init__(self, slot, prev):
        self.slot = slot
        self.prev = prev


def extend_env(prev, slot):
    return Env(slot, prev)


@jit.unroll_safe
def _lookup_small(env, idx):
    cur = env
    i = idx
    while i > 0:
        cur = cur.prev
        i -= 1
    return cur.slot


@jit.dont_look_inside
def _lookup_deep(env, idx):
    cur = env
    i = idx
    while i > 0:
        cur = cur.prev
        i -= 1
    return cur.slot


def lookup_env(env, idx):
    if env is None:
        raise _EvalBail()
    if idx <= 8:
        return _lookup_small(env, idx)
    return _lookup_deep(env, idx)


# ---- Linked argument and continuation stacks -----------------------------

class ArgNode(object):
    """Immutable linked argument stack (virtualized away inside JIT loops)."""

    _attrs_ = ['slot', 'tail']
    _immutable_fields_ = ['slot', 'tail']

    def __init__(self, slot, tail):
        self.slot = slot
        self.tail = tail


class Cont(object):
    _attrs_ = ['next']
    _immutable_fields_ = ['next']


class KUpdate(Cont):
    _attrs_ = ['thunk', 'args']
    _immutable_fields_ = ['thunk', 'args']

    def __init__(self, thunk, args, next):
        self.thunk = thunk
        self.args = args
        self.next = next


class KProj(Cont):
    _attrs_ = ['field_idx', 'args']
    _immutable_fields_ = ['field_idx', 'args']

    def __init__(self, field_idx, args, next):
        self.field_idx = field_idx
        self.args = args
        self.next = next


class KRecMajor(Cont):
    _attrs_ = ['rec_node', 'prefix', 'args']
    _immutable_fields_ = ['rec_node', 'prefix[*]', 'args']

    def __init__(self, rec_node, prefix, args, next):
        self.rec_node = rec_node
        self.prefix = prefix
        self.args = args
        self.next = next


class KNatOp1(Cont):
    _attrs_ = ['op_id', 'arg2', 'args']
    _immutable_fields_ = ['op_id', 'arg2', 'args']

    def __init__(self, op_id, arg2, args, next):
        self.op_id = op_id
        self.arg2 = arg2
        self.args = args
        self.next = next


class KNatOp2(Cont):
    _attrs_ = ['op_id', 'v1', 'args']
    _immutable_fields_ = ['op_id', 'v1', 'args']

    def __init__(self, op_id, v1, args, next):
        self.op_id = op_id
        self.v1 = v1
        self.args = args
        self.next = next


class KNatSucc(Cont):
    _attrs_ = ['succs']
    _immutable_fields_ = ['succs']

    def __init__(self, succs, next):
        self.succs = succs
        self.next = next


class KQuotLift(Cont):
    _attrs_ = ['fn_slot', 'args']
    _immutable_fields_ = ['fn_slot', 'args']

    def __init__(self, fn_slot, args, next):
        self.fn_slot = fn_slot
        self.args = args
        self.next = next


# ---- Immutable CodeNode graph --------------------------------------------

class CodeNode(object):
    _attrs_ = ['tag']
    _immutable_fields_ = ['tag']


class CVal(CodeNode):
    _attrs_ = ['val']
    _immutable_fields_ = ['val']

    def __init__(self, val):
        self.tag = TAG_VAL
        self.val = val


class CBVar(CodeNode):
    _attrs_ = ['idx']
    _immutable_fields_ = ['idx']

    def __init__(self, idx):
        self.tag = TAG_BVAR
        self.idx = idx


class CLam(CodeNode):
    _attrs_ = ['body']
    _immutable_fields_ = ['body']

    def __init__(self, body):
        self.tag = TAG_LAM
        self.body = body


class CApp(CodeNode):
    """Flattened application spine `fn args[0] args[1] ... args[n-1]`."""

    _attrs_ = ['fn', 'args']
    _immutable_fields_ = ['fn', 'args[*]']

    def __init__(self, fn, args):
        self.tag = TAG_APP
        self.fn = fn
        self.args = args


class CLet(CodeNode):
    _attrs_ = ['val_code', 'body']
    _immutable_fields_ = ['val_code', 'body']

    def __init__(self, val_code, body):
        self.tag = TAG_LET
        self.val_code = val_code
        self.body = body


class CProj(CodeNode):
    _attrs_ = ['struct_code', 'field_idx']
    _immutable_fields_ = ['struct_code', 'field_idx']

    def __init__(self, struct_code, field_idx):
        self.tag = TAG_PROJ
        self.struct_code = struct_code
        self.field_idx = field_idx


class CCtor(CodeNode):
    _attrs_ = [
        'cidx', 'ctor_id', 'induct_id', 'num_params', 'num_fields',
        'total_arity', 'tag_kind', 'zero_field_val', 'singleton_val', 'const',
    ]
    _immutable_fields_ = [
        'cidx', 'ctor_id', 'induct_id', 'num_params', 'num_fields',
        'total_arity', 'tag_kind', 'zero_field_val', 'singleton_val', 'const',
    ]

    def __init__(self, cidx, ctor_id, induct_id, num_params, num_fields,
                 tag_kind, const):
        self.tag = TAG_CTOR
        self.cidx = cidx
        self.ctor_id = ctor_id
        self.induct_id = induct_id
        self.num_params = num_params
        self.num_fields = num_fields
        self.total_arity = num_params + num_fields
        self.tag_kind = tag_kind
        self.const = const
        if tag_kind == CTOR_NAT_ZERO:
            self.zero_field_val = _NAT_ZERO_VAL
            self.singleton_val = _NAT_ZERO_VAL
        elif num_fields == 0:
            v = VCtor0(self)
            self.zero_field_val = v
            self.singleton_val = v if self.total_arity == 0 else None
        else:
            self.zero_field_val = None
            self.singleton_val = None


class CFullCtor(CodeNode):
    """Saturated constructor application storing only its `num_fields` field codes."""

    _attrs_ = ['ctor_node', 'field_codes']
    _immutable_fields_ = ['ctor_node', 'field_codes[*]']

    def __init__(self, ctor_node, field_codes):
        self.tag = TAG_FULL_CTOR
        self.ctor_node = ctor_node
        self.field_codes = field_codes


class CNatOp(CodeNode):
    """First-class native binary Nat operation body (`fun a b => op a b`)."""

    _attrs_ = ['op_id']
    _immutable_fields_ = ['op_id']

    def __init__(self, op_id):
        self.tag = TAG_NAT_OP
        self.op_id = op_id


_NAT_OP_BODIES = [CLam(CLam(CNatOp(op_id))) for op_id in range(15)]


class CDef(CodeNode):
    _attrs_ = ['const', 'decl', 'nat_op', 'body', 'is_compiled', 'name_str']
    _immutable_fields_ = [
        'const', 'decl', 'nat_op', 'body?', 'is_compiled?', 'name_str',
    ]

    def __init__(self, const, decl, nat_op):
        self.tag = TAG_DEF
        self.const = const
        self.decl = decl
        self.nat_op = nat_op
        if nat_op != OP_NONE:
            self.body = _NAT_OP_BODIES[nat_op]
            self.is_compiled = True
        else:
            self.body = None
            self.is_compiled = False
        self.name_str = const.name.str()


class CRec(CodeNode):
    _attrs_ = [
        'const', 'induct_id', 'num_params', 'num_motives', 'num_minors',
        'num_indices', 'skip', 'keep', 'is_nat_rec', 'is_k', 'is_simple_cidx',
        'rules_rhs', 'rules_nfields', 'rules_ctor_ids', 'rules_is_rec',
        'name_str',
    ]
    _immutable_fields_ = [
        'const', 'induct_id', 'num_params', 'num_motives', 'num_minors',
        'num_indices', 'skip', 'keep', 'is_nat_rec', 'is_k', 'is_simple_cidx',
        'rules_rhs[*]', 'rules_nfields[*]', 'rules_ctor_ids[*]',
        'rules_is_rec[*]', 'name_str',
    ]

    def __init__(self, const, induct_id, num_params, num_motives, num_minors,
                 num_indices, is_nat_rec, is_k, is_simple_cidx,
                 rules_rhs, rules_nfields, rules_ctor_ids, rules_is_rec):
        self.tag = TAG_REC
        self.const = const
        self.induct_id = induct_id
        self.num_params = num_params
        self.num_motives = num_motives
        self.num_minors = num_minors
        self.num_indices = num_indices
        self.skip = num_params + num_motives + num_minors + num_indices
        self.keep = num_params + num_motives + num_minors
        self.is_nat_rec = is_nat_rec
        self.is_k = is_k
        self.is_simple_cidx = is_simple_cidx
        self.rules_rhs = rules_rhs
        self.rules_nfields = rules_nfields
        self.rules_ctor_ids = rules_ctor_ids
        self.rules_is_rec = rules_is_rec
        self.name_str = const.name.str()

    @jit.elidable
    def rule_index(self, ctor_node):
        if self.is_simple_cidx and ctor_node.induct_id == self.induct_id:
            cidx = ctor_node.cidx
            if 0 <= cidx < len(self.rules_rhs):
                return cidx
        cid = ctor_node.ctor_id
        ids = self.rules_ctor_ids
        i = 0
        n = len(ids)
        while i < n:
            if ids[i] == cid:
                return i
            i += 1
        return -1


class CQuotLift(CodeNode):
    _attrs_ = []

    def __init__(self):
        self.tag = TAG_QUOT_LIFT


_C_QUOT_LIFT = CQuotLift()


class COpaque(CodeNode):
    _attrs_ = ['const']
    _immutable_fields_ = ['const']

    def __init__(self, const):
        self.tag = TAG_OPAQUE
        self.const = const


_BVAR_CACHE_SIZE = 128
_BVAR_NODES = [CBVar(i) for i in range(_BVAR_CACHE_SIZE)]


def _mk_bvar(idx):
    if 0 <= idx < _BVAR_CACHE_SIZE:
        return _BVAR_NODES[idx]
    return CBVar(idx)


# ---- Native Nat operations -----------------------------------------------

def _to_bigint(v):
    if isinstance(v, VSmallNat):
        return rbigint.fromint(v.n)
    assert isinstance(v, VBigNat)
    return v.big


@jit.dont_look_inside
def _small_gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a


@jit.dont_look_inside
def _small_pow(base, exp):
    if exp == 0:
        return 1
    if base == 0:
        return 0
    if base == 1:
        return 1
    if exp > LONG_BIT - 2:
        return -1
    res = 1
    b = base
    e = exp
    try:
        while e > 0:
            if e & 1:
                res = ovfcheck(res * b)
            e >>= 1
            if e > 0:
                b = ovfcheck(b * b)
    except OverflowError:
        return -1
    return res


@jit.dont_look_inside
def _eval_nat_op_big(op_id, v1, v2, cache):
    b1 = _to_bigint(v1)
    b2 = _to_bigint(v2)
    if op_id == OP_ADD:
        return mk_nat_from_bigint(b1.add(b2))
    if op_id == OP_SUB:
        if b1.lt(b2):
            return _NAT_ZERO_VAL
        return mk_nat_from_bigint(b1.sub(b2))
    if op_id == OP_MUL:
        return mk_nat_from_bigint(b1.mul(b2))
    if op_id == OP_POW:
        if b2.gt(_REDUCE_POW_MAX_EXP):
            raise _EvalBail()
        return mk_nat_from_bigint(b1.pow(b2))
    if op_id == OP_GCD:
        return mk_nat_from_bigint(b1.gcd(b2))
    if op_id == OP_MOD:
        if b2.eq(_BIG_ZERO):
            return mk_nat_from_bigint(b1)
        return mk_nat_from_bigint(b1.mod(b2))
    if op_id == OP_DIV:
        if b2.eq(_BIG_ZERO):
            return _NAT_ZERO_VAL
        return mk_nat_from_bigint(b1.div(b2))
    if op_id == OP_BEQ:
        res = cache.v_true if b1.eq(b2) else cache.v_false
        if res is None:
            raise _EvalBail()
        return res
    if op_id == OP_BLE:
        res = cache.v_true if b1.le(b2) else cache.v_false
        if res is None:
            raise _EvalBail()
        return res
    if op_id == OP_LAND:
        return mk_nat_from_bigint(b1.and_(b2))
    if op_id == OP_LOR:
        return mk_nat_from_bigint(b1.or_(b2))
    if op_id == OP_XOR:
        return mk_nat_from_bigint(b1.xor(b2))
    if op_id == OP_SHL:
        if b1.eq(_BIG_ZERO):
            return _NAT_ZERO_VAL
        if b2.gt(_REDUCE_POW_MAX_EXP):
            raise _EvalBail()
        return mk_nat_from_bigint(b1.lshift(b2.toint()))
    if op_id == OP_SHR:
        if b2.gt(_MAX_SMALL_NAT):
            return _NAT_ZERO_VAL
        return mk_nat_from_bigint(b1.rshift(b2.toint()))
    raise _EvalBail()


def _eval_nat_op(op_id, v1, v2, cache):
    if isinstance(v1, VSmallNat) and isinstance(v2, VSmallNat):
        a = v1.n
        b = v2.n
        if op_id == OP_ADD:
            try:
                return mk_small_nat(ovfcheck(a + b))
            except OverflowError:
                pass
        elif op_id == OP_SUB:
            return mk_small_nat(a - b if a >= b else 0)
        elif op_id == OP_MUL:
            try:
                return mk_small_nat(ovfcheck(a * b))
            except OverflowError:
                pass
        elif op_id == OP_POW:
            r = _small_pow(a, b)
            if r >= 0:
                return mk_small_nat(r)
        elif op_id == OP_MOD:
            return mk_small_nat(a if b == 0 else a % b)
        elif op_id == OP_DIV:
            return mk_small_nat(0 if b == 0 else a // b)
        elif op_id == OP_BEQ:
            res = cache.v_true if a == b else cache.v_false
            if res is None:
                raise _EvalBail()
            return res
        elif op_id == OP_BLE:
            res = cache.v_true if a <= b else cache.v_false
            if res is None:
                raise _EvalBail()
            return res
        elif op_id == OP_LAND:
            return mk_small_nat(a & b)
        elif op_id == OP_LOR:
            return mk_small_nat(a | b)
        elif op_id == OP_XOR:
            return mk_small_nat(a ^ b)
        elif op_id == OP_SHR:
            if b >= LONG_BIT:
                return _NAT_ZERO_VAL
            return mk_small_nat(a >> b)
        elif op_id == OP_SHL:
            if a == 0:
                return _NAT_ZERO_VAL
            if b < LONG_BIT - 2:
                res = a << b
                if res >= 0 and (res >> b) == a:
                    return mk_small_nat(res)
        elif op_id == OP_GCD:
            return mk_small_nat(_small_gcd(a, b))
    return _eval_nat_op_big(op_id, v1, v2, cache)


def _add_small_int(n, k):
    try:
        return mk_small_nat(ovfcheck(n + k))
    except OverflowError:
        return VBigNat(rbigint.fromint(n).add(rbigint.fromint(k)))


# ---- CodeCache (persistent per Environment) ------------------------------

def _const_eq(a, b):
    return syntactic_eq(a, b)


def _const_hash(a):
    return a.hash()


def _name_eq(a, b):
    return a.syntactic_eq(b)


def _name_hash(a):
    return a.hash()


def _canonical_const(const):
    levels = const.levels
    if not levels:
        return const
    changed = False
    normalized = []
    for level in levels:
        n = level.normalize()
        if n is not level:
            changed = True
        normalized.append(n)
    if not changed:
        return const
    return const.name.const(normalized)


def _subst_const_levels(const, level_subst):
    if level_subst is None or not const.levels:
        return const
    return const.subst_levels(level_subst)


def _code_has_rec(root):
    stack = [root]
    visited = {}
    while stack:
        n = stack.pop()
        if n is None or n in visited:
            continue
        visited[n] = None
        tag = n.tag
        if tag == TAG_REC:
            return True
        if tag == TAG_APP:
            assert isinstance(n, CApp)
            stack.append(n.fn)
            for a in n.args:
                stack.append(a)
        elif tag == TAG_LAM:
            assert isinstance(n, CLam)
            stack.append(n.body)
        elif tag == TAG_LET:
            assert isinstance(n, CLet)
            stack.append(n.val_code)
            stack.append(n.body)
        elif tag == TAG_PROJ:
            assert isinstance(n, CProj)
            stack.append(n.struct_code)
        elif tag == TAG_FULL_CTOR:
            assert isinstance(n, CFullCtor)
            for a in n.field_codes:
                stack.append(a)
    return False


def _compile_full_ctor(fn_node, cargs, fields_closed):
    nf = fn_node.num_fields
    if nf == 0:
        return CVal(fn_node.zero_field_val)
    np = fn_node.num_params
    field_codes = [None] * nf
    for i in range(nf):
        field_codes[i] = cargs[np + i]
    if fields_closed:
        if fn_node.tag_kind == CTOR_NAT_SUCC and nf == 1:
            fc0 = field_codes[0]
            if isinstance(fc0, CVal):
                v0 = fc0.val
                if isinstance(v0, VSmallNat) and v0.n < (1 << (LONG_BIT - 4)):
                    return CVal(mk_const_small_nat(v0.n + 1))
        slots = [None] * nf
        for i in range(nf):
            an = field_codes[i]
            if isinstance(an, CVal):
                slots[i] = an.val
            elif isinstance(an, CLam):
                slots[i] = VClosure(an, None)
            else:
                slots[i] = Thunk(an, None)
        if nf == 1:
            return CVal(VCtor1(fn_node, slots[0]))
        if nf == 2:
            return CVal(VCtor2(fn_node, slots[0], slots[1]))
        return CVal(VCtorN(fn_node, slots))
    return CFullCtor(fn_node, field_codes)


class CodeCache(object):
    """Persistent immutable `CodeNode` compiler attached to an `Environment`."""

    _attrs_ = [
        'declarations', '_consts', '_induct_ids', '_ctor_ids', '_str_vals',
        'v_true', 'v_false',
    ]
    _immutable_fields_ = ['declarations', 'v_true?', 'v_false?']

    def __init__(self, declarations):
        self.declarations = declarations
        self._consts = r_dict(_const_eq, _const_hash)
        self._induct_ids = {}
        self._ctor_ids = {}
        self._str_vals = {}
        self.v_true = None
        self.v_false = None

    def litstr_val(self, lit):
        val = self._str_vals.get(lit.val, None)
        if val is None:
            val = VLitStr(lit)
            self._str_vals[lit.val] = val
        return val

    def _refresh_bools(self):
        if self.v_true is None:
            node = self.const_node(_BOOL_TRUE)
            if isinstance(node, CCtor) and node.singleton_val is not None:
                self.v_true = node.singleton_val
        if self.v_false is None:
            node = self.const_node(_BOOL_FALSE)
            if isinstance(node, CCtor) and node.singleton_val is not None:
                self.v_false = node.singleton_val

    def _induct_id(self, name):
        idx = self._induct_ids.get(name, -1)
        if idx >= 0:
            return idx
        idx = len(self._induct_ids)
        self._induct_ids[name] = idx
        return idx

    def _ctor_id(self, name):
        idx = self._ctor_ids.get(name, -1)
        if idx >= 0:
            return idx
        idx = len(self._ctor_ids)
        self._ctor_ids[name] = idx
        return idx

    @jit.dont_look_inside
    def const_node(self, const):
        const = _canonical_const(const)
        node = self._consts.get(const, None)
        if node is not None:
            return node
        name = const.name
        if name.syntactic_eq(W_App._QUOT_LIFT):
            self._consts[const] = _C_QUOT_LIFT
            return _C_QUOT_LIFT
        if name.syntactic_eq(W_App._QUOT_MK):
            node = CCtor(
                cidx=0,
                ctor_id=self._ctor_id(name),
                induct_id=self._induct_id(name),
                num_params=2,
                num_fields=1,
                tag_kind=CTOR_QUOT_MK,
                const=const,
            )
            self._consts[const] = node
            return node
        decl = find_decl(self.declarations, name)
        if decl is None:
            # Don't cache absent declarations: streaming parse may declare them later.
            return COpaque(const)
        kind = decl.w_kind
        if isinstance(kind, W_Constructor):
            tag_kind = CTOR_NORMAL
            if name.syntactic_eq(_BOOL_TRUE.name):
                tag_kind = CTOR_BOOL_TRUE
            elif name.syntactic_eq(_BOOL_FALSE.name):
                tag_kind = CTOR_BOOL_FALSE
            elif name.syntactic_eq(NAT_ZERO.name):
                tag_kind = CTOR_NAT_ZERO
            elif name.syntactic_eq(_NAT_SUCC_NAME):
                tag_kind = CTOR_NAT_SUCC
            node = CCtor(
                cidx=kind.cidx,
                ctor_id=self._ctor_id(name),
                induct_id=self._induct_id(kind.induct),
                num_params=kind.num_params,
                num_fields=kind.num_fields,
                tag_kind=tag_kind,
                const=const,
            )
            self._consts[const] = node
            return node
        if isinstance(kind, W_Recursor):
            level_subst = None
            if decl.levels:
                if len(decl.levels) != len(const.levels):
                    raise _EvalBail()
                level_subst = {}
                for i in range(len(decl.levels)):
                    level_subst[decl.levels[i]] = const.levels[i]
            nrules = len(kind.rules)
            rules_rhs = [None] * nrules
            rules_nfields = [0] * nrules
            rules_ctor_ids = [0] * nrules
            rules_is_rec = [False] * nrules
            ind_id = self._induct_id(kind.all[0]) if kind.all else -1
            is_simple = len(kind.all) == 1
            for i in range(nrules):
                r = kind.rules[i]
                cdecl = find_decl(self.declarations, r.ctor_name)
                if cdecl is None:
                    is_simple = False
                else:
                    ckind = cdecl.w_kind
                    if not isinstance(ckind, W_Constructor):
                        is_simple = False
                    elif (ckind.cidx != i
                            or self._induct_id(ckind.induct) != ind_id):
                        is_simple = False
                rules_ctor_ids[i] = self._ctor_id(r.ctor_name)
                rules_nfields[i] = r.num_fields
            is_nat_rec = name.syntactic_eq(_NAT_REC_NAME)
            node = CRec(
                const=const,
                induct_id=ind_id,
                num_params=kind.num_params,
                num_motives=kind.num_motives,
                num_minors=kind.num_minors,
                num_indices=kind.num_indices,
                is_nat_rec=is_nat_rec,
                is_k=(kind.k == 1),
                is_simple_cidx=is_simple,
                rules_rhs=rules_rhs,
                rules_nfields=rules_nfields,
                rules_ctor_ids=rules_ctor_ids,
                rules_is_rec=rules_is_rec,
            )
            # Register before compiling rule RHSs because recursive recursors
            # (Nat.rec, List.rec, ...) reference themselves inside their rules.
            self._consts[const] = node
            for i in range(nrules):
                r = kind.rules[i]
                rhs_node = self.compile_wexpr(r.rhs, level_subst)
                rules_rhs[i] = rhs_node
                rules_is_rec[i] = _code_has_rec(rhs_node)
            return node
        if isinstance(kind, W_Definition):
            target = kind.get_delta_reduce_target()
            if target is not None:
                op_id = _nat_op_id(name)
                node = CDef(const, decl, op_id)
                self._consts[const] = node
                return node
        node = COpaque(const)
        self._consts[const] = node
        return node

    @jit.dont_look_inside
    def ensure_def_body(self, def_node):
        if def_node.is_compiled:
            return def_node.body
        decl = def_node.decl
        const = def_node.const
        kind = decl.w_kind
        assert isinstance(kind, W_Definition)
        target = kind.get_delta_reduce_target()
        assert target is not None
        level_subst = None
        if decl.levels:
            if len(decl.levels) != len(const.levels):
                raise _EvalBail()
            level_subst = {}
            for i in range(len(decl.levels)):
                level_subst[decl.levels[i]] = const.levels[i]
        body = self.compile_wexpr(target, level_subst)
        def_node.body = body
        def_node.is_compiled = True
        return body

    @jit.dont_look_inside
    def compile_wexpr(self, expr, level_subst):
        """Iteratively compile a `W_Expr` DAG into immutable `CodeNode`s."""
        memo = r_dict(_expr_is, _expr_id_hash)
        return self._compile_wexpr_iter(expr, level_subst, memo)

    def _compile_wexpr_iter(self, root, level_subst, memo):
        # Explicit post-order stack so deep literal Lists / nested apps
        # never blow the C stack.
        # Frames: (expr, state): state 0 = visit, state 1 = finish
        stack_expr = [root]
        stack_state = [0]
        while stack_expr:
            e = stack_expr.pop()
            st = stack_state.pop()
            if e in memo:
                continue
            if st == 0:
                cls = e.__class__
                if cls is W_BVar:
                    assert isinstance(e, W_BVar)
                    memo[e] = _mk_bvar(e.id)
                elif cls is W_LitNat:
                    assert isinstance(e, W_LitNat)
                    memo[e] = CVal(mk_const_nat_from_bigint(e.val))
                elif cls is W_LitStr:
                    assert isinstance(e, W_LitStr)
                    memo[e] = CVal(self.litstr_val(e))
                elif cls is W_Const:
                    assert isinstance(e, W_Const)
                    c = _subst_const_levels(e, level_subst)
                    node = self.const_node(c)
                    if isinstance(node, CCtor) and node.singleton_val is not None:
                        memo[e] = CVal(node.singleton_val)
                    else:
                        memo[e] = node
                elif cls is W_App:
                    # Flatten the entire spine iteratively.
                    cur = e
                    rev_args = []
                    while isinstance(cur, W_App):
                        rev_args.append(cur.arg)
                        cur = cur.fn
                    stack_expr.append(e)
                    stack_state.append(1)
                    if cur not in memo:
                        stack_expr.append(cur)
                        stack_state.append(0)
                    for a in rev_args:
                        if a not in memo:
                            stack_expr.append(a)
                            stack_state.append(0)
                elif cls is W_Lambda:
                    assert isinstance(e, W_Lambda)
                    stack_expr.append(e)
                    stack_state.append(1)
                    if e.body not in memo:
                        stack_expr.append(e.body)
                        stack_state.append(0)
                elif cls is W_Let:
                    assert isinstance(e, W_Let)
                    stack_expr.append(e)
                    stack_state.append(1)
                    if e.value not in memo:
                        stack_expr.append(e.value)
                        stack_state.append(0)
                    if e.body not in memo:
                        stack_expr.append(e.body)
                        stack_state.append(0)
                elif cls is W_Proj:
                    assert isinstance(e, W_Proj)
                    stack_expr.append(e)
                    stack_state.append(1)
                    if e.struct_expr not in memo:
                        stack_expr.append(e.struct_expr)
                        stack_state.append(0)
                else:
                    # W_Sort, W_ForAll, W_LitStr, W_FVar -> inert atom
                    memo[e] = CVal(VAtom(COpaque(None)))
            else:
                cls = e.__class__
                if cls is W_App:
                    cur = e
                    rev_args = []
                    while isinstance(cur, W_App):
                        rev_args.append(cur.arg)
                        cur = cur.fn
                    fn_node = memo[cur]
                    n = len(rev_args)
                    cargs = [None] * n
                    for i in range(n):
                        cargs[i] = memo[rev_args[n - 1 - i]]
                    if isinstance(fn_node, CCtor) and n == fn_node.total_arity:
                        fields_closed = True
                        np = fn_node.num_params
                        for i in range(np, n):
                            ae = rev_args[n - 1 - i]
                            if ae.loose_bvar_range() != 0 or ae.has_fvar():
                                fields_closed = False
                                break
                        memo[e] = _compile_full_ctor(
                            fn_node, cargs, fields_closed,
                        )
                    else:
                        memo[e] = CApp(fn_node, cargs)
                elif cls is W_Lambda:
                    assert isinstance(e, W_Lambda)
                    memo[e] = CLam(memo[e.body])
                elif cls is W_Let:
                    assert isinstance(e, W_Let)
                    memo[e] = CLet(memo[e.value], memo[e.body])
                elif cls is W_Proj:
                    assert isinstance(e, W_Proj)
                    memo[e] = CProj(memo[e.struct_expr], e.field_index)
        return memo[root]

    @jit.dont_look_inside
    def compile_handle(self, store, root_h):
        """Iteratively compile a `TermStore` handle DAG into `CodeNode`s."""
        from rpylean.machine import (
            KIND_APP, KIND_LAMBDA, KIND_LET, KIND_PROJ, is_leaf,
        )
        memo = {}
        stack_h = [root_h]
        stack_st = [0]
        while stack_h:
            h = stack_h.pop()
            st = stack_st.pop()
            if h in memo:
                continue
            if st == 0:
                if is_leaf(h):
                    e = store.leaf(h)
                    cls = e.__class__
                    if cls is W_BVar:
                        assert isinstance(e, W_BVar)
                        memo[h] = _mk_bvar(e.id)
                    elif cls is W_LitNat:
                        assert isinstance(e, W_LitNat)
                        memo[h] = CVal(mk_const_nat_from_bigint(e.val))
                    elif cls is W_LitStr:
                        assert isinstance(e, W_LitStr)
                        memo[h] = CVal(self.litstr_val(e))
                    elif cls is W_Const:
                        assert isinstance(e, W_Const)
                        node = self.const_node(e)
                        if (isinstance(node, CCtor)
                                and node.singleton_val is not None):
                            memo[h] = CVal(node.singleton_val)
                        else:
                            memo[h] = node
                    else:
                        memo[h] = CVal(VAtom(COpaque(None)))
                    continue
                kind = store.kind(h)
                if kind == KIND_APP:
                    cur = h
                    rev_args = []
                    while store.kind(cur) == KIND_APP:
                        rev_args.append(store.field_b(cur))
                        cur = store.field_a(cur)
                    stack_h.append(h)
                    stack_st.append(1)
                    if cur not in memo:
                        stack_h.append(cur)
                        stack_st.append(0)
                    for a in rev_args:
                        if a not in memo:
                            stack_h.append(a)
                            stack_st.append(0)
                elif kind == KIND_LAMBDA:
                    body = store.field_b(h)
                    stack_h.append(h)
                    stack_st.append(1)
                    if body not in memo:
                        stack_h.append(body)
                        stack_st.append(0)
                elif kind == KIND_LET:
                    pair = store.field_b(h)
                    val_h = store.field_a(pair)
                    body_h = store.field_b(pair)
                    stack_h.append(h)
                    stack_st.append(1)
                    if val_h not in memo:
                        stack_h.append(val_h)
                        stack_st.append(0)
                    if body_h not in memo:
                        stack_h.append(body_h)
                        stack_st.append(0)
                elif kind == KIND_PROJ:
                    s_h = store.field_a(h)
                    stack_h.append(h)
                    stack_st.append(1)
                    if s_h not in memo:
                        stack_h.append(s_h)
                        stack_st.append(0)
                else:
                    memo[h] = CVal(VAtom(COpaque(None)))
            else:
                kind = store.kind(h)
                if kind == KIND_APP:
                    cur = h
                    rev_args = []
                    while store.kind(cur) == KIND_APP:
                        rev_args.append(store.field_b(cur))
                        cur = store.field_a(cur)
                    fn_node = memo[cur]
                    n = len(rev_args)
                    cargs = [None] * n
                    for i in range(n):
                        cargs[i] = memo[rev_args[n - 1 - i]]
                    if isinstance(fn_node, CCtor) and n == fn_node.total_arity:
                        fields_closed = True
                        np = fn_node.num_params
                        for i in range(np, n):
                            ah = rev_args[n - 1 - i]
                            if (store.loose_bvar_range(ah) != 0
                                    or store.has_fvar(ah)):
                                fields_closed = False
                                break
                        memo[h] = _compile_full_ctor(
                            fn_node, cargs, fields_closed,
                        )
                    else:
                        memo[h] = CApp(fn_node, cargs)
                elif kind == KIND_LAMBDA:
                    memo[h] = CLam(memo[store.field_b(h)])
                elif kind == KIND_LET:
                    pair = store.field_b(h)
                    memo[h] = CLet(
                        memo[store.field_a(pair)], memo[store.field_b(pair)],
                    )
                elif kind == KIND_PROJ:
                    memo[h] = CProj(memo[store.field_a(h)], store.proj_index(h))
        return memo[root_h]


# ---- The meta-traced call-by-need abstract machine -----------------------

def _printable_location(rec_edge, code):
    tag = code.tag
    if tag == TAG_DEF:
        assert isinstance(code, CDef)
        return "def:%s" % code.name_str
    if tag == TAG_REC:
        assert isinstance(code, CRec)
        return "rec:%s" % code.name_str
    if tag == TAG_LAM:
        return "lam"
    if tag == TAG_APP:
        return "app"
    if tag == TAG_BVAR:
        return "bvar"
    if tag == TAG_PROJ:
        return "proj"
    if tag == TAG_LET:
        return "let"
    if tag == TAG_CTOR:
        return "ctor"
    if tag == TAG_FULL_CTOR:
        return "full_ctor"
    if tag == TAG_NAT_OP:
        return "nat_op"
    return "eval:%d" % tag


eval_jitdriver = jit.JitDriver(
    greens=['rec_edge', 'code'],
    reds=['steps', 'env', 'args', 'cont', 'cache', 'tc'],
    name='lean_eval',
    get_printable_location=_printable_location,
)


@jit.dont_look_inside
def _check_limits(tc):
    if tc.has_limits:
        tc.tick_wall_time()


@jit.dont_look_inside
def _expand_litstr(val, cache, tc):
    exp = val.expanded
    if exp is not None:
        return exp
    code = cache.compile_wexpr(val.lit.build_str_expr(), None)
    exp = eval_whnf(code, cache, tc)
    val.expanded = exp
    return exp


def _arg_to_slot(arg_code, env):
    tag = arg_code.tag
    if tag == TAG_VAL:
        assert isinstance(arg_code, CVal)
        return arg_code.val
    if tag == TAG_BVAR:
        assert isinstance(arg_code, CBVar)
        return lookup_env(env, arg_code.idx)
    if tag == TAG_LAM:
        assert isinstance(arg_code, CLam)
        return VClosure(arg_code, env)
    if tag == TAG_CTOR:
        assert isinstance(arg_code, CCtor)
        if arg_code.singleton_val is not None:
            return arg_code.singleton_val
    return Thunk(arg_code, env)


@jit.unroll_safe
def _push_spine(cargs, env, args):
    i = len(cargs) - 1
    while i >= 0:
        args = ArgNode(_arg_to_slot(cargs[i], env), args)
        i -= 1
    return args


@jit.unroll_safe
def _eval_ctor_fields(fc, env):
    nf = len(fc)
    out = [None] * nf
    i = 0
    while i < nf:
        out[i] = _arg_to_slot(fc[i], env)
        i += 1
    return out


@jit.unroll_safe
def _pop_prefix(args, skip):
    prefix = [None] * skip
    i = 0
    while i < skip:
        if args is None:
            raise _EvalBail()
        prefix[i] = args.slot
        args = args.tail
        i += 1
    return prefix, args


@jit.unroll_safe
def _push_ctor_fields(fields, count, args):
    i = count - 1
    while i >= 0:
        args = ArgNode(fields[i], args)
        i -= 1
    return args


@jit.unroll_safe
def _push_prefix_keep(prefix, keep, args):
    i = keep - 1
    while i >= 0:
        args = ArgNode(prefix[i], args)
        i -= 1
    return args


@jit.unroll_safe
def _pop_ctor_args(args, arity):
    n = 0
    cur = args
    while n < arity and cur is not None:
        n += 1
        cur = cur.tail
    collected = [None] * n
    i = 0
    while i < n:
        collected[i] = args.slot
        args = args.tail
        i += 1
    return collected, args


@jit.unroll_safe
def _mk_vctor_from_all_args(ctor_node, all_args):
    nf = ctor_node.num_fields
    if nf == 0:
        return ctor_node.zero_field_val
    np = ctor_node.num_params
    if nf == 1:
        return VCtor1(ctor_node, all_args[np])
    if nf == 2:
        return VCtor2(ctor_node, all_args[np], all_args[np + 1])
    fields = [None] * nf
    i = 0
    while i < nf:
        fields[i] = all_args[np + i]
        i += 1
    return VCtorN(ctor_node, fields)


def _collect_partial_ctor(existing, args):
    extra = 0
    cur = args
    while cur is not None:
        extra += 1
        cur = cur.tail
    n_exist = len(existing)
    out = [None] * (n_exist + extra)
    i = 0
    while i < n_exist:
        out[i] = existing[i]
        i += 1
    while args is not None:
        out[i] = args.slot
        args = args.tail
        i += 1
    return out


def eval_whnf(root_code, cache, tc):
    """Evaluate closed `root_code` to WHNF `Val`, or raise `_EvalBail`."""
    code = root_code
    rec_edge = False
    env = None
    args = None
    cont = None
    steps = 0

    while True:
        eval_jitdriver.jit_merge_point(
            code=code, rec_edge=rec_edge,
            steps=steps, env=env, args=args, cont=cont,
            cache=cache, tc=tc,
        )

        is_backedge = False
        slot = None
        tag = code.tag

        if tag == TAG_APP:
            assert isinstance(code, CApp)
            args = _push_spine(code.args, env, args)
            code = code.fn
            continue

        if tag == TAG_LAM:
            assert isinstance(code, CLam)
            if args is not None:
                env = extend_env(env, args.slot)
                args = args.tail
                code = code.body
                continue
            rec_edge = False
            slot = VClosure(code, env)
            env = None

        elif tag == TAG_BVAR:
            assert isinstance(code, CBVar)
            slot = lookup_env(env, code.idx)
            env = None

        elif tag == TAG_VAL:
            assert isinstance(code, CVal)
            rec_edge = False
            slot = code.val
            env = None

        elif tag == TAG_FULL_CTOR:
            assert isinstance(code, CFullCtor)
            if args is not None:
                raise _EvalBail()
            rec_edge = False
            fc = code.field_codes
            nf = len(fc)
            if nf == 1:
                slot = VCtor1(code.ctor_node, _arg_to_slot(fc[0], env))
            elif nf == 2:
                slot = VCtor2(
                    code.ctor_node,
                    _arg_to_slot(fc[0], env),
                    _arg_to_slot(fc[1], env),
                )
            else:
                slot = VCtorN(code.ctor_node, _eval_ctor_fields(fc, env))
            env = None

        elif tag == TAG_DEF:
            assert isinstance(code, CDef)
            op_id = code.nat_op
            if op_id != OP_NONE and args is not None and args.tail is not None:
                rec_edge = False
                arg1 = args.slot
                arg2 = args.tail.slot
                rest = args.tail.tail
                cont = KNatOp1(op_id, arg2, rest, cont)
                args = None
                env = None
                slot = arg1
            else:
                if code.is_compiled:
                    body = code.body
                else:
                    body = cache.ensure_def_body(code)
                code = body
                env = None
                if rec_edge:
                    rec_edge = False
                    is_backedge = True
                else:
                    continue

        elif tag == TAG_NAT_OP:
            assert isinstance(code, CNatOp)
            if env is None or env.prev is None:
                raise _EvalBail()
            rec_edge = False
            arg2 = env.slot
            arg1 = env.prev.slot
            cont = KNatOp1(code.op_id, arg2, args, cont)
            args = None
            env = None
            slot = arg1

        elif tag == TAG_REC:
            assert isinstance(code, CRec)
            rec_edge = False
            prefix, rem = _pop_prefix(args, code.skip)
            if rem is None:
                raise _EvalBail()
            major = rem.slot
            trailing = rem.tail
            cont = KRecMajor(code, prefix, trailing, cont)
            args = None
            env = None
            slot = major

        elif tag == TAG_CTOR:
            assert isinstance(code, CCtor)
            rec_edge = False
            if code.singleton_val is not None:
                slot = code.singleton_val
                env = None
            else:
                collected, rem = _pop_ctor_args(args, code.total_arity)
                if rem is not None:
                    raise _EvalBail()
                if len(collected) == code.total_arity:
                    slot = _mk_vctor_from_all_args(code, collected)
                else:
                    slot = VPartialCtor(code, collected)
                args = None
                env = None

        elif tag == TAG_LET:
            assert isinstance(code, CLet)
            val_slot = _arg_to_slot(code.val_code, env)
            env = extend_env(env, val_slot)
            code = code.body
            continue

        elif tag == TAG_PROJ:
            assert isinstance(code, CProj)
            cont = KProj(code.field_idx, args, cont)
            args = None
            code = code.struct_code
            continue

        elif tag == TAG_QUOT_LIFT:
            rec_edge = False
            prefix, rem = _pop_prefix(args, 6)
            fn_slot = prefix[3]
            major = prefix[5]
            cont = KQuotLift(fn_slot, rem, cont)
            args = None
            env = None
            slot = major

        else:
            # TAG_OPAQUE or unknown
            raise _EvalBail()

        # ---- Inner force / apply loop: resolve `slot` -> WHNF `val` ----
        if not is_backedge:
            assert slot is not None
            while True:
                if isinstance(slot, Val):
                    val = slot
                else:
                    assert isinstance(slot, Thunk)
                    cached = slot.val
                    if cached is not None:
                        val = cached
                    elif isinstance(slot, RecNatThunk):
                        cont = KUpdate(slot, args, cont)
                        args = ArgNode(
                            slot.motive,
                            ArgNode(
                                slot.zero_case,
                                ArgNode(
                                    slot.succ_case,
                                    ArgNode(slot.pred_slot, None),
                                ),
                            ),
                        )
                        code = jit.promote(slot.rec_node)
                        env = None
                        rec_edge = False
                        break
                    else:
                        cont = KUpdate(slot, args, cont)
                        args = None
                        code = jit.promote(slot.code)
                        env = slot.env
                        if rec_edge:
                            rec_edge = False
                            is_backedge = True
                        break

                if args is not None:
                    if isinstance(val, VClosure):
                        lam = jit.promote(val.lam_node)
                        env = extend_env(val.env, args.slot)
                        args = args.tail
                        code = lam.body
                        if rec_edge:
                            rec_edge = False
                            is_backedge = True
                        break
                    if isinstance(val, VPartialCtor):
                        ctor_node = jit.promote(val.ctor_node)
                        new_args = _collect_partial_ctor(val.collected, args)
                        if len(new_args) > ctor_node.total_arity:
                            raise _EvalBail()
                        if len(new_args) == ctor_node.total_arity:
                            val = _mk_vctor_from_all_args(ctor_node, new_args)
                        else:
                            val = VPartialCtor(ctor_node, new_args)
                        args = None
                        rec_edge = False
                    else:
                        raise _EvalBail()

                if cont is None:
                    return val

                if isinstance(cont, KUpdate):
                    cont.thunk.val = val
                    args = cont.args
                    cont = cont.next
                    slot = val
                    continue

                if isinstance(cont, KRecMajor):
                    rec_node = jit.promote(cont.rec_node)
                    prefix = cont.prefix
                    trailing = cont.args
                    next_cont = cont.next

                    if isinstance(val, VLitStr):
                        exp = val.expanded
                        if exp is None:
                            exp = _expand_litstr(val, cache, tc)
                        val = exp

                    if rec_node.is_nat_rec:
                        if isinstance(val, VSmallNat):
                            n = val.n
                            if n == 0:
                                target = prefix[1]
                                args = trailing
                                rec_edge = False
                            else:
                                pred = mk_small_nat(n - 1)
                                ih = RecNatThunk(
                                    rec_node, prefix[0], prefix[1], prefix[2], pred,
                                )
                                target = prefix[2]
                                args = ArgNode(pred, ArgNode(ih, trailing))
                                rec_edge = True
                        elif isinstance(val, VBigNat):
                            if val.big.eq(_BIG_ZERO):
                                target = prefix[1]
                                args = trailing
                                rec_edge = False
                            else:
                                pred = mk_nat_from_bigint(val.big.sub(_BIG_ONE))
                                ih = RecNatThunk(
                                    rec_node, prefix[0], prefix[1], prefix[2], pred,
                                )
                                target = prefix[2]
                                args = ArgNode(pred, ArgNode(ih, trailing))
                                rec_edge = True
                        elif isinstance(val, VCtor1):
                            cnode = jit.promote(val.ctor_node)
                            if cnode.tag_kind == CTOR_NAT_SUCC:
                                pred = val.f0
                                ih = RecNatThunk(
                                    rec_node, prefix[0], prefix[1], prefix[2], pred,
                                )
                                target = prefix[2]
                                args = ArgNode(pred, ArgNode(ih, trailing))
                                rec_edge = True
                            else:
                                raise _EvalBail()
                        else:
                            raise _EvalBail()

                        cont = next_cont
                        slot = target
                        continue

                    if isinstance(val, VCtor):
                        cnode = jit.promote(val.ctor_node)
                        ridx = rec_node.rule_index(cnode)
                        if ridx < 0:
                            raise _EvalBail()
                        rhs = rec_node.rules_rhs[ridx]
                        nfields = rec_node.rules_nfields[ridx]
                        if isinstance(val, VCtor0):
                            if nfields != 0:
                                raise _EvalBail()
                            new_args = trailing
                        elif isinstance(val, VCtor1):
                            if nfields != 1:
                                raise _EvalBail()
                            new_args = ArgNode(val.f0, trailing)
                        elif isinstance(val, VCtor2):
                            if nfields != 2:
                                raise _EvalBail()
                            new_args = ArgNode(val.f0, ArgNode(val.f1, trailing))
                        elif isinstance(val, VCtorN):
                            if nfields > len(val.fields):
                                raise _EvalBail()
                            new_args = _push_ctor_fields(
                                val.fields, nfields, trailing,
                            )
                        else:
                            raise _EvalBail()
                        new_args = _push_prefix_keep(
                            prefix, rec_node.keep, new_args,
                        )
                        args = new_args
                        cont = next_cont
                        code = rhs
                        env = None
                        rec_edge = rec_node.rules_is_rec[ridx]
                        break

                    raise _EvalBail()

                if isinstance(cont, KProj):
                    fidx = jit.promote(cont.field_idx)
                    if isinstance(val, VLitStr):
                        exp = val.expanded
                        if exp is None:
                            exp = _expand_litstr(val, cache, tc)
                        val = exp
                    if isinstance(val, VCtor1):
                        if fidx != 0:
                            raise _EvalBail()
                        slot = val.f0
                    elif isinstance(val, VCtor2):
                        if fidx == 0:
                            slot = val.f0
                        elif fidx == 1:
                            slot = val.f1
                        else:
                            raise _EvalBail()
                    elif isinstance(val, VCtorN):
                        if fidx >= len(val.fields):
                            raise _EvalBail()
                        slot = val.fields[fidx]
                    else:
                        raise _EvalBail()
                    args = cont.args
                    cont = cont.next
                    continue

                if isinstance(cont, KNatOp1):
                    if isinstance(val, VCtor1):
                        cnode = jit.promote(val.ctor_node)
                        if cnode.tag_kind == CTOR_NAT_SUCC:
                            slot = val.f0
                            cont = KNatSucc(1, cont)
                            continue
                        raise _EvalBail()
                    if not (isinstance(val, VSmallNat) or isinstance(val, VBigNat)):
                        raise _EvalBail()
                    slot = cont.arg2
                    cont = KNatOp2(cont.op_id, val, cont.args, cont.next)
                    continue

                if isinstance(cont, KNatOp2):
                    if isinstance(val, VCtor1):
                        cnode = jit.promote(val.ctor_node)
                        if cnode.tag_kind == CTOR_NAT_SUCC:
                            slot = val.f0
                            cont = KNatSucc(1, cont)
                            continue
                        raise _EvalBail()
                    if not (isinstance(val, VSmallNat) or isinstance(val, VBigNat)):
                        raise _EvalBail()
                    op_id = jit.promote(cont.op_id)
                    val = _eval_nat_op(op_id, cont.v1, val, cache)
                    args = cont.args
                    cont = cont.next
                    slot = val
                    continue

                if isinstance(cont, KNatSucc):
                    if isinstance(val, VCtor1):
                        cnode = jit.promote(val.ctor_node)
                        if cnode.tag_kind == CTOR_NAT_SUCC:
                            slot = val.f0
                            cont = KNatSucc(cont.succs + 1, cont.next)
                            continue
                        raise _EvalBail()
                    if isinstance(val, VSmallNat):
                        val = _add_small_int(val.n, cont.succs)
                        cont = cont.next
                        slot = val
                        continue
                    if isinstance(val, VBigNat):
                        val = VBigNat(val.big.add(rbigint.fromint(cont.succs)))
                        cont = cont.next
                        slot = val
                        continue
                    raise _EvalBail()

                if isinstance(cont, KQuotLift):
                    if isinstance(val, VCtor1):
                        cnode = jit.promote(val.ctor_node)
                        if cnode.tag_kind == CTOR_QUOT_MK:
                            slot = cont.fn_slot
                            args = ArgNode(val.f0, cont.args)
                            cont = cont.next
                            continue
                    raise _EvalBail()

                raise _EvalBail()

        if is_backedge:
            steps += 1
            if (steps & 16383) == 0:
                _check_limits(tc)
            eval_jitdriver.can_enter_jit(
                code=code, rec_edge=rec_edge,
                steps=steps, env=env, args=args, cont=cont,
                cache=cache, tc=tc,
            )


# ---- Entry point from Machine --------------------------------------------

def eval_closed_scalar(machine, h):
    """
    Evaluate a closed term handle ``h`` to a Bool or Nat scalar handle in
    ``machine.store``, or return 0 if evaluation bails or yields a non-scalar.
    """
    env = machine.tc.env
    cache = env._code_cache
    if cache is None:
        cache = CodeCache(env.declarations)
        env._code_cache = cache
    cache._refresh_bools()
    try:
        root = cache.compile_handle(machine.store, h)
        val = eval_whnf(root, cache, machine.tc)
    except _EvalBail:
        return 0
    if isinstance(val, VSmallNat):
        return machine.store.leaf_for(_mk_w_litnat(rbigint.fromint(val.n)))
    if isinstance(val, VBigNat):
        return machine.store.leaf_for(_mk_w_litnat(val.big))
    if isinstance(val, VCtor):
        tk = val.ctor_node.tag_kind
        if tk == CTOR_BOOL_TRUE:
            return machine.h_true
        if tk == CTOR_BOOL_FALSE:
            return machine.h_false
        if tk == CTOR_NAT_ZERO:
            return machine.h_nat_zero
    return 0
