"""
Definitions of Lean's quotient type.
"""
from rpylean.objects import Name, _mk_w_bvar, forall


u, v = Name.simple("u").as_level_param(), Name.simple("v").as_level_param()
alpha = Name.simple("α").implicit_binder(type=u.sort())
Quot = Name.simple("Quot")
r = Name.simple("r")
b0, b1 = _mk_w_bvar(0), _mk_w_bvar(1)
QUOT = forall(alpha, r.binder(type=b0))(  # FIXME: Actual definitions.
    u.sort(),
)
QUOT_MK = QUOT
QUOT_IND = QUOT
QUOT_LIFT = QUOT
