"""
Definitions of Lean's quotient type.
"""
from rpylean.objects import Name, W_BVar, forall


u, v = Name.simple("u").level(), Name.simple("v").level()
alpha = Name.simple("α").implicit_binder(type=u.sort())
Quot = Name.simple("Quot")
r = Name.simple("r")
b0, b1 = W_BVar(0), W_BVar(1)
QUOT = forall(alpha, r.binder(type=b0))(  # FIXME: Actual definitions.
    u.sort(),
)
QUOT_MK = QUOT
QUOT_IND = QUOT
QUOT_LIFT = QUOT
