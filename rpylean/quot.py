"""
Definitions of Lean's quotient type.
"""
from rpython.rlib.objectmodel import r_dict

from rpylean.objects import Name, W_BVar


u, v =  Name.simple("u").level(), Name.simple("v").level()
alpha = Name.simple("α").implicit_binder(type=u.sort())
Quot = Name.simple("Quot")
r = Name.simple("r")
b0, b1 = W_BVar(0), W_BVar(1)
QUOT = alpha.forall(
    body=r.binder(
        type=b0,
    ).forall(body=u.sort()),
)
QUOT_MK = None
QUOT_IND = None
QUOT_LIFT = None

QUOT_DECLS = r_dict(Name.eq, Name.hash)
