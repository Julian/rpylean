prelude

inductive Nat
| zero
| succ : Nat → Nat

inductive Bool
| true
| false

def A : Nat := .zero

def B : Bool := .true

