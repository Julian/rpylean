prelude

inductive True : Prop where
  | intro : True

theorem trueByRfl : True := True.intro
