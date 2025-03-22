prelude

inductive MyTrue : Prop where
  | intro : MyTrue

theorem trueByRfl: MyTrue := MyTrue.intro
