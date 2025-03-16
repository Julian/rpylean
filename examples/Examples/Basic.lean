prelude

inductive MyTrue : Prop where
  | intro : MyTrue

theorem true_by_rfl: MyTrue := MyTrue.intro
