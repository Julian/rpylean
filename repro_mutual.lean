mutual
inductive A2 (b : Bool) : Type where
  | mk : B2 b → A2 b
inductive B2 (b : Bool) : Type where
  | mkB : A2 b → B2 b
end

mutual
inductive C (b : Bool) : Type where
  | node : Array (D b) → C b
inductive D (b : Bool) : Type where
  | leaf : D b
  | up : C b → D b
end
