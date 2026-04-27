inductive ExtRat where
  | NaN : ExtRat
  | Infinity : Bool → ExtRat
  | Number : Rat → ExtRat
deriving DecidableEq, Repr
