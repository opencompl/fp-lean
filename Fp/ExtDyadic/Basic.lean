inductive ExtDyadic where
  | NaN : ExtDyadic
  | Infinity : Bool → ExtDyadic
  | Number : Dyadic → ExtDyadic
deriving DecidableEq
