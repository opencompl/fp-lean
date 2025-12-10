import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.Subtraction
import Fp.Negation
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat

@[simp] theorem e_sub_eq_add_neg (mode : RoundingMode) (a b : EFixedPoint w e) :
  e_sub mode a b = e_add mode a (e_neg b) := rfl

