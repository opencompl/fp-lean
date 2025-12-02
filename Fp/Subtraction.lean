import Fp.Basic
import Fp.Rounding
import Fp.Addition
import Fp.Negation

/--
Subtraction of two extended fixed-point numbers.
-/
@[bv_float_normalize]
def e_sub (mode : RoundingMode) (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
  e_add mode a (e_neg b)

/--
Subtraction of two floating-point numbers.

Implemented entirely within EFixedPoint using `e_sub`.
-/
@[bv_float_normalize]
def subfixed (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  round_to_packedFloat _ _ mode (e_sub mode a.toEFixed b.toEFixed)

/--
Subtraction of two floating-point numbers.

Implemented as a negation followed by an addition.
-/
@[bv_float_normalize]
def sub (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  add a (neg b) mode
