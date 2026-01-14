import Fp.Basic
import Fp.Rounding

/-- Negate the fixed point number -/
@[bv_normalize]
def f_neg (a : FixedPoint w e) : FixedPoint w e := { a with sign := !a.sign }

/-- Negate the extended fixed point number -/
@[bv_normalize]
def e_neg (a : EFixedPoint w e) : EFixedPoint w e :=
  open EFixedPoint in
  have := a.num.hExOffset
  if hN : a.state = .NaN then
    getNaN (by omega)
  else if hInf : a.state = .Infinity then
    getInfinity (!a.num.sign) (by omega)
  else
    let _ : a.state = .Number := by
      cases h : a.state <;> simp_all
    { a with num := f_neg a.num }

/-- Negate a floating-point number, by conversion to a fixed-point number. -/
@[bv_normalize]
def negfixed (a : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  EFixedPoint.round _ _ mode (e_neg a.toEFixed)

/--
Negate a floating-point number, by flipping the sign bit.

This implements the same function as `negfixed`, but is much simpler.
-/
@[bv_normalize]
def neg (a : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN then PackedFloat.getNaN _ _
  else { a with sign := !a.sign }

@[bv_normalize]
def abs (a : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN then PackedFloat.getNaN _ _
  else { a with sign := false }
