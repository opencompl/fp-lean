import Fp.Basic
import Fp.Rounding

/--
Addition of two fixed-point numbers.

When the sum is zero, the sign of the zero is dependent on the provided
rounding mode.
-/
@[bv_normalize]
def f_add (mode : RoundingMode) (a b : FixedPoint w e) : FixedPoint (w+1) e :=
  let hExOffset : e < w+1 := by
    exact Nat.lt_add_right 1 a.hExOffset
  let ax := BitVec.setWidth' (by omega) a.val
  let bx := BitVec.setWidth' (by omega) b.val
  if a.sign == b.sign then
    -- Addition of same-signed numbers always preserves sign
    {
      sign := a.sign
      val := BitVec.add ax bx
      hExOffset := hExOffset
    }
  else if BitVec.ult ax bx then
    {
      sign := b.sign
      val := BitVec.sub bx ax
      hExOffset := hExOffset
    }
  else if BitVec.ult bx ax then
    {
      sign := a.sign
      val := BitVec.sub ax bx
      hExOffset := hExOffset
    }
  else
    -- Signs are different but values are same, so return +0.0
    -- When rounding mode is RTN we should instead return -0.0
    {
      sign := mode = .RTN
      val := 0#_
      hExOffset := hExOffset
    }

/--
Addition of two extended fixed-point numbers.

When the sum is zero, the sign of the zero is dependent on the provided
rounding mode.
-/
@[bv_normalize]
def e_add (mode : RoundingMode) (a b : EFixedPoint w e) : EFixedPoint (w+1) e :=
  open EFixedPoint in
  let hExOffset : e < w + 1 := by
    exact Nat.lt_add_right 1 a.num.hExOffset
  -- As of 2025-04-14, bv_decide does not support pattern matches on more than
  -- one variable, so we'll have to deal with if-statements for now
  if hN : a.state = .NaN || b.state = .NaN then getNaN hExOffset
  else if hI1 : a.state = .Infinity && b.state = .Infinity then
    if a.num.sign == b.num.sign then getInfinity a.num.sign hExOffset
    else getNaN hExOffset
  else if hI2 : a.state = .Infinity then getInfinity a.num.sign hExOffset
  else if hI3 : b.state = .Infinity then getInfinity b.num.sign hExOffset
  else
  -- is this how to do assertions?
  let _ : a.state = .Number && b.state = .Number := by
    cases ha : a.state <;> cases hb : b.state <;> simp_all
  {
    state := .Number
    num := f_add mode a.num b.num
  }

/--
Addition of two floating point numbers, rounded to a floating point number
using the provided rounding mode.
-/
@[bv_normalize]
def add (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  round _ _ mode (e_add mode a.toEFixed b.toEFixed)

-- Proof by brute force (it takes a while)
/-
theorem PackedFloat_add_comm' (m : RoundingMode) (a b : PackedFloat 5 2)
  : (add a b m) = (add b a m) := by
  apply PackedFloat.inj
  simp [add, e_add, f_add, round, PackedFloat.toEFixed, -BitVec.shiftLeft_eq', -BitVec.ushiftRight_eq']
  bv_decide
-/

/-- info: { sign := +, ex := 0x04#5, sig := 0x0#2 } -/
#guard_msgs in #eval add (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8) .RNE
/-- info: { sign := +, ex := 0x04#5, sig := 0x1#2 } -/
#guard_msgs in #eval add (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8) .RNA
