import Fp.Basic
import Fp.Rounding
import Fp.Addition
import Fp.Multiplication

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

@[bv_normalize]
def fma (a b c : PackedFloat e s) (m : RoundingMode)
  : PackedFloat e s :=
  if a.isNaN || b.isNaN || c.isNaN ||
    (a.isInfinite && b.isZero) ||
    (b.isInfinite && a.isZero) then PackedFloat.getNaN _ _
  else if a.isInfinite || b.isInfinite then
    let interSign := (a.sign ^^ b.sign)
    if c.isInfinite && c.sign != interSign then
      PackedFloat.getNaN _ _
    else
      PackedFloat.getInfinity _ _ interSign
  else
    let sa := BitVec.ofBool (a.ex != 0) ++ a.sig
    let sb := BitVec.ofBool (b.ex != 0) ++ b.sig
    let shift : BitVec (e+1) :=
      (if a.ex == 0 then 0 else a.ex - 1).setWidth _ +
      (if b.ex == 0 then 0 else b.ex - 1).setWidth _
    let prod := sa.setWidth (2*(s+1)) * sb.setWidth (2*(s+1))
    let result : EFixedPoint (2*(2^e + s)) (2*(2^(e-1) + s - 2)) :=
      {
        state := .Number
        num := {
          sign := a.sign ^^ b.sign
          val := prod.setWidth _ <<< shift
          hExOffset := by
            have h := toEFixed_hExOffset e s
            omega
        }
      }
    -- Used for proving bounds
    have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
    let added_result := e_add m result (c.toEFixed.expand _ _ (by omega) (by omega))
    EFixedPoint.round _ _ m added_result
