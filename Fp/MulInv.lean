import Fp.Basic
import Fp.Rounding
import Fp.Proofs.Grind
import Fp.ForLean.Rat



def fixedWidthDivideAtPrecision (x y : BitVec w) (prec : Nat) (hprec : w + prec = outw)
    : BitVec outw :=
    let dividend := (x.setWidth outw <<< prec)
    let divisor := y.setWidth outw
    dividend / divisor

attribute [grind .] Nat.mul_lt_mul_of_lt_of_le -- blow up
-- attribute [grind] Nat.mul_lt_mul_of_lt_of_le
-- attribute [grind] Nat.mul_lt_mul_of_lt_of_le
-- attribute [grind] Nat.mul_lt_mul_of_lt_of_le
-- attribute [grind] Nat.mul_lt_mul_of_lt_of_le

@[simp]
theorem fixedWidthDivideAtPrecision_toNat_eq
    (x y : BitVec w) (prec : Nat) (hprec : w + prec = outw) :
    (fixedWidthDivideAtPrecision x y prec hprec).toNat =
      (x.toNat * 2 ^ prec) / y.toNat := by
  simp [fixedWidthDivideAtPrecision]
  have : x.toNat % 2^outw = x.toNat := by grind
  rw [this]
  have : y.toNat % 2^outw = y.toNat := by grind
  rw [this]
  rw [Nat.shiftLeft_eq]
  congr
  apply Nat.mod_eq_of_lt
  have : x.toNat < 2^w := by grind
  subst hprec
  rw [Nat.pow_add]
  apply Nat.mul_lt_mul_of_lt_of_le <;> grind

@[simp]
theorem Rat.add_div (a b c : Rat) :
    (a + b) / c = a / c + b / c := by
  grind

@[simp]
theorem Rat.mul_div_cancel_left
    (a c : Rat) (hc : c ≠ 0) :
    (c * a) / c = a := by
  grind

theorem Rat.mul_div_cancel_right
    (a c : Rat) (hc : c ≠ 0) :
    (a * c) / c = a := by
  grind

attribute [simp] Nat.mul_div_cancel
attribute [simp] Nat.mul_div_cancel_left
attribute [simp] Nat.mul_add_div

@[simp]
theorem Nat.mul_add_div'
    (a b c : Nat) (hc : c ≠ 0) :
    (c * a + b) / c = a + b / c := by
  apply Nat.mul_add_div
  omega

theorem fixedWidthDivideAtPrecision_abs_delta_eq
  (x y : BitVec w) (prec : Nat) (hprec : w + prec = outw) (hy : y.toNat ≠ 0) :
    ((Rat.ofNat x.toNat / Rat.ofNat y.toNat) -
      (Rat.ofNat ((x.toNat * 2 ^ prec) / y.toNat)) * Rat.twoPowInv prec) <
    Rat.twoPowInv prec := by
  have := Nat.div_add_mod x.toNat y.toNat
  rw [← this]
  simp [hy]
  generalize hk : x.toNat / y.toNat = k
  generalize hr : x.toNat % y.toNat = r
  have := Nat.div_add_mod (x.toNat * 2 ^ prec) y.toNat
  generalize hl : (x.toNat * 2 ^ prec / y.toNat) = l
  rw [hl] at this
  generalize hs :  x.toNat * 2 ^ prec % y.toNat  = s
  rw [hs] at this
  rw [← this]
  rw [Nat.mul_add_div]
  simp only [Nat.mod_div_self, Nat.add_zero, gt_iff_lt]

  -- rw [Rat.ofNat_div_ofNat_eq_ofNat_div_add_ofNat_mod (a := x.toNat * _)]
  sorry



/--
Fundamental theorem of fixed point division: dividing two integers and then scaling by a power of two
-/
theorem nat_div_loss_of_precision (prec n d : Nat) {hd : d ≠ 0} :
    ((Rat.ofInt (n * 2 ^ prec / d)) * Rat.twoPowInv prec  -  (mkRat n d)).abs < Rat.twoPowInv prec :=
  by
  sorry

/-- Compute the multiplicative inverse, with an output precision of 'f'.
(x/2^e)⁻¹ = 2^e/x = 2^(e+f)/x * 1/2^f. Numerator needs 'e + f + 1' bits.
-/
def f_mulinv (a : FixedPoint v e) : FixedPoint (v + f + 1) f :=
  let hExOffset := a.hExOffset
  let aExt : BitVec (v + f + 1) := a.val.zeroExtend _
  have : aExt.toNat = a.val.toNat := by grind
  have : e < v := by omega
  let twoPow : BitVec (v + f + 1) := BitVec.twoPow (v + f + 1) (e + f)
  let divResult := twoPow / aExt
  have hDivResult :
      divResult.toNat = 2 ^ (e + f) / a.val.toNat := by
    simp [divResult, twoPow, aExt]
    congr
    · rw [Nat.mod_eq_of_lt]
      apply Nat.two_pow_lt_two_pow_of_lt
      grind
    · grind
  let out : FixedPoint (v + f + 1) f := {
    sign := a.sign
    val := divResult
    hExOffset := by omega
  }
  out
