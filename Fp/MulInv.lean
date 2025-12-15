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

@[simp]
theorem Rat.ofNat_one_eq_one :
    Rat.ofNat 1 = 1 := by
  simp [Rat.ofNat, Rat.ofInt]

theorem Rat.ofNat_one_div_eq_inv_ofNat
    (b : Nat) :
    Rat.ofNat 1 / Rat.ofNat b  = (Rat.ofNat b)⁻¹ := by
  simp
  rw [Rat.div_def]
  grind

theorem Rat.twoPowInv_eq_inv (prec : Nat) :
    Rat.twoPowInv prec = (Rat.ofNat (2 ^ prec))⁻¹ := by
  simp [Rat.twoPowInv]
  rw [Rat.div_def]
  grind

theorem Rat.ofNat_two_pow_mul_twoPowInv_eq (n : Nat) (prec : Nat) :
    Rat.ofNat (n * 2 ^ prec) * Rat.twoPowInv prec = Rat.ofNat n := by
  rw [Rat.twoPowInv]
  rw [Rat.ofNat_mul]
  simp only [ofNat_one_eq_one]
  rw [Rat.div_def]
  simp only [Rat.one_mul]
  grind

@[simp]
theorem Rat.mul_inv_cancel_right'
    {a b : Rat} (hb : b ≠ 0 := by grind) :
    a * b * b⁻¹ = a := by
  rw [Rat.mul_assoc]
  rw [Rat.mul_inv_cancel]
  · grind
  · grind

@[grind .]
theorem Nat.two_pow_ne_zero (n : Nat) :
    2 ^ n ≠ 0 := by grind



-- Show the gap between 'y' and '⌊y*k⌋k⁻¹ is at most k⁻¹
theorem Rat.self_sub_mul_floor_inv_le {y k  : Rat} (hk : 0 < k := by grind) :
    y  - (y * k).floor * k⁻¹ ≤ k⁻¹ := by
  have : (y * k) < (((y * k).floor + 1) : Int) := by
    apply Rat.lt_floor_add_one
  have := (calc
    (y * k) * k⁻¹ < (((y * k).floor + 1) : Int) * k⁻¹ := by
      apply Rat.mul_lt_mul_right .. |>.mpr
      · grind
      · apply Rat.inv_pos.mpr
        grind)
  have : y < (((y * k).floor + 1) : Int) * k⁻¹ := by
    rw [Rat.mul_assoc] at this
    rw [Rat.mul_inv_cancel] at this
    · grind
    · grind
  simp at this
  rw [Rat.add_mul] at this
  simp at this
  grind

/-- Natural number division agrees with floor of the rational division -/
axiom Rat.ofNat_div_ofNat_eq_floor_div {a b : Nat} (hb : b > 0 := by grind):
    Rat.ofNat (a / b) = (Rat.ofNat a / Rat.ofNat b).floor

@[simp]
theorem Rat.num_ofNat' (n : Nat) :
    (Rat.ofNat n).num = n := by
  simp [Rat.ofNat, Rat.ofInt]

@[simp]
theorem Rat.den_ofNat' (n : Nat) :
    (Rat.ofNat n).den = 1 := by
  simp [Rat.ofNat, Rat.ofInt]

/-- Show that the difference between the real division value and the rounded divison value is at most 2^{-prec}. -/
theorem fixedWidthDivideAtPrecision_abs_delta_eq
  (n d : BitVec w) (prec : Nat) (hy : d.toNat ≠ 0) :
    ((Rat.ofNat n.toNat / Rat.ofNat d.toNat) -
      (Rat.ofNat ((n.toNat * 2 ^ prec) / d.toNat)) * Rat.twoPowInv prec) ≤
    Rat.twoPowInv prec := by
  have := Nat.div_add_mod n.toNat d.toNat
  rw [← this]
  simp [hy]
  generalize hk : n.toNat / d.toNat = k
  generalize hr : n.toNat % d.toNat = r
  rw [Nat.add_mul]
  rw [show d.toNat * k * 2 ^ prec = (d.toNat) * (k * 2 ^ prec) by grind]
  rw [Nat.mul_add_div (by grind)]
  simp
  rw [Rat.add_mul]
  rw [Rat.twoPowInv_eq_inv]
  simp
  -- have :=
  (calc
    Rat.ofNat k + Rat.ofNat r / Rat.ofNat d.toNat - (Rat.ofNat k + Rat.ofNat (r * 2 ^ prec / d.toNat) * (Rat.ofNat (2 ^ prec))⁻¹) =
      Rat.ofNat r / Rat.ofNat d.toNat - Rat.ofNat (r * 2 ^ prec / d.toNat) * (Rat.ofNat (2 ^ prec))⁻¹ := by grind)
  rw [Rat.ofNat_div_ofNat_eq_floor_div]
  simp
  have := (calc
     Rat.ofNat r / Rat.ofNat d.toNat < ↑((Rat.ofNat r / Rat.ofNat d.toNat).floor + 1) := by apply Rat.lt_floor_add_one
  )
  have := Rat.lt_floor_add_one (a := Rat.ofNat r / Rat.ofNat d.toNat)
  rw [show Rat.ofNat r * Rat.ofNat (2 ^ prec) / Rat.ofNat d.toNat = (Rat.ofNat r / Rat.ofNat d.toNat) * Rat.ofNat (2 ^ prec) by
    grind]
  apply Rat.self_sub_mul_floor_inv_le (y := Rat.ofNat r / Rat.ofNat d.toNat) (k := Rat.ofNat (2 ^ prec)) (hk := by
    simp [Rat.lt_iff]
    apply Int.pow_pos (by decide)
  )


-- [1, 10) / [1, 10) ∈ [0.1, 10)
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
