import Fp.Basic
import Fp.Rounding
import Fp.MulInv
import Fp.Proofs.Grind
import Fp.ForLean.Rat

/-
PLAN:

1. Prove that the mantissa, exponent value is correct upto some precision for 'div_on_packedFloat'.
2. Axiomatize what the rounder does for this level of precision.
3. Use these to prove that 'div' is correct.
4. Replace rounder with better rounder that doesn't need the expansion to fixed point.
5. Prove that better rounder is correct.
-/

structure FixedWidthDivideAtPrecisionResult (outw : Nat) where
  quotient : BitVec outw
  sticky : Bool

/--
Returns the quotient of `x` and `y` computed at a fixed precision,
as well as a sticky bit indicating whether there was any remainder.
-/
def fixedWidthDivideAtPrecision (x y : BitVec w) (prec : Nat) (outw : Nat) -- (hprec : w + prec = outw)
    : FixedWidthDivideAtPrecisionResult outw :=
    let dividend := (x.setWidth outw <<< prec)
    let divisor := y.setWidth outw
    {
      quotient := dividend / divisor,
      sticky := (dividend % divisor ≠ 0)
    }

/-- Compute the quotient with the sticky bit appended as the least significant bit. -/
def FixedWidthDivideAtPrecisionResult.quotWithSticky {outw : Nat} (r : FixedWidthDivideAtPrecisionResult outw) : BitVec (outw + 1) :=
  r.quotient ++ BitVec.ofBool r.sticky


attribute [grind .] Nat.mul_lt_mul_of_lt_of_le -- blow up

@[simp]
theorem toNat_quoteint_fixedWidthDivideAtPrecision_eq
    (x y : BitVec w) (prec : Nat) (outw : Nat) (hprec : w + prec = outw) :
    (fixedWidthDivideAtPrecision x y prec outw).quotient.toNat =
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
theorem remainder_fixedWidthDivideAtPrecision_eq_decide
    (x y : BitVec w) (prec : Nat) (outw : Nat) (hprec : w + prec = outw) :
    (fixedWidthDivideAtPrecision x y prec outw).sticky = (decide ((x.toNat * 2 ^ prec) % y.toNat ≠ 0)) := by
  simp [fixedWidthDivideAtPrecision]
  have hx : x.toNat % 2^outw = x.toNat := by grind
  have hy : y.toNat % 2^outw = y.toNat := by grind
  constructor
  · intros h
    have := congrArg BitVec.toNat h
    simp [Nat.shiftLeft_eq, hx, hy] at this
    grind
  · intros h
    apply BitVec.eq_of_toNat_eq
    simp
    grind

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


@[simp]
theorem Rat.num_ofNat' (n : Nat) :
    (Rat.ofNat n).num = n := by
  simp [Rat.ofNat, Rat.ofInt]

@[simp]
theorem Rat.den_ofNat' (n : Nat) :
    (Rat.ofNat n).den = 1 := by
  simp [Rat.ofNat, Rat.ofInt]

theorem Rat.ofNat_div_ofNat_eq_mkRat {a b : Nat}  :
      Rat.ofNat a / Rat.ofNat b = mkRat a b := by
  rw [Rat.mkRat_eq_div]
  simp [Rat.ofNat, Rat.ofInt]
  by_cases hb : b  = 0
  · simp [hb]
  · norm_cast

/-- 'a/b' equals '(a/gcd(a, b)) / (b/gcd(a, b)) -/
@[simp]
theorem Nat.gcd_div_gcd_eq (a b : Nat) :
    (a / Nat.gcd a b) / (b / Nat.gcd a b) = a / b := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_div_cancel']
    exact gcd_dvd_right a b

/-- Natural number division agrees with floor of the rational division -/
-- | TODO: do I want this as a simp lemma?
theorem Rat.ofNat_div_ofNat_eq_floor_div {a b : Nat} (hb : b > 0 := by grind):
      Rat.ofNat (a / b) = (Rat.ofNat a / Rat.ofNat b).floor := by
  rw [Rat.floor_def]
  rw [Rat.ofNat_div_ofNat_eq_mkRat]
  simp [Rat.num_mkRat, Rat.den_mkRat]
  by_cases hb : b = 0
  · grind
  · simp [hb]
    norm_cast
    rw [Nat.gcd_comm b a]
    simp
    norm_cast

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



/--
Unpacked significand, which will be 1xxxxxx or 0xxxx depending on whether the exponent is zero or not
TODO: Move to using UnpackedFloat.
-/
@[bv_normalize]
def PackedFloat.unpackedSignificand (x : PackedFloat e s) : BitVec (1 + s) :=
  BitVec.ofBool (x.ex ≠ 0) ++ x.sig

/-- Subtract b from a, but return 0 if a ≤ b. Mimics natural number subtraction. -/
def BitVec.monus (a : BitVec w) (b : BitVec w) : BitVec w :=
  if a ≤ b then 0#w else a - b


@[bv_normalize]
def divUnpackedFloat (a b : UnpackedFloat (exponentWidth e s) (s + 1)) (mode : RoundingMode) : PackedFloat e s :=
  let sign := a.sign ^^ b.sign
  -- 1.0000 vs 0.0000
  let sig_a := a.sig
  let sig_b := b.sig
  let div_len := 3*(s+1) -- (s + 1) because we add the bit.
  let unit_pos := 2*(s+1)
  let dividend := (sig_a.setWidth div_len <<< unit_pos)
  let divisor := sig_b.setWidth div_len
  -- Do division, collapse remainder to a single sticky bit
  let quot_with_sticky := (dividend / divisor) ++ BitVec.ofBool ((dividend % divisor) ≠ 0)
  -- Calculate shifts
  let divResult := fixedWidthDivideAtPrecision sig_a sig_b (prec := 2 * (s + 1)) (outw := 3 * (s + 1))
  -- let quot_with_sticky := divResult.quotWithSticky
  let expNumerator := a.ex -- if a.ex > 0 then a.ex - 1 else 0
  let expDenominator := b.ex -- if b.ex > 0 then b.ex - 1 else 0
  -- Shift and round
  -- | TODO: For the rounding, we still expand out into fixed point.
  -- We should instead use the cleverer rounder.
  if expNumerator ≥ expDenominator then
    let quot_lshift : EFixedPoint (2^e+div_len+1) (2^e+unit_pos+1) := {
      state := .Number
      num := {
        sign
        -- numerator is larger than denominator, so multiply by the correct amount.
        val := quot_with_sticky.setWidth _ <<< (expNumerator - expDenominator) <<< 2^e
        hExOffset := by
          grind
      }
    }
    round _ _ mode quot_lshift
  else
    let quot_rshift : EFixedPoint (2^e+div_len+1) (2^e+unit_pos+1) := {
      state := .Number
      num := {
        sign
        -- denominator is larger than numerator, so divide by the correct amount, but first increase the
        -- exponent to (2^e), so that the round function rounds correctly.
        -- TODO: understand the bounds on our rounding.
        -- we shift by '2^e' so we scale up by the same factor as we do with (2^e + unit_pos + 1),
        -- such that we represent the same number.
        val := ((quot_with_sticky.setWidth _ <<< 2^e) >>> (expDenominator - expNumerator))
        hExOffset := by
          grind
      }
    }
    round _ _ mode quot_rshift

/--
Division of two floating-point numbers, rounded to a floating point number
using the provided rounding mode.
-/
@[bv_normalize]
def divEUnpackedFloat (a b : EUnpackedFloat (exponentWidth e s) (s + 1)) (m : RoundingMode) : PackedFloat e s :=
  if a.isNaN ∨ b.isNaN ∨ (a.isInfinite ∧ b.isInfinite) ∨ (a.isZero ∧ b.isZero) then
    PackedFloat.getNaN _ _
  else if a.isInfinite ∨ b.isZero then
    PackedFloat.getInfinity _ _ (a.sign ^^ b.sign)
  else if b.isInfinite then
    { PackedFloat.getZero _ _ with sign := a.sign ^^ b.sign }
  else
    divUnpackedFloat a.num b.num m

@[bv_normalize]
def div (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  divEUnpackedFloat a.unpack b.unpack m
