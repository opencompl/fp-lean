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


/-- x ≥ y ↔ y ≤ x-/
@[bv_normalize]
def BitVec.sge (x y : BitVec w) : Bool := y.sle x

#check round


def BitVec.dropLsbs (bv : BitVec w) (n : Nat) : BitVec (w - n) :=
  (bv >>> n).setWidth _

theorem getMsbD_dropLsbs {w n : Nat} (h : n < w) (bv : BitVec w) :
    bv.getMsbD i = (bv.dropLsbs n).getMsbD i := by
  simp [BitVec.dropLsbs, BitVec.getMsbD]
  by_cases hi : i < w 
  · simp [hi]
    sorry
  · simp [hi]
    sorry

def BitVec.dropMsb (bv : BitVec w) (n : Nat) : BitVec (w - n) :=
  bv.setWidth _

/-

The correct way to think of an UnpackedFloat is as a fixed point number,
written in scientific notation.

So, consider fixed point numbers with three digits, dot right after the first digit (as in normal floating point).
This gives us:

→ 0.00 0.01 0.10 0.11 
→ 1.00 1.01 1.10 1.11

→ 0.00 = _ | 0.01 = 1.00 * 10^(-2) | 0.10 = 1.00 * 10^(-1) | 0.11 = 1.10 * 10^(-1)
→ 1.00 = 1.00 * 10^(0) | 1.01 = 1.01 * 10^(0) | 1.10 = 1.10 * 10^(0) | 1.11 = 1.11 * 10^(0)

Next, to encode the `1.00`, we write this as:

→ 0.00 = _ | 0.01 = (100 * 10^(-2)) * 10^(-2) | 0.10 = (100 * 10^(-2)) * 10^(-1) | 0.11 = (110 * 10^(-2)) * 10^(-1)
→ 1.00 = (100 * 10^(-2)) * 10^(0) | 1.01 = (101 * 10^(-2)) * 10^(0) | 1.10 = (110*10^(-2)) * 10^(0) | 1.11 = (111 * 10^(-2)) * 10^(0)

In this way, we can see our number as a composition of scientific notation with fixed-width exponent.
In the UnpackedFloat, we only store the exponent, not the constant fixed-point shift (10^(-2)), 
since this is common to all numbers, and also, morally, it is absorbed into the significand as a fixed-point.
-/

/-
#### Why guard and sticky bits:

Suppose we want to round to 0 bits of precision, using round to nearest even. Then, if we have:

- 10.1 -> 10
- 10.5???, we need to know if the ??? is zero or not.
   + 10.5000 -> 10
    * If it is zero, then we round to the nearest even, which is 10.
   + 10.5001 -> 11
    * If it is non-zero, we *always* round up to 11, since it's strictly closer to 11 than 10.
- 10.9 -> 11
- 11.5????? 
    + 11.5000 -> 12
      * If it is zero, then we round to the nearest even, which is 12.
    + 11.5001 -> 12
      * If it is non-zero, we *always* round up to 12, since it's strictly closer to 12 than 11.

Thus, see that just having one sticky bit is enough, since it tells us whether we are at the exact halfway point or not, and that's all we need to know.


We will return an EUnpackedFloat,
which can signal NaN/Infinity/Zero, in addition to normal numbers.


-/

-- the number is sig.toNat *  2 ^(-sigPrec) * 2 ^ (ex.toInt)
-- choose e = 0, s = 1 then see that after normalization, we e.
-- If our exponent is
def roundRNEFast (up : UnpackedFloat e s) : EUnpackedFloat e' s' :=
    let up := up.normalize
    if up.sig = 0
    then EUnpackedFloat.mkNumber {
      sign := up.sign
      ex := 0#e'
      sig := 0#s'
    }
    else
      -- we are in the <1.-----> case.
      -- let exOffset' := 2^(exWidth - 1) + sigWidth - 2
      -- trim bitvector
      -- can absorb 2^s component into the significand, but any more
      -- cannot be absorbed.
      if hExTooBig : up.ex > BitVec.ofInt e (maxNormalExp e') + BitVec.ofInt e s' then
        EUnpackedFloat.mkInfinity up.sign
      else if hExTooSmall : up.ex < BitVec.ofInt e (minNormalExp e') - BitVec.ofInt e s' then
      -- | too small to be subnormal.
        EUnpackedFloat.mkZero up.sign
      -- else if up.ex < BitVec.ofInt e (minNormalExp e) then
      --   -- | subnormal case.
      --   let shift := (BitVec.ofInt e (minNormalExp e) - up.ex).toNat
      --   let sig_shifted := up.sig >>> shift
        -- sorry
        -- let round_result := roundSignificandAndStickyBit up.sign sig_shifted s RoundingMode.RTZ
        -- EUnpackedFloat.mkSubnormal round_result
      else
        let adjustedExp :=
          if up.ex > BitVec.ofInt e (maxNormalExp e') then
            BitVec.ofInt e (maxNormalExp e)
          else if up.ex < BitVec.ofInt e (minNormalExp e') then
            BitVec.ofInt e (minNormalExp e')
          else
            up.ex
        let truncatedSig : BitVec s' :=
          if adjustedExp = up.ex then
            up.sig.truncate _
          else if adjustedExp < up.ex then
            -- we decreased exponent, so increase significand
            (up.sig <<< (up.ex - adjustedExp)).truncate _
          else
            -- we increased exponent, so decrease significand
            let shift := (adjustedExp - up.ex)
            (up.sig >>> shift).truncate _
        let remainder : BitVec (s - s') :=
          if adjustedExp = up.ex then
            up.sig.dropMsb s'
          else if adjustedExp < up.ex then
            (up.sig <<< (up.ex - adjustedExp)).dropMsb s'
          else
            let shift := (adjustedExp - up.ex)
            (up.sig >>> shift).dropMsb s'
        let guardBit := remainder.getMsbD 0
        let stickyBit : Bool := (remainder.dropMsb 1) ≠ 0
        let isOdd := truncatedSig.getMsbD 0
        let shouldRoundAway : Bool := guardBit && (stickyBit || isOdd)
        if shouldRoundAway then
          sorry
        else 
          sorry


        -- I need to ensure that exponent is in
        -- [minNormalExp-1, maxNormalExp]
        -- normal plus subnormal case.
        -- drop the number of bits that can fit into the exponent.

        -- let shouldRoundAway := shouldRoundAway .RNE
        -- | normal case.
        -- let round_result := roundSignificandAndStickyBit up.sign up.sig s RoundingMode.RTZ
        -- EUnpackedFloat.mkNormal (up.ex) round_result

@[bv_normalize]
def div_on_unpackedFloat (a b : UnpackedFloat (exponentWidth e s) (s + 1)) (mode : RoundingMode) : PackedFloat e s :=
  -- a.toRat = (-1)^a.sign * a.sig.toNat * 2 ^ (a.ex.toInt) * 2 ^(-s)
  -- a.toRat / b.toRat = (-1)^(a.sign⊕b.sign) * (a.sig.toNat /b.sig.toNat) * (2 ^ (a.ex.toInt) / 2 ^ (b.ex.toInt) *(2 ^(-s) / 2^(-s))
  -- = (-1)^(a.sign⊕b.sign) * (a.sig.toNat /b.sig.toNat) * 2 ^(a.ex.toInt - b.ex.toInt)
  -- = (-1)^(a.sign⊕b.sign) * (a.sig.toNat /b.sig.toNat) * 2 ^(a.ex.toInt - b.ex.toInt)
  let sign := a.sign ^^ b.sign
  let sig_a := a.sig
  let sig_b := b.sig
  let div_len := 3*(s+1) -- (s + 1) because we add the bit.
  let unit_pos := 2*(s+1)
  let dividend := (sig_a.setWidth div_len <<< unit_pos)
  let divisor := sig_b.setWidth div_len
  -- Do division, collapse remainder to a single sticky bit
  let quot_with_sticky := (dividend / divisor) ++ BitVec.ofBool ((dividend % divisor) ≠ 0)
  -- Calculate shifts
  -- let divResult := fixedWidthDivideAtPrecision sig_a sig_b (prec := 2 * (s + 1)) (outw := 3 * (s + 1))
  -- let quot_with_sticky := divResult.quotWithSticky
  let expNumerator := a.ex -- if a.ex > 0 then a.ex - 1 else 0
  let expDenominator := b.ex -- if b.ex > 0 then b.ex - 1 else 0
  -- Shift and round
  -- | TODO: For the rounding, we still expand out into fixed point.
  -- We should instead use the cleverer rounder.
  if expNumerator.sge expDenominator then
    -- +1 for the sticky bit.
    let quot_lshift : EFixedPoint (2^e+div_len+1) (unit_pos+1) := {
      state := .Number
      num := {
        sign
        -- numerator is larger than denominator, so multiply by the correct amount.
        val := quot_with_sticky.setWidth (2 ^ e + div_len + 1) <<< (expNumerator - expDenominator)
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right]
          apply Nat.lt_add_left
          omega
      }
    }
    round _ _ mode quot_lshift
    -- PackedFloat.mk true (BitVec.ofNat _ 0xcafebabe) (BitVec.ofNat _ 0xcafebabe)
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
        -- 2^(a.ex.toInt - b.ex.toInt) = 2^(-E + E + a.ex.toIn - b.ex.toInt)
        -- = 2^-E * 2^(E - b.ex.toInt + a.ex.toInt) [which is ≥ 1 ]
        val := ((quot_with_sticky.setWidth _ <<< 2^e) >>> (expDenominator - expNumerator))
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_left]
          omega
      }
    }
    round _ _ mode quot_rshift

/--
Division of two floating-point numbers, rounded to a floating point number
using the provided rounding mode.
-/
@[bv_normalize]
def div (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  let a := a.unpack
  let b := b.unpack
  -- a = 0, b = 0
  if a.isNaN ∨ b.isNaN ∨ (a.isInfinite ∧ b.isInfinite) ∨ (a.isZero ∧ b.isZero) then
    PackedFloat.getNaN _ _
  -- a = ∞, b = 0
  else if a.isInfinite ∨ b.isZero then
    PackedFloat.getInfinity _ _ (a.sign ^^ b.sign)
  -- a = *, b = ∞
  else if b.isInfinite then
    { PackedFloat.getZero _ _ with sign := a.sign ^^ b.sign }
  else if a.isZero then -- note that b must be finite here.
    { PackedFloat.getZero _ _ with sign := a.sign ^^ b.sign }
  else
    div_on_unpackedFloat a.num b.num m


/-- Dividing zero by a finite nonzero number gives a zero with the right sign. -/
theorem zero_div_is_zero (a b : PackedFloat 5 2) (ha : a.isZero) (hb : b.isNormOrSubnorm) (hb : ¬b.isZero)
  : (div a b .RTZ).isZero ∧ (div a b .RTZ).sign = a.sign ^^ b.sign := by
  bv_decide

def cex' : PackedFloat 5 2 where
  ex := 0#5
  sig := 2#2
  sign := false

/-- info: -15 -/
#guard_msgs in #eval cex'.unpack.num.ex.toInt

/-- info: 0 -/
#guard_msgs in #eval oneE5M2.unpack.num.ex.toInt

/-- info: { sign := +, ex := 0x00#5, sig := 0x2#2 } -/
#guard_msgs in #eval div_on_unpackedFloat cex'.unpack.num oneE5M2.unpack.num .RTZ

set_option debugAssertions true in
theorem div_one_is_id_on_numerator_ex_larger (a : PackedFloat 5 2) (h : a.unpack.num.ex.sge oneE5M2.unpack.num.ex)
  : (div a oneE5M2 .RTZ).equal_denotation a := by
  bv_decide

set_option debugAssertions true in
theorem div_one_is_id_on_numerator_ex_smaller (a : PackedFloat 5 2) (h : ¬ a.unpack.num.ex.sge oneE5M2.unpack.num.ex)
  : (div a oneE5M2 .RTZ).equal_denotation a := by
  bv_decide

theorem div_self_is_one' (a : PackedFloat 5 2)
  (h : ¬a.isNaN ∧ ¬a.isInfinite ∧ ¬a.isZero)
  : (div a a .RTZ) = oneE5M2 := by
  bv_decide
