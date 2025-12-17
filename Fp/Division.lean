import Fp.Basic
import Fp.Rounding
import Fp.MulInv

/-
PLAN:

1. Prove that the mantissa, exponent value is correct upto some precision for 'div_on_packedFloat'.
2. Axiomatize what the rounder does for this level of precision.
3. Use these to prove that 'div' is correct.
4. Replace rounder with better rounder that doesn't need the expansion to fixed point.
5. Prove that better rounder is correct.
-/


@[bv_normalize]
def f_div (a : FixedPoint v e) (b : FixedPoint w f) : FixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.hExOffset b.hExOffset
  let a' : BitVec (v+w) := a.val.setWidth' (by omega)
  let b' : BitVec (v+w) := b.val.setWidth' (by omega)
  {
    sign := a.sign ^^ b.sign
    -- | TODO: this needs alignment, no?
    val := a' / b'
    hExOffset
  }


/-- Unpacked significand, which will be 1xxxxxx or 0xxxx depending on whether the exponent is zero or not. -/
@[bv_normalize]
def PackedFloat.unpackedSignificand (x : PackedFloat e s) : BitVec (1 + s) :=
  BitVec.ofBool (x.ex ≠ 0) ++ x.sig

/-- Subtract b from a, but return 0 if a ≤ b. Mimics natural number subtraction. -/
def BitVec.monus (a : BitVec w) (b : BitVec w) : BitVec w :=
  if a ≤ b then 0#w else a - b


@[bv_normalize]
def div_on_packedFloat (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  let sign := a.sign ^^ b.sign
  -- 1.0000 vs 0.0000
  let sig_a := a.unpackedSignificand
  let sig_b := b.unpackedSignificand
  let div_len := 3*(s+1) -- (s + 1) because we add the bit.
  let unit_pos := 2*(s+1)
  let dividend := (sig_a.setWidth div_len <<< unit_pos)
  let divisor := sig_b.setWidth div_len
  -- Do division, collapse remainder to a single sticky bit
  let quot_with_sticky := (dividend / divisor) ++ BitVec.ofBool ((dividend % divisor) ≠ 0)
  -- Calculate shifts
  let divResult := fixedWidthDivideAtPrecision sig_a sig_b (prec := 2 * (s + 1)) (outw := 3 * (s + 1))
  -- let quot_with_sticky := divResult.quotWithSticky
  let expNumerator := if a.ex > 0 then a.ex - 1 else 0
  let expDenominator := if b.ex > 0 then b.ex - 1 else 0
  -- Shift and round
  -- | TODO: For the rounding, we still expand out into fixed point.
  -- We should instead use the cleverer rounder.
  if expNumerator ≥ expDenominator then
    let quot_lshift : EFixedPoint (2^e+div_len+1) (unit_pos+1) := {
      state := .Number
      num := {
        sign
        -- numerator is larger than denominator, so multiply by the correct amount.
        val := quot_with_sticky.setWidth _ <<< (expNumerator - expDenominator)
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right]
          apply Nat.lt_add_left
          omega
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
        val := (quot_with_sticky.setWidth _ <<< 2^e) >>> (expDenominator - expNumerator)
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
  if a.isNaN ∨ b.isNaN ∨ (a.isInfinite ∧ b.isInfinite) ∨ (a.isZero ∧ b.isZero) then
    PackedFloat.getNaN _ _
  else if a.isInfinite ∨ b.isZero then
    PackedFloat.getInfinity _ _ (a.sign ^^ b.sign)
  else if b.isInfinite then
    { PackedFloat.getZero _ _ with sign := a.sign ^^ b.sign }
  else
    div_on_packedFloat a b m
