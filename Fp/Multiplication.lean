import Fp.Basic
import Fp.UnpackedRound
import Fp.Rounding

@[bv_normalize]
def UnpackedFloat.mul (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (2 * s) :=
  {
    sign := sign
    -- Exponent guaranteed to fit in e+1 bits (no overflow):
    -- max: (2^(e-1) - 1) + (2^(e-1) - 1) + 1 = 2^e - 1 < 2^e
    -- min: -2^(e-1) + -2^(e-1) + 0 = -2^e
    -- Optimization: consider using `Bitvec.adc`
    ex := ex
    -- If product in range [2,4) (i.e., 1x...x), then it is already normalized.
    -- If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
    sig := sig
  }
  where
    -- use 'where' blocks since they create auxiliary defs which can be neatly unfolded.
    sigProd := x.sig.setWidth' (by omega) * y.sig.setWidth' (by omega)
    sig := sigProd <<< BitVec.ofBool !sigProd.msb
    ex := x.ex.signExtend (e + 1) + y.ex.signExtend (e + 1) + (BitVec.ofBool sigProd.msb).setWidth' (by omega)
    sign := x.sign ^^ y.sign

@[bv_normalize]
def EUnpackedFloat.mul (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isNaN || y.isNaN || x.isInfinite && y.isZero || y.isInfinite && x.isZero then
    mkNaN
  else bif x.isInfinite || y.isInfinite then
    mkInfinity (x.num.sign ^^ y.num.sign)
  else bif x.isZero || y.isZero then
    mkZero (x.num.sign ^^ y.num.sign)
  else
    UnpackedFloat.round (.mul x.num y.num) m

namespace PackedFloat

@[bv_normalize]
def mul (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.mul m x.unpack y.unpack).pack

instance : Mul (PackedFloat e s) where
  mul := .mul .RNE

@[bv_normalize]
theorem PackedFloat.mul_def {x y : PackedFloat e s} : x * y = PackedFloat.mul .RNE x y := rfl

end PackedFloat


-- our "bias" is (2 (s - 1)) = (2s - 2) but our width is (2s - 1)!
-- This is because when we write an unpacked float, we sometimes

-- the actual formula for multiplication should say that if we have
-- 'UnpackedFloat e s p * Unpackedfloat e s' p', then we get a
-- UnpackedFloat (e + 1) (s * s') (p + p'), where p is number of bits of precision.
-- The mismatch where `p` is conflated with `s` causes accounting problems.
-- / (s - 1) * (s - 1) = 2 (s - 1)
-- [1.1] * [1.1] = 1.5 * 1.5 = 3 / 2 * 3/2 = 9 / 4 = [1001] / 4 = [10.01]
-- 2*(s-1) + 1 = 2 * s - 1
-- 2^-s * 2^s = 2^(-2s)
-- 2^
@[bv_normalize]
def UnpackedFloat.mulUnadjustedMsb (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (2 * s) :=
  {
    sign := sign
    -- Exponent guaranteed to fit in e+1 bits (no overflow):
    -- max: (2^(e-1) - 1) + (2^(e-1) - 1) + 1 = 2^e - 1 < 2^e
    -- min: -2^(e-1) + -2^(e-1) + 0 = -2^e
    -- Optimization: consider using `Bitvec.adc`
    ex := ex
    -- If product in range [2,4) (i.e., 1x...x), then it is already normalized.
    -- If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
    sig := sig
  }
  where
    -- use 'where' blocks since they create auxiliary defs which can be neatly unfolded.
    sig := x.sig.setWidth' (by omega) * y.sig.setWidth' (by omega)
    ex := x.ex.signExtend (e + 1) + y.ex.signExtend (e + 1)
    sign := x.sign ^^ y.sign

-- If product in range [2,4) (i.e., 1x...x), then it is already normalized.
-- If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
def UnpackedFloat.mulAdjustMsb (u : UnpackedFloat (e + 1) (2 * s)) : UnpackedFloat (e + 1) (2 * s) := {
    sign := u.sign
    sig := sig
    ex := ex
  }
  where
    sig := u.sig <<< (BitVec.ofBool (!u.sig.msb))
    ex := u.ex + (BitVec.ofBool u.sig.msb).setWidth' (by omega)

/--
For reasoning, breaking the mulitplication circuit down into an unadjusted multiplication,
followed by an adjustment based on the msb.
-/
theorem UnpackedFloat.mul_eq_mulAdjustMsb_mulUnadjustedMsb (x y : UnpackedFloat e s) :
  x.mul y = (x.mulUnadjustedMsb y).mulAdjustMsb := rfl

private theorem Nat.pow_two_eq_mul_self (a : Nat) : a ^ 2 = a * a := by grind

-- | TODO: make a relation for approximated upto k bits, with guard?
-- in UnpackedFloat.toRat, we conflate the number of bits we use to *represent* the exponent,
-- with the actual "exponent range" we are working in (ie, the bias we want to apply.)
-- These two are different! For example, when we build a `UnpackedFloat` for multiplication,
-- we may use more bits to represent the exponent, but we are still 'interpreting'
-- the exponent in the old range, so we need to have a bias factor of `2^(-<old bias> + e)`.
theorem UnpackedFloat.toRat_mulUnadjustedMsb_eq_toRat_mul_toRat {a b : UnpackedFloat e s} :
    (a.mulUnadjustedMsb b).sign.toSign *
    ((a.mulUnadjustedMsb b).sig.toNat) *
    ((2 : Rat) ^ (a.mulUnadjustedMsb b).ex.toInt * (2 : Rat) ^ (- (s : Int))) =
      (a.toRat * b.toRat) := by
  simp [UnpackedFloat.mulUnadjustedMsb]
  simp [UnpackedFloat.toRat_eq_toRat']
  simp [UnpackedFloat.toRat']
  simp [UnpackedFloat.toExpInt]
  symm
  calc
    _ = ↑a.sign.toSign * ↑a.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - a.ex.toInt)) *
        (↑b.sign.toSign * ↑b.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - b.ex.toInt))) := by grind
    _ = (↑a.sign.toSign * ↑b.sign.toSign) * ↑a.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - a.ex.toInt)) *
        (↑b.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - b.ex.toInt))) := by grind
    _ = (↑a.sign.toSign * ↑b.sign.toSign) * (↑a.sig.toNat * ↑b.sig.toNat) *
          ((2 : Rat) ^ (-(↑(s - 1) - a.ex.toInt)) * (2 : Rat) ^ (-(↑(s - 1) - b.ex.toInt))) := by grind
  congr 1
  · congr 2
    · simp [UnpackedFloat.mulUnadjustedMsb.sign]
    · simp [UnpackedFloat.mulUnadjustedMsb.sig]
      rw [Nat.mod_eq_of_lt]
      · simp
      · have : a.sig.toNat < 2 ^ s := by grind
        have : b.sig.toNat < 2 ^ s := by grind
        rw [Nat.pow_mul']
        rw [Nat.pow_two_eq_mul_self]
        apply Nat.mul_lt_mul'' <;> assumption
  · rw [mulUnadjustedMsb.ex]
    apply congrArg
    rw [← Rat.zpow_add]
    rw [BitVec.toInt_add_of_not_saddOverflow]
    · rw [BitVec.toInt_signExtend_of_le (by lia)]
      rw [BitVec.toInt_signExtend_of_le (by lia)]
      congr
      have : 1 < s := by sorry
      simp [Int.neg_sub]
      norm_cast

      sorry
    · sorry
    · decide




/-- info: some 16 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 8 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 10 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 5 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 4 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 2 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 2 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 1 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some (1 / 4) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 * PackedFloat.ofRat 5 2 .RNE 1 2).toRat?
/-- info: some (1 / 8) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 * PackedFloat.ofRat 5 2 .RNE 1 4).toRat?
