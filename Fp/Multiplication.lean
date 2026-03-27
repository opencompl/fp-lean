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


/--
The result of raw multiplication, which has an un-normalized
significand and exponent. The interpretation of this bitpattern is given by
MulUnnormalized.toRat.
-/
structure MulUnnormalized (e s : Nat) where
  sig : BitVec (2 * s)
  ex : BitVec (e + 1)
  sign : Bool


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
def MulUnnormalized.mul (x y : UnpackedFloat e s) : MulUnnormalized e s :=
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

/--
The rational interpretation of this number. See that it has
two bits to the left of the decimal point, since 'sig' is '2s' long,
but the precisoin is `-2(s-1) = 2s - 2`.
This is normalized away in the next step, and this intermediate
computation is 'manually' normalized.
-/
def MulUnnormalized.toRat (m : MulUnnormalized e s) : Rat :=
  m.sign.toSign * m.sig.toNat * (2 : Rat) ^ (- ((2 * (s - 1) : Int) - m.ex.toInt))

/--
Perform the normalization step.
If product in range [2,4) (i.e., 1x...x), then it is already normalized.
If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
-/
def MulUnnormalized.mulAdjustMsb (u : MulUnnormalized e s) :
  UnpackedFloat (e + 1) (2 * s) := {
      sign := u.sign
      sig := sig
      ex := ex
    }
  where
    sig := u.sig <<< (BitVec.ofBool (!u.sig.msb))
    ex := u.ex + (BitVec.ofBool u.sig.msb).setWidth' (by omega)

/--
The multiplication circuit can be conceptualized as first

- computing the multiplication as unadjusted, that results in a number that two digits
  to the left of the dot, followed by digits of precision.
- normalizing the unadjusted number to push the msb up.
-/
theorem UnpackedFloat.mul_eq_mulAdjustMsb_mulUnadjustedMsb (x y : UnpackedFloat e s) :
    x.mul y = (MulUnnormalized.mul x y).mulAdjustMsb := by rfl

private theorem Nat.pow_two_eq_mul_self (a : Nat) : a ^ 2 = a * a := by grind

/--
The unadjusted result has the correct rational interpretation.
-/
theorem UnpackedFloat.toRat_mulUnadjustedMsb_eq_toRat_mul_toRat {a b : UnpackedFloat e s}
    (hs : 0 < s) :
    (MulUnnormalized.mul a b).toRat = (a.toRat * b.toRat) := by
  simp [MulUnnormalized.mul, MulUnnormalized.toRat]
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
  congr 2
  · simp [MulUnnormalized.mul.sign]
  · simp [MulUnnormalized.mul.sig]
    rw [Nat.mod_eq_of_lt]
    · simp
    · have : a.sig.toNat < 2 ^ s := by grind
      have : b.sig.toNat < 2 ^ s := by grind
      rw [Nat.pow_mul']
      rw [Nat.pow_two_eq_mul_self]
      apply Nat.mul_lt_mul'' <;> assumption
  · rw [MulUnnormalized.mul.ex]
    rw [← Rat.zpow_add (show 2 ≠ 0 by decide)]
    rw [BitVec.toInt_add]
    rw [BitVec.toInt_signExtend_of_le (by lia)]
    rw [BitVec.toInt_signExtend_of_le (by lia)]
    rw [Int.bmod_eq_of_le]
    · apply congrArg
      simp [Int.neg_sub]
      norm_cast
      grind
    · grind
    · grind



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
