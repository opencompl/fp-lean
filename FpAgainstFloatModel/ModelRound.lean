import FpAgainstFloatModel.ExtRat
import Init.Data.Float.Model.Float

/-!
# Model rounding: `roundWithAccuracy` value lemmas (foundation of `mul` agreement)

Self-contained `Nat` facts about Lean's `Float.Model.UnpackedFloat.roundWithAccuracy` — the
model ships no lemmas, so these are proven from the definitions. They characterize the
guard/round/sticky extraction of the `ExtendedMantissa` shift and show that `roundedMantissa`
is exactly round-to-nearest-ties-even. These feed the round-agreement theorem
(`roundWithAccuracy_exact_pack_toExtRat`, see `FpAgainstFloatModel/PLAN.md`) which bridges the
model rounder to the project's `smtLibRound`.
-/

set_option maxHeartbeats 1000000
open Float.Model.UnpackedFloat (ExtendedMantissa Accuracy)
open Float.Model.UnpackedFloat.ExtendedMantissa

namespace FpAgainstFloatModel

/-! ## Symbolic-width `BitVec` facts (for the generic pack/unpack round-trip over `Format`)

These are the width-generic replacements for the `by decide` steps in the binary64
`unpack_pack`, so the round-trip and round-agreement can be proven for any `Format` (any `e,s`),
not just `binary64`. -/

/-- `(-1 : BitVec e)` (all-ones) has `toNat = 2^e - 1`. -/
theorem neg_one_toNat (e : Nat) : ((-1#e) : BitVec e).toNat = 2 ^ e - 1 := by
  rw [show ((-1#e) : BitVec e) = BitVec.allOnes e from by simp [BitVec.neg_one_eq_allOnes],
    BitVec.toNat_allOnes]

/-- `1#s <<< (s-1)` (the packed-NaN top mantissa bit) has `toNat = 2^(s-1)`. -/
theorem toNat_one_shiftLeft (s : Nat) (hs : 0 < s) :
    ((1#s <<< (s-1)) : BitVec s).toNat = 2 ^ (s-1) := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have h1 : (1 : Nat) % 2 ^ s = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr (by omega))
  rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]

/-- `0#e = -1#e` is `False` (for `0 < e`) — zero exponent field is not all-ones. -/
theorem zero_ne_neg_one (e : Nat) (he : 0 < e) : ((0#e : BitVec e) = -1#e) = False := by
  rw [eq_iff_iff, iff_false, ← BitVec.toNat_inj, neg_one_toNat, BitVec.toNat_zero]
  have := Nat.one_lt_two_pow_iff.mpr (show e ≠ 0 by omega); omega

/-- `1#s <<< (s-1) = 0#s` is `False` (for `0 < s`) — the NaN mantissa is nonzero. -/
theorem one_shiftLeft_ne_zero (s : Nat) (hs : 0 < s) :
    ((1#s <<< (s-1) : BitVec s) = 0#s) = False := by
  rw [eq_iff_iff, iff_false, ← BitVec.toNat_inj, toNat_one_shiftLeft s hs, BitVec.toNat_zero]
  have := Nat.two_pow_pos (s-1); omega

/-- The pack/unpack round-trip on the non-finite constructors, **generic over `Format`**
(the base case of the generic `unpack_pack`; the finite case's exponent arithmetic is next). -/
theorem unpack_pack_notANumber (spec : Float.Model.Format) :
    Float.Model.UnpackedFloat.unpack spec (Float.Model.UnpackedFloat.pack spec .notANumber)
      = .notANumber := by
  simp [Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packedNaN,
    Float.Model.UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents,
    Float.Model.UnpackedFloat.unpackMantissa_packComponents, one_shiftLeft_ne_zero _ spec.hm]

theorem unpack_pack_infinity (spec : Float.Model.Format) (s : Float.Model.UnpackedFloat.Sign) :
    Float.Model.UnpackedFloat.unpack spec (Float.Model.UnpackedFloat.pack spec (.infinity s))
      = .infinity s := by
  have he := spec.he
  simp [Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packedInfinity,
    Float.Model.UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents,
    Float.Model.UnpackedFloat.unpackMantissa_packComponents, unpackSign_packComponents,
    ofBitVec_toBitVec]

theorem unpack_pack_zero (spec : Float.Model.Format) (s : Float.Model.UnpackedFloat.Sign) :
    Float.Model.UnpackedFloat.unpack spec (Float.Model.UnpackedFloat.pack spec (.zero s))
      = .zero s := by
  have he := spec.he
  simp [Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packedZero,
    Float.Model.UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents,
    Float.Model.UnpackedFloat.unpackMantissa_packComponents, unpackSign_packComponents,
    ofBitVec_toBitVec, zero_ne_neg_one _ he]

/-- A model finite value in canonical form for `spec` — **generic** (`2^s ≤ m < 2^(s+1)` normal,
`m < 2^s ∧ exp = minExponent` subnormal). Supersedes the binary64 `ModelCanonical`. -/
def ModelCanonicalFmt (spec : Float.Model.Format) : Float.Model.UnpackedFloat → Prop
  | .notANumber => True
  | .infinity _ => True
  | .zero _ => True
  | .finite _ m e' _ =>
      (2 ^ spec.mantissaBitsWithoutImplicit ≤ m ∧ m < 2 ^ spec.mantissaBits ∧
        spec.minExponent ≤ e' ∧
        e' ≤ (2 ^ (spec.exponentBits - 1) : Int) - 1 - spec.mantissaBitsWithoutImplicit)
      ∨ (m < 2 ^ spec.mantissaBitsWithoutImplicit ∧ e' = spec.minExponent)

/-! ## H1 — the `k`-fold shift of the exact seed extracts mantissa / guard / sticky -/

/-- Shifting the exact seed `⟨m,false,false⟩` right by `k` leaves `mantissa = m / 2^k`. -/
theorem em_shift_mantissa (m : Nat) (k : Nat) :
    (ExtendedMantissa.mk m false false >>> k).mantissa = m / 2 ^ k := by
  induction k with
  | zero => show m = m / 2 ^ 0; simp
  | succ k ih =>
    show (shiftRightOne (ExtendedMantissa.mk m false false >>> k)).mantissa = _
    rw [shiftRightOne]; simp only [ih]; rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- After `k+1` shifts, `roundBit` is bit `k` of `m` (the guard bit). -/
theorem em_shift_roundBit (m : Nat) (k : Nat) :
    (ExtendedMantissa.mk m false false >>> (k+1)).roundBit = (m / 2 ^ k % 2 != 0) := by
  show (shiftRightOne (ExtendedMantissa.mk m false false >>> k)).roundBit = _
  rw [shiftRightOne]; simp only [em_shift_mantissa]

/-- After `k+1` shifts, `stickyBit` is the OR of bits `0..k-1` of `m`. -/
theorem em_shift_stickyBit (m : Nat) (k : Nat) :
    (ExtendedMantissa.mk m false false >>> (k+1)).stickyBit = decide (m % 2 ^ k ≠ 0) := by
  induction k with
  | zero =>
    show (shiftRightOne (ExtendedMantissa.mk m false false)).stickyBit = _
    simp [shiftRightOne, Nat.mod_one]
  | succ k ih =>
    show (shiftRightOne (ExtendedMantissa.mk m false false >>> (k+1))).stickyBit = _
    rw [shiftRightOne, em_shift_roundBit, ih]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdec : m % 2 ^ (k+1) = 2 ^ k * (m / 2 ^ k % 2) + m % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul, Nat.add_comm]
    have hb : m / 2 ^ k % 2 = 0 ∨ m / 2 ^ k % 2 = 1 := by omega
    rcases hb with hb | hb <;> rw [hb] at hdec <;> rw [hb] <;> simp <;> omega

/-! ## H2 — the rounded mantissa is round-to-nearest-ties-even -/

/-- The model's `accuracy` in terms of the round/sticky fields. -/
theorem accuracy_eq (x : Nat) (b s : Bool) :
    (ExtendedMantissa.mk x b s).accuracy =
      bif b then (bif s then Accuracy.inexact .gt else Accuracy.inexact .eq)
            else (bif s then Accuracy.inexact .lt else Accuracy.exact) := by
  cases b <;> cases s <;> rfl

/-- The model's rounded mantissa after shifting the exact seed right by `k+1`:
round-to-nearest-ties-even of `m / 2^(k+1)` (down if guard 0; up if guard∧sticky; tie-to-even
if guard∧¬sticky). -/
theorem roundedMantissa_shift_succ (m k : Nat) :
    ((ExtendedMantissa.mk m false false) >>> (k+1)).roundedMantissa =
      m / 2 ^ (k+1)
        + (if m / 2 ^ k % 2 = 1 then (if m % 2 ^ k = 0 then m / 2 ^ (k+1) % 2 else 1) else 0) := by
  have hmant := em_shift_mantissa m (k+1)
  have hrb := em_shift_roundBit m k
  have hsb := em_shift_stickyBit m k
  rw [ExtendedMantissa.roundedMantissa,
    show ((ExtendedMantissa.mk m false false) >>> (k+1))
      = ExtendedMantissa.mk (((ExtendedMantissa.mk m false false) >>> (k+1)).mantissa)
          (((ExtendedMantissa.mk m false false) >>> (k+1)).roundBit)
          (((ExtendedMantissa.mk m false false) >>> (k+1)).stickyBit) from rfl,
    accuracy_eq, hmant, hrb, hsb]
  have hr01 : m / 2 ^ k % 2 = 0 ∨ m / 2 ^ k % 2 = 1 := by omega
  rcases hr01 with hr | hr <;> by_cases hs : m % 2 ^ k = 0 <;> rw [hr] <;>
    simp [hs, Accuracy.roundToNearestEven]

end FpAgainstFloatModel
