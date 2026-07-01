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
open Float.Model (UnpackedFloat)

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

/-! ## Generic finite pack/unpack round-trip

The finite case of the width-generic `unpack_pack`. Two `Nat`/`BitVec` helpers, then the
round-trip on `.finite` values in canonical form (both normal and subnormal binades), and finally
the assembled `unpack_pack_fmt` covering all four constructors. -/

/-- `((2^k : Nat) : Int) = (2:Int)^k` — feeds `omega` (no `Nat.cast_pow` without Mathlib). -/
theorem natCast_two_pow (k : Nat) : ((2^k : Nat) : Int) = (2:Int)^k := by simp

/-- `(1#1 ++ x).toNat = 2^s + x.toNat` — the implicit-bit prepend, width-generic. -/
theorem toNat_one_append_gen (s : Nat) (x : BitVec s) : (1#1 ++ x).toNat = 2 ^ s + x.toNat := by
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have h := Nat.two_pow_add_eq_or_of_lt x.isLt 1; grind

/-- The pack/unpack round-trip on a `.finite` value in canonical form, **generic over `Format`**
(needs `1 < exponentBits`, else a subnormal would overflow to `∞` at `e=1`). Normal and subnormal
binades handled separately; the exponent recovery is phrased through `exponentBias` to keep the
`2^(e-1)` term a single `omega` atom. -/
theorem unpack_pack_finite (spec : Float.Model.Format) (hE2 : 1 < spec.exponentBits)
    (s : Float.Model.UnpackedFloat.Sign)
    (m : Nat) (e' : Int) (hm : 0 < m)
    (h : ModelCanonicalFmt spec (.finite s m e' hm)) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec (.finite s m e' hm)) = .finite s m e' hm := by
  have hE := spec.he
  have hS := spec.hm
  have hcP := natCast_two_pow (spec.exponentBits - 1)
  have hcE := natCast_two_pow spec.exponentBits
  have hp1 : (1:Nat) ≤ 2^(spec.exponentBits-1) := Nat.one_le_two_pow
  have hpowN : 2 ^ spec.exponentBits = 2 ^ (spec.exponentBits - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have hpowI : (2:Int) ^ spec.exponentBits = (2:Int) ^ (spec.exponentBits - 1) * 2 := by rw [← hcE, ← hcP, hpowN]; omega
  have hbiasI : (spec.exponentBias : Int) = 2 ^ (spec.exponentBits - 1) - 1 := by unfold Float.Model.Format.exponentBias; omega
  have hmb : spec.mantissaBits = spec.mantissaBitsWithoutImplicit + 1 := by show 1 + _ = _ + 1; omega
  have hSpow : (2:Nat) ^ spec.mantissaBits = 2 ^ spec.mantissaBitsWithoutImplicit * 2 := by rw [hmb, Nat.pow_succ]
  have hminI : spec.minExponent = 2 - 2 ^ (spec.exponentBits - 1) - (spec.mantissaBitsWithoutImplicit : Int) := by unfold Float.Model.Format.minExponent Float.Model.Format.mantissaBits; omega
  have hminBiased : spec.minExponent = 1 - (spec.exponentBias:Int) - (spec.mantissaBitsWithoutImplicit:Int) := by rw [hminI, hbiasI]; omega
  have h4 : 4 ≤ 2 ^ spec.exponentBits := by
    rw [hpowN]; have : 2 ≤ 2 ^ (spec.exponentBits - 1) := Nat.one_lt_two_pow_iff.mpr (by omega); omega
  simp only [ModelCanonicalFmt] at h
  rcases h with ⟨hm1, hm2, he1, he2⟩ | ⟨hm1, he⟩
  · rw [hminI] at he1; rw [hSpow] at hm2
    have hbe_hi : (e' + (spec.exponentBias:Int) + (spec.mantissaBitsWithoutImplicit:Int)).toNat + 2 ≤ 2^spec.exponentBits := by rw [hbiasI]; omega
    have hbe_lt : (e' + (spec.exponentBias:Int) + (spec.mantissaBitsWithoutImplicit:Int)).toNat < 2^spec.exponentBits := by omega
    have hbe_ge : 0 < (e' + (spec.exponentBias:Int) + (spec.mantissaBitsWithoutImplicit:Int)).toNat := by rw [hbiasI]; omega
    have hbe_val : ((e' + (spec.exponentBias:Int) + (spec.mantissaBitsWithoutImplicit:Int)).toNat : Int) = e' + spec.exponentBias + spec.mantissaBitsWithoutImplicit := Int.toNat_of_nonneg (by rw [hbiasI]; omega)
    have hmmod : m % 2^spec.mantissaBitsWithoutImplicit = m - 2^spec.mantissaBitsWithoutImplicit := by rw [Nat.mod_eq_sub_mod hm1, Nat.mod_eq_of_lt (by omega)]
    have hlog : m.log2 + 1 = spec.mantissaBits := by
      rw [hmb]; have : m.log2 = spec.mantissaBitsWithoutImplicit := by rw [Nat.log2_eq_iff (by omega)]; omega
      omega
    simp only [UnpackedFloat.pack]
    rw [if_neg (by omega), if_pos hlog]
    simp only [UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents,
      Float.Model.UnpackedFloat.unpackMantissa_packComponents, unpackSign_packComponents, ofBitVec_toBitVec]
    rw [if_neg (by rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, neg_one_toNat, Nat.mod_eq_of_lt hbe_lt]; omega),
        if_neg (by rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt hbe_lt]; omega),
        UnpackedFloat.finite.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · rw [toNat_one_append_gen, BitVec.toNat_ofNat, hmmod]; omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbe_lt, hbe_val]; omega
  · rw [hminBiased] at he
    have hmmod : m % 2^spec.mantissaBitsWithoutImplicit = m := Nat.mod_eq_of_lt hm1
    have hbe0 : (e' + (spec.exponentBias:Int) + (spec.mantissaBitsWithoutImplicit:Int)).toNat + 1 < 2^spec.exponentBits := by rw [he]; omega
    have hlog : ¬ (m.log2 + 1 = spec.mantissaBits) := by
      rw [hmb]; have : m.log2 < spec.mantissaBitsWithoutImplicit := by rw [Nat.log2_lt (by omega)]; omega
      omega
    have hmpos : ¬ (BitVec.ofNat spec.mantissaBitsWithoutImplicit m = 0#spec.mantissaBitsWithoutImplicit) := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_zero, hmmod]; omega
    simp only [UnpackedFloat.pack]
    rw [if_neg (by omega), if_neg hlog]
    simp only [UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents,
      Float.Model.UnpackedFloat.unpackMantissa_packComponents, unpackSign_packComponents, ofBitVec_toBitVec]
    rw [if_neg (by rw [zero_ne_neg_one _ hE]; exact not_false)]
    simp only [if_true]
    rw [dif_neg hmpos, UnpackedFloat.finite.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · rw [BitVec.toNat_ofNat, hmmod]
    · rw [BitVec.toNat_zero]; omega

/-- The pack/unpack round-trip, **generic over `Format`**, for any model float in canonical form
(`ModelCanonicalFmt`). Assembles the four constructor cases; supersedes the binary64 `unpack_pack`. -/
theorem unpack_pack_fmt (spec : Float.Model.Format) (hE2 : 1 < spec.exponentBits)
    (u : Float.Model.UnpackedFloat) (h : ModelCanonicalFmt spec u) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec u) = u := by
  cases u with
  | notANumber => exact unpack_pack_notANumber spec
  | infinity s => exact unpack_pack_infinity spec s
  | zero s => exact unpack_pack_zero spec s
  | finite s m e' hm => exact unpack_pack_finite spec hE2 s m e' hm h

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
