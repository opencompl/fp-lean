import Fp
import Init.Data.Float.Model.Float

/-!
# General theory of `Float.Model` for the agreement proofs

Lean's `Float.Model` ships with essentially no lemmas (only `valid_pack`), so this file
develops the reusable facts needed to prove `PackedFloat ⇄ Float.Model` agreement:
bit reconstruction, unpack injectivity (off NaN), NaN characterization, and the packed-layout
extraction identities. Everything here is about `Float.Model`/its `UnpackedFloat` only.
-/

open Float.Model (UnpackedFloat)

namespace FpAgainstFloatModel

/-! ## NaN characterization -/

/-- The model's unpacked `isNaN` holds iff the value is exactly `notANumber`. -/
@[simp] theorem unpack_isNaN_iff (u : UnpackedFloat) : u.isNaN = true ↔ u = .notANumber := by
  cases u <;> simp [UnpackedFloat.isNaN]

/-- `Float.Model.isNaN fm` holds iff `fm` unpacks to `notANumber`. -/
theorem model_isNaN_iff_unpack (fm : Float.Model) : fm.isNaN = true ↔ fm.unpack = .notANumber := by
  unfold Float.Model.isNaN; exact unpack_isNaN_iff _

/-! ## Bit reconstruction and injectivity of `unpack` -/

/-- A `binary64` bit pattern equals the concatenation of its unpacked sign/exponent/mantissa
fields — i.e. `unpack`'s field extractions lose no information. -/
theorem unpack_reconstruct (b : BitVec Float.Model.Format.binary64.numBits) :
    UnpackedFloat.unpackSign b ++ UnpackedFloat.unpackExponent b ++ UnpackedFloat.unpackMantissa b = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [UnpackedFloat.unpackSign, UnpackedFloat.unpackExponent, UnpackedFloat.unpackMantissa,
    BitVec.extractLsb, BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  grind

/-- Two `binary64` patterns with the same non-`NaN` unpacking are equal. Off `NaN`, the
unpacked value determines the sign/exponent/mantissa, which (via `unpack_reconstruct`)
determine the bits. -/
theorem unpack_inj {b₁ b₂ : BitVec Float.Model.Format.binary64.numBits}
    (hne : UnpackedFloat.unpack .binary64 b₁ ≠ .notANumber)
    (h : UnpackedFloat.unpack .binary64 b₁ = UnpackedFloat.unpack .binary64 b₂) :
    b₁ = b₂ := by
  -- reduce to equality of the three field extractions, then reconstruct
  rw [← unpack_reconstruct b₁, ← unpack_reconstruct b₂]
  -- the extractions coincide because the unpacked forms coincide (off NaN)
  suffices hh : UnpackedFloat.unpackSign b₁ = UnpackedFloat.unpackSign b₂ ∧
      UnpackedFloat.unpackExponent b₁ = UnpackedFloat.unpackExponent b₂ ∧
      UnpackedFloat.unpackMantissa b₁ = UnpackedFloat.unpackMantissa b₂ by
    obtain ⟨h1, h2, h3⟩ := hh; rw [h1, h2, h3]
  -- `Sign.ofBitVec` is injective on the sign bit
  have hsinj : ∀ (x y : BitVec 1),
      UnpackedFloat.Sign.ofBitVec x = UnpackedFloat.Sign.ofBitVec y → x = y := by
    intro x y; unfold UnpackedFloat.Sign.ofBitVec; split <;> split <;> intro _ <;> bv_decide
  -- prepending the implicit leading `1` adds `2^52` to the significand's value
  have happ : ∀ (m : BitVec 52), (1#1 ++ m).toNat = 2 ^ 52 + m.toNat := by
    intro m; rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have h := Nat.two_pow_add_eq_or_of_lt m.isLt 1; grind
  have hlt : ∀ (m : BitVec 52), m.toNat < 2 ^ 52 := fun m => m.isLt
  have hbias : Float.Model.Format.binary64.exponentBias = 1023 := by decide
  simp only [UnpackedFloat.unpack, hbias] at h hne
  -- 16-way case split on the two classifications; each branch is either a constructor clash,
  -- a magnitude contradiction (normal vs subnormal mantissa), or field-wise equality.
  split at h <;> split at h <;> split at h <;> split at h <;>
    grind [BitVec.eq_of_toNat_eq]

end FpAgainstFloatModel
