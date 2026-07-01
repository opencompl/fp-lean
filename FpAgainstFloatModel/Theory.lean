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
  suffices h : UnpackedFloat.unpackSign b₁ = UnpackedFloat.unpackSign b₂ ∧
      UnpackedFloat.unpackExponent b₁ = UnpackedFloat.unpackExponent b₂ ∧
      UnpackedFloat.unpackMantissa b₁ = UnpackedFloat.unpackMantissa b₂ by
    obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]
  sorry

end FpAgainstFloatModel
