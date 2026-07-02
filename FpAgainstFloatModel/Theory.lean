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

/-! ## Pack / unpack round-trip on canonical values

Every `Float.Model` operation is `pack (op unpack…)`, so relating `PackedFloat` and
`Float.Model` requires knowing that `unpack (pack u) = u` for `u` in canonical form. -/

open Float.Model.UnpackedFloat in
/-- `unpackSign` recovers the sign bit written by `packComponents`. -/
theorem unpackSign_packComponents {spec : Float.Model.Format} {sign e m} :
    UnpackedFloat.unpackSign (UnpackedFloat.packComponents spec sign e m) = sign.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  have h1 := spec.hm; have h2 := spec.he
  simp only [UnpackedFloat.unpackSign, UnpackedFloat.packComponents, BitVec.extractLsb,
    BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  grind

/-- `Sign.ofBitVec` inverts `Sign.toBitVec`. -/
theorem ofBitVec_toBitVec (s : UnpackedFloat.Sign) : UnpackedFloat.Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

/-- A model `UnpackedFloat` is in canonical (correctly-rounded `binary64`) form: finite values
are either normal (significand in `[2^52, 2^53)`, exponent in range) or subnormal (significand
`< 2^52`, exponent pinned at `-1074`). This is exactly the shape produced by `unpack`. -/
def ModelCanonical : UnpackedFloat → Prop
  | .notANumber => True
  | .infinity _ => True
  | .zero _ => True
  | .finite _ m e _ =>
      (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971) ∨ (m < 2 ^ 52 ∧ e = -1074)

/-- Prepending the implicit leading `1` adds `2^52` to the significand's value. -/
theorem toNat_one_append (x : BitVec 52) : (1#1 ++ x).toNat = 2 ^ 52 + x.toNat := by
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have h := Nat.two_pow_add_eq_or_of_lt x.isLt 1; grind

/-- The pack/unpack round-trip: unpacking a canonical value's packing recovers it. This is the
universal enabler — since `neg`/`abs`/`add`/`mul`/… are all `pack (op (unpack …))`. -/
theorem unpack_pack (u : UnpackedFloat) (h : ModelCanonical u) :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 u) = u := by
  have hbias : Float.Model.Format.binary64.exponentBias = 1023 := by decide
  have hmbwi : Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 52 := by decide
  have heb : Float.Model.Format.binary64.exponentBits = 11 := by decide
  have hmb : Float.Model.Format.binary64.mantissaBits = 53 := by decide
  cases u with
  | notANumber =>
    simp only [UnpackedFloat.pack, UnpackedFloat.packedNaN, UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent_packComponents, Float.Model.UnpackedFloat.unpackMantissa_packComponents, hmbwi,
      show ((1#52 <<< (52 - 1) : BitVec 52) = 0#52) = False from by decide, reduceIte]
  | infinity s =>
    simp only [UnpackedFloat.pack, UnpackedFloat.packedInfinity, UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent_packComponents, Float.Model.UnpackedFloat.unpackMantissa_packComponents, unpackSign_packComponents,
      ofBitVec_toBitVec, reduceIte]
    rw [if_pos (by decide)]
  | zero s =>
    simp only [UnpackedFloat.pack, UnpackedFloat.packedZero, UnpackedFloat.unpack,
      Float.Model.UnpackedFloat.unpackExponent_packComponents, Float.Model.UnpackedFloat.unpackMantissa_packComponents, unpackSign_packComponents,
      ofBitVec_toBitVec]
    rw [if_neg (by decide), if_pos (by decide), dif_pos (by decide)]
  | finite s m e hm =>
    rcases h with ⟨hm1, hm2, he1, he2⟩ | ⟨hm1, he⟩
    · -- normal
      have hlog : m.log2 + 1 = 53 := by
        have : m.log2 = 52 := by rw [Nat.log2_eq_iff (by omega)]; omega
        omega
      simp only [UnpackedFloat.pack, hbias, hmbwi, heb, hmb]
      rw [if_neg (by omega), if_pos hlog]
      simp only [UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents, Float.Model.UnpackedFloat.unpackMantissa_packComponents,
        unpackSign_packComponents, ofBitVec_toBitVec, hbias, hmbwi, BitVec.toNat_ofNat]
      rw [if_neg (by rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_ofNat, BitVec.toNat_neg]; omega),
          if_neg (by rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_ofNat]; omega),
          UnpackedFloat.finite.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · rw [toNat_one_append]; simp only [BitVec.toNat_ofNat]; omega
      · omega
    · -- subnormal
      have hlog : ¬ (m.log2 + 1 = 53) := by
        have : m.log2 < 52 := by rw [Nat.log2_lt (by omega)]; omega
        omega
      subst he
      simp only [UnpackedFloat.pack, hbias, hmbwi, heb, hmb]
      rw [if_neg (by omega), if_neg hlog]
      simp only [UnpackedFloat.unpack, Float.Model.UnpackedFloat.unpackExponent_packComponents, Float.Model.UnpackedFloat.unpackMantissa_packComponents,
        unpackSign_packComponents, ofBitVec_toBitVec, hbias, hmbwi, BitVec.toNat_ofNat]
      rw [if_neg (by decide), if_pos (by decide),
          dif_neg (by rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_ofNat]; omega),
          UnpackedFloat.finite.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · omega
      · omega

/-- `unpack` always produces a canonical value. -/
theorem ModelCanonical_unpack (b : BitVec Float.Model.Format.binary64.numBits) :
    ModelCanonical (UnpackedFloat.unpack .binary64 b) := by
  have hbias : Float.Model.Format.binary64.exponentBias = 1023 := by decide
  have hmbwi : Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 52 := by decide
  have hml : (UnpackedFloat.unpackMantissa (spec := .binary64) b).toNat < 2 ^ 52 :=
    (UnpackedFloat.unpackMantissa b).isLt
  have hel : (UnpackedFloat.unpackExponent (spec := .binary64) b).toNat < 2 ^ 11 :=
    (UnpackedFloat.unpackExponent b).isLt
  simp only [UnpackedFloat.unpack, hbias, hmbwi]
  split
  · split <;> trivial
  · rename_i hexpNeg1
    split
    · split
      · trivial
      · rename_i hexp0 hmnz
        simp only [ModelCanonical]
        refine Or.inr ⟨hml, ?_⟩
        have : (UnpackedFloat.unpackExponent (spec := .binary64) b).toNat = 0 := by
          rw [← BitVec.toNat_inj] at hexp0; simpa using hexp0
        rw [this]; decide
    · rename_i hexp0
      simp only [ModelCanonical]
      have hne1 : (UnpackedFloat.unpackExponent (spec := .binary64) b).toNat ≠ 2 ^ 11 - 1 := by
        intro hc; apply hexpNeg1; rw [← BitVec.toNat_inj]
        simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]; omega
      have hne0 : (UnpackedFloat.unpackExponent (spec := .binary64) b).toNat ≠ 0 := by
        intro hc; apply hexp0; rw [← BitVec.toNat_inj]; simpa using hc
      rw [toNat_one_append]
      exact Or.inl ⟨by omega, by omega, by omega, by omega⟩

/-- `neg` preserves canonicity. -/
theorem ModelCanonical_neg (u : UnpackedFloat) (h : ModelCanonical u) : ModelCanonical u.neg := by
  cases u <;> exact h

/-- `abs` preserves canonicity. -/
theorem ModelCanonical_abs (u : UnpackedFloat) (h : ModelCanonical u) : ModelCanonical u.abs := by
  cases u <;> exact h

/-- The model's `neg` acts on the unpacked value by `UnpackedFloat.neg`. -/
theorem model_neg_unpack (fa : Float.Model) (hc : ModelCanonical fa.unpack) :
    (Float.Model.neg fa).unpack = fa.unpack.neg := by
  unfold Float.Model.neg Float.Model.unpack Float.Model.pack
  simp only [UInt64.toBitVec_ofBitVec]
  exact unpack_pack _ (ModelCanonical_neg _ hc)

/-- The model's `abs` acts on the unpacked value by `UnpackedFloat.abs`. -/
theorem model_abs_unpack (fa : Float.Model) (hc : ModelCanonical fa.unpack) :
    (Float.Model.abs fa).unpack = fa.unpack.abs := by
  unfold Float.Model.abs Float.Model.unpack Float.Model.pack
  simp only [UInt64.toBitVec_ofBitVec]
  exact unpack_pack _ (ModelCanonical_abs _ hc)

end FpAgainstFloatModel
