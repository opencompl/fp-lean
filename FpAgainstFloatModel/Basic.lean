import FpAgainstFloatModel.Theory

/-!
# `PackedFloat` agrees with Lean's `Float.Model` — shared foundation

Lean 4's `Float.Model` is the official non-opaque reference model of `Float`: a `UInt64`
together with a proof that the bit pattern is `binary64`-valid (a *single* canonical `NaN`).
Its operations `unpack → op → round → pack` are round-to-nearest-ties-to-even. It ships with
*no* lemmas — downstream float libraries are expected to prove their operations agree with
it and transfer their own lemmas across.

This development does that for `PackedFloat` at `binary64 = PackedFloat 11 52` (1 sign + 11
exponent + 52 significand bits, bias 1023).

## Design

Agreement is stated **at the circuit / bit level** — "the two libraries compute the same
64-bit pattern" — never through a rational/real value. The single relation is
`PackedFloat.ModelEquiv`, bit-equality *up to NaN* (both libraries canonicalize `NaN` to the
identical pattern, but a `PackedFloat` *input* may carry a non-canonical NaN). An optional
structural relation `UnpackedRel` at the unpacked level (comparing sign / `toNat` mantissa /
`toInt` exponent / classification — again no rationals) structures the operation proofs.

This file holds the shared definitions and the foundational lemmas; each operation's
agreement theorem lives in its own file under `FpAgainstFloatModel/`.

Proofs are scaffolded with `sorry`; every statement is fully typed. `toModelUnpacked` itself
is `sorry`-free and is validated empirically against `Float.Model.unpack`.
-/

open Float.Model (UnpackedFloat)

namespace FpAgainstFloatModel

/-! ## Part A — format / bit bridge -/

/-- `binary64` has exactly the `PackedFloat 11 52` bit width. -/
theorem binary64_numBits : Float.Model.Format.binary64.numBits = 1 + 11 + 52 := rfl

/-- The 64-bit pattern of a `PackedFloat 11 52`, viewed at `binary64.numBits`
(`binary64.numBits` is definitionally `1 + 11 + 52`, so no cast is needed). -/
def toBits64 (pf : PackedFloat 11 52) : BitVec Float.Model.Format.binary64.numBits :=
  pf.toBits

/-- A boolean sign bit as a `Float.Model` sign (`false ↦ positive`, matching IEEE). -/
def signToModel (b : Bool) : UnpackedFloat.Sign :=
  if b then .negative else .positive

/-! ## Part B — the semantic reading of a `PackedFloat` as a `Float.Model` unpacked value

`toModelUnpacked` reads the fields of a `PackedFloat 11 52` with `toNat`/`toInt` and produces
the model's inductive `UnpackedFloat`, matching `Float.Model.UnpackedFloat.unpack`'s exact
normalization (normal: mantissa `2^52 + sig`, exponent `expField - 1075`; subnormal:
mantissa `sig`, exponent `-1074`).  This *is* the statement "interpreting the fields matches
the Float Model". -/

/-- Interpret a `PackedFloat 11 52` as a `Float.Model.UnpackedFloat`, by state + fields. -/
def toModelUnpacked (pf : PackedFloat 11 52) : UnpackedFloat :=
  if pf.isNaN then .notANumber
  else if pf.isInfinite then .infinity (signToModel pf.sign)
  else if hz : pf.isZero then .zero (signToModel pf.sign)
  else if he : pf.ex = 0#11 then
    -- nonzero subnormal: `sig ≠ 0` here (not zero, exponent field 0)
    .finite (signToModel pf.sign) pf.sig.toNat (-1074) (by
      rcases Nat.eq_zero_or_pos pf.sig.toNat with h | h
      · exfalso
        apply hz
        have hsig : pf.sig = 0#52 := by apply BitVec.eq_of_toNat_eq; simp [h]
        simp [PackedFloat.isZero, he, hsig]
      · exact h)
  else
    -- normal: prepend the implicit leading 1
    .finite (signToModel pf.sign) (2 ^ 52 + pf.sig.toNat) ((pf.ex.toNat : Int) - 1075)
      (Nat.add_pos_left (Nat.two_pow_pos 52) _)

/-- Core correspondence: the field interpretation equals the model's own `unpack`. -/
theorem toModelUnpacked_eq_unpack (pf : PackedFloat 11 52) :
    toModelUnpacked pf = UnpackedFloat.unpack .binary64 (toBits64 pf) := by
  -- The three field extractions recover `pf`'s components (pure BitVec facts).
  have hs : UnpackedFloat.unpackSign (toBits64 pf) = BitVec.ofBool pf.sign := by
    unfold toBits64 UnpackedFloat.unpackSign PackedFloat.toBits; bv_decide
  have he : UnpackedFloat.unpackExponent (toBits64 pf) = pf.ex := by
    unfold toBits64 UnpackedFloat.unpackExponent PackedFloat.toBits; bv_decide
  have hm : UnpackedFloat.unpackMantissa (toBits64 pf) = pf.sig := by
    unfold toBits64 UnpackedFloat.unpackMantissa PackedFloat.toBits; bv_decide
  have hsign : UnpackedFloat.Sign.ofBitVec (BitVec.ofBool pf.sign) = signToModel pf.sign := by
    cases pf.sign <;> rfl
  have hbias : Float.Model.Format.binary64.exponentBias = 1023 := by decide
  have hallones : BitVec.allOnes 11 = -1#11 := by decide
  unfold UnpackedFloat.unpack toModelUnpacked
  simp only [hs, he, hm, hsign]
  simp only [PackedFloat.isNaN, PackedFloat.isInfinite, PackedFloat.isZero, hallones,
    BitVec.zero_eq, beq_iff_eq, bne_iff_ne, Bool.and_eq_true, Bool.or_eq_true,
    Nat.reduceEqDiff, decide_false, Bool.false_or, Bool.true_and, hbias]
  by_cases hnan : pf.ex = -1#11
  · by_cases hsig : pf.sig = 0#52 <;> simp [hnan, hsig]
  · by_cases hz : pf.ex = 0#11
    · by_cases hsig : pf.sig = 0#52 <;> simp [hnan, hz, hsig] <;> grind
    · simp only [hnan, hz, false_and, and_false, ↓reduceIte, ↓reduceDIte,
        UnpackedFloat.finite.injEq, true_and]
      refine ⟨?_, ?_⟩
      · rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        have h := Nat.two_pow_add_eq_or_of_lt pf.sig.isLt 1
        grind
      · grind

/-! ## Part B (cont.) — the equivalence relation -/

/-- `pf` and `fm` denote the same 64-bit `binary64` value, or both are `NaN`.
The single circuit-level agreement relation. -/
def _root_.PackedFloat.ModelEquiv (pf : PackedFloat 11 52) (fm : Float.Model) : Prop :=
  toBits64 pf = fm.toBits.toBitVec ∨ (pf.isNaN ∧ fm.isNaN)

/-- Bit-equality gives `ModelEquiv`. -/
theorem modelEquiv_of_toBits_eq {pf : PackedFloat 11 52} {fm : Float.Model}
    (h : toBits64 pf = fm.toBits.toBitVec) : pf.ModelEquiv fm := Or.inl h

/-- `toModelUnpacked` is `notANumber` exactly for `NaN` packed floats. -/
theorem toModelUnpacked_isNaN (pf : PackedFloat 11 52) :
    toModelUnpacked pf = .notANumber ↔ pf.isNaN := by
  unfold toModelUnpacked
  by_cases h : pf.isNaN <;> simp [h] <;>
    (by_cases h2 : pf.isInfinite <;> simp [h2] <;>
      (by_cases h3 : pf.isZero <;> simp [h3] <;>
        (by_cases h4 : pf.ex = 0#11 <;> simp [h4])))

/-- `ModelEquiv` characterized structurally: same classification, and matching unpacked value.
(The "state equivalence" spelled out.) Uses `unpack` injectivity off `NaN`. -/
theorem modelEquiv_iff_unpack {pf : PackedFloat 11 52} {fm : Float.Model} :
    pf.ModelEquiv fm ↔ toModelUnpacked pf = fm.unpack := by
  rw [toModelUnpacked_eq_unpack]
  unfold PackedFloat.ModelEquiv
  constructor
  · rintro (heq | ⟨h1, h2⟩)
    · rw [heq]; rfl
    · have e1 : UnpackedFloat.unpack .binary64 (toBits64 pf) = .notANumber :=
        (toModelUnpacked_eq_unpack pf) ▸ (toModelUnpacked_isNaN pf).mpr h1
      have e2 : fm.unpack = .notANumber := (model_isNaN_iff_unpack fm).mp h2
      rw [e1, e2]
  · intro h
    by_cases hn : UnpackedFloat.unpack .binary64 (toBits64 pf) = .notANumber
    · right
      exact ⟨(toModelUnpacked_isNaN pf).mp ((toModelUnpacked_eq_unpack pf).trans hn),
             (model_isNaN_iff_unpack fm).mpr (h ▸ hn)⟩
    · left; exact unpack_inj hn h

/-- `ofBits` on both sides agree. -/
theorem ofBits_modelEquiv (b : BitVec (1 + 11 + 52)) :
    (PackedFloat.ofBits 11 52 b).ModelEquiv (Float.Model.ofBits (UInt64.ofBitVec (b.cast (by decide)))) := by
  sorry

/-! ## Part C — structural relation at the unpacked level (no `Rat`), to structure proofs

Relates the project's `EUnpackedFloat` to the model's inductive `UnpackedFloat` by
classification + `toNat` significand + `toInt` exponent. -/

/-- A project `EUnpackedFloat` and a model `UnpackedFloat` represent the same value/state,
compared structurally (sign, `toNat` mantissa, `toInt` exponent) — no rational comparison. -/
def UnpackedRel (euf : EUnpackedFloat (exponentWidth 11 52) (52 + 1))
    (u : UnpackedFloat) : Prop :=
  match u with
  | .notANumber   => euf.isNaN
  | .infinity s   => euf.isInfinite ∧ signToModel euf.num.sign = s
  | .zero s       => euf.isZero ∧ signToModel euf.num.sign = s
  | .finite s m e _ =>
      euf.isNumber ∧ signToModel euf.num.sign = s ∧
      -- same normalized (mantissa, exponent), read via toNat/toInt (Rat-free)
      euf.num.sig.toNat = m ∧ (euf.num.ex.toInt - 52 : Int) = e

/-- `PackedFloat.unpack` agrees with the model's `unpack`, structurally. -/
theorem unpack_unpackRel (pf : PackedFloat 11 52) :
    UnpackedRel pf.unpack (UnpackedFloat.unpack .binary64 (toBits64 pf)) := by
  sorry

/-- If the unpacked forms are structurally related, their packings are `ModelEquiv`. -/
theorem pack_modelEquiv {euf : EUnpackedFloat (exponentWidth 11 52) (52 + 1)}
    {u : UnpackedFloat} (h : UnpackedRel euf u) :
    (euf.pack : PackedFloat 11 52).ModelEquiv (Float.Model.pack u) := by
  sorry

/-! ## Part D — sign-only operations (`neg`, `abs`)

These reduce to `toModelUnpacked` commuting with the corresponding `UnpackedFloat` operation
(a pure sign change), plus the model round-trip `model_neg_unpack`/`model_abs_unpack`. -/

/-- `signToModel` turns boolean negation into `Sign` negation. -/
theorem signToModel_not (b : Bool) : signToModel (!b) = -(signToModel b) := by
  cases b <;> rfl

/-- Negating a `PackedFloat` negates its model-unpacked value. -/
theorem toModelUnpacked_neg (a : PackedFloat 11 52) :
    toModelUnpacked (-a) = (toModelUnpacked a).neg := by
  show toModelUnpacked (PackedFloat.neg a) = _
  unfold toModelUnpacked
  simp only [show (PackedFloat.neg a).isNaN = a.isNaN from rfl,
    show (PackedFloat.neg a).isInfinite = a.isInfinite from rfl,
    show (PackedFloat.neg a).isZero = a.isZero from rfl,
    show (PackedFloat.neg a).ex = a.ex from rfl,
    show (PackedFloat.neg a).sig = a.sig from rfl,
    show (PackedFloat.neg a).sign = !a.sign from rfl, signToModel_not]
  by_cases h1 : a.isNaN <;> simp only [h1] <;>
    (try (by_cases h2 : a.isInfinite <;> simp only [h2] <;>
      (try (by_cases h3 : a.isZero <;> simp only [h3] <;>
        (try (by_cases h4 : a.ex = 0#11 <;> simp only [h4]))))))
  all_goals rfl

/-- Taking `abs` of a `PackedFloat` takes `abs` of its model-unpacked value. -/
theorem toModelUnpacked_abs (a : PackedFloat 11 52) :
    toModelUnpacked (a.abs) = (toModelUnpacked a).abs := by
  unfold toModelUnpacked
  simp only [show (PackedFloat.abs a).isNaN = a.isNaN from rfl,
    show (PackedFloat.abs a).isInfinite = a.isInfinite from rfl,
    show (PackedFloat.abs a).isZero = a.isZero from rfl,
    show (PackedFloat.abs a).ex = a.ex from rfl,
    show (PackedFloat.abs a).sig = a.sig from rfl,
    show (PackedFloat.abs a).sign = false from rfl]
  by_cases h1 : a.isNaN <;> simp only [h1] <;>
    (try (by_cases h2 : a.isInfinite <;> simp only [h2] <;>
      (try (by_cases h3 : a.isZero <;> simp only [h3] <;>
        (try (by_cases h4 : a.ex = 0#11 <;> simp only [h4]))))))
  all_goals rfl

end FpAgainstFloatModel
