import Fp
import Init.Data.Float.Model.Float

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

/-- The 64-bit pattern of a `PackedFloat 11 52`, viewed at `binary64.numBits`. -/
def toBits64 (pf : PackedFloat 11 52) : BitVec Float.Model.Format.binary64.numBits :=
  (pf.toBits).cast (by rw [binary64_numBits])

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

/-- Core correspondence: the field interpretation equals the model's own `unpack`.
(Validated empirically over many bit patterns; the `sorry` is the general proof.) -/
theorem toModelUnpacked_eq_unpack (pf : PackedFloat 11 52) :
    toModelUnpacked pf = UnpackedFloat.unpack .binary64 (toBits64 pf) := by
  sorry

/-! ## Part B (cont.) — the equivalence relation -/

/-- `pf` and `fm` denote the same 64-bit `binary64` value, or both are `NaN`.
The single circuit-level agreement relation. -/
def _root_.PackedFloat.ModelEquiv (pf : PackedFloat 11 52) (fm : Float.Model) : Prop :=
  toBits64 pf = fm.toBits.toBitVec ∨ (pf.isNaN ∧ fm.isNaN)

/-- Bit-equality gives `ModelEquiv`. -/
theorem modelEquiv_of_toBits_eq {pf : PackedFloat 11 52} {fm : Float.Model}
    (h : toBits64 pf = fm.toBits.toBitVec) : pf.ModelEquiv fm := Or.inl h

/-- `ModelEquiv` characterized structurally: same classification, and matching unpacked value.
(The "state equivalence" spelled out.) -/
theorem modelEquiv_iff_unpack {pf : PackedFloat 11 52} {fm : Float.Model} :
    pf.ModelEquiv fm ↔ toModelUnpacked pf = fm.unpack := by
  sorry

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

end FpAgainstFloatModel
