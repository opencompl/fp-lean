import FpAgainstFloatModel.ExtRat

/-! # `PackedFloat.mul` agrees with `Float.Model.mul` (round-to-nearest-even).

Structured through **relation C** (`ExtRat`): both sides round the *same* exact rational
product, so agreement reduces to

  `(a * b).toExtRat = modelToExtRat (fa * fb)`   (then `modelEquiv_of_toExtRat_eq`).

The **project side** is discharged by reusing `Fp.mul_eq_mul` (the bit-blasted `mul` equals,
up to NaN, the SMT-LIB spec = round of the exact `ExtRat` product): `mul_toExtRat_eq`.

The two remaining obligations are the genuine research-scale core — *proving Lean's
`Float.Model.mul` is correctly rounded (RNE)*, which the model itself does not establish:
- `model_mul_toExtRat` — the model's `mul` value equals the project's SMT-LIB round of the
  exact product (i.e. `roundWithAccuracy` implements the same round as the project);
- `mul_hzsign` — the ±0 sign of a (possibly underflowing) product agrees (both use `xorSign`).
-/

open Fp Fp.SmtLibSemantics PackedFloat

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

/-- **Project side (proven).** The bit-blasted `mul`'s value equals the SMT-LIB round of the
exact `ExtRat` product `a.toExtRat * b.toExtRat`. Direct from `Fp.mul_eq_mul`. -/
theorem mul_toExtRat_eq (a b : PackedFloat 11 52) :
    (a * b).toExtRat
      = (SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ 11 52) .RNE a b).toExtRat :=
  (EquivUptoNaN.toExtRat_eq
    (Fp.mul_eq_mul (sin := 52) (ein := 11) (by decide) (by decide) (by decide) .RNE rfl a b)).symm

/-- **Model round-agreement (remaining core).** Lean's `Float.Model.mul` value equals the
project's SMT-LIB round of the same exact product. This is where the model's `roundWithAccuracy`
must be shown to implement round-to-nearest-even correctly, matching the project's rounder. -/
theorem model_mul_toExtRat (ha : a.toExtRat = modelToExtRat fa) (hb : b.toExtRat = modelToExtRat fb) :
    (SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ 11 52) .RNE a b).toExtRat
      = modelToExtRat (fa * fb) := by
  sorry

/-- **±0 sign (remaining, mechanical).** When the product rounds to zero, the two sides agree on
its sign (both compute `xorSign` of the inputs, which match by `ModelEquiv`). -/
theorem mul_hzsign (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (a * b).isZero → (a * b).sign = (modelBits (fa * fb)).sign := by
  sorry

/-- Multiplication agrees, up to NaN. The product is exact pre-rounding on both sides. -/
theorem mul_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (a * b).ModelEquiv (fa * fb) := by
  apply modelEquiv_of_toExtRat_eq
  · rw [mul_toExtRat_eq a b,
      model_mul_toExtRat (toExtRat_eq_modelToExtRat_of_modelEquiv ha)
        (toExtRat_eq_modelToExtRat_of_modelEquiv hb)]
  · exact mul_hzsign ha hb

end FpAgainstFloatModel
