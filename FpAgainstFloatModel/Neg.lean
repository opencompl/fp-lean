import FpAgainstFloatModel.Basic

/-! # `PackedFloat.neg` agrees with `Float.Model.neg` (a pure sign flip). -/

namespace FpAgainstFloatModel

variable {a : PackedFloat 11 52} {fa : Float.Model}

/-- Negation agrees, up to NaN. Both flip the sign bit (NaN stays canonical). -/
theorem neg_agree (ha : a.ModelEquiv fa) : (-a).ModelEquiv (-fa) := by
  rw [modelEquiv_iff_unpack] at ha ⊢
  rw [toModelUnpacked_neg, ha, show (-fa) = Float.Model.neg fa from rfl,
    model_neg_unpack fa (ModelCanonical_unpack _)]

end FpAgainstFloatModel
