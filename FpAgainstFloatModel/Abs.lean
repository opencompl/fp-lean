import FpAgainstFloatModel.Basic

/-! # `PackedFloat.abs` agrees with `Float.Model.abs` (clears the sign bit). -/

namespace FpAgainstFloatModel

variable {a : PackedFloat 11 52} {fa : Float.Model}

/-- Absolute value agrees, up to NaN. Both set the sign bit to `false`. -/
theorem abs_agree (ha : a.ModelEquiv fa) : (a.abs).ModelEquiv (fa.abs) := by
  rw [modelEquiv_iff_unpack] at ha ⊢
  rw [toModelUnpacked_abs, ha, show fa.abs = Float.Model.abs fa from rfl,
    model_abs_unpack fa (ModelCanonical_unpack _)]

end FpAgainstFloatModel
