import Fp.Theorems.AgainstFloatModel.Basic

/-! # `PackedFloat.abs` agrees with `Float.Model.abs` (clears the sign bit). -/

namespace Fp.AgainstFloatModel

variable {a : PackedFloat 11 52} {fa : Float.Model}

/-- Absolute value agrees, up to NaN. Both set the sign bit to `false`. -/
theorem abs_agree (ha : a.ModelEquiv fa) : (a.abs).ModelEquiv (fa.abs) := by
  sorry

end Fp.AgainstFloatModel
