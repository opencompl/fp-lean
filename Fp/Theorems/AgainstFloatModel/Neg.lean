import Fp.Theorems.AgainstFloatModel.Basic

/-! # `PackedFloat.neg` agrees with `Float.Model.neg` (a pure sign flip). -/

namespace Fp.AgainstFloatModel

variable {a : PackedFloat 11 52} {fa : Float.Model}

/-- Negation agrees, up to NaN. Both flip the sign bit (NaN stays canonical). -/
theorem neg_agree (ha : a.ModelEquiv fa) : (-a).ModelEquiv (-fa) := by
  sorry

end Fp.AgainstFloatModel
