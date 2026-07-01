import FpAgainstFloatModel.Basic

/-! # `PackedFloat.div` agrees with `Float.Model.div` (round-to-nearest-even). -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

/-- Division agrees, up to NaN. Both compute a truncated quotient + sticky, then RNE round. -/
theorem div_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (a / b).ModelEquiv (fa / fb) := by
  sorry

end FpAgainstFloatModel
