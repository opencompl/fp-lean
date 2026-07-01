import FpAgainstFloatModel.Add

/-! # `PackedFloat.sub` agrees with `Float.Model.sub`. Both reduce to `add`+`neg`. -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

theorem sub_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (a - b).ModelEquiv (fa - fb) := by
  sorry

end FpAgainstFloatModel
