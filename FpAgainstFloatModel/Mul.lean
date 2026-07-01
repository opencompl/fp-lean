import FpAgainstFloatModel.Basic

/-! # `PackedFloat.mul` agrees with `Float.Model.mul` (round-to-nearest-even). -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

/-- Multiplication agrees, up to NaN. The product is exact pre-rounding on both sides. -/
theorem mul_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (a * b).ModelEquiv (fa * fb) := by
  sorry

end FpAgainstFloatModel
