import Fp.Theorems.AgainstFloatModel.Basic

/-! # `PackedFloat.sqrt` agrees with `Float.Model.sqrt` (round-to-nearest-even). -/

namespace Fp.AgainstFloatModel

variable {a : PackedFloat 11 52} {fa : Float.Model}

/-- Square root agrees, up to NaN. NOTE: unlike +,*,/ there is no existing project↔spec
`sqrt` theorem, so the inner circuit-agreement here is the largest obligation. -/
theorem sqrt_agree (ha : a.ModelEquiv fa) :
    (sqrt a .RNE).ModelEquiv (fa.sqrt) := by
  sorry

end Fp.AgainstFloatModel
