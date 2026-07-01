import FpAgainstFloatModel.Basic

/-! # `PackedFloat.add` agrees with `Float.Model.add` (round-to-nearest-even). -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

/-- Addition agrees, up to NaN. Proof factors as
`unpack agree (unpack_unpackRel) → UnpackedFloat.add agree (project vs Lean, structural)
→ round/blastSmtLibRound agree → pack agree (pack_modelEquiv)`. -/
theorem add_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (a + b).ModelEquiv (fa + fb) := by
  sorry

end FpAgainstFloatModel
