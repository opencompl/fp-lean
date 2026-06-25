import Fp.Theorems.UnpackedFloat.Round.Normalize

namespace Fp


/-# blastIsOverflowNonneg -/

@[simp]
theorem UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide  (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) :
    x.blastIsEarlyOverflowNonneg ep sp = decide (maxNormalExp ep < x.ex.toInt) := by
  simp [UnpackedFloat.blastIsEarlyOverflowNonneg]
  rw [BitVec.slt_eq_decide]
  rw [toInt_ofInt_maxNormalExp_eq_maxNormalExp_of_le (w := eu) he hs]
  · grind only

/-# blastIsUnderflowNonneg -/

@[simp]
theorem UnpackedFloat.blastUnderflowNonneg_eq_decide (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) :
    x.blastIsUnderflowNonneg ep sp = decide (x.ex.toInt < minSubnormalExp ep sp) := by
  simp [UnpackedFloat.blastIsUnderflowNonneg]
  rw [BitVec.slt_eq_decide]
  rw [toInt_ofInt_minSubnormalExp_eq_minSubnormalExp_of_le (w := eu) he hs]
  · grind only

/-# blastIsEarlyUnderflowNonneg -/

@[simp]
theorem UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) :
    x.blastIsEarlyUnderflowNonneg ep sp = decide (x.ex.toInt < minSubnormalExp ep sp - 1) := by
  simp [UnpackedFloat.blastIsEarlyUnderflowNonneg]
  rw [BitVec.slt_eq_decide]
  rw [toInt_ofInt_minSubnormalExp_sub_one_eq_minSubnormalExp_sub_one_of_le (w := eu) he hs]
  · grind only

@[simp]
theorem blastIsEarlyOverflowNonneg_neg (x : UnpackedFloat eu su) :
    (-x).blastIsEarlyOverflowNonneg tep tsp = x.blastIsEarlyOverflowNonneg tep tsp := rfl

@[simp]
theorem blastIsEarlyUnderflowNonneg_neg (x : UnpackedFloat eu su) :
    (-x).blastIsEarlyUnderflowNonneg tep tsp = x.blastIsEarlyUnderflowNonneg tep tsp := rfl

end Fp
