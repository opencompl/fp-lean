import Fp.Theorems.LowerUpperRound.Basic
import Fp.Theorems.LowerUpperRound.Functional

namespace Fp

#check PackedFloat.eq_getInfinity_of_lt_maxNormalNumber_of_isNaN_of_nonneg


theorem lower_Number_eq_getInfinity_of_maxNormalNumber_lt
  {ep sp : Nat}
  (hep : 0 < ep)
  (hsp : 0 < sp)
  (r : Rat)
  (hx :  r < (PackedFloat.maxNormalNumber ep sp true).toRat) :
  lower ep sp hep hsp (ExtRat.Number r) = PackedFloat.getInfinity ep sp false := by
  rw [lower]
  simp
  have : r ≠ 0 := by sorry
  simp [this]
  sorry


theorem upper_Number_eq_getInfinity_of_maxNormalNumber_lt
  {ep sp : Nat}
  (hep : 0 < ep)
  (hsp : 0 < sp)
  (r : Rat)
  (hx : (PackedFloat.maxNormalNumber ep sp false).toRat < r) :
  upper ep sp hep hsp (ExtRat.Number r) = PackedFloat.getInfinity ep sp false := by
  rw [upper]
  simp only [ExtRat.ExtRat.neg_number]
  rw [lower]
  simp
  have : r ≠ 0 := by sorry
  simp [this]
  sorry

end Fp
