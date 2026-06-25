import Fp.Theorems.UnpackedFloat.Round.ClearSignificand

namespace Fp




/-! # guardBitIndex -/

/--
The guard bit index when interpreted as a natural number
gives us the location of the guard bit inside the unpaked float.

The `hdiff*` hypotheses say that the exponent shift
`minNormalExp ep - x.ex.toInt` is representable at unpacked exponent width `eu`
and that the shifted guard position still lies inside the unpacked significand.
-/
theorem UnpackedFloat.toNat_guardBitIndex_eq (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    -- (heusu : eu ≤ su)
    :
    (x.guardBitIndex ep sp).toNat =
    (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat) := by
  have := @one_lt_exponentWidth ep sp
  have : su < 2 ^ su := by exact Nat.lt_two_pow_self
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)]
    · grind only
    · grind only
    · grind only

  rw [UnpackedFloat.guardBitIndex]
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.add_mod_mod, Nat.mod_add_mod]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      rw [Int.sub_toNat_eq_zero_of_le]
      · grind only [= Nat.mod_eq_of_lt]
      · grind only
    case isFalse h =>
      grind only [= Nat.mod_eq_of_lt]
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    exact hdiffLower
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    exact hdiffUpper

theorem UnpackedFloat.toNat_lsbIndex_eq (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    -- (heusu : eu ≤ su)
    :
    (x.lsbIndex ep sp).toNat =
    (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat + 1) := by
  have := @one_lt_exponentWidth ep sp
  have hsu : su < 2 ^ su := by exact Nat.lt_two_pow_self
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)]
    · grind only
    · grind only
    · grind only
  rw [UnpackedFloat.lsbIndex, UnpackedFloat.guardBitIndex]
  rw [BitVec.toNat_add]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      grind only [= Int.toNat_neg_eq_zero_of_nonpos, = Nat.mod_eq_of_lt, #37a5855c772b74a3]
    case isFalse h =>
      grind only [= Nat.mod_eq_of_lt]
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    grind only

end Fp
