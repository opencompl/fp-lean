import Fp.Theorems.UnpackedFloat.Round.GuardBitIndex

namespace Fp



/-! # extractGuardBit -/
theorem UnpackedFloat.blastExtractGuardBit_eq_true_iff
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.blastExtractGuardBit ep sp = true ↔
    x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat) := by
  simp [UnpackedFloat.blastExtractGuardBit]
  constructor
  · intros h
    obtain h := BitVec.ne_iff_getLsbD_ne .. |>.mp h
    obtain ⟨i, hi⟩ := h
    simp only [BitVec.getLsbD_and, BitVec.getlsbD_oneHotBV, BitVec.getLsbD_zero, ne_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, not_imp,
      Decidable.not_not] at hi
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at hi
    grind only
  · intros h
    intros hcontra
    obtain hcontra := BitVec.eq_iff_getLsbD_eq .. |>.mp hcontra
    simp at hcontra
    specialize hcontra _ h (by grind)
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at hcontra
    grind only

/--
The guard bit is the bit at the lower index at '2' (when `su = sp + 2`),
plus the offset from the exponent difference, which accounts for shifts when we are subnormal.
-/
theorem UnpackedFloat.extractGuardBit_eq_getLsbD
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.blastExtractGuardBit ep sp =  x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat)  := by
  have := UnpackedFloat.blastExtractGuardBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  grind only [#65b0223044fbdd80]

end Fp
