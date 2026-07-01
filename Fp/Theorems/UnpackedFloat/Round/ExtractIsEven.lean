import Fp.Theorems.UnpackedFloat.Round.ExtractGuardBit

namespace Fp



@[simp]
theorem UnpackedFloat.blastExtractIsEven_eq_true_iff
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    x.blastExtractIsEven ep sp = true ↔
    (x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1) = false):= by
  simp [UnpackedFloat.blastExtractIsEven]
  constructor
  · intros h
    try simp only at h
    rw [BitVec.eq_iff_getLsbD_eq] at h
    simp only [BitVec.getLsbD_and, BitVec.getlsbD_oneHotBV, BitVec.getLsbD_zero, Bool.and_eq_false_imp, decide_eq_true_eq,
      decide_eq_false_iff_not] at h
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    specialize h _ hcontra
    rw [UnpackedFloat.toNat_lsbIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at h
    grind only
  · intros h
    try simp only at h
    rw [BitVec.eq_iff_getLsbD_eq]
    intros i
    simp
    intros hx hi
    intros hcontra
    rw [UnpackedFloat.toNat_lsbIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at hcontra
    grind only


theorem blastExtractIsEven_eq_not_getLsbD
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.blastExtractIsEven ep sp = !x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1)  := by
  have := UnpackedFloat.blastExtractIsEven_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  grind

theorem getLsbD_eq_not_blastExtractIsEven
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1) = !x.blastExtractIsEven ep sp := by
  have := UnpackedFloat.blastExtractIsEven_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  grind

/--
info: 'Fp.UnpackedFloat.blastExtractIsEven_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastExtractIsEven_eq_true_iff


-- TODO: 'toRatSig' lemma about what the guardBit tracks.

end Fp
