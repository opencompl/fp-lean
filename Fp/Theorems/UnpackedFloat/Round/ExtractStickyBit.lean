import Fp.Theorems.UnpackedFloat.Round.ExtractIsEven

namespace Fp




theorem extractStickyBit_eq_true_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
  (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
  (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
  :
  x.blastExtractStickyBit ep sp = true ↔
    -- This makes sense,
    -- Consider when `su = sp + 2`.
    -- Then we're saying that some bit
    -- after the guard bit is nonzero.
     (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  simp [UnpackedFloat.blastExtractStickyBit]
  rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe]
  rw [show (su - 1 - (sp + 1)) = su - (sp + 2) by grind only]
  rw [show su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat =
       ((su + (minNormalExp ep - x.ex.toInt).toNat)) - (sp + 2) by grind only]
  · rw [show (su - (su + (minNormalExp ep - x.ex.toInt).toNat - (sp + 2))) =
        (sp + 2 - (minNormalExp ep - x.ex.toInt).toNat) by grind only]
    constructor
    · intros heq
      rw [BitVec.eq_iff_getLsbD_eq] at heq
      simp at heq
      obtain ⟨i, hi⟩ := heq
      exists i
      grind only
    · intros h
      simp at h
      intros hcontra
      rw [BitVec.eq_iff_getLsbD_eq] at hcontra
      simp at hcontra
      obtain ⟨i, hi⟩ := h
      specialize hcontra i (by grind)
      obtain ⟨hi1, hi2⟩ := hi
      grind
theorem extractStickyBit_eq_false_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
  (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
  (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
  :
  x.blastExtractStickyBit ep sp = false ↔
    -- This makes sense,
    -- This says that all the lower bits are false.
     (∀ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat →
      x.sig.getLsbD i = false) := by
  have htrue := extractStickyBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  rw [iff_iff_not_iff_not] at htrue
  grind only [#da50, #0b53, #b326]

/--
The sticky bit tracks whether there is a bit
below the guard bit that is 1.
This is equivalent to saying that there exists some bit below the guard bit that is 1.
-/
theorem UnpackedFloat.blastExtractStickyBit_eq_decide
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
  (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
  (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
  :
  x.blastExtractStickyBit ep sp = decide (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  by_cases hextract : x.blastExtractStickyBit ep sp = true
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
    grind only [#46e5, #0b53]
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
    simp at this
    grind only [#46e5, #0b53]

/--
info: 'Fp.UnpackedFloat.blastExtractStickyBit_eq_decide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastExtractStickyBit_eq_decide
end Fp
