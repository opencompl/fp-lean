import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.PackedFloat.Negation
import Fp.Theorems.PackedFloat.Ordering
import Fp.Theorems.LowerUpperRound
import Fp.Theorems.PackedUnpackedRel

namespace Fp


/--
`p iff q` iff `not p iff not q`.
-/
theorem iff_iff_not_iff_not {p q : Prop} :
    (p ↔ q) ↔ (¬ p ↔ ¬ q) := by
  grind

/-! # extractIsEven -/

theorem and_oneHotBV_eq_zero_iff (x i : BitVec w)  :
    x &&& (BitVec.oneHotBV i) = 0#w ↔ x.getLsbD i.toNat = false := by
  constructor
  · intros h
    rw [BitVec.eq_iff_getLsbD_eq] at h
    simp at h
    specialize h i.toNat
    grind only [= BitVec.getLsbD_of_ge]
  · intros h
    ext k hk
    simp
    intros hk
    have := i.getElem_oneHotBV ⟨k, by omega⟩
    grind only [= BitVec.getLsbD_eq_getElem, = Fin.getElem_fin]

@[simp]
theorem BitVec.and_allOnes_eq_self (bv : BitVec n) :
    bv &&& (BitVec.allOnes n) = bv := by
  ext UnpackedFloat.blastExtractGuardBit
  simp

@[simp]
theorem BitVec.allOnes_and_eq_self (bv : BitVec n) :
    (BitVec.allOnes n) &&& bv = bv := by
  ext i hi
  simp
/--
Zero extension to a larger width does not change the value.
-/
theorem BitVec.toNat_zeroExtend_of_le {n m : Nat} (bv : BitVec n) (h : n ≤ m) :
    (bv.zeroExtend m).toNat = bv.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le]
  grind only

end Fp
