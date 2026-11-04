import Fp.Theorems.UnpackedFloat.Round.LowerUpper

namespace Fp




/-# `blastRounderForSign` matches `rounderForSign`-/


@[simp]
theorem UnpackedFloat.blastRounderForSign_of_sign_eq_true_eq
    (x : UnpackedFloat eu su)
    (hsign : x.sign = true) :
    x.blastRounderForSign ep sp = x.blastUpper ep sp := by
  simp [UnpackedFloat.blastRounderForSign, hsign]

theorem UnpackedFloat.blastRounderForSign_of_sign_eq_false_eq
    (x : UnpackedFloat eu su)
    (hsign : x.sign = false) :
    x.blastRounderForSign ep sp = x.blastLower ep sp := by
  simp [UnpackedFloat.blastRounderForSign, hsign]


theorem UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero (he : 1 < ep) (hs : 0 < sp)
    (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hx0 : x.isZero) :
  (x.blastRounderForSign ep sp).Rel
    ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).rounderForSign x.sign
        (ExtRat.Number 0)) := by
  have hnotEO : x.blastIsEarlyOverflowNonneg ep sp = false :=
    UnpackedFloat.blastIsEarlyOverflowNonneg_eq_false_of_isZero he hs heu x hxnorm hx0
  by_cases hsign : x.sign
  · simp [hsign]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact (UnpackedFloat.blastUpper_Rel_smtLibUpper he hs hsu heu x hxnorm hnotEO)
  · simp [hsign]
    rw [UnpackedFloat.blastRounderForSign_of_sign_eq_false_eq x (by grind)]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact
      (UnpackedFloat.blastLower_Rel_smtLibLower he hs hsu heu x hxnorm hnotEO)

/--
info: 'Fp.UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero

end Fp
