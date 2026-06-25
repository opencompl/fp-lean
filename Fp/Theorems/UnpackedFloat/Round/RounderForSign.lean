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


theorem UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hx0 : x.isZero) :
  (x.blastRounderForSign ep sp).Rel
    ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).rounderForSign x.sign
        (ExtRat.Number 0)) := by
  by_cases hsign : x.sign
  · simp [hsign]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact (UnpackedFloat.blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm)
  · simp [hsign]
    rw [UnpackedFloat.blastRounderForSign_of_sign_eq_false_eq x (by grind)]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact
      (UnpackedFloat.blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm)

/--
info: 'Fp.UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero

end Fp
