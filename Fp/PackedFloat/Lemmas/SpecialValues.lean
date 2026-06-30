import Fp.PackedFloat.Lemmas.Ordering

/-!
## Lemmas about distinguished `PackedFloat` values

Classification and rational-value facts for the min/max normal/subnormal numbers
and the E5M2 constants.
-/

namespace PackedFloat

@[simp, grind .]
theorem isNorm_maxNormalNumber_eq_decide
    (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).isNorm =
    decide (1 < exWidth) := by
  simp [PackedFloat.maxNormalNumber, isNorm]
  rcases exWidth with rfl | rfl  | exWidth
  · simp
  · simp
  · simp
    constructor
    · intros hcontra
      have := BitVec.toInt_inj.mpr hcontra
      simp only [BitVec.toInt_sub, BitVec.toInt_allOnes, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ,
        ↓reduceIte, Int.reduceNeg, BitVec.toInt_one_of_lt, Int.reduceSub] at this
      rw [Int.bmod_eq_of_le] at this
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · grind only
    · intros hcontra
      have := BitVec.toInt_inj.mpr hcontra
      simp only [BitVec.toInt_sub, BitVec.toInt_allOnes, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ,
        ↓reduceIte, Int.reduceNeg, BitVec.toInt_one_of_lt, Int.reduceSub, BitVec.toInt_zero] at this
      rw [Int.bmod_eq_of_le] at this
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · grind only

@[simp, grind .]
theorem isNorm_maxNormalNumber_of_lt_e (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).isNorm = true := by
  simp [PackedFloat.maxNormalNumber, isNorm]
  constructor
  · intros hcontra
    have : BitVec.allOnes e = BitVec.allOnes e + 1#e := by
      grind only
    simp at this
    grind only
  · intros hcontra
    have : BitVec.allOnes e = 0#e + 1#e := by
      rw [← hcontra]
      grind only
    simp at this
    grind only

@[simp]
theorem isNorm_minNormalNumber (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.minNormalNumber e s sign).isNorm = true := by
  simp [PackedFloat.minNormalNumber, isNorm]
  constructor
  · apply BitVec.toNat_ne_iff_ne.mp
    simp
    rw [Nat.mod_eq_of_lt (by grind)]
    have : 2^2 ≤ 2 ^ e := by
      exact Fp.Nat.two_pow_le_two_pow_of_le he
    grind only
  · grind only

@[simp]
theorem toRatSig_minNormalNumber (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.minNormalNumber e s sign).toRatSig = 1 := by
  rw [toRatSig]
  simp [isNorm_minNormalNumber, he]
  grind only

@[simp]
theorem toRatExp_minNormalNumber (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.minNormalNumber e s sign).toRatExp = minNormalExp e := by
  rw [toRatExp]
  simp [isNorm_minNormalNumber, he]
  norm_cast
  rw [Nat.mod_eq_of_lt (by grind)]
  rw [minNormalExp]
  have : 0 < bias e := by exact bias_pos_of_one_lt e he
  grind only


@[simp]
theorem toRatSig_maxNormalNumber (e s : Nat) (he : 2 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).toRatSig = 2 - 2 ^ (- (s : Int)) := by
  rw [toRatSig]
  simp [isNorm_maxNormalNumber_eq_decide]
  have : 0 < 2 ^ s := by grind only [!Nat.two_pow_pos]
  rw [Rat.natCast_sub_of_le (by grind only)]
  simp
  rw [Rat.sub_div_eq_div_sub_div]
  rw [Rat.div_self_eq_one_of_ne_zero (by grind only [Rat.two_pow_nat_ne_zero])]
  rw [Rat.one_div_zpow_natCast_eq_zpow_neg]
  grind only

@[simp]
theorem toRatExp_maxNormalNumber (e s : Nat) (he : 2 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).toRatExp = maxNormalExp e := by
  rw [toRatExp]
  rw [isNorm_maxNormalNumber_eq_decide]
  simp only [decide_eq_true_eq, ex_maxNormalNumber]
  simp only [show 1 < e by grind, if_true]
  rw [maxNormalExp]
  rw [bias]
  rw [BitVec.toNat_allOnes_sub_one_eq_twoPow_sub_two _ (by grind only)]
  grind

@[simp, grind .]
theorem isNonzeroSubnorm_minSubnormalNumber_eq_decide
    (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minSubnormalNumber exWidth sigWidth sign).isNonzeroSubnorm =
    (decide (0 < exWidth) && decide (0 < sigWidth)) := by
  simp [PackedFloat.minSubnormalNumber, isNonzeroSubnorm]
  rcases exWidth with rfl | rfl | exWidth
  · simp
  · simp
    rcases sigWidth with rfl | sigWidth
    · simp
    · simp
  · simp
    rcases sigWidth with rfl | sigWidth
    · simp
    · simp

@[simp, grind .]
theorem isNonzeroSubnorm_maxSubnormalNumber_eq_decide
    (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxSubnormalNumber exWidth sigWidth sign).isNonzeroSubnorm =
    (decide (0 < exWidth) && decide (0 < sigWidth)) := by
  simp [PackedFloat.maxSubnormalNumber, isNonzeroSubnorm]
  rcases exWidth with rfl | rfl | exWidth
  · simp
  · simp
    rcases sigWidth with rfl | sigWidth
    · simp
    · simp
  · simp
    rcases sigWidth with rfl | sigWidth
    · simp
    · simp

@[simp, grind .]
theorem isNorm_minNormalNumber_eq_decide
  (exWidth sigWidth : Nat) (sign : Bool) :
  (PackedFloat.minNormalNumber exWidth sigWidth sign).isNorm =
  decide (1 < exWidth) := by
  simp [PackedFloat.minNormalNumber, isNorm]
  rcases exWidth with rfl | rfl | exWidth
  · simp
  · simp
  · simp
    intros hcontra
    have := BitVec.toInt_inj.mpr hcontra
    simp at this

end PackedFloat
