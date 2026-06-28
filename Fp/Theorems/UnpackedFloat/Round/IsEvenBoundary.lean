import Fp.Theorems.UnpackedFloat.Round.IsEvenLowerCore

namespace Fp

open UnpackedFloat

/-! # `isEven` at the underflow boundary

At `x.ex = minSubnormalExp − 1` (the only exponent that is `blastIsUnderflowNonneg` yet *not*
`blastIsEarlyUnderflowNonneg`), the shift amount `off = (minNormalExp − x.ex).toNat = sp + 1`. There the
guard-bit lives at the MSB (`su − 1`) and the LSB index `su` is out of range, so `blastExtractIsEven x`
is vacuously `true` and `needsRounding x` is forced `true` (a normalized significand has its MSB set).
The lower approximant is `+0` (even) and the upper is the smallest subnormal (odd), and these line up
with the bitblasted predicates — exactly as in the in-range case. -/

/-- Boundary variant of `toNat_lsbIndex_eq` (the shift may reach `sp + 1`). -/
theorem toNat_lsbIndex_eq_succ (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp + 1) :
    (x.lsbIndex ep sp).toNat = (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat + 1) := by
  have := @one_lt_exponentWidth ep sp
  have hsu' : su < 2 ^ su := Nat.lt_two_pow_self
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)] <;> grind only
  rw [UnpackedFloat.lsbIndex, UnpackedFloat.guardBitIndex, BitVec.toNat_add]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      grind only [= Int.toNat_neg_eq_zero_of_nonpos, = Nat.mod_eq_of_lt, #37a5855c772b74a3]
    case isFalse h => grind only [= Nat.mod_eq_of_lt]
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]; grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]; grind only

/-- Boundary variant of `toNat_guardBitIndex_eq` (the shift may reach `sp + 1`). -/
theorem toNat_guardBitIndex_eq_succ (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp + 1) :
    (x.guardBitIndex ep sp).toNat = (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat) := by
  have := @one_lt_exponentWidth ep sp
  have hsu' : su < 2 ^ su := Nat.lt_two_pow_self
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)] <;> grind only
  rw [UnpackedFloat.guardBitIndex, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.add_mod_mod, Nat.mod_add_mod]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      rw [Int.sub_toNat_eq_zero_of_le] <;> grind only [= Nat.mod_eq_of_lt]
    case isFalse h => grind only [= Nat.mod_eq_of_lt]
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]; exact hdiffLower
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]; exact hdiffUpper

/-- At the boundary (`off = sp + 1`) the inspected LSB index is `su` (out of range), so
`blastExtractIsEven` is vacuously true. -/
theorem blastExtractIsEven_eq_true_of_off_eq_succ (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1) :
    x.blastExtractIsEven ep sp = true := by
  have hlsb : (x.lsbIndex ep sp).toNat = su := by
    rw [toNat_lsbIndex_eq_succ hep hsp heu hsu x hdiffLower hdiffUpper (by omega), hoff]; omega
  simp only [UnpackedFloat.blastExtractIsEven, decide_eq_true_eq]
  rw [and_oneHotBV_eq_zero_iff, hlsb]
  exact BitVec.getLsbD_of_ge x.sig su (by omega)

/-- At the boundary, the guard bit is the (set) MSB, so `needsRounding` is true. -/
theorem needsRounding_eq_true_of_off_eq_succ_of_msb (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1) (hmsb : x.sig.msb = true) :
    x.needsRounding ep sp = true := by
  have hgbi : (x.guardBitIndex ep sp).toNat = su - 1 := by
    rw [toNat_guardBitIndex_eq_succ hep hsp heu hsu x hdiffLower hdiffUpper (by omega), hoff]; omega
  have hlast : x.sig.getLsbD (su - 1) = true := (BitVec.msb_eq_getLsbD_last x.sig).symm.trans hmsb
  have hgb : x.blastExtractGuardBit ep sp = true := by
    unfold UnpackedFloat.blastExtractGuardBit
    simp only [ne_eq, decide_eq_true_eq]
    rw [and_oneHotBV_eq_zero_iff, hgbi, hlast]
    simp
  simp [UnpackedFloat.needsRounding, hgb]

/-- At the boundary, the guard bit is the (set) MSB, hence `true`. -/
theorem blastExtractGuardBit_eq_true_of_off_eq_succ_of_msb (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1) (hmsb : x.sig.msb = true) :
    x.blastExtractGuardBit ep sp = true := by
  have hgbi : (x.guardBitIndex ep sp).toNat = su - 1 := by
    rw [toNat_guardBitIndex_eq_succ hep hsp heu hsu x hdiffLower hdiffUpper (by omega), hoff]; omega
  have hlast : x.sig.getLsbD (su - 1) = true := (BitVec.msb_eq_getLsbD_last x.sig).symm.trans hmsb
  unfold UnpackedFloat.blastExtractGuardBit
  simp only [ne_eq, decide_eq_true_eq]
  rw [and_oneHotBV_eq_zero_iff, hgbi, hlast]
  simp

/-- Shared boundary setup: at `blastIsUnderflowNonneg ∧ ¬blastIsEarlyUnderflow`, the exponent is
`minSubnormalExp − 1`, the shift is in range, and `0 < x.toRat' < minSubnormalNumber`. -/
private theorem boundary_facts {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (minNormalExp ep - x.ex.toInt).toNat = sp + 1 ∧
    (-2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt) ∧
    (minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1)) ∧
    0 < x.toRat' ∧ x.toRat' < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
  have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hexlt : x.ex.toInt < minSubnormalExp ep sp := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu] at hunder; simpa using hunder
  have hexge : minSubnormalExp ep sp - 1 ≤ x.ex.toInt := by
    rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu] at hnotearlyunder
    simp only [decide_eq_false_iff_not, Int.not_lt] at hnotearlyunder; exact hnotearlyunder
  have hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1 := by grind
  have hmaxN : minSubnormalExp ep sp ≤ maxNormalExp ep := by
    have hb := bias_pos_of_one_lt ep (by grind)
    rw [minSubnormalExp_eq_neg_bias_minus_s_minus_one (by grind)]; simp only [maxNormalExp]; omega
  obtain ⟨hdiffLower, hdiffUpper⟩ :=
    shift_range (by grind) hs heu (exInt := x.ex.toInt) (by grind) (by grind)
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  have hlt : x.toRat' < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hs]
    have hub := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x (by grind) hxsign
    have hexub : x.ex.toInt + 1 ≤ minNormalExp ep - (sp : Int) := by grind
    have hmono := Rat.two_pow_le_two_pow_of_le hexub
    grind
  exact ⟨hoff, hdiffLower, hdiffUpper, hxpos, hlt⟩

/-- Boundary case of the CORE (lower): `lower = +0` (even) and `blastExtractIsEven x = true`. -/
theorem isEven_smtLibLower_eq_blastExtractIsEven_boundary_of_sign_false {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = x.blastExtractIsEven ep sp := by
  obtain ⟨hoff, hdiffLower, hdiffUpper, _, _⟩ :=
    boundary_facts he hs heu hsu x hxsign hmsb hunder hnotearlyunder
  have hbe := blastExtractIsEven_eq_true_of_off_eq_succ (by grind) hs heu hsu x hdiffLower hdiffUpper hoff
  have hlow : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = PackedFloat.getZero ep sp false := by
    refine eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') _ _ ?_ ?_ ?_ ?_
    · simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp)
    · simp [PackedFloat.isNaN_getZero] <;> grind
    · exact lsLawfulLower_smtLibLower ep sp (by grind) hs (ExtRat.Number x.toRat')
    · exact isLawfulLower_Number_getZero_of_underflowNonneg (by grind) hs heu (by grind) x hxsign hunder
  rw [hlow, hbe]
  simp [SmtLibSemantics.roundableIsEven_of_packedFloat, PackedFloat.sig_getZero]

/-- Boundary case of the upper lemma: `upper = minSubnormalNumber` (odd) and `needsRounding`, so
`isEven(upper) = false = !blastExtractIsEven x`, matching the `bif needsRounding` arm. -/
theorem isEven_smtLibUpper_eq_boundary_of_sign_false {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = (bif x.needsRounding ep sp then !x.blastExtractIsEven ep sp else x.blastExtractIsEven ep sp) := by
  obtain ⟨hoff, hdiffLower, hdiffUpper, hxpos, hlt⟩ :=
    boundary_facts he hs heu hsu x hxsign hmsb hunder hnotearlyunder
  have hbe := blastExtractIsEven_eq_true_of_off_eq_succ (by grind) hs heu hsu x hdiffLower hdiffUpper hoff
  have hnr := needsRounding_eq_true_of_off_eq_succ_of_msb (by grind) hs heu hsu x hdiffLower hdiffUpper hoff hmsb
  have hupp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = PackedFloat.minSubnormalNumber ep sp false := by
    refine eq_of_IsLawfulUpper_of_IsLawfulUpper ep sp (ExtRat.Number x.toRat') _ _ ?_ ?_ ?_ ?_
    · simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp)
    · simpa using PackedFloat.not_isNaN_minSubnormalNumber ep sp false (by grind) hs
    · exact isLawfulUpper_smtLibUpper ep sp (by grind) hs (ExtRat.Number x.toRat')
    · exact isLawfulUpper_minSubnormalNumber_of_pos_of_le (by grind) hs x.toRat' hxpos (Rat.le_of_lt hlt)
  rw [hupp, hnr, hbe]
  simp [SmtLibSemantics.roundableIsEven_of_packedFloat, PackedFloat.minSubnormalNumber] <;> grind

/-! ### Full (in-range ∪ boundary) nonnegative lemmas and both-sign unifiers

These weaken the in-range `¬blastIsUnderflowNonneg` to `¬blastIsEarlyUnderflowNonneg` by dispatching
on `blastIsUnderflowNonneg` (boundary vs in-range). They require `x.sig.msb = true` (the input is a
nonzero normalized float — guaranteed for `x.truncateFittingExponent` of a nonzero value at the RNE
call site). -/

/-- `isEven(lower) = blastExtractIsEven x` for nonnegative `x` whether in range or at the boundary. -/
theorem isEven_smtLibLower_eq_blastExtractIsEven_full_of_sign_false {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = x.blastExtractIsEven ep sp := by
  by_cases hbu : x.blastIsUnderflowNonneg ep sp = true
  · exact isEven_smtLibLower_eq_blastExtractIsEven_boundary_of_sign_false
      he hs heu hsu x hxsign hmsb hbu hnotearlyunder
  · simp only [Bool.not_eq_true] at hbu
    exact isEven_smtLibLower_eq_blastExtractIsEven_of_sign_false
      he hs heu hsu x hxsign hxnorm hbu hnotover

/-- `isEven(upper) = bif needsRounding then !blastExtract else blastExtract` for nonnegative `x`,
in range or at the boundary. -/
theorem isEven_smtLibUpper_eq_full_of_sign_false {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = (bif x.needsRounding ep sp then !x.blastExtractIsEven ep sp else x.blastExtractIsEven ep sp) := by
  by_cases hbu : x.blastIsUnderflowNonneg ep sp = true
  · exact isEven_smtLibUpper_eq_boundary_of_sign_false
      he hs heu hsu x hxsign hmsb hbu hnotearlyunder
  · simp only [Bool.not_eq_true] at hbu
    exact isEven_smtLibUpper_eq_of_sign_false
      he hs heu hsu x hxsign hxnorm hbu hnotover

/-- Both-sign unifier (full): `isEven(lower) = blastIsEvenLower x`, in range or at the boundary. -/
theorem isEven_smtLibLower_eq_blastIsEvenLower_full {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = x.blastIsEvenLower ep sp := by
  have he' : 0 < ep := by grind
  by_cases hsign : x.sign = false
  · rw [show x.blastIsEvenLower ep sp = x.blastExtractIsEven ep sp from by
      simp [UnpackedFloat.blastIsEvenLower, UnpackedFloat.blastIsEven,
        UnpackedFloat.blastIsEvenNonneg, hsign, Bool.cond_self]]
    exact isEven_smtLibLower_eq_blastExtractIsEven_full_of_sign_false
      he hs heu hsu x hsign hxnorm hmsb hnotearlyunder hnotover
  · have hsignt : x.sign = true := by simp only [Bool.not_eq_false] at hsign; exact hsign
    have hnegval : (-(ExtRat.Number x.toRat')) = ExtRat.Number ((-x).toRat') :=
      (congrArg ExtRat.Number (UnpackedFloat.toRat'_neg x)).symm
    rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp he' hs (ExtRat.Number x.toRat') (by simp),
      isEven_neg, hnegval,
      isEven_smtLibUpper_eq_full_of_sign_false he hs heu hsu (-x)
        (by simp [UnpackedFloat.neg_sign, hsignt])
        (UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm) hmsb hnotearlyunder hnotover,
      show (-x).needsRounding ep sp = x.needsRounding ep sp from rfl,
      show (-x).blastExtractIsEven ep sp = x.blastExtractIsEven ep sp from rfl]
    simp [UnpackedFloat.blastIsEvenLower, UnpackedFloat.blastIsEven,
      UnpackedFloat.blastIsEvenNeg, hsignt]

/-- Both-sign unifier (full): `isEven(upper) = blastIsEvenUpper x`, in range or at the boundary. -/
theorem isEven_smtLibUpper_eq_blastIsEvenUpper_full {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = x.blastIsEvenUpper ep sp := by
  have he' : 0 < ep := by grind
  by_cases hsign : x.sign = false
  · rw [show x.blastIsEvenUpper ep sp
        = (bif x.needsRounding ep sp then !x.blastExtractIsEven ep sp else x.blastExtractIsEven ep sp)
        from by simp [UnpackedFloat.blastIsEvenUpper, UnpackedFloat.blastIsEven,
          UnpackedFloat.blastIsEvenNonneg, hsign]]
    exact isEven_smtLibUpper_eq_full_of_sign_false
      he hs heu hsu x hsign hxnorm hmsb hnotearlyunder hnotover
  · have hsignt : x.sign = true := by simp only [Bool.not_eq_false] at hsign; exact hsign
    have hnegval : (-(ExtRat.Number x.toRat')) = ExtRat.Number ((-x).toRat') :=
      (congrArg ExtRat.Number (UnpackedFloat.toRat'_neg x)).symm
    rw [smtLibUpper_eq_neg_smtLibLower_neg ep sp he' hs (ExtRat.Number x.toRat') (by simp),
      isEven_neg, hnegval,
      isEven_smtLibLower_eq_blastExtractIsEven_full_of_sign_false he hs heu hsu (-x)
        (by simp [UnpackedFloat.neg_sign, hsignt])
        (UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm) hmsb hnotearlyunder hnotover,
      show (-x).blastExtractIsEven ep sp = x.blastExtractIsEven ep sp from rfl]
    simp [UnpackedFloat.blastIsEvenUpper, UnpackedFloat.blastIsEven,
      UnpackedFloat.blastIsEvenNeg, hsignt, Bool.not_not]

end Fp
