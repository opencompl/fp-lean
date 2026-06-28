import Fp.Theorems.UnpackedFloat.Round.RounderForSign
import Fp.Theorems.UnpackedFloat.Round.IsEvenBoundary

namespace Fp

/-- The lower approximant's value is the round-toward-zero value, for a nonnegative in-range
normalized float. (The witness pins `lower = pack(roundTZ)`; this exposes just the `toRat`.) -/
theorem smtLibLower_lower_toRat_eq_blastRoundTowardZero
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
      = (x.blastRoundTowardZero ep sp).toRat' := by
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, _, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      he hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hs _)
  rw [← hpflow]
  exact hToRat.symm


/-- Nonnegative, in-range, and wide enough (`sp+1` precision fits): `blastIsLowerHalf = !guardBit`
matches the SMT `lowerHalf` (= `lower_sp = lower_{sp+1}`) via the guard-bit bridge. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_false_wide
    {eu su ep sp : Nat} (he : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hsu_sp : sp + 2 ≤ su := by omega
  -- propagate the in-range flags from `sp` to `sp+1`.
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotunder; simpa using hnotunder
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hmsub : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    omega
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  -- both lower approximants are finite, and equal their round-toward-zero values.
  have hfinL := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range
    he hs heu_sp hsu_sp x hxsign hxnorm hnotunder hnotover
  have hfinL1 := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range (sp := sp + 1)
    he (by omega) heu (by omega) x hxsign hxnorm hnotunder1 hnotover1
  have hpinL := smtLibLower_lower_toRat_eq_blastRoundTowardZero
    (by grind) hs heu_sp hsu_sp x hxsign hxnorm hnotunder hnotover
  have hpinL1 := smtLibLower_lower_toRat_eq_blastRoundTowardZero (sp := sp + 1)
    (by grind) (by omega) heu (by omega) x hxsign hxnorm hnotunder1 hnotover1
  rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_embed_eq,
    SmtLibSemantics.instExtendedRat.smtLibEq, PackedFloat.toExtRat_eq_toExtRat']
  rw [PackedFloat.toExtRat'_eq_toRat_of hfinL, PackedFloat.toExtRat'_eq_toRat_of hfinL1,
    ExtRat.Number.injEq, hpinL, hpinL1,
    UnpackedFloat.blastRoundTowardZero_toRat'_eq_succ_iff_not_guardBit
      (by grind) hs heu hsu x hxsign hnotunder hnotover]
  unfold UnpackedFloat.blastIsLowerHalf UnpackedFloat.blastIsLowerHalfNonneg
  simp only [hxsign, Bool.false_eq_true, if_false]
  cases h : x.blastExtractGuardBit ep sp <;> simp [h]

/-- Nonnegative at the underflow boundary (`x.ex = minSubnormalExp_sp − 1 = minSubnormalExp_{sp+1}`):
`lower_sp = +0` but `lower_{sp+1} > 0` (x is in range at `sp+1`), so `lowerHalf = false`; and the guard
bit is the (set) MSB, so `!guard = false`. Both sides are `false`. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_false_boundary
    {eu su ep sp : Nat} (he : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  obtain ⟨hoff, hdiffLower, hdiffUpper, hxpos, hlt⟩ :=
    boundary_facts he hs heu_sp (by omega) x hxsign hmsb hunder hnotearlyunder
  have hguard := blastExtractGuardBit_eq_true_of_off_eq_succ_of_msb (by grind) hs heu_sp (by omega)
    x hdiffLower hdiffUpper hoff hmsb
  -- `lower_sp = +0`.
  have hlowsp : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = PackedFloat.getZero ep sp false := by
    refine eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') _ _ ?_ ?_ ?_ ?_
    · simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp)
    · simp [PackedFloat.isNaN_getZero] <;> grind
    · exact lsLawfulLower_smtLibLower ep sp (by grind) hs (ExtRat.Number x.toRat')
    · exact isLawfulLower_Number_getZero_of_underflowNonneg (by grind) hs heu_sp (by grind) x hxsign hunder
  -- `x` is in range at `sp+1`.
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hms1 : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
      simp only [minSubnormalExp, maxSubnormalExp]; grind
    grind
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  have hfinL1 := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range (sp := sp + 1)
    he (by omega) heu (by omega) x hxsign hxnorm hnotunder1 hnotover1
  -- `lower_{sp+1}.sign = false`, hence `lower_{sp+1}.toRat > 0`.
  have hsignL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).sign = false := by
    obtain ⟨pf, hpfNotNaN, hpfLower, _, hSign, _⟩ :=
      UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero (sp := sp + 1)
        (by grind) (by omega) heu (by omega) x hxsign hxnorm hnotunder1 hnotover1
    have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)) :=
      eq_of_IsLawfulLower_of_IsLawfulLower ep (sp + 1) (ExtRat.Number x.toRat') pf _ hpfNotNaN
        (by simpa using not_isNaN_lower_of_ne_NaN ep (sp + 1) (by grind) (by omega) _ (by simp))
        hpfLower (lsLawfulLower_smtLibLower ep (sp + 1) (by grind) (by omega) _)
    rw [← hpflow, ← hSign, sign_blastRoundTowardZero, hxsign]
  have hlowsp1pos : 0 < (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat := by
    have hne := PackedFloat.toRat_ne_zero hfinL1
    have hnn := PackedFloat.sign_iff_toRat_neg hfinL1
    rw [hsignL1] at hnn; grind
  -- assemble: both sides are `false`.
  rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_embed_eq, hlowsp,
    SmtLibSemantics.instExtendedRat.smtLibEq]
  rw [show (PackedFloat.getZero ep sp false).toExtRat = ExtRat.Number 0 from by
      rw [PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero] <;> grind)],
    PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfinL1]
  unfold UnpackedFloat.blastIsLowerHalf UnpackedFloat.blastIsLowerHalfNonneg
  simp only [hxsign, Bool.false_eq_true, if_false, hguard, ExtRat.Number.injEq]
  grind


/-# blastIsLowerHalf -/

/-- `blastIsLowerHalf` agrees with the SMT-LIB `lowerHalf` predicate. Hypotheses match the isEven
theorems (so the RNE call site can supply them for `x.truncateFittingExponent`): a nonzero normalized
input, no early over/underflow. The SMT `lowerHalf` compares the lower approximant at precisions `sp`
and `sp+1`; the circuit's `!guardBit` matches via `blastRoundTowardZero_toRat'_eq_succ_iff_not_guardBit`. -/
theorem blastIsLowerHalf_iff_smtLibLowerHalf
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
    := by
  sorry

theorem blastIsLowerHalf_eq
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
  x.blastIsLowerHalf ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')) := by
  have := blastIsLowerHalf_iff_smtLibLowerHalf he hs heu hsu x hxnorm hmsb hnotunder hnotover
  grind

/--
info: 'Fp.blastIsLowerHalf_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blastIsLowerHalf_eq

@[simp]
theorem blastTieBreak_iff_smtLibTieBreak (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') := by
  simp [UnpackedFloat.blastIsTieBreak]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

/--
info: 'Fp.blastTieBreak_iff_smtLibTieBreak' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blastTieBreak_iff_smtLibTieBreak

@[simp]
theorem blastIsTieBreak_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat')) := by
  have := blastTieBreak_iff_smtLibTieBreak he hs x
  grind

/--
info: 'Fp.blastIsTieBreak_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blastIsTieBreak_eq

end Fp
