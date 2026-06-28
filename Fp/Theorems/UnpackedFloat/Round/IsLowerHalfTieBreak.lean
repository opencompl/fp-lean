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
