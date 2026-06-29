import Fp.Theorems.UnpackedFloat.Round.RounderForSign
import Fp.Theorems.UnpackedFloat.Round.IsEvenBoundary

namespace Fp

/-- **Sticky theory.** `needsRounding` at precision `sp+1` equals the sticky bit at precision `sp`:
both are "some significand bit strictly below the `sp` guard index is set". (At `sp+1` the guard index
drops by one, so `guard_{sp+1} || sticky_{sp+1}` ranges over exactly the bits `< guardIndex_sp`.) -/
theorem needsRounding_succ_eq_blastExtractStickyBit
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su) (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    x.needsRounding ep (sp + 1) = x.blastExtractStickyBit ep sp := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hst_sp := extractStickyBit_eq_false_iff he hs heu_sp (by omega) x hdiffLower hdiffUpper hdiffNatLe
  have hst_sp1 := extractStickyBit_eq_false_iff he (by omega) heu (by omega) x hdiffLower hdiffUpper (by omega)
  have hgb_sp1 := UnpackedFloat.blastExtractGuardBit_eq_true_iff he (by omega) heu (by omega)
    x hdiffLower hdiffUpper (by omega)
  -- Both predicates are `false` iff every significand bit below the `sp` guard index is `0`.
  have key : x.needsRounding ep (sp + 1) = false ↔ x.blastExtractStickyBit ep sp = false := by
    rw [hst_sp]
    unfold UnpackedFloat.needsRounding
    rw [Bool.or_eq_false_iff]
    have hgf : x.blastExtractGuardBit ep (sp + 1) = false
        ↔ x.sig.getLsbD (su - (sp + 1 + 2) + (minNormalExp ep - x.ex.toInt).toNat) = false := by
      rw [← Bool.not_eq_true, hgb_sp1]; simp
    rw [hgf, hst_sp1]
    constructor
    · rintro ⟨hg, hlt⟩ i hi
      rcases Nat.lt_or_ge i (su - (sp + 1 + 2) + (minNormalExp ep - x.ex.toInt).toNat) with h | h
      · exact hlt i h
      · have : i = su - (sp + 1 + 2) + (minNormalExp ep - x.ex.toInt).toNat := by omega
        rw [this]; exact hg
    · intro hall
      exact ⟨hall _ (by omega), fun i hi => hall i (by omega)⟩
  cases hnr : x.needsRounding ep (sp + 1) <;> cases hst : x.blastExtractStickyBit ep sp <;> simp_all

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

/-- The lower approximant's exponent is `x.ex + off` (from the witness's `toRatExp` conjunct). -/
theorem smtLibLower_lower_toRatExp_eq
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRatExp
      = x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int) := by
  obtain ⟨pf, hpfNotNaN, hpfLower, _, _, hexpeq, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      he hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hs _)
  rw [← hpflow]; exact hexpeq

/-- **Lower bridge.** `lower_{sp+1}.toRat = lower_sp.toRat + (guard ? ulp_{sp+1} : 0)`, with
`ulp_{sp+1} = 2^(x.ex − (sp+1) + off)` — from the round-toward-zero guard-bit add lemma + the pins. -/
theorem smtLibLower_succ_toRat_eq_lower_add_guard_ulp
    {eu su ep sp : Nat} (he : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        + (if x.blastExtractGuardBit ep sp then
            (2 : Rat) ^ (x.ex.toInt - ((sp : Int) + 1) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
          else 0) := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotunder; simpa using hnotunder
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    omega
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  rw [smtLibLower_lower_toRat_eq_blastRoundTowardZero (sp := sp + 1) (by grind) (by omega) heu (by omega)
        x hxsign hxnorm hnotunder1 hnotover1,
    UnpackedFloat.blastRoundTowardZero_succ_toRat'_eq_add_guardBit (by grind) hs heu hsu x hxsign hnotunder hnotover,
    smtLibLower_lower_toRat_eq_blastRoundTowardZero (by grind) hs heu_sp (by omega)
        x hxsign hxnorm hnotunder hnotover]

/-- **Upper foundation lemma.** For a nonnegative in-range normalized float whose lower approximant is
not `maxNormal` (so the successor is finite), the upper approximant is the lower plus one ULP exactly
when rounding is needed: `upper.toRat = lower.toRat + (needsRounding ? ulp : 0)` with
`ulp = 2^(-sp)·2^(lower.toRatExp)`. From `upper = lower` (representable) / `lower.successorAwayFromZero`
(needs rounding) and `toRat_successorAwayFromZero_eq`. -/
theorem smtLibUpper_toRat_eq_lower_add_ulp
    {eu su ep sp : Nat} (he : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        + (if x.needsRounding ep sp then
            (2 : Rat) ^ (-(sp : Int))
              * 2 ^ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRatExp
          else 0) := by
  have he' : 0 < ep := by grind
  have hmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
    (by grind) hs heu x hxnorm hnotunder
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  have hfinL := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range
    he hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hLnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN :=
    by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfinL
  have hLinf : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isInfinite :=
    by simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfinL
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hs _)
  have hsignL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).sign
      = false := by rw [← hpflow, ← hSign, sign_blastRoundTowardZero, hxsign]
  by_cases hnr : x.needsRounding ep sp = true
  · have hne : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        ≠ x.toRat' := by
      rw [← hpflow, ← hToRat]
      intro hc
      have := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
        (by grind) hs heu hsu x hxsign hnotunder hnotover).mp hc
      rw [this] at hnr; simp at hnr
    have hfinSucc := PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal
      (by grind) hs _ hsignL hfinL hmaxL
    rw [upper_eq_lower_successorAwayFromZero_of_ne (by grind) hs x.toRat' hxpos hfinL hfinSucc hsignL hne,
      PackedFloat.toRat_successorAwayFromZero_eq _ hLnan hLinf (by rw [hsignL]; exact hmaxL) (by grind) hs,
      hnr]
    simp [hsignL, Bool.toSign]
  · have hnr' : x.needsRounding ep sp = false := by grind
    have hrepr : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        = x.toRat' := by
      rw [← hpflow, ← hToRat]
      exact (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
        (by grind) hs heu hsu x hxsign hnotunder hnotover).mpr hnr'
    rw [upper_eq_lower_of_lower_isNormOrNonzeroSubnorm he' hs x.toRat' hfinL hrepr, hnr']
    simp

/-- **Upper foundation lemma at `sp+1`, sticky form.** The same statement at precision `sp+1`, with
`needsRounding_{sp+1}` rewritten to the `sp` sticky bit (`needsRounding_succ_eq_blastExtractStickyBit`):
`upper_{sp+1}.toRat = lower_{sp+1}.toRat + (stickyBit_sp ? ulp_{sp+1} : 0)`. -/
theorem smtLibUpper_succ_toRat_eq_lower_add_sticky_ulp
    {eu su ep sp : Nat} (he : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep (sp + 1) = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat
        + (if x.blastExtractStickyBit ep sp then
            (2 : Rat) ^ (-((sp : Int) + 1))
              * 2 ^ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRatExp
          else 0) := by
  rw [smtLibUpper_toRat_eq_lower_add_ulp (sp := sp + 1) he (by omega) heu (by omega)
        x hxsign hxnorm hnotunder hnotover hmaxL,
    needsRounding_succ_eq_blastExtractStickyBit (by grind) hs heu hsu x hdiffLower hdiffUpper hdiffNatLe]
  simp

/-- **Upper bridge.** `upper_sp.toRat = upper_{sp+1}.toRat ⟺ guard == sticky` (nonnegative, in-range,
wide, both lowers ≠ maxNormal). From the two upper foundation lemmas + the lower bridge: writing
`u = 2^(x.ex-(sp+1)+off)`, `upper_sp − upper_{sp+1} = (needsRounding?2u:0) − (guard?u:0) − (sticky?u:0)`,
which vanishes (with `u > 0`, `needsRounding = guard||sticky`) exactly when `guard = sticky`. -/
theorem smtLibUpper_eq_iff_guard_eq_sticky
    {eu su ep sp : Nat} (he : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false)
    (hmaxL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    ((SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        = (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat)
      ↔ (x.blastExtractGuardBit ep sp = x.blastExtractStickyBit ep sp) := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotunder; simpa using hnotunder
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    omega
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  rw [smtLibUpper_toRat_eq_lower_add_ulp he hs heu_sp (by omega) x hxsign hxnorm hnotunder hnotover hmaxL,
    smtLibUpper_succ_toRat_eq_lower_add_sticky_ulp he hs heu hsu x hxsign hxnorm
      hnotunder1 hnotover1 hmaxL1 hdiffLower hdiffUpper hdiffNatLe,
    smtLibLower_succ_toRat_eq_lower_add_guard_ulp he hs heu hsu x hxsign hxnorm hnotunder hnotover,
    smtLibLower_lower_toRatExp_eq (by grind) hs heu_sp (by omega) x hxsign hxnorm hnotunder hnotover,
    smtLibLower_lower_toRatExp_eq (sp := sp + 1) (by grind) (by omega) heu (by omega) x hxsign hxnorm
      hnotunder1 hnotover1]
  have hzne : (2 : Rat) ≠ 0 := by grind
  have hC : (2 : Rat) ^ (-((sp : Int) + 1)) * 2 ^ (x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int))
      = 2 ^ (x.ex.toInt - ((sp : Int) + 1) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
    rw [Rat.zpow_mul_zpow hzne]; congr 1; grind
  have hA : (2 : Rat) ^ (-(sp : Int)) * 2 ^ (x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int))
      = 2 * 2 ^ (x.ex.toInt - ((sp : Int) + 1) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
    have h2 := Rat.zpow_mul_zpow hzne (1 : Int)
      (x.ex.toInt - ((sp : Int) + 1) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
    rw [Rat.zpow_one] at h2
    rw [Rat.zpow_mul_zpow hzne, h2]; congr 1; grind
  have hupos : (0 : Rat) < 2 ^ (x.ex.toInt - ((sp : Int) + 1) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) :=
    Rat.two_pow_pos _
  rw [hA, hC]
  generalize hu : (2 : Rat) ^ (x.ex.toInt - ((sp : Int) + 1) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) = u
    at hupos ⊢
  unfold UnpackedFloat.needsRounding
  cases hg : x.blastExtractGuardBit ep sp <;> cases hst : x.blastExtractStickyBit ep sp <;>
    simp only [hg, hst, Bool.or_false, Bool.or_true, Bool.true_or, Bool.false_or, if_true, if_false,
      Bool.true_eq_false, Bool.false_eq_true] <;> grind

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
