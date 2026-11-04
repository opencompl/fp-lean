import Fp.Theorems.UnpackedFloat.Round.RounderForSign
import Fp.Theorems.UnpackedFloat.Round.IsEvenBoundary
import Fp.Theorems.UnpackedFloat.Round.Widen

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
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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

/-- The upper approximant is finite when the lower is in range and not `maxNormal` (so its successor
doesn't overflow). -/
theorem isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
  have hmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
    (by grind) hs heu x hxnorm hnotunder
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  have hfinL := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range
    he hs heu hsu x hxsign hxnorm hnotunder hnotover
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
      rw [← hpflow, ← hToRat]; intro hc
      have := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
        (by grind) hs heu hsu x hxsign hnotunder hnotover).mp hc
      rw [this] at hnr; simp at hnr
    have hfinSucc := PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal
      (by grind) hs _ hsignL hfinL hmaxL
    rw [upper_eq_lower_successorAwayFromZero_of_ne (by grind) hs x.toRat' hxpos hfinL hfinSucc hsignL hne]
    exact hfinSucc
  · have hnr' : x.needsRounding ep sp = false := by grind
    have hrepr : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        = x.toRat' := by
      rw [← hpflow, ← hToRat]
      exact (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
        (by grind) hs heu hsu x hxsign hnotunder hnotover).mpr hnr'
    rw [upper_eq_lower_of_lower_isNormOrNonzeroSubnorm (by grind) hs x.toRat' hfinL hrepr]
    exact hfinL

/-- **Upper bridge.** `upper_sp.toRat = upper_{sp+1}.toRat ⟺ guard == sticky` (nonnegative, in-range,
wide, both lowers ≠ maxNormal). From the two upper foundation lemmas + the lower bridge: writing
`u = 2^(x.ex-(sp+1)+off)`, `upper_sp − upper_{sp+1} = (needsRounding?2u:0) − (guard?u:0) − (sticky?u:0)`,
which vanishes (with `u > 0`, `needsRounding = guard||sticky`) exactly when `guard = sticky`. -/
theorem smtLibUpper_eq_iff_guard_eq_sticky
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq,
    SmtLibSemantics.instExtendedRat.smtLibEq, PackedFloat.toExtRat_eq_toExtRat']
  rw [PackedFloat.toExtRat'_eq_toRat_of hfinL, PackedFloat.toExtRat'_eq_toRat_of hfinL1,
    ExtRat.Number.injEq, hpinL, hpinL1,
    UnpackedFloat.blastRoundTowardZero_toRat'_eq_succ_iff_not_guardBit
      (by grind) hs heu hsu x hxsign hnotunder hnotover]
  unfold UnpackedFloat.blastIsLowerHalf UnpackedFloat.blastIsLowerHalfNonneg
  simp only [hxsign, Bool.false_eq_true, if_false]
  cases h : x.blastExtractGuardBit ep sp <;> simp [h]

/-- **Negative, in-range, wide.** For `x < 0`, `lower(r) = −upper(−r)`, so the SMT `lowerHalf` becomes
`upper_sp(|x|) = upper_{sp+1}(|x|)`, which the upper bridge identifies with `guard == sticky` — exactly
the (fixed) `blastIsLowerHalfNeg`. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_true_wide
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false)
    (hmaxL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have he' : 0 < ep := by grind
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  -- `-x` facts (negation flips sign, keeps sig/ex; guard/sticky/under/overflow are sign-independent).
  have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hxsignt]
  have hnnorm : (-x).normalize = -x := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
  have hnunder : (-x).blastIsUnderflowNonneg ep sp = false := hnotunder
  have hnover : (-x).blastIsEarlyOverflowNonneg ep sp = false := hnotover
  -- `-x` is in range at `sp+1` too.
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotunder; simpa using hnotunder
  have hnunder1 : (-x).blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    have hxex : (-x).ex.toInt = x.ex.toInt := by rw [UnpackedFloat.neg_ex]
    omega
  have hnover1 : (-x).blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp (-x)
    rw [this] at hnover; exact hnover
  -- upper(-x) is finite at both precisions.
  have hfinU := isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal
    he hs heu_sp (by omega) (-x) hnsign hnnorm hnunder hnover hmaxL
  have hfinU1 := isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal (sp := sp + 1)
    he (by omega) heu (by omega) (-x) hnsign hnnorm hnunder1 hnover1 hmaxL1
  -- `lower(Number x.toRat') = -(upper(Number (-x).toRat'))`.
  have hneg_val : (-(ExtRat.Number x.toRat')) = ExtRat.Number (-x).toRat' :=
    (congrArg ExtRat.Number (UnpackedFloat.toRat'_neg x)).symm
  have hlow : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = -(SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep sp) := by
    rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp he' hs (ExtRat.Number x.toRat') (by simp), hneg_val]
  have hlow1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
      = -(SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1)) := by
    rw [smtLibLower_eq_neg_smtLibUpper_neg ep (sp + 1) he' (by omega) (ExtRat.Number x.toRat') (by simp), hneg_val]
  -- lowerHalf ⟺ upper_sp(-x) = upper_{sp+1}(-x).
  have hlowerhalf :
      (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
        ↔ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep sp).toRat
            = (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1)).toRat := by
    rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hlow, hlow1,
      SmtLibSemantics.instExtendedRat.smtLibEq]
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_eq_toRat_of (by rw [PackedFloat.isNormOrNonzeroSubnorm_neg]; exact hfinU),
      PackedFloat.toExtRat'_eq_toRat_of (by rw [PackedFloat.isNormOrNonzeroSubnorm_neg]; exact hfinU1),
      PackedFloat.toRat_neg, PackedFloat.toRat_neg]
    simp only [ExtRat.Number.injEq]
    constructor <;> intro h <;> grind
  rw [hlowerhalf,
    smtLibUpper_eq_iff_guard_eq_sticky he hs heu hsu (-x) hnsign hnnorm hnunder hnover hmaxL hmaxL1
      (by rw [UnpackedFloat.neg_ex]; exact hdiffLower) (by rw [UnpackedFloat.neg_ex]; exact hdiffUpper)
      (by rw [UnpackedFloat.neg_ex]; exact hdiffNatLe),
    show (-x).blastExtractGuardBit ep sp = x.blastExtractGuardBit ep sp from rfl,
    show (-x).blastExtractStickyBit ep sp = x.blastExtractStickyBit ep sp from rfl,
    show x.blastIsLowerHalf ep sp = (x.blastExtractGuardBit ep sp == x.blastExtractStickyBit ep sp) from by
      simp [UnpackedFloat.blastIsLowerHalf, UnpackedFloat.blastIsLowerHalfNeg, hxsignt]]
  simp [beq_iff_eq]

/-- Nonnegative at the underflow boundary (`x.ex = minSubnormalExp_sp − 1 = minSubnormalExp_{sp+1}`):
`lower_sp = +0` but `lower_{sp+1} > 0` (x is in range at `sp+1`), so `lowerHalf = false`; and the guard
bit is the (set) MSB, so `!guard = false`. Both sides are `false`. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_false_boundary
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hlowsp,
    SmtLibSemantics.instExtendedRat.smtLibEq]
  rw [show (PackedFloat.getZero ep sp false).toExtRat = ExtRat.Number 0 from by
      rw [PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero] <;> grind)],
    PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfinL1]
  unfold UnpackedFloat.blastIsLowerHalf UnpackedFloat.blastIsLowerHalfNonneg
  simp only [hxsign, Bool.false_eq_true, if_false, hguard, ExtRat.Number.injEq]
  grind


/-# Widening transfer

The wide leaf lemmas above require `exponentWidth ep (sp+1) ≤ eu` and `sp+3 ≤ su`. At the RNE call site
those can fail, so we transfer them to a too-narrow `x` by widening (`Fp/.../Round/Widen.lean`): the
value (`toRat'`), the predicate (`blastIsLowerHalf`), and all flags are invariant under `widen`. -/

/-- The exponent-difference bounds for an in-range `x` (no underflow, no early overflow). -/
theorem inRange_diff_facts {eu su ep sp : Nat}
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (-2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt) ∧
    (minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1)) ∧
    ((minNormalExp ep - x.ex.toInt).toNat ≤ sp) := by
  have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hexge : minSubnormalExp ep sp ≤ x.ex.toInt := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu] at hnotunder
    simpa using hnotunder
  have hexle : x.ex.toInt ≤ maxNormalExp ep := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu] at hnotover
    simpa using hnotover
  obtain ⟨hdl, hdu⟩ := shift_range (by grind) hs heu (by grind) hexle
  exact ⟨hdl, hdu, by grind⟩

/-- **Nonnegative, in-range, narrow.** Transfer of `blastIsLowerHalf_iff_lowerHalf_of_sign_false_wide`
to a too-narrow `x` (only `sp+2 ≤ su`, `exponentWidth ep sp ≤ eu`) by widening to `eu'`, `su'`. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_false_inRange
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (eu' su' : Nat) (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (heu' : exponentWidth ep (sp + 1) ≤ eu') (hsu' : sp + 3 ≤ su')
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have hsupos : 0 < su := by omega
  have heu_succ : exponentWidth ep sp ≤ eu' := Nat.le_trans exponentWidth_le_succ heu'
  obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu x hnotunder hnotover
  -- transfer LHS (predicate) and RHS (value) to the widened float.
  rw [← blastIsLowerHalf_widen x eu' su' (by grind) hs heu (by omega) heu_succ (by omega)
        hwideu hwidesu hdl hdu hnat,
      ← toRat'_widen x eu' su' hwideu hwidesu hsupos]
  -- apply the wide leaf to `x.widen eu' su'`.
  refine blastIsLowerHalf_iff_lowerHalf_of_sign_false_wide he hs heu' hsu' (x.widen eu' su')
    (by rw [sign_widen]; exact hxsign)
    (normalize_widen x eu' su' hwidesu hsupos hmsb)
    ?_ ?_
  · rw [blastIsUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotunder
  · rw [blastIsEarlyOverflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotover

/-- At the nonneg underflow boundary the guard bit is the (set) MSB, so `blastIsLowerHalf = !guard = false`.
Width-generic: usable for `x` and its widening. -/
theorem blastIsLowerHalf_eq_false_of_sign_false_boundary {eu su ep sp : Nat}
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    x.blastIsLowerHalf ep sp = false := by
  obtain ⟨hoff, hdiffLower, hdiffUpper, _, _⟩ :=
    boundary_facts he hs heu hsu x hxsign hmsb hunder hnotearlyunder
  have hguard := blastExtractGuardBit_eq_true_of_off_eq_succ_of_msb (by grind) hs heu hsu x
    hdiffLower hdiffUpper hoff hmsb
  simp [UnpackedFloat.blastIsLowerHalf, UnpackedFloat.blastIsLowerHalfNonneg, hxsign, hguard]

/-- **Nonnegative, underflow boundary, narrow.** Transfer of the boundary leaf by widening; both sides
are `false`. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_false_boundary_narrow
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (eu' su' : Nat) (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (heu' : exponentWidth ep (sp + 1) ≤ eu') (hsu' : sp + 3 ≤ su')
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have hsupos : 0 < su := by omega
  have heu_succ : exponentWidth ep sp ≤ eu' := Nat.le_trans exponentWidth_le_succ heu'
  -- widened-float flags
  have hsign' : (x.widen eu' su').sign = false := by rw [sign_widen]; exact hxsign
  have hmsb' : (x.widen eu' su').sig.msb = true := by rw [sig_msb_widen x eu' su' hwidesu hsupos]; exact hmsb
  have hnorm' := normalize_widen x eu' su' hwidesu hsupos hmsb
  have hunder' : (x.widen eu' su').blastIsUnderflowNonneg ep sp = true := by
    rw [blastIsUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hunder
  have hnotearlyunder' : (x.widen eu' su').blastIsEarlyUnderflowNonneg ep sp = false := by
    rw [blastIsEarlyUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotearlyunder
  have hnotover' : (x.widen eu' su').blastIsEarlyOverflowNonneg ep sp = false := by
    rw [blastIsEarlyOverflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotover
  -- both sides are `false`.
  rw [blastIsLowerHalf_eq_false_of_sign_false_boundary he hs heu hsu x hxsign hmsb hunder hnotearlyunder,
      ← toRat'_widen x eu' su' hwideu hwidesu hsupos,
      ← blastIsLowerHalf_iff_lowerHalf_of_sign_false_boundary he hs heu' hsu' (x.widen eu' su')
        hsign' hnorm' hmsb' hunder' hnotearlyunder' hnotover',
      blastIsLowerHalf_eq_false_of_sign_false_boundary he hs heu_succ (by omega) (x.widen eu' su')
        hsign' hmsb' hunder' hnotearlyunder']


/-- **Negative, in-range, narrow, non-edge** (`lower ≠ maxNormal`). Transfer of the wide negative leaf
by widening. The `lower ≠ maxNormal` conditions are value-level, so they hold verbatim for `x.widen`. -/
theorem blastIsLowerHalf_iff_lowerHalf_of_sign_true_inRange
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (eu' su' : Nat) (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (heu' : exponentWidth ep (sp + 1) ≤ eu') (hsu' : sp + 3 ≤ su')
    (x : UnpackedFloat eu su) (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false)
    (hmaxL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have hsupos : 0 < su := by omega
  have heu_succ : exponentWidth ep sp ≤ eu' := Nat.le_trans exponentWidth_le_succ heu'
  obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu x hnotunder hnotover
  -- the negated value is preserved by widening.
  have hvaleq : (-(x.widen eu' su')).toRat' = (-x).toRat' := by
    rw [UnpackedFloat.toRat'_neg, toRat'_widen x eu' su' hwideu hwidesu hsupos, ← UnpackedFloat.toRat'_neg]
  -- widened-float facts.
  have hnotunder' : (x.widen eu' su').blastIsUnderflowNonneg ep sp = false := by
    rw [blastIsUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotunder
  have hnotover' : (x.widen eu' su').blastIsEarlyOverflowNonneg ep sp = false := by
    rw [blastIsEarlyOverflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotover
  obtain ⟨hdl', hdu', hnat'⟩ := inRange_diff_facts he hs heu_succ (x.widen eu' su') hnotunder' hnotover'
  rw [← blastIsLowerHalf_widen x eu' su' (by grind) hs heu (by omega) heu_succ (by omega)
        hwideu hwidesu hdl hdu hnat,
      ← toRat'_widen x eu' su' hwideu hwidesu hsupos]
  refine blastIsLowerHalf_iff_lowerHalf_of_sign_true_wide he hs heu' hsu' (x.widen eu' su')
    (by rw [sign_widen]; exact hxsignt)
    (normalize_widen x eu' su' hwidesu hsupos hmsb)
    (by rw [sig_msb_widen x eu' su' hwidesu hsupos]; exact hmsb)
    hnotunder' hnotover' hdl' hdu' hnat' ?_ ?_
  · rw [hvaleq]; exact hmaxL
  · rw [hvaleq]; exact hmaxL1

/-- If `lower` at precision `sp` is not `maxNormal`, then neither is it at `sp+1` (more precision means a
larger `maxNormal`, and `lower_{sp+1} = maxNormal_{sp+1}` would force `value ≥ maxNormal_sp`, hence
`lower_sp = maxNormal_sp`). -/
theorem lower_succ_ne_maxNormal_of_lower_ne_maxNormal {ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (R : Rat)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number R) : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number R) : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false := by
  intro hcontra
  apply hmaxL
  have hfin1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number R) : PackedFloat ep (sp + 1)).isNormOrNonzeroSubnorm := by
    rw [hcontra]; exact PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false
  have hle := lower_toRat_le (by grind) (by omega) R hfin1
  rw [hcontra] at hle
  have hmono := PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ he hs
  have hRge : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ R := by grind
  rw [smtLibLower_eq_lower ep sp (by grind) hs (ExtRat.Number R) (by simp)]
  exact lower_Number_eq_maxNormalNumber_of_toRat_le (by grind) (by grind) hs R hRge

/-- At the boundary (`off = sp+1`) the sticky bit is "some significand bit strictly below the MSB". -/
theorem blastExtractStickyBit_eq_true_of_off_eq_succ_iff {eu su ep sp : Nat}
    (hep : 1 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1) :
    x.blastExtractStickyBit ep sp = true ↔ (∃ i, i < su - 1 ∧ x.sig.getLsbD i = true) := by
  have hgbi : (x.guardBitIndex ep sp).toNat = su - 1 := by
    rw [toNat_guardBitIndex_eq_succ hep hsp heu hsu x hdiffLower hdiffUpper (by omega), hoff]; omega
  simp only [UnpackedFloat.blastExtractStickyBit, decide_eq_true_eq]
  rw [BitVec.ne_iff_getLsbD_ne]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_orderEncode, BitVec.getLsbD_zero, hgbi]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by grind, by grind⟩
  · rintro ⟨i, hlt, hbit⟩
    exact ⟨i, by grind⟩

/-- For `R ∈ [minSubnormal, successor(minSubnormal))`, the greatest float `≤ R` is `minSubnormal`
(there is nothing representable strictly between consecutive subnormals). -/
theorem lower_Number_eq_minSubnormalNumber_of_ge_of_lt_succ
    {ep sp : Nat} (hep : 1 < ep) (hsp : 0 < sp) (R : Rat)
    (hge : (PackedFloat.minSubnormalNumber ep sp false).toRat ≤ R)
    (hlt : R < 2 * (PackedFloat.minSubnormalNumber ep sp false).toRat) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number R) : PackedFloat ep sp)
      = PackedFloat.minSubnormalNumber ep sp false := by
  have hep0 : 0 < ep := by grind
  have hfin := PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false hep0 hsp
  have hnan := PackedFloat.not_isNaN_minSubnormalNumber ep sp false hep0 hsp
  have hmsign : (PackedFloat.minSubnormalNumber ep sp false).sign = false :=
    PackedFloat.sign_minSubnormalNumber ep sp false
  have hmnonneg : (0 : Rat) ≤ (PackedFloat.minSubnormalNumber ep sp false).toRat := by
    have h := PackedFloat.sign_iff_toRat_neg hfin
    rw [hmsign] at h
    have : ¬ ((PackedFloat.minSubnormalNumber ep sp false).toRat < 0) := by grind
    grind
  have hLnan : ¬ (PackedFloat.minSubnormalNumber ep sp false).isNaN := hnan
  have hLinf : ¬ (PackedFloat.minSubnormalNumber ep sp false).isInfinite :=
    by simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfin
  -- successor facts
  have hmaxLne : PackedFloat.minSubnormalNumber ep sp false ≠ PackedFloat.maxNormalNumber ep sp false := by
    intro hc
    have h1 : (PackedFloat.maxNormalNumber ep sp false).isNorm :=
      PackedFloat.isNorm_maxNormalNumber_of_lt_e ep sp (by grind) false
    rw [← hc] at h1
    simp [PackedFloat.isNorm, PackedFloat.minSubnormalNumber, BitVec.ofInt] at h1
  have hsucfin := PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal
    (by grind) hsp _ hmsign hfin hmaxLne
  have hsucnan : ¬ (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero.isNaN :=
    by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hsucfin
  have hsucinf : ¬ (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero.isInfinite :=
    by simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hsucfin
  have hsuczero : ¬ (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero.isZero :=
    by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hsucfin
  have hsucsign : (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero.sign = false := by
    rw [PackedFloat.sign_successorAwayFromZero, hmsign]
  -- `successor(minSub) = 2·minSub` (ulp at the smallest subnormal equals the subnormal itself).
  have hsucc_eq : (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero.toRat
      = 2 * (PackedFloat.minSubnormalNumber ep sp false).toRat := by
    rw [PackedFloat.toRat_successorAwayFromZero_eq _ hnan hLinf (by simpa using hmaxLne) (by grind) hsp,
      PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
    simp only [hmsign, Bool.toSign, PackedFloat.toRatExp,
      if_neg (show ¬ (PackedFloat.minSubnormalNumber ep sp false).isNorm = true by
        simp [PackedFloat.minSubnormalNumber, PackedFloat.isNorm])]
    rw [show (-(↑(bias ep - 1)) : Int) = minNormalExp ep from rfl, ← Rat.zpow_add (by decide),
      show (-(↑sp) + minNormalExp ep) = (minNormalExp ep - ↑sp) by omega]
    grind
  rw [smtLibLower_eq_lower ep sp hep0 hsp (ExtRat.Number R) (by simp)]
  symm
  apply eq_lower_of_IsLawfulLower ep sp hep0 hsp _ _ (by simp)
  constructor
  · show (PackedFloat.minSubnormalNumber ep sp false).toExtRat ≤ ExtRat.Number R
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfin]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]; exact hge
  · intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number R := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']; exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso; rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'; simp at hy'
    | infCase sign =>
      cases sign
      case false => exfalso; rw [PackedFloat.toExtRat'_getInfinity hsp] at hy'; simp at hy'
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp)
          (by simp [hmsign]) (by simp [hsp]) hnan
    | zeroCase sign =>
      cases sign
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp [PackedFloat.sign_getZero])
          (by simp [hmsign]) (by simp [hsp] <;> grind) hnan
      case false =>
        apply PackedFloat.le_of_toExtRat'_le_toExtRat' hep0 hsp
          (PackedFloat.getZero ep sp false) (PackedFloat.minSubnormalNumber ep sp false)
          (by simp [hsp] <;> grind) hnan
        · intro h1 h2 h3
          simp [PackedFloat.sign_getZero] at h3
        · intro h1 _ _
          exfalso
          have h2 := PackedFloat.not_isZero_of_isNormOrSubnorm hfin
          simp at h2; simp [h2] at h1
        · rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [hsp] <;> grind),
            PackedFloat.toExtRat'_eq_toRat_of hfin]
          simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]; exact hmnonneg
    | numCase n hn =>
      by_cases hsign : n.sign
      · exact PackedFloat.le_of_nonneg_of_neg _ _ hsign (by simp [hmsign])
          (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn) hnan
      · have hnsign : n.sign = false := by simpa using hsign
        have hnnan : ¬ n.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn
        have hnzero : ¬ n.isZero := by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hn
        have hnle : n.toRat ≤ R := by
          rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
          simpa only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] using hy'
        have hnlt : n.toRat < (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero.toRat := by
          rw [hsucc_eq]; grind
        by_cases hle : n ≤ PackedFloat.minSubnormalNumber ep sp false
        · exact hle
        · exfalso
          -- `¬ (n ≤ minSub)` ⟹ `minSub < n`, but `n < successor(minSub)` — nothing lies strictly between.
          have hmn : PackedFloat.minSubnormalNumber ep sp false < n :=
            PackedFloat.lt_of_not_le n _ (by grind) hle
          have hnsucc_le : n ≤ (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero := by
            apply PackedFloat.le_of_toExtRat'_le_toExtRat'_of_nonneg_of_nonneg hep0 hsp n
              ((PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero) hnnan hsucnan
              hnzero hsuczero hnsign hsucsign
            rw [PackedFloat.toExtRat'_eq_toRat_of hn, PackedFloat.toExtRat'_eq_toRat_of hsucfin]
            simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
            exact Rat.le_of_lt hnlt
          have hnsucc_ne : n ≠ (PackedFloat.minSubnormalNumber ep sp false).successorAwayFromZero := by
            intro hcon; rw [hcon] at hnlt; exact absurd hnlt (by grind)
          exact PackedFloat.elim_self_lt_lt_successor (by grind) hsp _ n hmsign hnsign hnan hnnan
            hLinf hmn ⟨hnsucc_le, hnsucc_ne⟩

/-- A significand with its MSB set has `toNat = 2^(su-1)` iff no lower bit is set. -/
theorem sig_toNat_eq_two_pow_iff_no_bit_below_msb {su : Nat} (sig : BitVec su) (hsu : 0 < su)
    (hmsb : sig.getLsbD (su - 1) = true) :
    sig.toNat = 2 ^ (su - 1) ↔ ¬ ∃ i, i < su - 1 ∧ sig.getLsbD i = true := by
  have hgl : ∀ j, sig.toNat.testBit j = sig.getLsbD j := fun j => by rw [BitVec.getLsbD]
  constructor
  · intro h
    rintro ⟨i, hi, hbit⟩
    have hf : sig.getLsbD i = false := by rw [← hgl, h, Nat.testBit_two_pow]; simp; omega
    rw [hf] at hbit; simp at hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow, hgl]
    by_cases hi : i = su - 1
    · subst hi; rw [hmsb]; simp
    · by_cases hib : i < su - 1
      · have hf : sig.getLsbD i = false := Bool.eq_false_iff.mpr (fun hc => h ⟨i, hib, hc⟩)
        rw [hf]; simp; omega
      · rw [BitVec.getLsbD_of_ge sig i (by omega)]; simp; omega

/-- **At the boundary, `needsRounding_{sp+1} = sticky_sp`.** (The `off ≤ sp` sticky theory
`needsRounding_succ_eq_blastExtractStickyBit` does not apply at `off = sp+1`; here both sides equal
"some significand bit strictly below the MSB is set": at precision `sp+1` the guard is bit `su-2` and
the sticky ranges over bits `< su-2`, together exactly the bits `< su-1`.) -/
theorem needsRounding_succ_eq_blastExtractStickyBit_of_off_eq_succ {eu su ep sp : Nat}
    (hep : 1 < ep) (hsp : 0 < sp) (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1) :
    x.needsRounding ep (sp + 1) = x.blastExtractStickyBit ep sp := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  rw [UnpackedFloat.needsRounding,
    UnpackedFloat.extractGuardBit_eq_getLsbD (sp := sp + 1) hep (by omega) heu (by omega) x
      hdiffLower hdiffUpper (by omega),
    UnpackedFloat.blastExtractStickyBit_eq_decide (sp := sp + 1) hep (by omega) heu (by omega) x
      hdiffLower hdiffUpper (by omega)]
  rw [hoff]
  rw [Bool.eq_iff_iff]
  rw [Bool.or_eq_true, decide_eq_true_eq]
  rw [show su - (sp + 1 + 2) + (sp + 1) = su - 2 by omega]
  rw [blastExtractStickyBit_eq_true_of_off_eq_succ_iff hep hsp heu_sp (by omega) x
    hdiffLower hdiffUpper hoff]
  constructor
  · rintro (hg | ⟨i, hi, hb⟩)
    · exact ⟨su - 2, by omega, hg⟩
    · exact ⟨i, by omega, hb⟩
  · rintro ⟨i, hi, hb⟩
    by_cases hisu2 : i = su - 2
    · exact Or.inl (by rw [← hisu2]; exact hb)
    · exact Or.inr ⟨i, by omega, hb⟩

/-- At the underflow boundary (`off = sp+1`), the guard bit is the set MSB, so the negative
`blastIsLowerHalf = (guard == sticky) = sticky`. Sign-independent exponent facts (derived for `x`
directly, since `boundary_facts` itself needs `sign = false`). -/
theorem blastIsLowerHalf_eq_blastExtractStickyBit_of_sign_true_boundary {eu su ep sp : Nat}
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsignt : x.sign = true) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    x.blastIsLowerHalf ep sp = x.blastExtractStickyBit ep sp := by
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
  have hguard := blastExtractGuardBit_eq_true_of_off_eq_succ_of_msb (by grind) hs heu hsu x
    hdiffLower hdiffUpper hoff hmsb
  simp [UnpackedFloat.blastIsLowerHalf, UnpackedFloat.blastIsLowerHalfNeg, hxsignt, hguard]

/-- **Negative underflow boundary, wide.** `lowerHalf` of the tiny negative value reduces (via
`lower = -upper(-·)`) to `upper_sp(|x|) = upper_{sp+1}(|x|)`. Here `upper_sp(|x|) = minSub_sp = 2^(ex+1)`
while `upper_{sp+1}(|x|) = lower_{sp+1} + (needsRounding_{sp+1} ? ulp : 0) = 2^ex·(1 + sticky)` (lower pin
+ foundation + `needsRounding_{sp+1} = sticky`), so the two agree iff `sticky`. -/
theorem smtLibLowerHalf_iff_blastExtractStickyBit_of_sign_true_boundary
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
      ↔ x.blastExtractStickyBit ep sp = true := by
  have he' : 0 < ep := by grind
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hsu_sp : sp + 2 ≤ su := by omega
  -- `-x` facts (sign flips, ex/sig unchanged; flags are sign-independent).
  have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hxsignt]
  have hnmsb : (-x).sig.msb = true := by rw [UnpackedFloat.neg_sig]; exact hmsb
  have hnex : (-x).ex.toInt = x.ex.toInt := by rw [UnpackedFloat.neg_ex]
  have hnunder : (-x).blastIsUnderflowNonneg ep sp = true := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp, hnex,
      ← UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp]; exact hunder
  have hnearly : (-x).blastIsEarlyUnderflowNonneg ep sp = false := by
    rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu_sp, hnex,
      ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu_sp]; exact hnotearlyunder
  obtain ⟨hoff', hdL', hdU', hxpos', hlt'⟩ :=
    boundary_facts he hs heu_sp hsu_sp (-x) hnsign hnmsb hnunder hnearly
  -- the exponent at the boundary, and the two subnormal magnitudes.
  have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hexval : x.ex.toInt = minNormalExp ep - ((sp : Int) + 1) := by
    have h1 : x.ex.toInt < minSubnormalExp ep sp := by
      rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp] at hunder
      simpa using hunder
    have h2 : minSubnormalExp ep sp - 1 ≤ x.ex.toInt := by
      rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu_sp] at hnotearlyunder
      simpa only [decide_eq_false_iff_not, Int.not_lt] using hnotearlyunder
    grind
  have hminSub1 : (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat = (2 : Rat) ^ (x.ex.toInt) := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep (sp + 1) (by grind) (by omega), hexval]
    congr 1
  have hminSub : (PackedFloat.minSubnormalNumber ep sp false).toRat = (2 : Rat) ^ (x.ex.toInt + 1) := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hs, hexval]
    congr 1; push_cast; omega
  have hmaxN : minSubnormalExp ep sp ≤ maxNormalExp ep := by
    have hb := bias_pos_of_one_lt ep (by grind)
    rw [minSubnormalExp_eq_neg_bias_minus_s_minus_one (by grind)]; simp only [maxNormalExp]; omega
  have hexlt : x.ex.toInt < minSubnormalExp ep sp := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp] at hunder
    simpa using hunder
  -- `-x` is in range at `sp+1`.
  have hnunder1 : (-x).blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hms1 : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    rw [hnex]; grind
  have hnover1 : (-x).blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    rw [hnex]; simp only [decide_eq_false_iff_not, Int.not_lt]
    grind
  have hnnorm : (-x).normalize = -x := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
  -- `lower_{sp+1}(|x|) = minSub_{sp+1}` (the subnormal floor of a value in `[minSub_{sp+1}, 2·minSub_{sp+1})`).
  have hge1 : (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat ≤ (-x).toRat' := by
    rw [hminSub1]
    have h := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false (-x) (by grind) hnsign hnmsb
    rw [hnex] at h; exact h
  have h2ex : (2 : Rat) ^ (x.ex.toInt + 1) = 2 * 2 ^ (x.ex.toInt) := by
    rw [Rat.zpow_add (by decide) x.ex.toInt 1, Rat.zpow_one, Rat.mul_comm]
  have hlt1 : (-x).toRat' < 2 * (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat := by
    rw [hminSub1, ← h2ex, ← hminSub]; exact hlt'
  have hlowpin : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1))
      = PackedFloat.minSubnormalNumber ep (sp + 1) false :=
    lower_Number_eq_minSubnormalNumber_of_ge_of_lt_succ he (by omega) (-x).toRat' hge1 hlt1
  have hmaxL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false := by
    rw [hlowpin]; intro hc
    have h1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).isNorm :=
      PackedFloat.isNorm_maxNormalNumber_of_lt_e ep (sp + 1) (by grind) false
    rw [← hc] at h1; simp [PackedFloat.isNorm, PackedFloat.minSubnormalNumber, BitVec.ofInt] at h1
  -- `upper_sp(|x|) = minSub_sp`.
  have hupsp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.minSubnormalNumber ep sp false := by
    refine eq_of_IsLawfulUpper_of_IsLawfulUpper ep sp (ExtRat.Number (-x).toRat') _ _ ?_ ?_ ?_ ?_
    · simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs (ExtRat.Number (-x).toRat') (by simp)
    · simpa using PackedFloat.not_isNaN_minSubnormalNumber ep sp false (by grind) hs
    · exact isLawfulUpper_smtLibUpper ep sp (by grind) hs (ExtRat.Number (-x).toRat')
    · exact isLawfulUpper_minSubnormalNumber_of_pos_of_le (by grind) hs (-x).toRat' hxpos'
        (Rat.le_of_lt hlt')
  have hfinU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
    rw [hupsp]; exact PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hs
  have hfinU1 := isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal
    he (by omega) heu (by omega) (-x) hnsign hnnorm hnunder1 hnover1 hmaxL1
  -- lowerHalf reduces to `upper_sp(|x|) = upper_{sp+1}(|x|)`.
  have hneg_val : (-(ExtRat.Number x.toRat')) = ExtRat.Number (-x).toRat' :=
    (congrArg ExtRat.Number (UnpackedFloat.toRat'_neg x)).symm
  have hlow : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = -(SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep sp) := by
    rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp he' hs (ExtRat.Number x.toRat') (by simp), hneg_val]
  have hlow1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
      = -(SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1)) := by
    rw [smtLibLower_eq_neg_smtLibUpper_neg ep (sp + 1) he' (by omega) (ExtRat.Number x.toRat') (by simp),
      hneg_val]
  have hlowerhalf :
      (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
        ↔ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep sp).toRat
            = (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1)).toRat := by
    rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hlow, hlow1,
      SmtLibSemantics.instExtendedRat.smtLibEq]
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_eq_toRat_of (by rw [PackedFloat.isNormOrNonzeroSubnorm_neg]; exact hfinU),
      PackedFloat.toExtRat'_eq_toRat_of (by rw [PackedFloat.isNormOrNonzeroSubnorm_neg]; exact hfinU1),
      PackedFloat.toRat_neg, PackedFloat.toRat_neg]
    simp only [ExtRat.Number.injEq]; constructor <;> intro h <;> grind
  rw [hlowerhalf, hupsp, hminSub,
    smtLibUpper_toRat_eq_lower_add_ulp (sp := sp + 1) he (by omega) heu (by omega) (-x) hnsign hnnorm
      hnunder1 hnover1 hmaxL1,
    needsRounding_succ_eq_blastExtractStickyBit_of_off_eq_succ (by grind) hs heu (by omega) (-x)
      hdL' hdU' hoff',
    show (-x).blastExtractStickyBit ep sp = x.blastExtractStickyBit ep sp from rfl,
    smtLibLower_lower_toRatExp_eq (sp := sp + 1) (by grind) (by omega) heu (by omega) (-x) hnsign hnnorm
      hnunder1 hnover1, hoff', hnex,
    hlowpin, hminSub1, h2ex]
  -- `2·2^ex = 2^ex + (sticky ? ulp : 0)` ⟺ `sticky`, with `ulp = 2^(-(sp+1))·2^(ex+(sp+1)) = 2^ex`.
  have hulp : (2 : Rat) ^ (-(((sp + 1 : Nat) : Int))) * 2 ^ (x.ex.toInt + (((sp + 1 : Nat) : Int)))
      = 2 ^ (x.ex.toInt) := by
    rw [← Rat.zpow_add (by decide)]; congr 1; push_cast; omega
  have hpos : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
  rw [hulp]
  cases hst : x.blastExtractStickyBit ep sp <;> simp only [hst, if_true, if_false, Bool.false_eq_true] <;>
    constructor <;> intro h <;> grind

/-- Widening preserves the sticky bit at the boundary (`off = sp+1`), where the general `off ≤ sp`
preservation does not apply. Both sides are "some significand bit strictly below the MSB is set". -/
theorem blastExtractStickyBit_widen_boundary {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hep : 1 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (heu' : exponentWidth ep sp ≤ eu') (hsu' : sp + 2 ≤ su')
    (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hoff : (minNormalExp ep - x.ex.toInt).toNat = sp + 1) :
    (x.widen eu' su').blastExtractStickyBit ep sp = x.blastExtractStickyBit ep sp := by
  have hge : 1 ≤ eu := by have := @zero_lt_exponentWidth ep sp; omega
  obtain ⟨hbl, hbu⟩ := widen_diff_bounds hwideu hge (minNormalExp ep - x.ex.toInt) hdiffLower hdiffUpper
  have hexw : (x.widen eu' su').ex.toInt = x.ex.toInt := ex_toInt_widen x eu' su' hwideu
  rw [Bool.eq_iff_iff,
    blastExtractStickyBit_eq_true_of_off_eq_succ_iff hep hsp heu' hsu' (x.widen eu' su')
      (by rw [hexw]; exact hbl) (by rw [hexw]; exact hbu) (by rw [hexw]; exact hoff),
    blastExtractStickyBit_eq_true_of_off_eq_succ_iff hep hsp heu hsu x hdiffLower hdiffUpper hoff]
  constructor
  · rintro ⟨i, hi, hb⟩
    rw [getLsbD_sig_widen x eu' su'] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hge', hlt'⟩, hb⟩ := hb
    exact ⟨i - (su' - su), by omega, hb⟩
  · rintro ⟨j, hj, hb⟩
    refine ⟨j + (su' - su), by omega, ?_⟩
    rw [getLsbD_sig_widen x eu' su']
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨by omega, by omega⟩, by rw [show j + (su' - su) - (su' - su) = j by omega]; exact hb⟩

/-- **Negative underflow boundary, narrow.** `blastIsLowerHalf = sticky` (circuit) and `lowerHalf = sticky`
(via the wide leaf on the widening, since `lowerHalf` and `sticky` are both widening-invariant here). -/
theorem blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_true_boundary_narrow
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (eu' su' : Nat) (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (heu' : exponentWidth ep (sp + 1) ≤ eu') (hsu' : sp + 3 ≤ su')
    (x : UnpackedFloat eu su) (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have hsupos : 0 < su := by omega
  have heu_succ : exponentWidth ep sp ≤ eu' := Nat.le_trans exponentWidth_le_succ heu'
  -- diff facts for `x` at the boundary.
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
  -- widened-float boundary flags.
  have hsignt' : (x.widen eu' su').sign = true := by rw [sign_widen]; exact hxsignt
  have hmsb' : (x.widen eu' su').sig.msb = true := by rw [sig_msb_widen x eu' su' hwidesu hsupos]; exact hmsb
  have hunder' : (x.widen eu' su').blastIsUnderflowNonneg ep sp = true := by
    rw [blastIsUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hunder
  have hnotearly' : (x.widen eu' su').blastIsEarlyUnderflowNonneg ep sp = false := by
    rw [blastIsEarlyUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotearlyunder
  rw [blastIsLowerHalf_eq_blastExtractStickyBit_of_sign_true_boundary he hs heu hsu x hxsignt hmsb
        hunder hnotearlyunder,
    ← toRat'_widen x eu' su' hwideu hwidesu hsupos,
    smtLibLowerHalf_iff_blastExtractStickyBit_of_sign_true_boundary he hs heu' hsu' (x.widen eu' su')
      hsignt' (normalize_widen x eu' su' hwidesu hsupos hmsb) hmsb' hunder' hnotearly',
    blastExtractStickyBit_widen_boundary x eu' su' (by grind) hs heu hsu heu_succ (by omega)
      hwideu hwidesu hdiffLower hdiffUpper hoff]

/-- For a representable value, the SMT-LIB `lowerHalf` is vacuously true: the lower approximants at
widths `sp` and `sp+1` both equal the value itself (`smtLibLower_eq_self` + `exists_widen`), so their
embeddings agree. -/
theorem smtLibLowerHalf_of_representable {ep sp : Nat} (he : 0 < ep) (hs : 0 < sp)
    (b : PackedFloat ep sp) (hb : b.isNormOrNonzeroSubnorm) :
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf
      (ExtRat.Number b.toRat) := by
  rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
  obtain ⟨b', hb', hbval⟩ := PackedFloat.exists_widen he hs b hb
  have hbnan : ¬ b.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hb
  have hb'nan : ¬ b'.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hb'
  have hbzero : ¬ b.isZero := by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hb
  have hb'zero : ¬ b'.isZero := by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hb'
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq]
  rw [smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN he hs b (ExtRat.Number b.toRat) hbnan hbzero
        (by rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hb]),
      show ExtRat.Number b.toRat = ExtRat.Number b'.toRat from by rw [hbval],
      smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN he (by grind) b' (ExtRat.Number b'.toRat) hb'nan
        hb'zero (by rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hb'])]
  simp only [SmtLibSemantics.instExtendedRat.smtLibEq, PackedFloat.toExtRat_eq_toExtRat']
  rw [PackedFloat.toExtRat'_eq_toRat_of hb, PackedFloat.toExtRat'_eq_toRat_of hb', hbval]

/-! ### `lower = maxNormal` overflow edge (negative)

At this edge `x.toRat' = -|x|` with `|x| ≥ maxNormal_sp`, so `ex = maxNormalExp` and the SMT lower
approximant of `x.toRat'` is `-∞` once `|x|` strictly exceeds `maxNormal`. The three value-ranges below
each satisfy `blastIsLowerHalf = lowerHalf` (verified by hand): the circuit's `guard == sticky` matches
because at this binade `guard = 1 ⟺ |x| ≥ maxNormal_{sp+1}` and `sticky` flags any lower set bit. The
ranges are stated as `axiom`s — the only remaining gap in the `blastIsLowerHalf` bitblasting proof — because
formalizing the `guard/sticky ↔ value` bridge requires new bit-level↔value machinery with no existing support.

- Range 1 (`|x| = maxNormal_sp`, representable): both `lower_sp`, `lower_{sp+1}` are `-maxNormal_sp`; `lowerHalf
  = true`, and `guard = sticky = 0` so `guard == sticky = true`.
- Range 2 (`maxNormal_sp < |x| ≤ maxNormal_{sp+1}`): `lower_sp = -∞` but `lower_{sp+1}` finite, so `lowerHalf
  = false`; `guard = 0`, `sticky = 1`, so `guard == sticky = false`.
- Range 3 (`maxNormal_{sp+1} < |x|`): both lowers are `-∞`; `lowerHalf = true`, and `guard = sticky = 1`. -/

/-- **Range 1: `|x| = maxNormal_sp` (representable).** `x.toRat'` is exactly `maxNormal_sp(sign=true)`, so
`lowerHalf` is vacuously true; and `needsRounding = false` (the round-toward-zero value is the lower
approximant `= maxNormal = |x|`), so `blastIsLowerHalfNeg = (guard == sticky) = true`. -/
theorem blastIsLowerHalf_edge_eq_maxNormal {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false)
    (heq : (-x).toRat' = (PackedFloat.maxNormalNumber ep sp false).toRat) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have he' : 0 < ep := by grind
  -- `-x` facts (sign flips, ex/sig unchanged).
  have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hxsignt]
  have hnnorm : (-x).normalize = -x := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
  have hnunder : (-x).blastIsUnderflowNonneg ep sp = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu, UnpackedFloat.neg_ex,
      ← UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu]; exact hnotunder
  have hnover : (-x).blastIsEarlyOverflowNonneg ep sp = false := by
    rw [blastIsEarlyOverflowNonneg_neg]; exact hnotover
  -- LHS: `needsRounding = false`, hence `blastIsLowerHalfNeg = (guard == sticky) = true`.
  have hpin := smtLibLower_lower_toRat_eq_blastRoundTowardZero (by grind) hs heu hsu (-x) hnsign hnnorm
    hnunder hnover
  rw [hmaxL] at hpin
  have hround : ((-x).blastRoundTowardZero ep sp).toRat' = (-x).toRat' := by rw [← hpin, heq]
  have hxneed : x.needsRounding ep sp = false :=
    (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding (by grind) hs heu hsu (-x)
      hnsign hnunder hnover).mp hround
  have hLHS : x.blastIsLowerHalf ep sp = true := by
    have hgst : x.blastExtractGuardBit ep sp = false ∧ x.blastExtractStickyBit ep sp = false := by
      have h := hxneed; unfold UnpackedFloat.needsRounding at h
      simpa [Bool.or_eq_false_iff] using h
    obtain ⟨hg, hst⟩ := hgst
    simp [UnpackedFloat.blastIsLowerHalf, UnpackedFloat.blastIsLowerHalfNeg, hxsignt, hg, hst]
  -- RHS: `lowerHalf` of the representable value `maxNormal_sp(true)`.
  have hval : x.toRat' = (PackedFloat.maxNormalNumber ep sp true).toRat := by
    have h1 : -x.toRat' = (PackedFloat.maxNormalNumber ep sp false).toRat := by
      rw [← UnpackedFloat.toRat'_neg]; exact heq
    rw [show (PackedFloat.maxNormalNumber ep sp true).toRat
        = -(PackedFloat.maxNormalNumber ep sp false).toRat from by
      rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]]
    grind
  have hRHS : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
    rw [hval]
    exact smtLibLowerHalf_of_representable he' hs (PackedFloat.maxNormalNumber ep sp true)
      (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false)
  exact iff_of_true hLHS hRHS

/-- **Lemma A.** For `R < -maxNormal_sp` (a negative value whose magnitude exceeds `maxNormal_sp`), the
SMT-LIB lower approximant at precision `sp` is `-∞` (`getInfinity true`). -/
theorem smtLibLower_eq_neg_getInfinity_of_lt {ep sp : Nat} (he : 1 < ep) (hs : 0 < sp) (R : Rat)
    (hR : R < (PackedFloat.maxNormalNumber ep sp true).toRat) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number R) : PackedFloat ep sp)
      = PackedFloat.getInfinity ep sp true := by
  rw [smtLibLower_eq_lower ep sp (by grind) hs (ExtRat.Number R) (by simp)]
  exact lower_Number_eq_getInfinity_of_maxNormalNumber_lt (by grind) hs R hR

/-- The width-`(sp+1)` representative of `maxNormal_sp`: append a low `0` bit to the all-ones
significand (the exponent is unchanged). It has the same value as `maxNormal_sp`, and its
`successorAwayFromZero` is `maxNormal_{sp+1}` — i.e. `maxNormal_sp` is the immediate predecessor of
`maxNormal_{sp+1}` at precision `sp+1`. -/
private def maxNormalWiden (ep sp : Nat) : PackedFloat ep (sp + 1) :=
  { sign := false, ex := BitVec.allOnes ep - 1#ep, sig := (BitVec.allOnes sp).concat false }

private theorem isNormOrNonzeroSubnorm_maxNormalWiden {ep sp : Nat} (he : 1 < ep) :
    (maxNormalWiden ep sp).isNormOrNonzeroSubnorm := by
  have hnormM : (PackedFloat.maxNormalNumber ep sp false).isNorm = true :=
    PackedFloat.isNorm_maxNormalNumber_of_lt_e ep sp he false
  simp only [PackedFloat.isNorm, PackedFloat.ex_maxNormalNumber, bne_iff_ne, Bool.and_eq_true,
    ne_eq] at hnormM
  simp only [maxNormalWiden, PackedFloat.isNormOrNonzeroSubnorm, bne_iff_ne, ne_eq, Bool.and_eq_true,
    Bool.or_eq_true]
  grind

private theorem toRat_maxNormalWiden (ep sp : Nat) :
    (maxNormalWiden ep sp).toRat = (PackedFloat.maxNormalNumber ep sp false).toRat := by
  have hsig : ((BitVec.allOnes sp).concat false).toNat = 2 * (BitVec.allOnes sp).toNat := by
    rw [BitVec.toNat_concat]; grind
  have hhalf : (↑(2 * (BitVec.allOnes sp).toNat) : Rat) / 2 ^ (sp + 1)
      = ↑(BitVec.allOnes sp).toNat / 2 ^ sp := by
    have hpow : (2 : Rat) ^ (sp + 1) = 2 * 2 ^ sp := by
      have h : ((2 ^ (sp + 1) : Nat) : Rat) = ((2 * 2 ^ sp : Nat) : Rat) := by rw [Nat.pow_succ]; grind
      rw [Rat.natCast_pow, Rat.natCast_mul, Rat.natCast_pow] at h; simpa using h
    rw [hpow]; push_cast; grind
  simp only [maxNormalWiden, PackedFloat.maxNormalNumber, PackedFloat.toRat, PackedFloat.toRatSig,
    PackedFloat.toRatExp, PackedFloat.isNorm, hsig, hhalf]

private theorem successorAwayFromZero_maxNormalWiden {ep sp : Nat} (he : 1 < ep) :
    (maxNormalWiden ep sp).successorAwayFromZero = PackedFloat.maxNormalNumber ep (sp + 1) false := by
  have hnormM : (PackedFloat.maxNormalNumber ep sp false).isNorm = true :=
    PackedFloat.isNorm_maxNormalNumber_of_lt_e ep sp he false
  simp only [PackedFloat.isNorm, PackedFloat.ex_maxNormalNumber, bne_iff_ne, Bool.and_eq_true,
    ne_eq] at hnormM
  obtain ⟨hexallones, hexzero⟩ := hnormM
  have hnan : (maxNormalWiden ep sp).isNaN = false := by
    simp only [maxNormalWiden, PackedFloat.isNaN, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    grind
  have hinf : (maxNormalWiden ep sp).isInfinite = false := by
    simp only [maxNormalWiden, PackedFloat.isInfinite, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq]
    grind
  have hsigne : (maxNormalWiden ep sp).sig ≠ BitVec.allOnes (sp + 1) := by
    simp only [maxNormalWiden]
    intro hc
    have hcc := congrArg BitVec.toNat hc
    rw [BitVec.toNat_concat, BitVec.toNat_allOnes, BitVec.toNat_allOnes] at hcc
    have hp : 2 ^ (sp + 1) = 2 * 2 ^ sp := by rw [Nat.pow_succ]; grind
    have hpos := Nat.two_pow_pos sp
    grind
  have hsigsucc : (maxNormalWiden ep sp).sig + 1#(sp + 1) = BitVec.allOnes (sp + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [maxNormalWiden, BitVec.toNat_add, BitVec.toNat_concat, BitVec.toNat_allOnes,
      BitVec.toNat_ofNat]
    have hp : 2 ^ (sp + 1) = 2 * 2 ^ sp := by rw [Nat.pow_succ]; grind
    have hpos := Nat.two_pow_pos sp
    grind
  unfold PackedFloat.successorAwayFromZero
  simp only [hnan, hinf, Bool.false_eq_true, if_false]
  rw [if_pos hsigne]
  apply PackedFloat.ext
  · rw [PackedFloat.sign_sucessorAwayFromZero_sigSucc]; simp [maxNormalWiden, PackedFloat.maxNormalNumber]
  · rw [PackedFloat.ex_sucessorAwayFromZero_sigSucc]; simp [maxNormalWiden, PackedFloat.maxNormalNumber]
  · rw [PackedFloat.sig_sucessorAwayFromZero_sigSucc, hsigsucc]; simp [PackedFloat.maxNormalNumber]

private theorem not_isNaN_maxNormalWiden {ep sp : Nat} (he : 1 < ep) :
    ¬ (maxNormalWiden ep sp).isNaN := by
  simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm (isNormOrNonzeroSubnorm_maxNormalWiden he)

private theorem not_isInfinite_maxNormalWiden {ep sp : Nat} (he : 1 < ep) :
    ¬ (maxNormalWiden ep sp).isInfinite := by
  simpa using
    PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm (isNormOrNonzeroSubnorm_maxNormalWiden he)

private theorem maxNormalWiden_ne_maxNormalNumber {ep sp : Nat} :
    maxNormalWiden ep sp ≠ PackedFloat.maxNormalNumber ep (sp + 1) false := by
  intro hc
  have hsigeq := congrArg PackedFloat.sig hc
  simp only [maxNormalWiden, PackedFloat.sig_maxNormalNumber] at hsigeq
  have hcc := congrArg BitVec.toNat hsigeq
  rw [BitVec.toNat_concat, BitVec.toNat_allOnes, BitVec.toNat_allOnes] at hcc
  have hp : 2 ^ (sp + 1) = 2 * 2 ^ sp := by rw [Nat.pow_succ]; grind
  have hpos := Nat.two_pow_pos sp
  grind

/-- `maxNormalWiden.toRat + 1 ulp = maxNormal_{sp+1}.toRat` (the successor value). -/
private theorem toRat_add_ulp_maxNormalWiden {ep sp : Nat} (he : 1 < ep) :
    (maxNormalWiden ep sp).toRat
      + (2 : Rat) ^ (-((sp + 1 : Nat) : Int)) * 2 ^ ((maxNormalWiden ep sp).toRatExp)
      = (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat := by
  have h := PackedFloat.toRat_successorAwayFromZero_eq (maxNormalWiden ep sp)
    (not_isNaN_maxNormalWiden he) (not_isInfinite_maxNormalWiden he)
    (by rw [show (maxNormalWiden ep sp).sign = false from rfl]; exact maxNormalWiden_ne_maxNormalNumber)
    he (by grind)
  rw [successorAwayFromZero_maxNormalWiden he] at h
  rw [show (maxNormalWiden ep sp).sign = false from rfl] at h
  simp only [Bool.toSign, Bool.false_eq_true, if_false] at h
  push_cast at h ⊢
  grind

/-- **Positive lower gap.** For `S ∈ [maxNormal_sp, maxNormal_{sp+1})`, the greatest float `≤ S` at
precision `sp+1` is `maxNormalWiden` (value `maxNormal_sp`): nothing representable lies strictly between
`maxNormal_sp` and `maxNormal_{sp+1}`. -/
private theorem smtLibLower_succ_eq_maxNormalWiden_of_ge_of_lt {ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (S : Rat)
    (hge : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ S)
    (hlt : S < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number S) : PackedFloat ep (sp + 1))
      = maxNormalWiden ep sp := by
  rw [smtLibLower_eq_lower ep (sp + 1) (by grind) (by grind) (ExtRat.Number S) (by simp)]
  symm
  apply eq_lower_of_IsLawfulLower ep (sp + 1) (by grind) (by grind) _ _ (by simp)
  apply PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp (by grind) (by grind) S
    (maxNormalWiden ep sp) rfl (isNormOrNonzeroSubnorm_maxNormalWiden he)
  · rw [toRat_maxNormalWiden]; exact hge
  · rw [toRat_add_ulp_maxNormalWiden he]; exact hlt

/-- **Positive upper gap.** For `S ∈ (maxNormal_sp, maxNormal_{sp+1}]`, the least float `≥ S` at
precision `sp+1` is `maxNormal_{sp+1}` (nothing representable lies strictly between `maxNormal_sp` and
`maxNormal_{sp+1}`). -/
private theorem smtLibUpper_succ_eq_maxNormalNumber_of_lt_of_le {ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (S : Rat)
    (hgt : (PackedFloat.maxNormalNumber ep sp false).toRat < S)
    (hle : S ≤ (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number S) : PackedFloat ep (sp + 1))
      = PackedFloat.maxNormalNumber ep (sp + 1) false := by
  have hSpos : 0 < S := by have := PackedFloat.toRat_maxNormalNumber_nonneg (ep := ep) (sp := sp) he; grind
  refine eq_of_IsLawfulUpper_of_IsLawfulUpper ep (sp + 1) (ExtRat.Number S) _ _ ?_ ?_ ?_ ?_
  · simpa using not_isNaN_upper_of_ne_NaN ep (sp + 1) (by grind) (by grind) (ExtRat.Number S) (by simp)
  · simpa using PackedFloat.not_isNaN_maxNormalNumber ep (sp + 1) false (by grind)
  · exact isLawfulUpper_smtLibUpper ep (sp + 1) (by grind) (by grind) (ExtRat.Number S)
  · refine PackedFloat.isLawfulUpper_of_le_toRat_of_no_float_between (by grind) (by grind) S
      (PackedFloat.maxNormalNumber ep (sp + 1) false) rfl
      (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false) hSpos hle ?_
    intro y hysign hyfin hylt
    apply Classical.byContradiction
    intro hcon
    have hSley : S ≤ y.toRat := by grind
    have hfinmw : (maxNormalWiden ep sp).isNormOrNonzeroSubnorm := isNormOrNonzeroSubnorm_maxNormalWiden he
    have hmwlt : maxNormalWiden ep sp < y :=
      (lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm (by grind) (by grind) (maxNormalWiden ep sp) y
        hfinmw hyfin).mpr (by rw [toRat_maxNormalWiden]; grind)
    have hyltsucc : y < (maxNormalWiden ep sp).successorAwayFromZero := by
      rw [successorAwayFromZero_maxNormalWiden he]
      exact (lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm (by grind) (by grind) y
        (PackedFloat.maxNormalNumber ep (sp + 1) false) hyfin
        (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false)).mpr hylt
    exact PackedFloat.elim_self_lt_lt_successor (by grind) (by grind) (maxNormalWiden ep sp) y
      rfl hysign (not_isNaN_maxNormalWiden he) (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hyfin)
      (not_isInfinite_maxNormalWiden he) hmwlt hyltsucc

/-- **Lemma B.** For `R ∈ [-maxNormal_{sp+1}, -maxNormal_sp)`, the SMT-LIB lower approximant at precision
`sp+1` is `-maxNormal_{sp+1}` (`maxNormalNumber true`): `maxNormal_sp` is the immediate predecessor of
`maxNormal_{sp+1}` at precision `sp+1`, so nothing representable lies strictly between them. -/
theorem smtLibLower_succ_eq_maxNormalNumber_true_of_ge_of_lt {ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (R : Rat)
    (hge : (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat ≤ R)
    (hlt : R < (PackedFloat.maxNormalNumber ep sp true).toRat) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number R) : PackedFloat ep (sp + 1))
      = PackedFloat.maxNormalNumber ep (sp + 1) true := by
  have he' : 0 < ep := by grind
  have hmaxT : ∀ q : Nat, (PackedFloat.maxNormalNumber ep q true).toRat
      = -(PackedFloat.maxNormalNumber ep q false).toRat := fun q => by
    rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
  rw [smtLibLower_eq_neg_smtLibUpper_neg ep (sp + 1) he' (by grind) (ExtRat.Number R) (by simp),
    show (-(ExtRat.Number R)) = ExtRat.Number (-R) from rfl,
    smtLibUpper_succ_eq_maxNormalNumber_of_lt_of_le (by grind) hs (-R)
      (by rw [hmaxT] at hlt; grind) (by rw [hmaxT] at hge; grind),
    ← PackedFloat.neg_maxNormalNumber_false']

/-- **Blast side of the overflow edge (wide).** For a wide negative `x` whose magnitude `|x| = (-x).toRat'`
exceeds `maxNormal_sp` (and `lower_sp(|x|) = maxNormal_sp`), the circuit `blastIsLowerHalf = (guard ==
sticky)` is `true` exactly when `|x| > maxNormal_{sp+1}`. The guard bit fires iff `|x| ≥ maxNormal_{sp+1}`
(`roundTZ_sp = roundTZ_{sp+1}` only when no carry) and the sticky bit fires iff `|x| ≠ maxNormal_{sp+1}`
(`needsRounding_{sp+1}`, i.e. `roundTZ_{sp+1} ≠ |x|`); they agree (both `1`) only above `maxNormal_{sp+1}`. -/
private theorem blastIsLowerHalf_edge_eq_decide_wide {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su) (x : UnpackedFloat eu su)
    (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false)
    (hgt : (PackedFloat.maxNormalNumber ep sp false).toRat < (-x).toRat') :
    x.blastIsLowerHalf ep sp = decide ((PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < (-x).toRat') := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hsu_sp : sp + 2 ≤ su := by omega
  -- `-x` facts (sign flips, ex/sig unchanged; flags sign-independent).
  have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hxsignt]
  have hnnorm : (-x).normalize = -x := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
  have hnex : (-x).ex.toInt = x.ex.toInt := by rw [UnpackedFloat.neg_ex]
  have hnunder : (-x).blastIsUnderflowNonneg ep sp = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp, UnpackedFloat.neg_ex,
      ← UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp]; exact hnotunder
  have hnover : (-x).blastIsEarlyOverflowNonneg ep sp = false := by
    rw [blastIsEarlyOverflowNonneg_neg]; exact hnotover
  have hunderE : minSubnormalExp ep sp ≤ (-x).ex.toInt := by
    have h := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp (-x)
    rw [h] at hnunder; simpa using hnunder
  have hoverE : (-x).ex.toInt ≤ maxNormalExp ep := by
    have h := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp (-x)
    rw [h] at hnover; simpa using hnover
  have hnunder1 : (-x).blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hms1 : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    grind
  have hnover1 : (-x).blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]; grind
  obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu_sp (-x) hnunder hnover
  -- The circuit (`sign = true`) is `guard == sticky` (bits sign-independent).
  simp only [UnpackedFloat.blastIsLowerHalf, hxsignt, if_true, UnpackedFloat.blastIsLowerHalfNeg]
  rw [show x.blastExtractGuardBit ep sp = (-x).blastExtractGuardBit ep sp from rfl,
    show x.blastExtractStickyBit ep sp = (-x).blastExtractStickyBit ep sp from rfl]
  -- `roundTZ_sp(|x|) = maxNormal_sp`; `roundTZ_{sp+1}(|x|) = lower_{sp+1}(|x|)`.
  have hrtz_sp : ((-x).blastRoundTowardZero ep sp).toRat' = (PackedFloat.maxNormalNumber ep sp false).toRat := by
    rw [← smtLibLower_lower_toRat_eq_blastRoundTowardZero (by grind) hs heu_sp hsu_sp (-x) hnsign hnnorm
      hnunder hnover, hmaxL]
  have hrtz_sp1 : ((-x).blastRoundTowardZero ep (sp + 1)).toRat'
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1)).toRat :=
    (smtLibLower_lower_toRat_eq_blastRoundTowardZero (sp := sp + 1) (by grind) (by grind) heu (by omega)
      (-x) hnsign hnnorm hnunder1 hnover1).symm
  have hguardiff := UnpackedFloat.blastRoundTowardZero_toRat'_eq_succ_iff_not_guardBit (by grind) hs heu hsu
    (-x) hnsign hnunder hnover
  have hneediff := UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding (by grind)
    (by grind) heu (by omega) (-x) hnsign hnunder1 hnover1
  have hst := needsRounding_succ_eq_blastExtractStickyBit (by grind) hs heu hsu (-x) hdl hdu hnat
  by_cases hcase : (-x).toRat' < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat
  · -- `maxNormal_sp < |x| < maxNormal_{sp+1}`: `guard = 0`, `sticky = 1` ⇒ `false`.
    have hlow1 := smtLibLower_succ_eq_maxNormalWiden_of_ge_of_lt (by grind) hs (-x).toRat' (by grind) hcase
    have hguardF : (-x).blastExtractGuardBit ep sp = false :=
      hguardiff.mp (by rw [hrtz_sp, hrtz_sp1, hlow1, toRat_maxNormalWiden])
    have hstickyT : (-x).blastExtractStickyBit ep sp = true := by
      rw [← hst]
      have hroundval : ((-x).blastRoundTowardZero ep (sp + 1)).toRat'
          = (PackedFloat.maxNormalNumber ep sp false).toRat := by rw [hrtz_sp1, hlow1, toRat_maxNormalWiden]
      have hne : ((-x).blastRoundTowardZero ep (sp + 1)).toRat' ≠ (-x).toRat' := by rw [hroundval]; grind
      cases hnr : (-x).needsRounding ep (sp + 1)
      · exact absurd (hneediff.mpr hnr) hne
      · rfl
    rw [hguardF, hstickyT]
    exact (decide_eq_false (by grind)).symm
  · -- `|x| ≥ maxNormal_{sp+1}`: `guard = 1`; `sticky = (|x| ≠ maxNormal_{sp+1})`.
    have hcase' : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat ≤ (-x).toRat' := by grind
    have hlow1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep (sp + 1))
        = PackedFloat.maxNormalNumber ep (sp + 1) false := by
      rw [smtLibLower_eq_lower ep (sp + 1) (by grind) (by grind) _ (by simp)]
      exact lower_Number_eq_maxNormalNumber_of_toRat_le (by grind) (by grind) (by grind) (-x).toRat' hcase'
    have hmono := PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ he hs
    have hguardT : (-x).blastExtractGuardBit ep sp = true := by
      cases hg : (-x).blastExtractGuardBit ep sp
      · exfalso
        have heq := hguardiff.mpr hg
        rw [hrtz_sp, hrtz_sp1, hlow1] at heq
        grind
      · rfl
    by_cases hVeq : (-x).toRat' = (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat
    · have hstickyF : (-x).blastExtractStickyBit ep sp = false := by
        rw [← hst]; exact hneediff.mp (by rw [hrtz_sp1, hlow1, hVeq])
      rw [hguardT, hstickyF]
      exact (decide_eq_false (by grind)).symm
    · have hstickyT : (-x).blastExtractStickyBit ep sp = true := by
        rw [← hst]
        have hroundval : ((-x).blastRoundTowardZero ep (sp + 1)).toRat'
            = (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat := by rw [hrtz_sp1, hlow1]
        have hne : ((-x).blastRoundTowardZero ep (sp + 1)).toRat' ≠ (-x).toRat' := by rw [hroundval]; grind
        cases hnr : (-x).needsRounding ep (sp + 1)
        · exact absurd (hneediff.mpr hnr) hne
        · rfl
      rw [hguardT, hstickyT]
      exact (decide_eq_true (by grind)).symm

/-- **Blast side of the overflow edge (narrow).** Transfer of the wide blast lemma by widening to
`eu' = max eu (exponentWidth ep (sp+1))`, `su' = max su (sp+3)` (value and circuit are widen-invariant). -/
private theorem blastIsLowerHalf_edge_eq_decide {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false)
    (hgt : (PackedFloat.maxNormalNumber ep sp false).toRat < (-x).toRat') :
    x.blastIsLowerHalf ep sp = decide ((PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < (-x).toRat') := by
  have hsupos : 0 < su := by omega
  let eu' := max eu (exponentWidth ep (sp + 1))
  let su' := max su (sp + 3)
  have hwideu : eu ≤ eu' := Nat.le_max_left _ _
  have hwidesu : su ≤ su' := Nat.le_max_left _ _
  have heu' : exponentWidth ep (sp + 1) ≤ eu' := Nat.le_max_right _ _
  have hsu' : sp + 3 ≤ su' := Nat.le_max_right _ _
  have heu_succ : exponentWidth ep sp ≤ eu' := Nat.le_trans exponentWidth_le_succ heu'
  obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu x hnotunder hnotover
  have hvaleq : (-(x.widen eu' su')).toRat' = (-x).toRat' := by
    rw [UnpackedFloat.toRat'_neg, toRat'_widen x eu' su' hwideu hwidesu hsupos, ← UnpackedFloat.toRat'_neg]
  rw [← blastIsLowerHalf_widen x eu' su' (by grind) hs heu (by omega) heu_succ (by omega)
        hwideu hwidesu hdl hdu hnat, ← hvaleq]
  refine blastIsLowerHalf_edge_eq_decide_wide he hs heu' hsu' (x.widen eu' su')
    (by rw [sign_widen]; exact hxsignt)
    (normalize_widen x eu' su' hwidesu hsupos hmsb)
    (by rw [sig_msb_widen x eu' su' hwidesu hsupos]; exact hmsb)
    ?_ ?_ ?_ ?_
  · rw [blastIsUnderflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotunder
  · rw [blastIsEarlyOverflowNonneg_widen x eu' su' (by grind) hs heu heu_succ hwideu]; exact hnotover
  · rw [hvaleq]; exact hmaxL
  · rw [hvaleq]; exact hgt

/-- **Range 2: `maxNormal_sp < |x| ≤ maxNormal_{sp+1}`.** `lower_sp = -∞` (Lemma A) but `lower_{sp+1} =
-maxNormal_{sp+1}` (Lemma B), so `lowerHalf = false`; and `blastIsLowerHalf = false` (`guard == sticky`
with `guard = 1 ⟺ |x| = maxNormal_{sp+1}` and `sticky` flagging non-representability at `sp+1`). -/
theorem blastIsLowerHalf_edge_between_maxNormal {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false)
    (h1 : (PackedFloat.maxNormalNumber ep sp false).toRat < (-x).toRat')
    (h2 : (-x).toRat' ≤ (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have he' : 0 < ep := by grind
  -- `x.toRat' = -|x| ∈ [-maxNormal_{sp+1}, -maxNormal_sp)`.
  have hmaxT : ∀ q : Nat, (PackedFloat.maxNormalNumber ep q true).toRat
      = -(PackedFloat.maxNormalNumber ep q false).toRat := fun q => by
    rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
  have hneg : (-x).toRat' = -x.toRat' := UnpackedFloat.toRat'_neg x
  have hvlt : x.toRat' < (PackedFloat.maxNormalNumber ep sp true).toRat := by rw [hmaxT]; grind
  have hvge : (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat ≤ x.toRat' := by rw [hmaxT]; grind
  -- `lowerHalf = false` via Lemmas A and B.
  have hlowsp := smtLibLower_eq_neg_getInfinity_of_lt (by grind) hs x.toRat' hvlt
  have hlowsp1 := smtLibLower_succ_eq_maxNormalNumber_true_of_ge_of_lt he hs x.toRat' hvge hvlt
  have hfinmax : (PackedFloat.maxNormalNumber ep (sp + 1) true).isNormOrNonzeroSubnorm :=
    PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) true
  have hlowerhalf_false :
      ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
    rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hlowsp, hlowsp1,
      SmtLibSemantics.instExtendedRat.smtLibEq, PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_eq_toRat_of hfinmax]
    grind
  -- `blastIsLowerHalf = false` (`|x| ≤ maxNormal_{sp+1}`).
  have hblast_false : x.blastIsLowerHalf ep sp = false := by
    rw [blastIsLowerHalf_edge_eq_decide he hs heu hsu x hxsignt hxnorm hmsb hnotunder hnotover hmaxL h1]
    exact decide_eq_false (by grind)
  exact iff_of_false (by rw [hblast_false]; simp) hlowerhalf_false

/-- **Range 3: `maxNormal_{sp+1} < |x|`.** Both `lower_sp` and `lower_{sp+1}` are `-∞` (Lemma A at both
precisions, since `x.toRat' < -maxNormal_{sp+1} < -maxNormal_sp`), so `lowerHalf = true`; and
`blastIsLowerHalf = true` (`guard = sticky = 1`). -/
theorem blastIsLowerHalf_edge_above_maxNormal {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false)
    (h : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < (-x).toRat') :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have he' : 0 < ep := by grind
  have hneg : (-x).toRat' = -x.toRat' := UnpackedFloat.toRat'_neg x
  have hmaxT : ∀ q : Nat, (PackedFloat.maxNormalNumber ep q true).toRat
      = -(PackedFloat.maxNormalNumber ep q false).toRat := fun q => by
    rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
  -- `x.toRat' < -maxNormal_{sp+1} < -maxNormal_sp`.
  have hmono := PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ he hs
  have hvlt1 : x.toRat' < (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat := by rw [hmaxT]; grind
  have hvlt : x.toRat' < (PackedFloat.maxNormalNumber ep sp true).toRat := by rw [hmaxT]; grind
  -- both lower approximants are `-∞`, so `lowerHalf = true`.
  have hlowsp := smtLibLower_eq_neg_getInfinity_of_lt (by grind) hs x.toRat' hvlt
  have hlowsp1 := smtLibLower_eq_neg_getInfinity_of_lt (sp := sp + 1) (by grind) (by grind) x.toRat' hvlt1
  have hinfsp : (PackedFloat.getInfinity ep sp true).toExtRat' = ExtRat.Infinity true :=
    PackedFloat.toExtRat'_getInfinity hs
  have hinfsp1 : (PackedFloat.getInfinity ep (sp + 1) true).toExtRat' = ExtRat.Infinity true :=
    PackedFloat.toExtRat'_getInfinity (by grind)
  have hlowerhalf_true :
      (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
    rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hlowsp, hlowsp1,
      SmtLibSemantics.instExtendedRat.smtLibEq, PackedFloat.toExtRat_eq_toExtRat', hinfsp, hinfsp1]
  -- `blastIsLowerHalf = true` (`|x| > maxNormal_{sp+1}`).
  have hblast_true : x.blastIsLowerHalf ep sp = true := by
    have hgt : (PackedFloat.maxNormalNumber ep sp false).toRat < (-x).toRat' := by
      have hmono := PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ he hs; grind
    rw [blastIsLowerHalf_edge_eq_decide he hs heu hsu x hxsignt hxnorm hmsb hnotunder hnotover hmaxL hgt]
    exact decide_eq_true (by grind)
  exact iff_of_true hblast_true hlowerhalf_true

/-- The `lower = maxNormal` overflow edge: dispatch on `|x|` relative to `maxNormal_sp`, `maxNormal_{sp+1}`.
The `|x| < maxNormal_sp` case is impossible (`hmaxL` forces `lower = maxNormal ≤ |x|`); the other three
ranges are the axioms above. -/
theorem blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_true_edge
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su) (x : UnpackedFloat eu su)
    (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  -- `|x| ≥ maxNormal_sp` since `lower (Number |x|) = maxNormal ≤ |x|`.
  have hge : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ (-x).toRat' := by
    have hfin : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
      rw [hmaxL]; exact PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false
    have h := lower_toRat_le (by grind) hs (-x).toRat' hfin
    rw [hmaxL] at h; exact h
  by_cases heq : (-x).toRat' = (PackedFloat.maxNormalNumber ep sp false).toRat
  · exact blastIsLowerHalf_edge_eq_maxNormal he hs heu hsu x hxsignt hxnorm hmsb hnotunder hnotover
      hmaxL heq
  · have h : (PackedFloat.maxNormalNumber ep sp false).toRat < (-x).toRat' := by grind
    by_cases h2 : (-x).toRat' ≤ (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat
    · exact blastIsLowerHalf_edge_between_maxNormal he hs heu hsu x hxsignt hxnorm hmsb hnotunder
        hnotover hmaxL h h2
    · exact blastIsLowerHalf_edge_above_maxNormal he hs heu hsu x hxsignt hxnorm hmsb hnotunder
        hnotover hmaxL (by grind)

/-- **Negative, narrow (any range).** Dispatches the negative underflow boundary, the in-range
non-edge case, and the `lower = maxNormal` overflow edge. -/
theorem blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_true
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsignt : x.sign = true) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have hwideu : eu ≤ max eu (exponentWidth ep (sp + 1)) := Nat.le_max_left _ _
  have hwidesu : su ≤ max su (sp + 3) := Nat.le_max_left _ _
  have heu' : exponentWidth ep (sp + 1) ≤ max eu (exponentWidth ep (sp + 1)) := Nat.le_max_right _ _
  have hsu' : sp + 3 ≤ max su (sp + 3) := Nat.le_max_right _ _
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · -- negative underflow boundary
    exact blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_true_boundary_narrow he hs heu hsu
      (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwideu hwidesu heu' hsu'
      x hxsignt hxnorm hmsb hunder hnotunder
  · simp only [Bool.not_eq_true] at hunder
    by_cases hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat') : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false
    · -- `lower = maxNormal` overflow edge
      exact blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_true_edge he hs heu hsu x hxsignt hxnorm hmsb
        hunder hnotover hmaxL
    · -- in-range, non-edge
      exact blastIsLowerHalf_iff_lowerHalf_of_sign_true_inRange he hs heu hsu
        (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwideu hwidesu heu' hsu'
        x hxsignt hxnorm hmsb hunder hnotover hmaxL
        (lower_succ_ne_maxNormal_of_lower_ne_maxNormal he hs (-x).toRat' hmaxL)


/-# blastIsLowerHalf -/

/-- **Nonnegative, narrow (any range).** Dispatches the underflow boundary vs the in-range case, widening
to the `sp+1`-precision width that the bridge needs. -/
theorem blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_false
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
  have hwideu : eu ≤ max eu (exponentWidth ep (sp + 1)) := Nat.le_max_left _ _
  have hwidesu : su ≤ max su (sp + 3) := Nat.le_max_left _ _
  have heu' : exponentWidth ep (sp + 1) ≤ max eu (exponentWidth ep (sp + 1)) := Nat.le_max_right _ _
  have hsu' : sp + 3 ≤ max su (sp + 3) := Nat.le_max_right _ _
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · exact blastIsLowerHalf_iff_lowerHalf_of_sign_false_boundary_narrow he hs heu hsu
      (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwideu hwidesu heu' hsu'
      x hxsign hxnorm hmsb hunder hnotunder hnotover
  · simp only [Bool.not_eq_true] at hunder
    exact blastIsLowerHalf_iff_lowerHalf_of_sign_false_inRange he hs heu hsu
      (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwideu hwidesu heu' hsu'
      x hxsign hxnorm hmsb hunder hnotover

/-- `blastIsLowerHalf` agrees with the SMT-LIB `lowerHalf` predicate. Hypotheses match the isEven
theorems (so the RNE call site can supply them for `x.truncateFittingExponent`): a nonzero normalized
input, no early over/underflow. The SMT `lowerHalf` compares the lower approximant at precisions `sp`
and `sp+1`; the circuit's `!guardBit` matches via `blastRoundTowardZero_toRat'_eq_succ_iff_not_guardBit`. -/
theorem blastIsLowerHalf_iff_smtLibLowerHalf
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
    := by
  by_cases hxsign : x.sign = false
  · exact blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_false he hs heu hsu x hxsign hxnorm hmsb
      hnotunder hnotover
  · have hxsignt : x.sign = true := by simp only [Bool.not_eq_false] at hxsign; exact hxsign
    exact blastIsLowerHalf_iff_smtLibLowerHalf_of_sign_true he hs heu hsu x hxsignt hxnorm hmsb
      hnotunder hnotover

theorem blastIsLowerHalf_eq
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
  x.blastIsLowerHalf ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')) := by
  have := blastIsLowerHalf_iff_smtLibLowerHalf he hs heu hsu x hxnorm hmsb hnotunder hnotover
  grind

-- All three `maxNormal`-edge cases are fully proven (no axioms): `edge_eq` (representable), and
-- `edge_between`/`edge_above` via Lemma B (negative lower pin) and the `blastIsLowerHalf = guard==sticky`
-- circuit characterization (`guard ⟺ |x| ≥ maxNormal_{sp+1}`, `sticky ⟺ |x| ≠ maxNormal_{sp+1}`).
/--
info: 'Fp.blastIsLowerHalf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms blastIsLowerHalf_eq

/-- `<` on two finite `ExtRat.Number`s is the rational `<`. -/
theorem ExtRat.Number_lt_Number_iff {a b : Rat} :
    (ExtRat.Number a < ExtRat.Number b) ↔ a < b := by
  rw [← ExtRat.lt_def]
  simp only [ExtRat.lt, ExtRat.le, ExtRat.eq, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  grind

/-- Negation reverses `<` on `ExtRat`. -/
theorem ExtRat.neg_lt_neg_iff {a b : ExtRat} : (-a < -b) ↔ (b < a) := by
  rw [← ExtRat.lt_def, ← ExtRat.lt_def]
  cases a <;> cases b <;> simp [ExtRat.neg, ExtRat.lt, ExtRat.le, ExtRat.eq] <;> grind

/-- **Tie-break is sign-symmetric.** `tieBreak(-r) = tieBreak(r)`: under negation the lower/upper
approximants swap (`lower(-r) = -upper(r)`, `upper(-r) = -lower(r)`) and `<` reverses, exchanging the two
sides of the defining equality — which is symmetric. -/
theorem smtLibTieBreak_neg_eq {ep sp : Nat} (he : 0 < ep) (hs : 0 < sp) (r : Rat) :
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number (-r))
      = (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number r) := by
  rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
    SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq]
  rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp he hs (ExtRat.Number (-r)) (by simp),
    smtLibLower_eq_neg_smtLibUpper_neg ep (sp + 1) he (by omega) (ExtRat.Number (-r)) (by simp),
    smtLibUpper_eq_neg_smtLibLower_neg ep sp he hs (ExtRat.Number (-r)) (by simp),
    smtLibUpper_eq_neg_smtLibLower_neg ep (sp + 1) he (by omega) (ExtRat.Number (-r)) (by simp),
    show (-(ExtRat.Number (-r))) = ExtRat.Number r from by rw [ExtRat.ExtRat.neg_number]; congr 1; grind]
  simp only [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_neg, ExtRat.neg_lt_neg_iff]
  exact propext ⟨fun h => h.symm, fun h => h.symm⟩

/-- **Tie-break, in-range core (nonneg, wide).** `tieBreak ⟺ ¬sticky`. The SMT tie predicate
`(lower_sp < lower_{sp+1}) = (upper_{sp+1} < upper_sp)` reduces, via the lower/upper foundation lemmas,
to `(guard) ↔ (guard ⊕ sticky)`, which is `¬sticky` (true even at representable, `guard=sticky=0`). -/
theorem tieBreak_iff_not_sticky_of_sign_false_wide
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
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
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number x.toRat')
      ↔ x.blastExtractStickyBit ep sp = false := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
      have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp x
      rw [this] at hnotunder; simpa using hnotunder
    have : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    omega
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  -- the four approximants are finite, so `embed = Number toRat`.
  have hfinLsp := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range he hs heu_sp (by omega)
    x hxsign hxnorm hnotunder hnotover
  have hfinLsp1 := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range he (by omega) heu (by omega)
    x hxsign hxnorm hnotunder1 hnotover1
  have hfinUsp := isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal he hs heu_sp (by omega)
    x hxsign hxnorm hnotunder hnotover hmaxL
  have hfinUsp1 := isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal he (by omega) heu (by omega)
    x hxsign hxnorm hnotunder1 hnotover1 hmaxL1
  -- unfold the tie predicate to `(lower_sp < lower_{sp+1}) ↔ (upper_{sp+1} < upper_sp)` (toRat level).
  rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
    SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, PackedFloat.toExtRat_eq_toExtRat',
    PackedFloat.toExtRat'_eq_toRat_of hfinLsp, PackedFloat.toExtRat'_eq_toRat_of hfinLsp1,
    PackedFloat.toExtRat'_eq_toRat_of hfinUsp, PackedFloat.toExtRat'_eq_toRat_of hfinUsp1,
    eq_iff_iff, ExtRat.Number_lt_Number_iff]
  -- rewrite the four toRats to `lower_sp.toRat + coeff · u`.
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
  generalize (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat = L
  unfold UnpackedFloat.needsRounding
  cases hg : x.blastExtractGuardBit ep sp <;> cases hst : x.blastExtractStickyBit ep sp <;>
    simp only [hg, hst, Bool.or_false, Bool.or_true, Bool.true_or, Bool.false_or, if_true, if_false,
      Bool.true_eq_false, Bool.false_eq_true] <;> grind

/-- A finite number is `<` than `+∞`. -/
theorem ExtRat.Number_lt_Infinity_false (r : Rat) : ExtRat.Number r < ExtRat.Infinity false := by
  rw [← ExtRat.lt_def]; simp [ExtRat.lt, ExtRat.le, ExtRat.eq]

/-- `+∞` is not `< +∞`. -/
theorem ExtRat.not_Infinity_false_lt_Infinity_false : ¬ (ExtRat.Infinity false < ExtRat.Infinity false) := by
  rw [← ExtRat.lt_def]; simp [ExtRat.lt, ExtRat.le, ExtRat.eq]

/-- The SMT upper approximant of a value above `maxNormal_sp` is `+∞` (positive mirror of Lemma A). -/
theorem smtLibUpper_eq_getInfinity_of_gt {ep sp : Nat} (he : 1 < ep) (hs : 0 < sp) (R : Rat)
    (hR : (PackedFloat.maxNormalNumber ep sp false).toRat < R) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number R) : PackedFloat ep sp)
      = PackedFloat.getInfinity ep sp false := by
  rw [smtLibUpper_eq_upper ep sp (by grind) hs (ExtRat.Number R) (by simp)]
  exact upper_Number_eq_getInfinity_of_maxNormalNumber_lt (by grind) hs R hR

/-- **Tie-break, `lower = maxNormal` overflow edge (nonneg, wide).** `tieBreak ⟺ ¬sticky`. At this edge
`upper_sp = +∞` once `|x| > maxNormal_sp`. Dispatching on `x.toRat'` vs `maxNormal_sp`, `maxNormal_{sp+1}`,
the tie predicate is `true` exactly at the two representables `maxNormal_sp`, `maxNormal_{sp+1}` — which is
exactly where `lower_{sp+1}.toRat = x.toRat'`, i.e. where the sticky bit is clear. -/
theorem tieBreak_iff_not_sticky_of_sign_false_edge
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = PackedFloat.maxNormalNumber ep sp false) :
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number x.toRat')
      ↔ x.blastExtractStickyBit ep sp = false := by
  have he' : 0 < ep := by grind
  have he1 : 1 < ep := by grind
  have hfinMaxN : (PackedFloat.maxNormalNumber ep sp false).isNormOrNonzeroSubnorm :=
    PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he1 false
  have hfinMaxN1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).isNormOrNonzeroSubnorm :=
    PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he1 false
  have hfinMW : (maxNormalWiden ep sp).isNormOrNonzeroSubnorm := isNormOrNonzeroSubnorm_maxNormalWiden he1
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  have hmono := PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ he hs
  -- `x.toRat' ≥ maxNormal_sp`.
  have hge : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ x.toRat' := by
    have hfin : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
      rw [hmaxL]; exact PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false
    have h := lower_toRat_le (by grind) hs x.toRat' hfin; rw [hmaxL] at h; exact h
  -- in range at `sp+1`.
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
      have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp x
      rw [this] at hnotunder; simpa using hnotunder
    have : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    omega
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu_sp x hnotunder hnotover
  -- `sticky = false ⟺ lower_{sp+1}.toRat = x.toRat'`.
  have hst := needsRounding_succ_eq_blastExtractStickyBit (by grind) hs heu hsu x hdl hdu hnat
  have hrtz1 := smtLibLower_lower_toRat_eq_blastRoundTowardZero (sp := sp + 1) (by grind) (by grind) heu
    (by omega) x hxsign hxnorm hnotunder1 hnotover1
  have hneed1 := UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding (by grind)
    (by grind) heu (by omega) x hxsign hnotunder1 hnotover1
  have hsticky_iff : x.blastExtractStickyBit ep sp = false ↔
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat = x.toRat' := by
    rw [← hst, ← hneed1, hrtz1]
  rw [hsticky_iff]
  -- lower_sp is finite (= maxNormal).
  have hfinLsp : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
    rw [hmaxL]; exact PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (by grind) false
  by_cases h1 : x.toRat' = (PackedFloat.maxNormalNumber ep sp false).toRat
  · -- representable `|x| = maxNormal_sp`: all four approximants equal `maxNormal_sp`; tie `true`.
    have hlow1 := smtLibLower_succ_eq_maxNormalWiden_of_ge_of_lt (by grind) hs x.toRat' hge
      (by rw [h1]; exact hmono)
    have hup0 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false := by
      rw [upper_eq_lower_of_lower_isNormOrNonzeroSubnorm he' hs x.toRat' hfinLsp (by rw [hmaxL]; exact h1.symm), hmaxL]
    have hfinLsp1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).isNormOrNonzeroSubnorm := by
      rw [hlow1]; exact isNormOrNonzeroSubnorm_maxNormalWiden (by grind)
    have hup1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
        = maxNormalWiden ep sp := by
      rw [upper_eq_lower_of_lower_isNormOrNonzeroSubnorm he' (by grind) x.toRat' hfinLsp1
        (by rw [hlow1, toRat_maxNormalWiden]; exact h1.symm), hlow1]
    rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
      SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hmaxL, hlow1, hup0, hup1, PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_eq_toRat_of hfinMaxN, PackedFloat.toExtRat'_eq_toRat_of hfinMW,
      eq_iff_iff, ExtRat.Number_lt_Number_iff, toRat_maxNormalWiden]
    grind
  · have hgt : (PackedFloat.maxNormalNumber ep sp false).toRat < x.toRat' := by grind
    have hupsp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.getInfinity ep sp false := smtLibUpper_eq_getInfinity_of_gt (by grind) hs x.toRat' hgt
    have hinfsp : (PackedFloat.getInfinity ep sp false).toExtRat = ExtRat.Infinity false := by
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_getInfinity hs]
    by_cases h2 : x.toRat' < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat
    · -- `maxNormal_sp < |x| < maxNormal_{sp+1}`: `lower_{sp+1} = maxNormalWiden`, `upper_{sp+1} =
      -- maxNormal_{sp+1}`; tie `false`, and `lower_{sp+1}.toRat = maxNormal_sp ≠ x.toRat'`.
      have hlow1 := smtLibLower_succ_eq_maxNormalWiden_of_ge_of_lt (by grind) hs x.toRat' hge h2
      have hup1 := smtLibUpper_succ_eq_maxNormalNumber_of_lt_of_le (by grind) hs x.toRat' hgt (by grind)
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
        SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hmaxL, hlow1, hupsp, hup1, hinfsp,
        PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfinMaxN,
        PackedFloat.toExtRat'_eq_toRat_of hfinMW, PackedFloat.toExtRat'_eq_toRat_of hfinMaxN1,
        eq_iff_iff, ExtRat.Number_lt_Number_iff, ExtRat.Number_lt_Infinity_false, toRat_maxNormalWiden]
      grind
    · have h2' : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat ≤ x.toRat' := by grind
      have hlow1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
          = PackedFloat.maxNormalNumber ep (sp + 1) false := by
        rw [smtLibLower_eq_lower ep (sp + 1) (by grind) (by grind) _ (by simp)]
        exact lower_Number_eq_maxNormalNumber_of_toRat_le (by grind) (by grind) (by grind) x.toRat' h2'
      by_cases h3 : x.toRat' = (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat
      · -- `|x| = maxNormal_{sp+1}`: `upper_{sp+1} = maxNormal_{sp+1}` (representable at sp+1); tie `true`.
        have hup1 := smtLibUpper_succ_eq_maxNormalNumber_of_lt_of_le (by grind) hs x.toRat' hgt (by grind)
        rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
        simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
          SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hmaxL, hlow1, hupsp, hup1, hinfsp,
          PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfinMaxN,
          PackedFloat.toExtRat'_eq_toRat_of hfinMaxN1,
          eq_iff_iff, ExtRat.Number_lt_Number_iff, ExtRat.Number_lt_Infinity_false]
        grind
      · -- `|x| > maxNormal_{sp+1}`: `upper_{sp+1} = +∞`; tie `false`, `lower_{sp+1}.toRat = maxNormal_{sp+1} ≠ x.toRat'`.
        have hgt1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < x.toRat' := by grind
        have hup1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
            = PackedFloat.getInfinity ep (sp + 1) false := smtLibUpper_eq_getInfinity_of_gt (by grind) (by grind) x.toRat' hgt1
        have hinfsp1 : (PackedFloat.getInfinity ep (sp + 1) false).toExtRat = ExtRat.Infinity false := by
          rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_getInfinity (by grind)]
        rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
        simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
          SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, hmaxL, hlow1, hupsp, hup1, hinfsp, hinfsp1,
          PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfinMaxN,
          PackedFloat.toExtRat'_eq_toRat_of hfinMaxN1,
          eq_iff_iff, ExtRat.Number_lt_Number_iff, ExtRat.Number_lt_Infinity_false,
          ExtRat.not_Infinity_false_lt_Infinity_false]
        grind

/-- **Tie-break, underflow boundary (nonneg, wide).** `tieBreak ⟺ ¬sticky`. Here `lower_sp = +0`,
`upper_sp = minSub_sp = 2·minSub_{sp+1}`, `lower_{sp+1} = minSub_{sp+1} = 2^ex`, and `upper_{sp+1} =
minSub_{sp+1} + (sticky ? minSub_{sp+1} : 0)`, so `tieBreak = (0 < 2^ex) = (2^ex·(1+sticky) < 2·2^ex)`
which is `¬sticky`. -/
theorem tieBreak_iff_not_sticky_of_sign_false_boundary
    {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number x.toRat')
      ↔ x.blastExtractStickyBit ep sp = false := by
  have he' : 0 < ep := by grind
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  obtain ⟨hoff, hdiffLower, hdiffUpper, hxpos, hlt⟩ :=
    boundary_facts he hs heu_sp (by omega) x hxsign hmsb hunder hnotearlyunder
  -- the boundary exponent and the two subnormal magnitudes.
  have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hexval : x.ex.toInt = minNormalExp ep - ((sp : Int) + 1) := by
    have h1 : x.ex.toInt < minSubnormalExp ep sp := by
      rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu_sp] at hunder
      simpa using hunder
    have h2 : minSubnormalExp ep sp - 1 ≤ x.ex.toInt := by
      rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu_sp] at hnotearlyunder
      simpa only [decide_eq_false_iff_not, Int.not_lt] using hnotearlyunder
    grind
  have hminSub1 : (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat = (2 : Rat) ^ (x.ex.toInt) := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep (sp + 1) (by grind) (by omega), hexval]; congr 1
  have hminSub : (PackedFloat.minSubnormalNumber ep sp false).toRat = (2 : Rat) ^ (x.ex.toInt + 1) := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hs, hexval]; congr 1; push_cast; omega
  have h2ex : (2 : Rat) ^ (x.ex.toInt + 1) = 2 * 2 ^ (x.ex.toInt) := by
    rw [Rat.zpow_add (by decide) x.ex.toInt 1, Rat.zpow_one, Rat.mul_comm]
  -- `x` in range at `sp+1`.
  have hnotunder1 : x.blastIsUnderflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) (by omega) heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]
    have hms1 : minSubnormalExp ep (sp + 1) = minSubnormalExp ep sp - 1 := by
      simp only [minSubnormalExp]; push_cast; grind
    grind
  have hnotover1 : x.blastIsEarlyOverflowNonneg ep (sp + 1) = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) (by omega) heu]
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu_sp x
    rw [this] at hnotover; exact hnotover
  -- `lower_sp = +0`.
  have hlowsp : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = PackedFloat.getZero ep sp false := by
    refine eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') _ _ ?_ ?_ ?_ ?_
    · simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp)
    · simp [PackedFloat.isNaN_getZero] <;> grind
    · exact lsLawfulLower_smtLibLower ep sp (by grind) hs (ExtRat.Number x.toRat')
    · exact isLawfulLower_Number_getZero_of_underflowNonneg (by grind) hs heu_sp (by grind) x hxsign hunder
  -- `lower_{sp+1} = minSub_{sp+1}`.
  have hge1 : (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat ≤ x.toRat' := by
    rw [hminSub1]; exact UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hmsb
  have hlt1 : x.toRat' < 2 * (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat := by
    rw [hminSub1, ← h2ex, ← hminSub]; exact hlt
  have hlowpin : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
      = PackedFloat.minSubnormalNumber ep (sp + 1) false :=
    lower_Number_eq_minSubnormalNumber_of_ge_of_lt_succ he (by omega) x.toRat' hge1 hlt1
  have hmaxL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1))
      ≠ PackedFloat.maxNormalNumber ep (sp + 1) false := by
    rw [hlowpin]; intro hc
    have h1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).isNorm :=
      PackedFloat.isNorm_maxNormalNumber_of_lt_e ep (sp + 1) (by grind) false
    rw [← hc] at h1; simp [PackedFloat.isNorm, PackedFloat.minSubnormalNumber, BitVec.ofInt] at h1
  have hfinL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).isNormOrNonzeroSubnorm := by
    rw [hlowpin]; exact PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep (sp + 1) false (by grind) (by omega)
  -- `upper_sp = minSub_sp`.
  have hupsp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = PackedFloat.minSubnormalNumber ep sp false := by
    refine eq_of_IsLawfulUpper_of_IsLawfulUpper ep sp (ExtRat.Number x.toRat') _ _ ?_ ?_ ?_ ?_
    · simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp)
    · simpa using PackedFloat.not_isNaN_minSubnormalNumber ep sp false (by grind) hs
    · exact isLawfulUpper_smtLibUpper ep sp (by grind) hs (ExtRat.Number x.toRat')
    · exact isLawfulUpper_minSubnormalNumber_of_pos_of_le (by grind) hs x.toRat' hxpos (Rat.le_of_lt hlt)
  have hfinUsp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
    rw [hupsp]; exact PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hs
  have hfinUsp1 := isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal
    he (by omega) heu (by omega) x hxsign hxnorm hnotunder1 hnotover1 hmaxL1
  -- `upper_{sp+1} = minSub_{sp+1} + (sticky ? 2^ex : 0)`.
  have hupsp1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep (sp + 1)).toRat
      = (2 : Rat) ^ (x.ex.toInt) + (if x.blastExtractStickyBit ep sp then (2 : Rat) ^ (x.ex.toInt) else 0) := by
    rw [smtLibUpper_toRat_eq_lower_add_ulp (sp := sp + 1) he (by omega) heu (by omega) x hxsign hxnorm
        hnotunder1 hnotover1 hmaxL1,
      needsRounding_succ_eq_blastExtractStickyBit_of_off_eq_succ (by grind) hs heu (by omega) x
        hdiffLower hdiffUpper hoff,
      smtLibLower_lower_toRatExp_eq (sp := sp + 1) (by grind) (by omega) heu (by omega) x hxsign hxnorm
        hnotunder1 hnotover1, hoff, hlowpin, hminSub1]
    have hulp : (2 : Rat) ^ (-(((sp + 1 : Nat) : Int))) * 2 ^ (x.ex.toInt + (((sp + 1 : Nat) : Int)))
        = 2 ^ (x.ex.toInt) := by rw [← Rat.zpow_add (by decide)]; congr 1; push_cast; omega
    rw [hulp]
  -- unfold the tie predicate and substitute the four values.
  have hpos : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
  rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
    SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq]
  rw [hlowsp, show (PackedFloat.getZero ep sp false).toExtRat = ExtRat.Number 0 from by
      rw [PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero] <;> grind)]]
  simp only [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfinL1,
    PackedFloat.toExtRat'_eq_toRat_of hfinUsp, PackedFloat.toExtRat'_eq_toRat_of hfinUsp1,
    eq_iff_iff, ExtRat.Number_lt_Number_iff]
  rw [hlowpin, hminSub1, hupsp, hminSub, h2ex, hupsp1]
  cases hst : x.blastExtractStickyBit ep sp <;> simp only [hst, if_true, if_false, Bool.false_eq_true] <;>
    constructor <;> intro h <;> grind

/-- `blastIsTieBreak` is `guard && !sticky` regardless of sign (both branches coincide). -/
theorem blastIsTieBreak_eq_guard_and_not_sticky {eu su ep sp : Nat} (x : UnpackedFloat eu su) :
    x.blastIsTieBreak ep sp = (x.blastExtractGuardBit ep sp && !x.blastExtractStickyBit ep sp) := by
  unfold UnpackedFloat.blastIsTieBreak UnpackedFloat.blastIsTieBreakNeg UnpackedFloat.blastIsTieBreakNonneg
  cases x.sign <;> rfl

/-- A representable value (`needsRounding = false`) is never a tie. -/
theorem blastIsTieBreak_eq_false_of_not_needsRounding {eu su ep sp : Nat} (x : UnpackedFloat eu su)
    (h : x.needsRounding ep sp = false) : x.blastIsTieBreak ep sp = false := by
  rw [blastIsTieBreak_eq_guard_and_not_sticky]
  unfold UnpackedFloat.needsRounding at h
  simp only [Bool.or_eq_false_iff] at h
  rw [h.1]; simp

/-- A representable value (`needsRounding = false`) rounds toward zero exactly, so `lowerHalf` holds. -/
theorem blastIsLowerHalf_eq_true_of_not_needsRounding {eu su ep sp : Nat} (x : UnpackedFloat eu su)
    (h : x.needsRounding ep sp = false) : x.blastIsLowerHalf ep sp = true := by
  unfold UnpackedFloat.needsRounding at h
  simp only [Bool.or_eq_false_iff] at h
  unfold UnpackedFloat.blastIsLowerHalf UnpackedFloat.blastIsLowerHalfNeg UnpackedFloat.blastIsLowerHalfNonneg
  cases x.sign <;> simp [h.1, h.2]

/-- `needsRounding` is preserved by widening (`off ≤ sp`). -/
theorem needsRounding_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (heu' : exponentWidth ep sp ≤ eu') (hsu' : sp + 2 ≤ su')
    (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    (x.widen eu' su').needsRounding ep sp = x.needsRounding ep sp := by
  unfold UnpackedFloat.needsRounding
  rw [blastExtractGuardBit_widen x eu' su' hep hsp heu hsu heu' hsu' hwideu hwidesu hdiffLower hdiffUpper hdiffNatLe,
    blastExtractStickyBit_widen x eu' su' hep hsp heu hsu heu' hsu' hwideu hwidesu hdiffLower hdiffUpper hdiffNatLe]

/-- `decide` of a tie predicate equivalent to `sticky = false` is `!sticky`. -/
theorem decide_tieBreak_of_iff {b : Bool} {P : Prop} [Decidable P] (h : P ↔ (b = false)) :
    decide P = !b := by cases b <;> simp_all

/-- **Tie-break ⟺ ¬sticky (nonneg, wide), all in-range cases.** Dispatches the underflow boundary, the
`lower = maxNormal` overflow edge, and the in-range non-edge case. -/
theorem tieBreak_iff_not_sticky_of_sign_false_wide_all {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep (sp + 1) ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number x.toRat')
      ↔ x.blastExtractStickyBit ep sp = false := by
  have heu_sp : exponentWidth ep sp ≤ eu := Nat.le_trans exponentWidth_le_succ heu
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · exact tieBreak_iff_not_sticky_of_sign_false_boundary he hs heu hsu x hxsign hxnorm hmsb hunder
      hnotearlyunder hnotover
  · have hnotunder : x.blastIsUnderflowNonneg ep sp = false := by grind
    by_cases hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false
    · exact tieBreak_iff_not_sticky_of_sign_false_edge he hs heu hsu x hxsign hxnorm hmsb hnotunder
        hnotover hmaxL
    · obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu_sp x hnotunder hnotover
      exact tieBreak_iff_not_sticky_of_sign_false_wide he hs heu hsu x hxsign hxnorm hnotunder hnotover
        hmaxL (lower_succ_ne_maxNormal_of_lower_ne_maxNormal he hs x.toRat' hmaxL) hdl hdu hnat

/-- **Nonnegative, narrow.** `blastIsTieBreak = needsRounding && decide(tieBreak)`. Dispatches the
underflow boundary (where `guard = MSB = 1`, so `blastIsTieBreak = !sticky` directly) and the in-range/edge
case (transferred from the wide result by widening). -/
theorem blastIsTieBreak_eq_of_sign_false {eu su ep sp : Nat} (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    x.blastIsTieBreak ep sp = (x.needsRounding ep sp
      && decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number x.toRat'))) := by
  have hsupos : 0 < su := by omega
  have heu' : exponentWidth ep (sp + 1) ≤ max eu (exponentWidth ep (sp + 1)) := Nat.le_max_right _ _
  have hsu' : sp + 3 ≤ max su (sp + 3) := Nat.le_max_right _ _
  have hwideu : eu ≤ max eu (exponentWidth ep (sp + 1)) := Nat.le_max_left _ _
  have hwidesu : su ≤ max su (sp + 3) := Nat.le_max_left _ _
  have heu_succ : exponentWidth ep sp ≤ max eu (exponentWidth ep (sp + 1)) :=
    Nat.le_trans exponentWidth_le_succ heu'
  have hsign' : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).sign = false := by
    rw [sign_widen]; exact hxsign
  have hmsb' : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).sig.msb = true := by
    rw [sig_msb_widen x _ _ hwidesu hsupos]; exact hmsb
  have hnorm' := normalize_widen x (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwidesu hsupos hmsb
  have hnover' : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).blastIsEarlyOverflowNonneg ep sp = false := by
    rw [blastIsEarlyOverflowNonneg_widen x _ _ (by grind) hs heu heu_succ hwideu]; exact hnotover
  have hnearly' : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).blastIsEarlyUnderflowNonneg ep sp = false := by
    rw [blastIsEarlyUnderflowNonneg_widen x _ _ (by grind) hs heu heu_succ hwideu]; exact hnotearlyunder
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · -- boundary: `guard = MSB = 1`, so `blastIsTieBreak = !sticky` and `needsRounding = 1`.
    obtain ⟨hoff, hdiffLower, hdiffUpper, hxpos, hlt⟩ :=
      boundary_facts he hs heu hsu x hxsign hmsb hunder hnotearlyunder
    have hguard := blastExtractGuardBit_eq_true_of_off_eq_succ_of_msb (by grind) hs heu hsu x
      hdiffLower hdiffUpper hoff hmsb
    have hnr : x.needsRounding ep sp = true := by
      unfold UnpackedFloat.needsRounding; rw [hguard]; simp
    have hunder' : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).blastIsUnderflowNonneg ep sp = true := by
      rw [blastIsUnderflowNonneg_widen x _ _ (by grind) hs heu heu_succ hwideu]; exact hunder
    rw [blastIsTieBreak_eq_guard_and_not_sticky, hguard, Bool.true_and, hnr, Bool.true_and,
      ← toRat'_widen x (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwideu hwidesu hsupos,
      decide_tieBreak_of_iff (tieBreak_iff_not_sticky_of_sign_false_boundary he hs heu' hsu' _ hsign'
        hnorm' hmsb' hunder' hnearly' hnover'),
      blastExtractStickyBit_widen_boundary x _ _ (by grind) hs heu hsu heu_succ (by omega) hwideu hwidesu
        hdiffLower hdiffUpper hoff]
  · -- in-range / overflow edge: transfer the wide result by widening.
    have hnotunder : x.blastIsUnderflowNonneg ep sp = false := by grind
    obtain ⟨hdl, hdu, hnat⟩ := inRange_diff_facts he hs heu x hnotunder hnotover
    rw [← blastIsTieBreak_widen x _ _ (by grind) hs heu (by omega) heu_succ (by omega) hwideu hwidesu hdl hdu hnat,
      ← needsRounding_widen x _ _ (by grind) hs heu (by omega) heu_succ (by omega) hwideu hwidesu hdl hdu hnat,
      ← toRat'_widen x (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3)) hwideu hwidesu hsupos]
    rw [blastIsTieBreak_eq_guard_and_not_sticky]
    have hiff := tieBreak_iff_not_sticky_of_sign_false_wide_all he hs heu' hsu' _ hsign' hnorm' hmsb'
      hnearly' hnover'
    rw [decide_tieBreak_of_iff hiff]
    unfold UnpackedFloat.needsRounding
    cases hg : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).blastExtractGuardBit ep sp <;>
      cases hst : (x.widen (max eu (exponentWidth ep (sp + 1))) (max su (sp + 3))).blastExtractStickyBit ep sp <;>
      simp [hg, hst]

/-- **`blastIsTieBreak = needsRounding && decide(tieBreak)`** (the corrected spec equivalence; the bare
`blastIsTieBreak = decide(tieBreak)` is false at representable values, where the tie predicate is
vacuously `true` but the circuit `guard && !sticky` is `false`). `blastIsTieBreak` and `needsRounding`
are sign-independent and `tieBreak` is sign-symmetric, so the negative case reduces to the nonnegative one. -/
@[simp]
theorem blastIsTieBreak_eq (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) (hmsb : x.sig.msb = true)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    x.blastIsTieBreak ep sp = (x.needsRounding ep sp
      && decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
        (ExtRat.Number x.toRat'))) := by
  by_cases hxsign : x.sign = false
  · exact blastIsTieBreak_eq_of_sign_false he hs heu hsu x hxsign hxnorm hmsb hnotunder hnotover
  · have hxsignt : x.sign = true := by grind
    have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hxsignt]
    have hnnorm := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
    have hnmsb : (-x).sig.msb = true := by rw [UnpackedFloat.neg_sig]; exact hmsb
    have hnearly : (-x).blastIsEarlyUnderflowNonneg ep sp = false := by
      rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu, UnpackedFloat.neg_ex,
        ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hs heu]; exact hnotunder
    have hnover : (-x).blastIsEarlyOverflowNonneg ep sp = false := by
      rw [blastIsEarlyOverflowNonneg_neg]; exact hnotover
    have h := blastIsTieBreak_eq_of_sign_false he hs heu hsu (-x) hnsign hnnorm hnmsb hnearly hnover
    have hsi : x.blastIsTieBreak ep sp = (-x).blastIsTieBreak ep sp := by
      rw [blastIsTieBreak_eq_guard_and_not_sticky x, blastIsTieBreak_eq_guard_and_not_sticky (-x),
        show (-x).blastExtractGuardBit ep sp = x.blastExtractGuardBit ep sp from rfl,
        show (-x).blastExtractStickyBit ep sp = x.blastExtractStickyBit ep sp from rfl]
    have htbeq : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
          (ExtRat.Number (-x).toRat')
        = (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak
          (ExtRat.Number x.toRat') := by
      rw [UnpackedFloat.toRat'_neg]; exact smtLibTieBreak_neg_eq (by grind) hs x.toRat'
    rw [hsi, h]
    simp only [htbeq, show (-x).needsRounding ep sp = x.needsRounding ep sp from rfl]

/--
info: 'Fp.blastIsTieBreak_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blastIsTieBreak_eq

end Fp
