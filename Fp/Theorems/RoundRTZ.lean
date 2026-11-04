import Fp.Theorems.RoundEquiv

/-!
# RTZ (round toward zero) rounding: circuit ↔ SMT-LIB spec bridges

Mirror of `Fp/Theorems/RoundRTP.lean` for the `RTZ` mode.  See that file for the
layering rationale (these live above `RoundEquiv` to avoid an import cycle).

For `RTZ`, the circuit `blastSmtLibRoundRTZ = if sign then blastUpper else
blastLower` and the spec `roundRTZ = if gtZero then lower else upper` for nonzero
values.  The main case is a single sign split connecting the circuit's `sign` to
the spec's `gtZero`/`ltZero` (via `toRat'_nonneg_of_sign_false` /
`sign_eq_decide_toRat'_lt_zero`), each branch closed by `blastLower_Rel_smtLibLower`
/ `blastUpper_Rel_smtLibUpper`.  Overflow is always `maxNormal` (no sign
dependence); underflow is the RNE-style "always 0" and reuses the RNE boundary
lemma.  No lowerHalf/tieBreak/isEven reasoning.
-/

namespace Fp

/-- For a nonzero rational, the SMT-LIB `RTZ` rounder is the `lower` approximant when
`r > 0` and the `upper` approximant when `r < 0` (round toward zero). -/
private theorem roundRTZ_eq_of_ne_zero {eout sout : Nat} {sign : Bool}
    (r : Rat) (hr0 : r ≠ 0) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).roundRTZ sign (ExtRat.Number r)
      = if 0 < r then
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout)
        else
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat eout sout) := by
  have hnotzero : ¬ SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hr0]
  rw [SmtLibSemantics.RoundMethod.roundRTZ, if_neg hnotzero]
  by_cases hpos : 0 < r
  · have hgt : SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      simp only [SmtLibSemantics.instExtendedRat.gtZero]
      rw [← ExtRat.ExtRat.zero_def, ExtRat.num_lt_num_iff]; simpa using hpos
    rw [if_pos hgt, if_pos hpos]
    simp only [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
  · have hlt : r < 0 := by grind
    have hngt : ¬ SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      simp only [SmtLibSemantics.instExtendedRat.gtZero]
      rw [← ExtRat.ExtRat.zero_def, ExtRat.num_lt_num_iff]; simp; grind
    have hltZ : SmtLibSemantics.ExtendedNumber.ltZero (ExtRat.Number r) := by
      simp only [SmtLibSemantics.instExtendedRat.ltZero]
      rw [← ExtRat.ExtRat.zero_def, ExtRat.num_lt_num_iff]; simpa using hlt
    rw [if_neg hngt, if_pos hltZ, if_neg hpos]
    simp only [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq]

/-- **Exact-value RTZ bridge.** Analogue of `toExtRat_round_Rel_smtLibRound_of_RNE`. -/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTZ
    (he : 1 < ep)
    (hep : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RTZ  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTZ
        sign (ExtRat.Number r)) := by
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  simp [UnpackedFloat.toRat_eq_toRat']
  by_cases hzero : x.isZero
  · simp [hzero, hs]
    rw [roundRTZ_zero]
    · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
      · grind only
    · grind only
  · have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
    have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
    rw [if_neg hx0]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
    · simp [hover]
      rw [roundRTZ_eq_of_ne_zero x.toRat' hx0]
      have hmag : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs :=
        UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm hzero hover
      have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat
          < (2 : Rat) ^ (maxNormalExp ep + 1) := PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
      by_cases hsign : x.sign = false
      · -- positive overflow: spec `lower = maxNormalNumber false`, circuit `mkNumber (maxNormal false)`
        have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
        have hpos : 0 < x.toRat' := by grind
        have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
        rw [habs] at hmag
        have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ x.toRat' := by grind
        have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
            = PackedFloat.maxNormalNumber ep sp false := by
          rw [smtLibLower_eq_lower ep sp (by grind) hs _ (by simp),
            lower_Number_eq_maxNormalNumber_of_toRat_le he (by grind) hs x.toRat' hle]
        rw [if_pos hpos, hL]
        simp [blastRounderSpecialCaseOverflow, hsign]
        apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
        · simp
        · simp only [EUnpackedFloat.num_mkNumber]
          apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
          · exact UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber hs (by omega) hep (Nat.le_refl _)
          · simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]
      · -- negative overflow: spec `upper = maxNormalNumber true`, circuit `mkNumber (maxNormal true)`
        have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
        rw [habs] at hmag
        have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ -x.toRat' := by grind
        have hU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
            = PackedFloat.maxNormalNumber ep sp true := by
          rw [smtLibUpper_eq_upper ep sp (by grind) hs _ (by simp), upper, ExtRat.ExtRat.neg_number,
            lower_Number_eq_maxNormalNumber_of_toRat_le he (by grind) hs (-x.toRat') hle,
            PackedFloat.neg_maxNormalNumber_false']
        rw [if_neg (by grind), hU]
        simp [blastRounderSpecialCaseOverflow, hsignt]
        apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
        · simp
        · simp only [EUnpackedFloat.num_mkNumber]
          apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
          · exact UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber hs (by omega) hep (Nat.le_refl _)
          · simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]
    · simp [hover]
      rw [roundRTZ_eq_of_ne_zero x.toRat' hx0]
      by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp
      · -- (early) underflow: spec is `getZero`; circuit is `mkZero`
        simp [hunder]
        have hmag : (x.toRat').abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1) :=
          UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder
        have hB : (PackedFloat.minSubnormalNumber ep sp false).toRat
            = (2 : Rat) ^ (minSubnormalExp ep sp) := by
          rw [PackedFloat.toExtRat_minSubnormal_eq ep sp he hs]; congr 1
          simp only [minSubnormalExp, maxSubnormalExp]; grind
        have hstep : (2 : Rat) ^ (minSubnormalExp ep sp - 1)
            < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
          rw [hB, show (2 : Rat) ^ (minSubnormalExp ep sp)
              = 2 ^ (minSubnormalExp ep sp - 1) * 2 from by
            rw [← Rat.zpow_add_one (by grind : (2 : Rat) ≠ 0)]; congr 1; grind]
          have hpos : (0 : Rat) < 2 ^ (minSubnormalExp ep sp - 1) := Rat.two_pow_pos _
          grind
        by_cases hsign : x.sign = false
        · -- positive tiny: spec `lower = getZero false`, circuit `mkZero false`
          have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
          have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
          rw [habs] at hmag
          have hpos : 0 < x.toRat' := by grind
          rw [if_pos hpos,
            smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he hs x.toRat' (by grind) (by grind)]
          simp [blastRounderSpecialCaseUnderflow, hsign]
          apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
          grind
        · -- negative tiny: spec `upper = getZero true`, circuit `mkZero true`
          have hsignt : x.sign = true := by grind
          have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
          have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
          rw [habs] at hmag
          rw [if_neg (by grind),
            smtLibUpper_eq_getZero_of_nonpos_of_gt ep sp he hs x.toRat' (by grind) (by grind)]
          simp [blastRounderSpecialCaseUnderflow, hsignt]
          apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
          grind
      · -- main case: circuit `blastLower`/`blastUpper` (sign split), spec `lower`/`upper`
        simp [hunder]
        by_cases hsign : x.sign = false
        · -- sign false ⟹ `0 < x.toRat'` ⟹ spec `lower`, circuit `blastLower`
          have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
          have hpos : 0 < x.toRat' := by grind
          simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTZ,
            sign_truncateFittingExponent, hsign, Bool.false_eq_true, if_false]
          rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x
              hzero hxnorm (by simpa using hunder) (by simpa using hover)]
          rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind)
              (by grind) (by grind) (by grind)]
          rw [if_pos hpos]
          exact UnpackedFloat.blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm (by simpa using hover)
        · -- sign true ⟹ `x.toRat' < 0` ⟹ spec `upper`, circuit `blastUpper`
          have hsignt : x.sign = true := by grind
          have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
          simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTZ,
            sign_truncateFittingExponent, hsignt, if_true]
          rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x
              hzero hxnorm (by simpa using hunder) (by simpa using hover)]
          rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind)
              (by grind) (by grind) (by grind)]
          rw [if_neg (show ¬ (0 < x.toRat') by grind)]
          exact UnpackedFloat.blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm (by simpa using hover)

/-- **Finiteness companion of `toExtRat_round_Rel_smtLibRound_of_RTZ`.** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RTZ
    (he : 1 < ep) (hep : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true) :
    (x.blastSmtLibRound ep sp .RTZ : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTZ
            sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTZ
            sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  subst r sign
  have hzero : x.isZero = false := UnpackedFloat.isZero_eq_false_of_msb x hmsb
  have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
  have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
  simp only [SmtLibSemantics.RoundMethod.round_RTZ_eq, UnpackedFloat.toRat_eq_toRat']
  rw [roundRTZ_eq_of_ne_zero x.toRat' hx0]
  rw [UnpackedFloat.blastSmtLibRound, if_neg (by simp [hzero])] at hstate
  by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
  · rw [if_pos hover] at hstate
    have hmag : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs :=
      UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm (by simp [hzero]) hover
    have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat
        < (2 : Rat) ^ (maxNormalExp ep + 1) := PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
    by_cases hsign : x.sign = false
    · -- positive overflow: spec `lower = maxNormalNumber false`, finite.
      have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
      have hpos : 0 < x.toRat' := by grind
      have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
      rw [habs] at hmag
      have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ x.toRat' := by grind
      have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
          = PackedFloat.maxNormalNumber ep sp false := by
        rw [smtLibLower_eq_lower ep sp (by grind) hs _ (by simp),
          lower_Number_eq_maxNormalNumber_of_toRat_le he (by grind) hs x.toRat' hle]
      rw [if_pos hpos, hL]
      refine ⟨PackedFloat.not_isNaN_maxNormalNumber ep sp false (by grind), ?_⟩
      simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
        (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he false)
    · -- negative overflow: spec `upper = maxNormalNumber true`, finite.
      have hsignt : x.sign = true := by grind
      have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
      have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
      rw [habs] at hmag
      have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ -x.toRat' := by grind
      have hU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
          = PackedFloat.maxNormalNumber ep sp true := by
        rw [smtLibUpper_eq_upper ep sp (by grind) hs _ (by simp), upper, ExtRat.ExtRat.neg_number,
          lower_Number_eq_maxNormalNumber_of_toRat_le he (by grind) hs (-x.toRat') hle,
          PackedFloat.neg_maxNormalNumber_false']
      rw [if_neg (by grind), hU]
      refine ⟨PackedFloat.not_isNaN_maxNormalNumber ep sp true (by grind), ?_⟩
      simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
        (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he true)
  · rw [if_neg (by simpa using hover)] at hstate
    by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
    · -- underflow: spec `getZero`, finite.
      rw [if_pos hunder] at hstate
      have hmag : (x.toRat').abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1) :=
        UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder
      have hB : (PackedFloat.minSubnormalNumber ep sp false).toRat
          = (2 : Rat) ^ (minSubnormalExp ep sp) := by
        rw [PackedFloat.toExtRat_minSubnormal_eq ep sp he hs]; congr 1
        simp only [minSubnormalExp, maxSubnormalExp]; grind
      have hstep : (2 : Rat) ^ (minSubnormalExp ep sp - 1)
          < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
        rw [hB, show (2 : Rat) ^ (minSubnormalExp ep sp)
            = 2 ^ (minSubnormalExp ep sp - 1) * 2 from by
          rw [← Rat.zpow_add_one (by grind : (2 : Rat) ≠ 0)]; congr 1; grind]
        have hpos : (0 : Rat) < 2 ^ (minSubnormalExp ep sp - 1) := Rat.two_pow_pos _
        grind
      by_cases hsign : x.sign = false
      · have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
        have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
        rw [habs] at hmag
        have hpos : 0 < x.toRat' := by grind
        rw [if_pos hpos,
          smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he hs x.toRat' (by grind) (by grind)]
        refine ⟨?_, ?_⟩
        · rw [PackedFloat.isNaN_getZero]; simp; grind
        · rw [PackedFloat.isInfinite_getZero]; simp; grind
      · have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
        rw [habs] at hmag
        rw [if_neg (by grind),
          smtLibUpper_eq_getZero_of_nonpos_of_gt ep sp he hs x.toRat' (by grind) (by grind)]
        refine ⟨?_, ?_⟩
        · rw [PackedFloat.isNaN_getZero]; simp; grind
        · rw [PackedFloat.isInfinite_getZero]; simp; grind
    · -- main case: circuit finite `blastLower`/`blastUpper` ⟹ spec `lower`/`upper` finite.
      rw [if_neg (by simpa using hunder)] at hstate
      simp only [Bool.not_eq_true] at hover hunder
      have htnorm := normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
        he hs heu hsu x (by simp [hzero]) hxnorm
      have htmsb : (x.truncateFittingExponent ep sp).sig.msb = true :=
        (UnpackedFloat.normalize_eq_self_iff x (by simpa [UnpackedFloat.isZero] using hzero)).mp hxnorm
      have htover : (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
        rw [blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x hover hunder]; exact hover
      have hztoRat : (x.truncateFittingExponent ep sp).toRat' = x.toRat' :=
        toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
          he hs heu hover hunder
      simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTZ,
        sign_truncateFittingExponent, EUnpackedFloat.state_normalize] at hstate
      by_cases hsign : x.sign = false
      · -- sign false ⟹ spec `lower`, circuit `blastLower`.
        have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
        have hpos : 0 < x.toRat' := by grind
        rw [if_pos hpos]
        simp only [hsign, Bool.false_eq_true, if_false] at hstate
        have hLnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
          simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp)
        have hLfin := UnpackedFloat.not_isInfinite_smtLibLower_of_blastLower_state_Number
          hep hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hstate
        rw [hztoRat] at hLfin
        exact ⟨hLnan, hLfin⟩
      · -- sign true ⟹ spec `upper`, circuit `blastUpper`.
        have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        rw [if_neg (by grind)]
        simp only [hsignt, if_true] at hstate
        have hUnan : ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
          simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs _ (by simp)
        have hUfin := UnpackedFloat.not_isInfinite_smtLibUpper_of_blastUpper_state_Number
          hep hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hstate
        rw [hztoRat] at hUfin
        exact ⟨hUnan, hUfin⟩

/-- info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTZ' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTZ

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_finite_of_RTZ' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_finite_of_RTZ

/-- **StickyEquiv RTZ bridge.** Analogue of
`UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`. -/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_RTZ_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RTZ : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTZ sign (ExtRat.Number r)) := by
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RTZ x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RTZ sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTZ he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm

/-- **Finiteness companion of `blastSmtLibRound_Rel_round_of_RTZ_of_stickyEquiv`.** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RTZ_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RTZ : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTZ sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTZ sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RTZ x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RTZ sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.blastSmtLibRound_finite_of_RTZ he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm hmsb hstate

/-- The normalized RTZ blast-rounder output is `Packable`: `blastSmtLibRoundRTZ` is a
sign split between `blastUpper` and `blastLower`, both of which are normalize fixed
points (so `Packable`). -/
theorem UnpackedFloat.blastSmtLibRoundRTZ_normalize_Packable
    (hep : 1 < ep) (hs : 0 < sp) (hsu : sp + 2 ≤ su)
    (z : UnpackedFloat (exponentWidth ep sp) su) (hznorm : z.normalize = z)
    (hnotEU : z.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotEO : z.blastIsEarlyOverflowNonneg ep sp = false) :
    (z.blastSmtLibRoundRTZ ep sp).normalize.Packable := by
  have heu : exponentWidth ep sp ≤ exponentWidth ep sp := Nat.le_refl _
  have hU : (z.blastUpper ep sp).normalize.Packable := by
    rw [UnpackedFloat.blastUpper_normalize_eq_self hep hs heu hsu z hznorm hnotEU hnotEO]
    exact UnpackedFloat.blastUpper_Packable hep hs hsu z hznorm hnotEU hnotEO
  have hL : (z.blastLower ep sp).normalize.Packable := by
    rw [UnpackedFloat.blastLower_normalize_eq_self hep hs heu hsu z hznorm hnotEU hnotEO]
    exact UnpackedFloat.blastLower_Packable hep hs hsu z hznorm hnotEU hnotEO
  unfold UnpackedFloat.blastSmtLibRoundRTZ
  split
  · exact hU
  · exact hL

/-- `blastSmtLibRound` (RTZ) output is always `Packable`. -/
theorem UnpackedFloat.blastSmtLibRound_Packable_of_RTZ
    (hep : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RTZ).Packable := by
  have he : 1 < ep := by grind
  rw [UnpackedFloat.blastSmtLibRound]
  by_cases hzero : x.isZero = true
  · rw [if_pos hzero]
    exact EUnpackedFloat.mkZero_Packable he hs x.sign
  · rw [if_neg hzero]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
    · rw [if_pos hover]
      -- RTZ overflow is `maxNormal` for both signs (never `∞`).
      rw [show blastRounderSpecialCaseOverflow (tep := ep) (tsp := sp) .RTZ x.sign
          = EUnpackedFloat.mkNumber (UnpackedFloat.maxNormal _ _ ep sp x.sign) by
        simp [blastRounderSpecialCaseOverflow]]
      exact EUnpackedFloat.mkNumber_Packable
        (UnpackedFloat.maxNormal_Packable_of_sign he hs x.sign)
    · rw [if_neg hover]
      by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
      · rw [if_pos hunder]
        -- RTZ underflow is `mkZero` for both signs.
        rw [show blastRounderSpecialCaseUnderflow (tep := ep) (tsp := sp) .RTZ x.sign
            = EUnpackedFloat.mkZero x.sign by simp [blastRounderSpecialCaseUnderflow]]
        exact EUnpackedFloat.mkZero_Packable he hs x.sign
      · rw [if_neg hunder]
        simp only [Bool.not_eq_true] at hover hunder
        have htnorm := normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
          he hs heu hsu x (by simpa using hzero) hxnorm
        have htover : (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
          rw [blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x hover hunder]
          exact hover
        have htunder : (x.truncateFittingExponent ep sp).blastIsEarlyUnderflowNonneg ep sp = false := by
          rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs (Nat.le_refl _),
            toInt_ex_truncateFittingExponent he hs heu x hover hunder,
            ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x]
          exact hunder
        show ((x.truncateFittingExponent ep sp).blastSmtLibRoundRTZ ep sp).normalize.Packable
        exact UnpackedFloat.blastSmtLibRoundRTZ_normalize_Packable hep hs hsu
          (x.truncateFittingExponent ep sp) htnorm htunder htover

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_Packable_of_RTZ' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_Packable_of_RTZ

end Fp
