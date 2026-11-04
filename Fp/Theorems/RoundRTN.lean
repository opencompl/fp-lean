import Fp.Theorems.RoundEquiv

/-!
# RTN (round toward negative) rounding: circuit ↔ SMT-LIB spec bridges

Mirror of `Fp/Theorems/RoundRTP.lean` for the `RTN` mode.  See that file for the
layering rationale (these live above `RoundEquiv` to avoid an import cycle).

For `RTN`, the circuit `blastSmtLibRoundRTN = blastLower` unconditionally and the
spec `roundRTN = lower` for nonzero values, so the main case reduces to a single
`blastLower_Rel_smtLibLower`.  This is the mirror image of `RTP` under the
lower/upper ↔ negation duality.  Directed overflow:
`blastRounderSpecialCaseOverflow .RTN` is `∞` for `sign = true`, else `maxNormal`.
-/

namespace Fp

/-- For a nonzero rational, the SMT-LIB `RTN` rounder is exactly the `lower`
approximant.  Mirror of `roundRTP_eq_smtLibUpper_of_ne_zero`. -/
private theorem roundRTN_eq_smtLibLower_of_ne_zero {eout sout : Nat} {sign : Bool}
    (r : Rat) (hr0 : r ≠ 0) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).roundRTN sign (ExtRat.Number r)
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout) := by
  have hnotzero : ¬ SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hr0]
  rw [SmtLibSemantics.RoundMethod.roundRTN, if_neg hnotzero]
  simp only [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]

/-- The `true`-sign analogue of
`UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber`
(which is stated only for `false`), obtained by the negation duality. -/
private theorem toRat'_minSubnormalForPackedFloat_true_eq
    (ep sp eu : Nat) (he : 1 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) :
    (UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp true).toRat'
      = (PackedFloat.minSubnormalNumber ep sp true).toRat := by
  have key : (UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp true)
      = -(UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp false) := by
    simp [UnpackedFloat.minSubnormalForPackedFloat, UnpackedFloat.neg_def, UnpackedFloat.neg]
  have hneg_pf : -(PackedFloat.minSubnormalNumber ep sp false)
      = PackedFloat.minSubnormalNumber ep sp true := by
    simp [PackedFloat.neg_def, PackedFloat.neg, PackedFloat.minSubnormalNumber]
  rw [key, UnpackedFloat.toRat'_neg,
    UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber ep sp eu he hsp heu,
    ← PackedFloat.toRat_neg, hneg_pf]

/-- **Exact-value RTN bridge.** Analogue of `toExtRat_round_Rel_smtLibRound_of_RNE`. -/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTN
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RTN  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTN
        sign (ExtRat.Number r)) := by
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  simp [UnpackedFloat.toRat_eq_toRat']
  by_cases hzero : x.isZero
  · simp [hzero, hs]
    rw [roundRTN_zero]
    · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
      · grind only
    · grind only
  · by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
    · simp [hover]
      have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
      rw [roundRTN_eq_smtLibLower_of_ne_zero x.toRat' hx0, if_neg hx0]
      -- magnitude bound at overflow, plus the sign/value relationship
      have hmag : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs :=
        UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm hzero hover
      have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
      have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat
          < (2 : Rat) ^ (maxNormalExp ep + 1) := PackedFloat.toRat_maxNormalNumber_lt_two_pow he hs
      have hflip : (PackedFloat.maxNormalNumber ep sp true).toRat
          = - (PackedFloat.maxNormalNumber ep sp false).toRat := by
        rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
      by_cases hsign : x.sign = false
      · -- positive overflow: circuit `mkNumber (maxNormal … false)`, spec `lower = maxNormal false`
        have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
        have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
        rw [habs] at hmag
        have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ x.toRat' := by grind
        have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
            = PackedFloat.maxNormalNumber ep sp false := by
          rw [smtLibLower_eq_lower ep sp (by grind) hs _ (by simp),
            lower_Number_eq_maxNormalNumber_of_toRat_le he (by grind) hs x.toRat' hle]
        rw [hL]
        simp [blastRounderSpecialCaseOverflow, hsign]
        apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
        · simp
        · simp only [EUnpackedFloat.num_mkNumber]
          apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
          · exact UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber hs (by omega) he (Nat.le_refl _)
          · simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]
      · -- negative overflow: circuit `mkInfinity true`, spec `lower = -∞`
        have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
        rw [habs] at hmag
        have hLinf : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
            = PackedFloat.getInfinity ep sp true := by
          rw [smtLibLower_eq_lower ep sp (by grind) hs _ (by simp),
            lower_Number_eq_getInfinity_of_maxNormalNumber_lt (by grind) hs x.toRat' (by grind)]
        rw [hLinf]
        simp [blastRounderSpecialCaseOverflow, hsignt]
        apply EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign
        · simp [EUnpackedFloat.mkInfinity]
        · rw [PackedFloat.isInfinite_getInfinity]; simp [hs]
        · simp [EUnpackedFloat.mkInfinity, EUnpackedFloat.sign, PackedFloat.sign_getInfinity]
    · simp [hover]
      by_cases hx0 : x.toRat' = 0
      · simp [hx0]
        rw [roundRTN_zero]
        · apply EUnpackedFloat.Rel_of_Rel_of_isZero_of_isZero_of_eq_sign
          · simp
          · simp; grind only
          · simp
        · grind
      · simp [hx0]
        rw [roundRTN_eq_smtLibLower_of_ne_zero x.toRat' hx0]
        by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp
        · -- (early) underflow: `lower` is `-0`/`minSubnormal` depending on sign
          simp [hunder]
          have hmag : (x.toRat').abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1) :=
            UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder
          have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
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
          · -- positive tiny: circuit `mkZero false`, spec `lower = +0`
            have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
            have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
            rw [habs] at hmag
            rw [smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he hs x.toRat' (by grind) (by grind)]
            simp [blastRounderSpecialCaseUnderflow, hsign]
            apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
            grind
          · -- negative tiny: circuit `mkNumber minSubnormal`, spec `lower = -minSubnormal`
            have hsignt : x.sign = true := by grind
            have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
            have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
            rw [habs] at hmag
            rw [smtLibLower_eq_minSub_of_neg_of_gt ep sp he hs x.toRat' (by grind) (by grind)]
            simp [blastRounderSpecialCaseUnderflow, hsignt]
            apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
            · simp
            · simp only [EUnpackedFloat.num_mkNumber]
              apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
              · exact toRat'_minSubnormalForPackedFloat_true_eq
                  ep sp (exponentWidth ep sp) he hs (Nat.le_refl _)
              · simp [UnpackedFloat.minSubnormalForPackedFloat, PackedFloat.sign_minSubnormalNumber]
        · -- main case: circuit `blastLower`, spec `lower`
          simp [hunder]
          simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTN]
          rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self he hs heu hsu x
              hzero hxnorm (by simpa using hunder) (by simpa using hover)]
          rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind)
              (by grind) (by grind) (by grind)]
          exact UnpackedFloat.blastLower_Rel_smtLibLower he hs hsu heu x hxnorm (by simpa using hover)

/-- **Finiteness companion of `toExtRat_round_Rel_smtLibRound_of_RTN`.** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RTN
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true) :
    (x.blastSmtLibRound ep sp .RTN : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTN
            sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTN
            sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  subst r sign
  have hzero : x.isZero = false := UnpackedFloat.isZero_eq_false_of_msb x hmsb
  have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
  have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
  simp only [SmtLibSemantics.RoundMethod.round_RTN_eq, UnpackedFloat.toRat_eq_toRat']
  rw [roundRTN_eq_smtLibLower_of_ne_zero x.toRat' hx0]
  -- Reduce the circuit-state hypothesis through `blastSmtLibRound`'s branches.
  rw [UnpackedFloat.blastSmtLibRound, if_neg (by simp [hzero])] at hstate
  by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
  · rw [if_pos hover] at hstate
    have hmag : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs :=
      UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm (by simp [hzero]) hover
    have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat
        < (2 : Rat) ^ (maxNormalExp ep + 1) := PackedFloat.toRat_maxNormalNumber_lt_two_pow he hs
    by_cases hsign : x.sign = false
    · -- positive overflow: spec `lower = maxNormalNumber false`, finite.
      have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
      have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
      rw [habs] at hmag
      have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ x.toRat' := by grind
      have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
          = PackedFloat.maxNormalNumber ep sp false := by
        rw [smtLibLower_eq_lower ep sp (by grind) hs _ (by simp),
          lower_Number_eq_maxNormalNumber_of_toRat_le he (by grind) hs x.toRat' hle]
      rw [hL]
      refine ⟨PackedFloat.not_isNaN_maxNormalNumber ep sp false (by grind), ?_⟩
      simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
        (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he false)
    · -- negative overflow: circuit is `∞` (state `Infinity`), contradicting `state = Number`.
      have hsignt : x.sign = true := by grind
      simp [blastRounderSpecialCaseOverflow, hsignt, EUnpackedFloat.mkInfinity] at hstate
  · rw [if_neg (by simpa using hover)] at hstate
    by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
    · -- underflow: spec `lower` is `getZero false` / `minSubnormal true`, both finite.
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
        rw [smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he hs x.toRat' (by grind) (by grind)]
        refine ⟨?_, ?_⟩
        · rw [PackedFloat.isNaN_getZero]; simp; grind
        · rw [PackedFloat.isInfinite_getZero]; simp; grind
      · have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
        rw [habs] at hmag
        rw [smtLibLower_eq_minSub_of_neg_of_gt ep sp he hs x.toRat' (by grind) (by grind)]
        refine ⟨PackedFloat.not_isNaN_minSubnormalNumber ep sp true (by grind) hs, ?_⟩
        simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
          (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp true (by grind) hs)
    · -- main case: circuit finite `blastLower` ⟹ spec `lower` is finite.
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
      simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTN,
        EUnpackedFloat.state_normalize] at hstate
      have hLnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
        simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp)
      have hLfin := UnpackedFloat.not_isInfinite_smtLibLower_of_blastLower_state_Number
        he hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hstate
      rw [hztoRat] at hLfin
      exact ⟨hLnan, hLfin⟩

/-- info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTN' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTN

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_finite_of_RTN' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_finite_of_RTN

/-- **StickyEquiv RTN bridge.** Analogue of
`UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`. -/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_RTN_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RTN : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTN sign (ExtRat.Number r)) := by
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RTN x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RTN sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTN he hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm

/-- **Finiteness companion of `blastSmtLibRound_Rel_round_of_RTN_of_stickyEquiv`.** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RTN_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RTN : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTN sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTN sign (ExtRat.Number r)).isInfinite := by
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
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RTN x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RTN sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.blastSmtLibRound_finite_of_RTN he hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm hmsb hstate

/-- The normalized RTN blast-rounder output is `Packable`: `blastSmtLibRoundRTN` is
just `blastLower`, which is a normalize fixed point (so `Packable`). -/
theorem UnpackedFloat.blastSmtLibRoundRTN_normalize_Packable
    (hep : 1 < ep) (hs : 0 < sp) (hsu : sp + 2 ≤ su)
    (z : UnpackedFloat (exponentWidth ep sp) su) (hznorm : z.normalize = z)
    (hnotEU : z.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotEO : z.blastIsEarlyOverflowNonneg ep sp = false) :
    (z.blastSmtLibRoundRTN ep sp).normalize.Packable := by
  have heu : exponentWidth ep sp ≤ exponentWidth ep sp := Nat.le_refl _
  unfold UnpackedFloat.blastSmtLibRoundRTN
  rw [UnpackedFloat.blastLower_normalize_eq_self hep hs heu hsu z hznorm hnotEU hnotEO]
  exact UnpackedFloat.blastLower_Packable hep hs hsu z hznorm hnotEU hnotEO

/-- `blastSmtLibRound` (RTN) output is always `Packable`. -/
theorem UnpackedFloat.blastSmtLibRound_Packable_of_RTN
    (hep : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RTN).Packable := by
  have he : 1 < ep := by grind
  rw [UnpackedFloat.blastSmtLibRound]
  by_cases hzero : x.isZero = true
  · rw [if_pos hzero]
    exact EUnpackedFloat.mkZero_Packable he hs x.sign
  · rw [if_neg hzero]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
    · rw [if_pos hover]
      by_cases hsign : x.sign = true
      · exact EUnpackedFloat.Packable_of_state_ne_Number (by
          simp [blastRounderSpecialCaseOverflow, hsign])
      · simp only [Bool.not_eq_true] at hsign
        rw [show blastRounderSpecialCaseOverflow (tep := ep) (tsp := sp) .RTN x.sign
            = EUnpackedFloat.mkNumber (UnpackedFloat.maxNormal _ _ ep sp x.sign) by
          simp [blastRounderSpecialCaseOverflow, hsign]]
        exact EUnpackedFloat.mkNumber_Packable
          (UnpackedFloat.maxNormal_Packable_of_sign he hs x.sign)
    · rw [if_neg hover]
      by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
      · rw [if_pos hunder]
        by_cases hsign : x.sign = false
        · rw [show blastRounderSpecialCaseUnderflow (tep := ep) (tsp := sp) .RTN x.sign
              = EUnpackedFloat.mkZero x.sign by simp [blastRounderSpecialCaseUnderflow, hsign]]
          exact EUnpackedFloat.mkZero_Packable he hs x.sign
        · simp only [Bool.not_eq_false] at hsign
          rw [show blastRounderSpecialCaseUnderflow (tep := ep) (tsp := sp) .RTN x.sign
              = EUnpackedFloat.mkNumber (UnpackedFloat.minSubnormalForPackedFloat _ _ ep sp x.sign) by
            simp [blastRounderSpecialCaseUnderflow, hsign]]
          exact EUnpackedFloat.mkNumber_Packable
            (UnpackedFloat.minSubnormalForPackedFloat_Packable_of_sign he hs x.sign)
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
        show ((x.truncateFittingExponent ep sp).blastSmtLibRoundRTN ep sp).normalize.Packable
        exact UnpackedFloat.blastSmtLibRoundRTN_normalize_Packable hep hs hsu
          (x.truncateFittingExponent ep sp) htnorm htunder htover

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_Packable_of_RTN' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_Packable_of_RTN

end Fp
