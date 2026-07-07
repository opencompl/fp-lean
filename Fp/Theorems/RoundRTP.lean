import Fp.Theorems.RoundEquiv

/-!
# RTP (round toward positive) rounding: circuit ↔ SMT-LIB spec bridges

This file mirrors, for the `RTP` rounding mode, the RNE bridge theorems:
* the *exact-value* bridge `UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE`
  (`Fp/Theorems/UnpackedFloat/Round/RNE.lean`), and
* its `stickyEquiv` generalization
  `UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`
  (`Fp/Theorems/Addition.lean`),
together with the two finiteness companions.

Layering note: unlike the RNE exact-value bridge (which lives in the
`UnpackedFloat.Round` aggregator layer because it is reused by `Multiplication`),
these live *above* `RoundEquiv` — importing `RoundEquiv` transitively provides
both the full family of `Round` lemmas (bracket keystones
`blastLower_Rel_smtLibLower` / `blastUpper_Rel_smtLibUpper`, the guard/sticky
extraction lemmas, and the RNE boundary lemmas we reuse) and the mode-generic
sticky machinery (`round_congr_of_RoundEquiv`, `round_eq_round_of_ne_zero`,
`roundEquiv_of_stickyEquiv`).  Placing all four RTP theorems in one file therefore
avoids the import cycle that would arise from wiring a mode file into the
`UnpackedFloat.Round` aggregator.

For `RTP`, the circuit `blastSmtLibRoundRTP = blastUpper` unconditionally and the
spec `roundRTP = upper` for nonzero values, so the main case reduces to a single
`blastUpper_Rel_smtLibUpper`.  The only mode-specific subtlety is directed
overflow (`blastRounderSpecialCaseOverflow .RTP` is `∞` for `sign = false`, else
`maxNormal`).
-/

namespace Fp

/-- For a nonzero rational, the SMT-LIB `RTP` rounder is exactly the `upper`
approximant. -/
private theorem roundRTP_eq_smtLibUpper_of_ne_zero {eout sout : Nat} {sign : Bool}
    (r : Rat) (hr0 : r ≠ 0) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).roundRTP sign (ExtRat.Number r)
      = (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat eout sout) := by
  have hnotzero : ¬ SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hr0]
  rw [SmtLibSemantics.RoundMethod.roundRTP, if_neg hnotzero]
  simp only [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq]

/-- **Exact-value RTP bridge.** The bit-blasted `RTP` rounder agrees (up to NaN,
via `Rel`) with the SMT-LIB `RTP` rounder on the exact value `r = x.toRat`.
Analogue of `UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE`. -/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTP
    (he : 1 < ep)
    (hep : 2 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RTP  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTP
        sign (ExtRat.Number r)) := by
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  simp [UnpackedFloat.toRat_eq_toRat']
  by_cases hzero : x.isZero
  · simp [hzero, hs]
    rw [roundRTP_zero]
    · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
      · grind only
    · grind only
  · by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
    · simp [hover]
      have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
      rw [roundRTP_eq_smtLibUpper_of_ne_zero x.toRat' hx0, if_neg hx0]
      -- magnitude bound at overflow, plus the sign/value relationship
      have hmag : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs :=
        UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm hzero hover
      have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
      have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat
          < (2 : Rat) ^ (maxNormalExp ep + 1) := PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
      by_cases hsign : x.sign = false
      · -- positive overflow: circuit `mkInfinity`, spec `upper = +∞`
        have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
        have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
        rw [habs] at hmag
        have hUinf : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
            = PackedFloat.getInfinity ep sp false := by
          rw [smtLibUpper_eq_upper ep sp (by grind) hs _ (by simp),
            upper_Number_eq_getInfinity_of_maxNormalNumber_lt (by grind) hs x.toRat' (by grind)]
        rw [hUinf]
        simp [blastRounderSpecialCaseOverflow, hsign]
        apply EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign
        · simp [EUnpackedFloat.mkInfinity]
        · rw [PackedFloat.isInfinite_getInfinity]; simp [hs]
        · simp [EUnpackedFloat.mkInfinity, EUnpackedFloat.sign, PackedFloat.sign_getInfinity]
      · -- negative overflow: circuit `mkNumber (maxNormal … true)`, spec `upper = maxNormal true`
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
        rw [hU]
        simp [blastRounderSpecialCaseOverflow, hsignt]
        apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
        · simp
        · simp only [EUnpackedFloat.num_mkNumber]
          apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
          · exact UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber hs (by omega) hep (Nat.le_refl _)
          · simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]
    · simp [hover]
      by_cases hx0 : x.toRat' = 0
      · simp [hx0]
        rw [roundRTP_zero]
        · apply EUnpackedFloat.Rel_of_Rel_of_isZero_of_isZero_of_eq_sign
          · simp
          · simp; grind only
          · simp
        · grind
      · simp [hx0]
        rw [roundRTP_eq_smtLibUpper_of_ne_zero x.toRat' hx0]
        by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp
        · -- (early) underflow: `upper` is `minSubnormal`/`-0` depending on sign
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
          · -- positive tiny: circuit `mkNumber minSubnormal`, spec `upper = minSubnormal`
            have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
            have habs : x.toRat'.abs = x.toRat' := by rw [Rat.abs, if_pos (by grind)]
            rw [habs] at hmag
            have hpos : 0 < x.toRat' := by grind
            rw [smtLibUpper_eq_minSub_of_pos_of_lt ep sp he hs x.toRat' hpos (by grind)]
            simp [blastRounderSpecialCaseUnderflow, hsign]
            apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
            · simp
            · simp only [EUnpackedFloat.num_mkNumber]
              apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
              · exact UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber
                  ep sp (exponentWidth ep sp) he hs (Nat.le_refl _)
              · simp [UnpackedFloat.minSubnormalForPackedFloat, PackedFloat.sign_minSubnormalNumber]
          · -- negative tiny: circuit `mkZero true`, spec `upper = -0`
            have hsignt : x.sign = true := by grind
            have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
            have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
            rw [habs] at hmag
            rw [smtLibUpper_eq_getZero_of_nonpos_of_gt ep sp he hs x.toRat' (by grind) (by grind)]
            simp [blastRounderSpecialCaseUnderflow, hsignt]
            apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
            grind
        · -- main case: circuit `blastUpper`, spec `upper`
          simp [hunder]
          simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTP]
          rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x
              hzero hxnorm (by simpa using hunder) (by simpa using hover)]
          rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind)
              (by grind) (by grind) (by grind)]
          exact UnpackedFloat.blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm (by simpa using hover)

/-- **Finiteness companion of `toExtRat_round_Rel_smtLibRound_of_RTP`.**
When the circuit is a finite `Number`, the SMT-LIB `RTP` round of the exact value
is neither NaN nor infinite.  Analogue of `blastSmtLibRound_finite_of_RNE`. -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RTP
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true) :
    (x.blastSmtLibRound ep sp .RTP : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTP
            sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTP
            sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  subst r sign
  have hzero : x.isZero = false := UnpackedFloat.isZero_eq_false_of_msb x hmsb
  have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
  have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
  simp only [SmtLibSemantics.RoundMethod.round_RTP_eq, UnpackedFloat.toRat_eq_toRat']
  rw [roundRTP_eq_smtLibUpper_of_ne_zero x.toRat' hx0]
  -- Reduce the circuit-state hypothesis through `blastSmtLibRound`'s branches.
  rw [UnpackedFloat.blastSmtLibRound, if_neg (by simp [hzero])] at hstate
  by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
  · rw [if_pos hover] at hstate
    have hmag : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs :=
      UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm (by simp [hzero]) hover
    have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat
        < (2 : Rat) ^ (maxNormalExp ep + 1) := PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
    by_cases hsign : x.sign = false
    · -- positive overflow: circuit is `∞` (state `Infinity`), contradicting `state = Number`.
      simp [blastRounderSpecialCaseOverflow, hsign, EUnpackedFloat.mkInfinity] at hstate
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
      rw [hU]
      refine ⟨PackedFloat.not_isNaN_maxNormalNumber ep sp true (by grind), ?_⟩
      simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
        (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he true)
  · rw [if_neg (by simpa using hover)] at hstate
    by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
    · -- underflow: spec `upper` is `minSubnormal false` / `getZero true`, both finite.
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
        rw [smtLibUpper_eq_minSub_of_pos_of_lt ep sp he hs x.toRat' hpos (by grind)]
        refine ⟨PackedFloat.not_isNaN_minSubnormalNumber ep sp false (by grind) hs, ?_⟩
        simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
          (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hs)
      · have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        have habs : x.toRat'.abs = -x.toRat' := by rw [Rat.abs, if_neg (by grind)]
        rw [habs] at hmag
        rw [smtLibUpper_eq_getZero_of_nonpos_of_gt ep sp he hs x.toRat' (by grind) (by grind)]
        refine ⟨?_, ?_⟩
        · rw [PackedFloat.isNaN_getZero]; simp; grind
        · rw [PackedFloat.isInfinite_getZero]; simp; grind
    · -- main case: circuit finite `blastUpper` ⟹ spec `upper` is finite.
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
      simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRTP,
        EUnpackedFloat.state_normalize] at hstate
      have hUnan : ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
        simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs _ (by simp)
      have hUfin := UnpackedFloat.not_isInfinite_smtLibUpper_of_blastUpper_state_Number
        hep hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hstate
      rw [hztoRat] at hUfin
      exact ⟨hUnan, hUfin⟩

/-- info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTP' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTP

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_finite_of_RTP' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_finite_of_RTP

/-- **StickyEquiv RTP bridge.** As `toExtRat_round_Rel_smtLibRound_of_RTP`, but the
exact value `r` need only be a sticky compression of `x.toRat`.  Analogue of
`UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`. -/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_RTP_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RTP : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTP sign (ExtRat.Number r)) := by
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RTP x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RTP sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTP he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm

/-- **Finiteness companion of `blastSmtLibRound_Rel_round_of_RTP_of_stickyEquiv`.**
Analogue of `blastSmtLibRound_finite_of_RNE_of_stickyEquiv`. -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RTP_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RTP : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTP sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RTP sign (ExtRat.Number r)).isInfinite := by
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
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RTP x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RTP sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.blastSmtLibRound_finite_of_RTP he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm hmsb hstate

end Fp
