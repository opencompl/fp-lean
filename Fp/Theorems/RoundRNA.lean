import Fp.Theorems.RoundEquiv

/-!
# RNA (round nearest, ties away) rounding: circuit ↔ SMT-LIB spec bridges

Mirror of `Fp/Theorems/RoundRTP.lean` for the `RNA` mode.  See that file for the
layering rationale (these live above `RoundEquiv` to avoid an import cycle).

For `RNA`, the circuit `blastSmtLibRoundRNA` and the spec `roundRNA` both branch on
`sign × lowerHalf × tieBreak` (ties always resolve away from zero).  This is the
hardest of the four directed/nearest modes: it reuses the existing predicate
bridges `blastIsLowerHalf_eq` / `blastIsTieBreak_eq` (the same ones RNE uses) with
a full sign-split case analysis, but — unlike RNE — never consults the isEven
parity of the candidates.  Overflow/underflow are the RNE-style `∞`/`0` and reuse
the RNE boundary lemmas directly.
-/

namespace Fp

/--
Rounding (RNA) any number of magnitude at least `2 ^ (maxNormalExp ep + 1)`
produces the infinity whose sign is the sign of the number.  Clone of
`roundRNE_eq_infinity_of_maxNormalExp_lt` with the `roundRNA` arm selection.
-/
private theorem roundRNA_eq_infinity_of_maxNormalExp_lt
  (he : 1 < ep)
  (hep : 2 < ep)
  (hs : 0 < sp)
  (r : Rat)
  (hsign : sign = decide (r < 0))
  (hr : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ r.abs) :
  ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
        (ExtRat.Number r)) = PackedFloat.getInfinity ep sp sign := by
  have hep0 : 0 < ep := by omega
  have hsp1 : 0 < sp + 1 := by omega
  have hpow_pos : (0 : Rat) < 2 ^ (maxNormalExp ep + 1) := Rat.two_pow_pos _
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    simp [Rat.abs] at hr
    grind
  have hfinN := PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp) he false
  have hfinN1 := PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp + 1) he false
  have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat < 2 ^ (maxNormalExp ep + 1) :=
    PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
  have hmaxlt1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < 2 ^ (maxNormalExp ep + 1) :=
    PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hsp1
  have hmono : (PackedFloat.maxNormalNumber ep sp false).toRat
      < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat :=
    PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ hep hs
  have hnotnan : ¬ (SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number r)) := by
    simp
  have hnotzero : ¬ (SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r)) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]
    simp [hr0]
  by_cases hneg : r < 0
  case neg =>
    -- positive case: `2 ^ (maxNormalExp + 1) ≤ r`
    have habs : r.abs = r := by
      simp [Rat.abs, hneg]
    rw [habs] at hr
    have hsignF : sign = false := by simp [hsign, hneg]
    -- evaluations of the four bounds
    have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false := by
      rw [smtLibLower_eq_lower ep sp hep0 hs _ (by simp),
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hs r (by grind)]
    have hL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.maxNormalNumber ep (sp + 1) false := by
      rw [smtLibLower_eq_lower ep (sp + 1) hep0 hsp1 _ (by simp),
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hsp1 r (by grind)]
    have hU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.getInfinity ep sp false := by
      rw [smtLibUpper_eq_upper ep sp hep0 hs _ (by simp),
        upper_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hs r (by grind)]
    have hU1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.getInfinity ep (sp + 1) false := by
      rw [smtLibUpper_eq_upper ep (sp + 1) hep0 hsp1 _ (by simp),
        upper_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hsp1 r (by grind)]
    -- conditions
    have hLH : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq, hL, hL1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_toRat_of hfinN, PackedFloat.toExtRat'_eq_toRat_of hfinN1]
      simp only [ExtRat.Number.injEq]
      grind
    have hRU : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).upper (ExtRat.Number r) = PackedFloat.getInfinity ep sp false := by
      rw [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq, hU]
    have hgt : SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.gtZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      grind
    rw [SmtLibSemantics.RoundMethod.roundRNA]
    rw [if_neg hnotnan, if_pos ⟨hgt, hLH⟩, hRU, hsignF]
  case pos =>
    -- negative case: `r ≤ -2 ^ (maxNormalExp + 1)`
    have habs : r.abs = -r := by
      rw [Rat.abs, if_neg (by grind)]
    rw [habs] at hr
    have hsignT : sign = true := by simp [hsign, hneg]
    have hflip : (PackedFloat.maxNormalNumber ep sp true).toRat
        = - (PackedFloat.maxNormalNumber ep sp false).toRat := by
      rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
    have hflip1 : (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat
        = - (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat := by
      rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
    -- evaluations of the four bounds
    have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.getInfinity ep sp true := by
      rw [smtLibLower_eq_lower ep sp hep0 hs _ (by simp),
        lower_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hs r (by grind)]
    have hL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.getInfinity ep (sp + 1) true := by
      rw [smtLibLower_eq_lower ep (sp + 1) hep0 hsp1 _ (by simp),
        lower_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hsp1 r (by grind)]
    have hU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp true := by
      rw [smtLibUpper_eq_upper ep sp hep0 hs _ (by simp), upper, ExtRat.ExtRat.neg_number,
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hs (-r) (by grind),
        PackedFloat.neg_maxNormalNumber_false']
    have hU1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.maxNormalNumber ep (sp + 1) true := by
      rw [smtLibUpper_eq_upper ep (sp + 1) hep0 hsp1 _ (by simp), upper, ExtRat.ExtRat.neg_number,
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hsp1 (-r) (by grind),
        PackedFloat.neg_maxNormalNumber_false']
    -- conditions
    have hLH : ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq, hL, hL1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1]
    have hRL : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lower (ExtRat.Number r) = PackedFloat.getInfinity ep sp true := by
      rw [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq, hL]
    have hlz : SmtLibSemantics.ExtendedNumber.ltZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.ltZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      exact hneg
    have hng : ¬ SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.gtZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      grind
    rw [SmtLibSemantics.RoundMethod.roundRNA]
    rw [if_neg hnotnan,
      if_neg (fun h => hng h.1),
      if_neg (fun h => hng h.1),
      if_neg hnotzero,
      if_neg (fun h => absurd hLH h.2.1),
      if_pos ⟨hlz, Or.inl hLH⟩, hRL, hsignT]

/--
Rounding (RNA) any number whose absolute value is strictly smaller than *half the
minimum subnormal* of the target format produces a zero, whose sign is the sign of
the number itself.  Clone of `roundRNE_eq_zero_of_lt_minNormalExp` with the
`roundRNA` arm selection.
-/
private theorem roundRNA_eq_zero_of_lt_minNormalExp
  (he : 1 < ep)
  (hs : 0 < sp)
  (r : Rat)
  (hsign : sign = decide (r < 0))
  (hr : r.abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1)) :
  ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
        (ExtRat.Number r)) = PackedFloat.getZero ep sp sign := by
  have he' : 0 < ep := by grind
  have hsp1 : 0 < sp + 1 := by omega
  have hB : (PackedFloat.minSubnormalNumber ep sp false).toRat = (2 : Rat) ^ (minSubnormalExp ep sp) := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep sp he hs]; congr 1
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hA : (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat
      = (2 : Rat) ^ (minSubnormalExp ep sp - 1) := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep (sp + 1) he hsp1]; congr 1
    simp only [minSubnormalExp, maxSubnormalExp]; push_cast; grind
  have hAB : (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat
      < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
    rw [hA, hB,
      show (2 : Rat) ^ (minSubnormalExp ep sp) = 2 ^ (minSubnormalExp ep sp - 1) * 2 from by
        rw [← Rat.zpow_add_one (by grind : (2 : Rat) ≠ 0)]; congr 1; grind]
    have hpos : (0 : Rat) < 2 ^ (minSubnormalExp ep sp - 1) := Rat.two_pow_pos _
    grind
  have hbnd : r < (2 : Rat) ^ (minSubnormalExp ep sp - 1)
      ∧ -(2 : Rat) ^ (minSubnormalExp ep sp - 1) < r := by
    simp only [Rat.abs_def_lt] at hr; split at hr <;> grind
  have hrlt1 : r < (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat := by
    rw [hA]; exact hbnd.1
  have hrgt1 : -(PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat < r := by
    rw [hA]; exact hbnd.2
  have hrlt : r < (PackedFloat.minSubnormalNumber ep sp false).toRat := by grind
  have hrgt : -(PackedFloat.minSubnormalNumber ep sp false).toRat < r := by grind
  have hgz : ∀ (S : Nat) (b : Bool), (PackedFloat.getZero ep S b).toExtRat = ExtRat.Number 0 :=
    fun S b => by rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_getZero b he']
  have hms : ∀ (S : Nat) (b : Bool), 0 < S →
      (PackedFloat.minSubnormalNumber ep S b).toExtRat
        = ExtRat.Number ((PackedFloat.minSubnormalNumber ep S b).toRat) :=
    fun S b hS => by rw [PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_eq_toRat_of
        (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep S b (by grind) hS)]
  have hmt : ∀ (S : Nat), 0 < S → (PackedFloat.minSubnormalNumber ep S true).toRat
      = -(PackedFloat.minSubnormalNumber ep S false).toRat := fun S hS => by
    have hflip : -(PackedFloat.minSubnormalNumber ep S false) = PackedFloat.minSubnormalNumber ep S true := by
      simp [PackedFloat.neg_def, PackedFloat.neg, PackedFloat.minSubnormalNumber]
    rw [← hflip, PackedFloat.toRat_neg]
  by_cases hr0 : r = 0
  · subst hr0; simpa using (roundRNA_zero (eout := ep) (sout := sp) (zeroSign := sign) he')
  have hnotnan : ¬ (SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number r)) := by simp
  have hnotzero : ¬ (SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r)) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hr0]
  by_cases hrpos : 0 < r
  · -- `r > 0`: `lowerHalf` holds, so RNA rounds down to `+0`.
    have hsignF : sign = false := by simp [hsign, hrpos]; grind
    have hLsp : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.getZero ep sp false :=
      smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he hs r (Rat.le_of_lt hrpos) hrlt
    have hLsp1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.getZero ep (sp + 1) false :=
      smtLibLower_eq_getZero_of_nonneg_of_lt ep (sp + 1) he hsp1 r (Rat.le_of_lt hrpos) hrlt1
    have hUsp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.minSubnormalNumber ep sp false :=
      smtLibUpper_eq_minSub_of_pos_of_lt ep sp he hs r hrpos hrlt
    have hUsp1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.minSubnormalNumber ep (sp + 1) false :=
      smtLibUpper_eq_minSub_of_pos_of_lt ep (sp + 1) he hsp1 r hrpos hrlt1
    have hLH : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) := by
      rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq, hLsp, hLsp1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [hgz, hgz]
    have hRL : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lower (ExtRat.Number r) = PackedFloat.getZero ep sp false := by
      rw [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq, hLsp]
    have hgt : SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.gtZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      exact hrpos
    rw [SmtLibSemantics.RoundMethod.roundRNA]
    rw [if_neg hnotnan,
      if_neg (fun h => absurd hLH h.2),
      if_pos ⟨hgt, hLH⟩, hRL, hsignF]
  · -- `r < 0`: neither `lowerHalf` nor tie, so RNA rounds up (away from zero) to `-0`.
    have hrneg : r < 0 := by grind
    have hsignT : sign = true := by simp [hsign, hrneg]
    have hLsp : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.minSubnormalNumber ep sp true :=
      smtLibLower_eq_minSub_of_neg_of_gt ep sp he hs r hrneg hrgt
    have hLsp1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.minSubnormalNumber ep (sp + 1) true :=
      smtLibLower_eq_minSub_of_neg_of_gt ep (sp + 1) he hsp1 r hrneg hrgt1
    have hUsp : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.getZero ep sp true :=
      smtLibUpper_eq_getZero_of_nonpos_of_gt ep sp he hs r (Rat.le_of_lt hrneg) hrgt
    have hUsp1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.getZero ep (sp + 1) true :=
      smtLibUpper_eq_getZero_of_nonpos_of_gt ep (sp + 1) he hsp1 r (Rat.le_of_lt hrneg) hrgt1
    have hLH : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) := by
      rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq, hLsp, hLsp1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [hms _ _ hs, hms _ _ hsp1, hmt _ hs, hmt _ hsp1]
      simp only [ExtRat.Number.injEq]
      grind
    have hTB : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq,
        SmtLibSemantics.smtLibV_upper_eq, hLsp, hLsp1, hUsp, hUsp1]
      rw [hgz, hgz, hms _ _ hs, hms _ _ hsp1, hmt _ hs, hmt _ hsp1]
      have h1 : (ExtRat.Number (-(PackedFloat.minSubnormalNumber ep sp false).toRat)
          < ExtRat.Number (-(PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat)) := by
        simp only [ExtRat.num_lt_num_iff, decide_eq_true_eq]; grind
      have h2 : ¬ ((ExtRat.Number 0 : ExtRat) < ExtRat.Number 0) := by simp
      intro hcontra
      rw [hcontra] at h1
      exact h2 h1
    have hRU : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).upper (ExtRat.Number r) = PackedFloat.getZero ep sp true := by
      rw [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq, hUsp]
    have hlz : SmtLibSemantics.ExtendedNumber.ltZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.ltZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      exact hrneg
    have hng : ¬ SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.gtZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      grind
    rw [SmtLibSemantics.RoundMethod.roundRNA]
    rw [if_neg hnotnan,
      if_neg (fun h => hng h.1),
      if_neg (fun h => hng h.1),
      if_neg hnotzero,
      if_pos ⟨hlz, hLH, hTB⟩, hRU, hsignT]

/-- For a nonzero rational, the SMT-LIB `RNA` rounder is `lower` / `upper` according
to a clean `lowerHalf` / `tieBreak` split (ties always resolving away from zero). -/
private theorem roundRNA_eq_of_ne_zero {eout sout : Nat} {sign : Bool}
    (r : Rat) (hr0 : r ≠ 0) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).roundRNA sign (ExtRat.Number r)
      = if 0 < r then
          (if (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)
            then (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout)
            else (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat eout sout))
        else
          (if (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)
                ∨ (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)
            then (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout)
            else (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat eout sout)) := by
  have hnotnan : ¬ (SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number r)) := by simp
  have hnotzero : ¬ (SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r)) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hr0]
  rw [SmtLibSemantics.RoundMethod.roundRNA, if_neg hnotnan]
  by_cases hpos : 0 < r
  · have hgt : SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.gtZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      exact hpos
    rw [if_pos hpos]
    by_cases hlh : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)
    · rw [if_neg (fun h => absurd hlh h.2), if_pos ⟨hgt, hlh⟩, if_pos hlh,
        SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
    · rw [if_pos ⟨hgt, hlh⟩, if_neg hlh,
        SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq]
  · have hneg : r < 0 := by grind
    have hlz : SmtLibSemantics.ExtendedNumber.ltZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.ltZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      exact hneg
    have hng : ¬ SmtLibSemantics.ExtendedNumber.gtZero (ExtRat.Number r) := by
      rw [SmtLibSemantics.instExtendedRat.gtZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number_lt_Number_iff]
      grind
    rw [if_neg hpos, if_neg (fun h => hng h.1), if_neg (fun h => hng h.1), if_neg hnotzero]
    by_cases hor : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)
          ∨ (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)
    · rw [if_neg (fun h => hor.elim (fun hl => h.2.1 hl) (fun ht => h.2.2 ht)),
        if_pos ⟨hlz, hor⟩, if_pos hor,
        SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
    · have hnl : ¬ (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
          SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) := fun h => hor (Or.inl h)
      have hnt : ¬ (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV
          SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) := fun h => hor (Or.inr h)
      rw [if_pos ⟨hlz, hnl, hnt⟩, if_neg hor,
        SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq]

/-- **Exact-value RNA bridge.** Analogue of `toExtRat_round_Rel_smtLibRound_of_RNE`. -/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNA
    (he : 1 < ep)
    (hep : 2 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RNA  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNA
        sign (ExtRat.Number r)) := by
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  simp [UnpackedFloat.toRat_eq_toRat']
  by_cases hzero : x.isZero
  · simp [hzero, hs]
    rw [roundRNA_zero]
    · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
      · grind only
    · grind only
  · have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
    have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
    · simp [hover]
      simp [blastRounderSpecialCaseOverflow]
      simp [hx0]
      rw [roundRNA_eq_infinity_of_maxNormalExp_lt]
      · apply EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign
        · simp
        · grind
        · simp
      · simp [he]
      · simp [hep]
      · simp [hs]
      · exact UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
      · exact UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm hzero hover
    · simp [hover]
      by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp
      · simp [hunder]
        simp [blastRounderSpecialCaseUnderflow]
        rw [roundRNA_eq_zero_of_lt_minNormalExp]
        · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
          · grind only
        · simp [he]
        · simp [hs]
        · exact UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
        · exact UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder
      · -- main case
        simp [hunder]
        have hoverF : x.blastIsEarlyOverflowNonneg ep sp = false := by simpa using hover
        have hunderF : x.blastIsEarlyUnderflowNonneg ep sp = false := by simpa using hunder
        have hsig : x.sig ≠ 0#su := by simpa [UnpackedFloat.isZero] using hzero
        have htnorm := normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
          he hs heu hsu x hzero hxnorm
        have htmsb : (x.truncateFittingExponent ep sp).sig.msb = true :=
          (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
        have htover : (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
          rw [blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x hoverF hunderF]; exact hoverF
        have htunder : (x.truncateFittingExponent ep sp).blastIsEarlyUnderflowNonneg ep sp = false := by
          rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs (Nat.le_refl _)
              (x.truncateFittingExponent ep sp),
            toInt_ex_truncateFittingExponent he hs heu x hoverF hunderF,
            ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x]
          exact hunderF
        have htoRat : (x.truncateFittingExponent ep sp).toRat' = x.toRat' :=
          toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
            he hs heu hoverF hunderF
        have closeU : (((x.truncateFittingExponent ep sp).blastUpper ep sp).normalize).Rel
            (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
          rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x
              hzero hxnorm hunderF hoverF,
            blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind)
              hoverF hunderF]
          exact UnpackedFloat.blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm hoverF
        have closeL : (((x.truncateFittingExponent ep sp).blastLower ep sp).normalize).Rel
            (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
          rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x
              hzero hxnorm hunderF hoverF,
            blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind)
              hoverF hunderF]
          exact UnpackedFloat.blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm hoverF
        rw [if_neg hx0]
        rw [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRNA,
          sign_truncateFittingExponent,
          blastIsLowerHalf_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
            htnorm htmsb htunder htover, htoRat]
        rw [roundRNA_eq_of_ne_zero x.toRat' hx0]
        by_cases hsign : x.sign = false
        · -- positive
          have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
          have hpos : 0 < x.toRat' := by grind
          rw [if_pos hpos]
          by_cases hlh : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
              SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
          · rw [if_pos hlh]
            simp only [hsign, hlh, decide_true, decide_false, Bool.not_true, Bool.not_false,
              Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
              Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true]
            exact closeL
          · rw [if_neg hlh]
            simp only [hsign, hlh, decide_true, decide_false, Bool.not_true, Bool.not_false,
              Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
              Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true]
            exact closeU
        · -- negative
          have hsignt : x.sign = true := by grind
          have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
          rw [if_neg (show ¬ (0 < x.toRat') by grind)]
          by_cases hnrd : (x.truncateFittingExponent ep sp).needsRounding ep sp = true
          · rw [blastIsTieBreak_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
                htnorm htmsb htunder htover, hnrd, Bool.true_and, htoRat]
            by_cases hor : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
                  ∨ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat')
            · rw [if_pos hor]
              have hld : (decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat'))
                  || decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat'))) = true := by
                rcases hor with h | h
                · simp [h]
                · simp [h]
              have harm3 : (!decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat'))
                  && !decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat'))) = false := by
                rcases hor with h | h
                · simp [h]
                · simp [h]
              simp only [hsignt, harm3, decide_true, decide_false, Bool.not_true, Bool.not_false,
                Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
                Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
                Bool.true_eq_false]
              rw [hld]
              exact closeL
            · rw [if_neg hor]
              have hnl : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := fun h => hor (Or.inl h)
              have hnt : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                  SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') := fun h => hor (Or.inr h)
              simp only [hsignt, hnl, hnt, decide_true, decide_false, Bool.not_true, Bool.not_false,
                Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
                Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true]
              exact closeU
          · -- representable: `blastIsLowerHalf = true`, so circuit rounds to `blastLower`; and
            -- `lowerHalf` holds, so the SMT round selects `lower`.
            have hnrd' : (x.truncateFittingExponent ep sp).needsRounding ep sp = false := by grind
            have hLHtrue : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
              have h1 := blastIsLowerHalf_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
                htnorm htmsb htunder htover
              rw [blastIsLowerHalf_eq_true_of_not_needsRounding _ hnrd', htoRat] at h1
              exact of_decide_eq_true h1.symm
            rw [if_pos (Or.inl hLHtrue)]
            simp only [hsignt, hLHtrue, decide_true, decide_false, Bool.not_true, Bool.not_false,
              Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
              Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true]
            exact closeL

/-- **Finiteness companion of `toExtRat_round_Rel_smtLibRound_of_RNA`.** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RNA
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true) :
    (x.blastSmtLibRound ep sp .RNA : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNA
            sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNA
            sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  subst r sign
  have hzero : x.isZero = false := UnpackedFloat.isZero_eq_false_of_msb x hmsb
  have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
  have hsgn := UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
  simp only [SmtLibSemantics.RoundMethod.round_RNA_eq, UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.blastSmtLibRound, if_neg (by simp [hzero])] at hstate
  by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
  · -- overflow ⟹ circuit is `mkInfinity` (state `Infinity`), contradicting `state = Number`.
    rw [if_pos hover,
      show blastRounderSpecialCaseOverflow (tep := ep) (tsp := sp) .RNA x.sign
        = EUnpackedFloat.mkInfinity x.sign from rfl] at hstate
    simp [EUnpackedFloat.mkInfinity] at hstate
  · rw [if_neg (by simpa using hover)] at hstate
    by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
    · -- underflow ⟹ round result is `getZero`, which is finite.
      rw [roundRNA_eq_zero_of_lt_minNormalExp he hs x.toRat'
          (UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0)
          (UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder)]
      refine ⟨?_, ?_⟩
      · simp [PackedFloat.isNaN_getZero] <;> grind
      · simp [PackedFloat.isInfinite_getZero] <;> grind
    · -- main branch: round result collapses to `upper`/`lower`; finiteness from the helpers.
      rw [if_neg (by simpa using hunder)] at hstate
      simp only [Bool.not_eq_true] at hover hunder
      have hoverF : x.blastIsEarlyOverflowNonneg ep sp = false := hover
      have hunderF : x.blastIsEarlyUnderflowNonneg ep sp = false := hunder
      have hsig : x.sig ≠ 0#su := by simpa [UnpackedFloat.isZero] using hzero
      have htnorm := normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
        he hs heu hsu x (by simp [hzero]) hxnorm
      have htmsb : (x.truncateFittingExponent ep sp).sig.msb = true :=
        (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
      have htover : (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
        rw [blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x hoverF hunderF]; exact hoverF
      have htunder : (x.truncateFittingExponent ep sp).blastIsEarlyUnderflowNonneg ep sp = false := by
        rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs (Nat.le_refl _)
            (x.truncateFittingExponent ep sp),
          toInt_ex_truncateFittingExponent he hs heu x hoverF hunderF,
          ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x]
        exact hunderF
      have htoRat : (x.truncateFittingExponent ep sp).toRat' = x.toRat' :=
        toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
          he hs heu hoverF hunderF
      have hUnan : ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
        simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs _ (by simp)
      have hLnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
        simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp)
      have hUfin : ((x.truncateFittingExponent ep sp).blastUpper ep sp).state = State.Number →
          ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isInfinite := by
        intro hsU
        have := UnpackedFloat.not_isInfinite_smtLibUpper_of_blastUpper_state_Number
          hep hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hsU
        rwa [htoRat] at this
      have hLfin : ((x.truncateFittingExponent ep sp).blastLower ep sp).state = State.Number →
          ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isInfinite := by
        intro hsL
        have := UnpackedFloat.not_isInfinite_smtLibLower_of_blastLower_state_Number
          hep hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hsL
        rwa [htoRat] at this
      rw [roundRNA_eq_of_ne_zero x.toRat' hx0]
      simp only [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRNA,
        sign_truncateFittingExponent,
        blastIsLowerHalf_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
          htnorm htmsb htunder htover, htoRat] at hstate
      by_cases hsign : x.sign = false
      · -- positive
        have hnneg : ¬ (x.toRat' < 0) := by rw [hsign] at hsgn; simpa using hsgn.symm
        have hpos : 0 < x.toRat' := by grind
        rw [if_pos hpos]
        by_cases hlh : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
            SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
        · rw [if_pos hlh]
          simp only [hsign, hlh, decide_true, decide_false, Bool.not_true, Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
            Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
            EUnpackedFloat.state_normalize] at hstate
          exact ⟨hLnan, hLfin hstate⟩
        · rw [if_neg hlh]
          simp only [hsign, hlh, decide_true, decide_false, Bool.not_true, Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
            Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
            EUnpackedFloat.state_normalize] at hstate
          exact ⟨hUnan, hUfin hstate⟩
      · -- negative
        have hsignt : x.sign = true := by grind
        have hneg : x.toRat' < 0 := by rw [hsignt] at hsgn; simpa using hsgn
        rw [if_neg (show ¬ (0 < x.toRat') by grind)]
        by_cases hnrd : (x.truncateFittingExponent ep sp).needsRounding ep sp = true
        · rw [blastIsTieBreak_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover, hnrd, Bool.true_and, htoRat] at hstate
          by_cases hor : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
              SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
                ∨ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
              SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat')
          · rw [if_pos hor]
            have hld : (decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat'))
                || decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat'))) = true := by
              rcases hor with h | h
              · simp [h]
              · simp [h]
            have harm3 : (!decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat'))
                && !decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat'))) = false := by
              rcases hor with h | h
              · simp [h]
              · simp [h]
            simp only [hsignt, harm3, decide_true, decide_false, Bool.not_true, Bool.not_false,
              Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
              Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
              Bool.true_eq_false] at hstate
            rw [hld, EUnpackedFloat.state_normalize] at hstate
            exact ⟨hLnan, hLfin hstate⟩
          · rw [if_neg hor]
            have hnl : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := fun h => hor (Or.inl h)
            have hnt : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') := fun h => hor (Or.inr h)
            simp only [hsignt, hnl, hnt, decide_true, decide_false, Bool.not_true, Bool.not_false,
              Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
              Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
              Bool.true_eq_false, EUnpackedFloat.state_normalize] at hstate
            exact ⟨hUnan, hUfin hstate⟩
        · -- representable
          have hnrd' : (x.truncateFittingExponent ep sp).needsRounding ep sp = false := by grind
          have hLHtrue : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
              SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
            have h1 := blastIsLowerHalf_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover
            rw [blastIsLowerHalf_eq_true_of_not_needsRounding _ hnrd', htoRat] at h1
            exact of_decide_eq_true h1.symm
          rw [if_pos (Or.inl hLHtrue)]
          simp only [hsignt, hLHtrue, decide_true, decide_false, Bool.not_true, Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true,
            Bool.or_false, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
            EUnpackedFloat.state_normalize] at hstate
          exact ⟨hLnan, hLfin hstate⟩

/-- info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNA' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNA

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_finite_of_RNA' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_finite_of_RNA

/-- **StickyEquiv RNA bridge.** Analogue of
`UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`. -/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_RNA_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RNA : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNA sign (ExtRat.Number r)) := by
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RNA x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RNA sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNA he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm

/-- **Finiteness companion of `blastSmtLibRound_Rel_round_of_RNA_of_stickyEquiv`.** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RNA_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RNA : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNA sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNA sign (ExtRat.Number r)).isInfinite := by
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
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RNA x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RNA sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.blastSmtLibRound_finite_of_RNA he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm hmsb hstate

end Fp
