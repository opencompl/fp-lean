import Fp.Theorems.UnpackedFloat.Round.IsEvenUpperLower

namespace Fp


/--
Rounding (RNE) any number of magnitude at least `2 ^ (maxNormalExp ep + 1)`
produces the infinity whose sign is the sign of the number.

NOTE (statement corrected): the original hypothesis was
`2 ^ maxNormalExp ep < r.abs`, which does NOT force rounding to infinity
(counterexample `(ep, sp) = (3, 2)`, `r = 9`: `lower = 8`, `upper = 10`,
RNE returns `8`). The hypothesis was strengthened to
`2 ^ (maxNormalExp ep + 1) ≤ r.abs` (dischargeable at the call site from
`maxNormalExp ep < x.ex.toInt` and a normalized significand). Additionally
`hsign : sign = decide (r < 0)` was ADDED: without
`hsign` the conclusion is false for, e.g., positive `r` and `sign = true`
(the result `+∞` does not depend on `sign` for nonzero `r`).
-/
theorem roundRNE_eq_infinity_of_maxNormalExp_lt
  (he : 1 < ep)
  (hs : 0 < sp)
  (r : Rat)
  (hsign : sign = decide (r < 0))
  (hr : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ r.abs) :
  ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
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
    PackedFloat.toRat_maxNormalNumber_lt_two_pow he hs
  have hmaxlt1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < 2 ^ (maxNormalExp ep + 1) :=
    PackedFloat.toRat_maxNormalNumber_lt_two_pow he hsp1
  have hmono : (PackedFloat.maxNormalNumber ep sp false).toRat
      < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat :=
    PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ he hs
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
    have hTB : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq,
        SmtLibSemantics.smtLibV_upper_eq, hL, hL1, hU, hU1]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_toRat_of hfinN, PackedFloat.toExtRat'_eq_toRat_of hfinN1,
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1]
      have h1 : (ExtRat.Number (PackedFloat.maxNormalNumber ep sp false).toRat
          < ExtRat.Number (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat) := by
        simp [hmono]
      have h2 : ¬ ((ExtRat.Infinity false : ExtRat) < ExtRat.Infinity false) := by
        simp
      intro hcontra
      rw [hcontra] at h1
      exact h2 h1
    have hRU : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).upper (ExtRat.Number r) = PackedFloat.getInfinity ep sp false := by
      rw [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq, hU]
    rw [SmtLibSemantics.RoundMethod.roundRNE]
    rw [if_neg hnotnan, if_pos ⟨hnotzero, by simp [hLH], by simp [hTB]⟩, hRU, hsignF]
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
    have hTB : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq,
        SmtLibSemantics.smtLibV_upper_eq, hL, hL1, hU, hU1]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1,
        PackedFloat.toExtRat'_eq_toRat_of (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he true),
        PackedFloat.toExtRat'_eq_toRat_of (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he true)]
      have h1 : ¬ ((ExtRat.Infinity true : ExtRat) < ExtRat.Infinity true) := by
        simp
      have h2 : (ExtRat.Number (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat
          < ExtRat.Number (PackedFloat.maxNormalNumber ep sp true).toRat) := by
        have : (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat
            < (PackedFloat.maxNormalNumber ep sp true).toRat := by
          rw [hflip, hflip1]
          grind
        simp [this]
      intro hcontra
      rw [← hcontra] at h2
      exact h1 h2
    have hRL : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lower (ExtRat.Number r) = PackedFloat.getInfinity ep sp true := by
      rw [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq, hL]
    rw [SmtLibSemantics.RoundMethod.roundRNE]
    rw [if_neg hnotnan,
      if_neg (by intro h; exact absurd hLH (by simpa using h.2.1)),
      if_neg (by intro h; exact hTB h.2.1),
      if_neg (by intro h; exact hTB h.2.1),
      if_pos ⟨hnotzero, hLH⟩, hRL, hsignT]

/--
An overflowing, normalized, nonzero float has magnitude strictly above `2 ^ maxNormalExp ep`.
-/
theorem UnpackedFloat.two_pow_maxNormalExp_lt_abs_toRat'
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hzero : ¬ x.isZero)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (2 : Rat) ^ maxNormalExp ep < (x.toRat').abs := by
  -- exponent strictly above maxNormalExp
  have hover' : maxNormalExp ep < x.ex.toInt := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
    grind
  -- the significand is nonzero and normalized, so its msb is set
  have hsig : x.sig ≠ 0#su := by
    simp [UnpackedFloat.isZero] at hzero
    exact hzero
  have hmsb : x.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hle : 2 ^ (su - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hmsb
  -- |toRat'| = sig.toNat * 2 ^ toExpInt
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsignat : (0 : Rat) < (x.sig.toNat : Rat) := by
    have : 0 < x.sig.toNat := by
      have : 0 < 2 ^ (su - 1) := Nat.two_pow_pos _
      omega
    exact_mod_cast this
  have habs : (x.toRat').abs = (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [UnpackedFloat.toRat', Rat.abs]
    cases hsgn : x.sign
    · simp [Bool.toSign]
      intros hlt
      exfalso
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
    · simp [Bool.toSign]
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
  rw [habs]
  -- 2 ^ (su-1) * 2 ^ toExpInt = 2 ^ ex.toInt
  have hexp : x.toExpInt = x.ex.toInt - ((su - 1 : Nat) : Int) := by
    simp [UnpackedFloat.toExpInt]
    omega
  have h1 : ((2 : Rat) ^ ((su - 1 : Nat) : Int)) * (2 : Rat) ^ x.toExpInt = (2 : Rat) ^ x.ex.toInt := by
    rw [Rat.zpow_mul_zpow (by grind)]
    have heq : ((su - 1 : Nat) : Int) + x.toExpInt = x.ex.toInt := by
      rw [hexp]; omega
    rw [heq]
  have key : (2 : Rat) ^ x.ex.toInt ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [← h1]
    apply Rat.mul_le_mul_of_nonneg_right
    · rw [Rat.zpow_natCast]
      have : ((2 ^ (su - 1) : Nat) : Rat) ≤ (x.sig.toNat : Rat) := by
        exact_mod_cast hle
      simpa [Rat.natCast_pow] using this
    · exact Rat.le_of_lt hpos
  have hstrict : (2 : Rat) ^ maxNormalExp ep < (2 : Rat) ^ x.ex.toInt := by
    have h2 : (2 : Rat) * (2 : Rat) ^ maxNormalExp ep = (2 : Rat) ^ (maxNormalExp ep + 1) :=
      Rat.mul_self_zpow_eq_zpow_succ (by grind)
    have h3 : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (2 : Rat) ^ x.ex.toInt :=
      Rat.two_pow_le_two_pow_of_le (by omega)
    have h4 : (0 : Rat) < (2 : Rat) ^ maxNormalExp ep := Rat.two_pow_pos _
    grind
  grind

/--
An overflowing, normalized, nonzero float has magnitude at least `2 ^ (maxNormalExp ep + 1)`.
Strengthened form of `two_pow_maxNormalExp_lt_abs_toRat'`, used to discharge the
corrected hypothesis of `roundRNE_eq_infinity_of_maxNormalExp_lt`.
-/
theorem UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat'
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hzero : ¬ x.isZero)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs := by
  -- exponent strictly above maxNormalExp
  have hover' : maxNormalExp ep < x.ex.toInt := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
    grind
  -- the significand is nonzero and normalized, so its msb is set
  have hsig : x.sig ≠ 0#su := by
    simp [UnpackedFloat.isZero] at hzero
    exact hzero
  have hmsb : x.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hle : 2 ^ (su - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hmsb
  -- |toRat'| = sig.toNat * 2 ^ toExpInt
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsignat : (0 : Rat) < (x.sig.toNat : Rat) := by
    have : 0 < x.sig.toNat := by
      have : 0 < 2 ^ (su - 1) := Nat.two_pow_pos _
      omega
    exact_mod_cast this
  have habs : (x.toRat').abs = (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [UnpackedFloat.toRat', Rat.abs]
    cases hsgn : x.sign
    · simp [Bool.toSign]
      intros hlt
      exfalso
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
    · simp [Bool.toSign]
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
  rw [habs]
  -- 2 ^ (su-1) * 2 ^ toExpInt = 2 ^ ex.toInt
  have hexp : x.toExpInt = x.ex.toInt - ((su - 1 : Nat) : Int) := by
    simp [UnpackedFloat.toExpInt]
    omega
  have h1 : ((2 : Rat) ^ ((su - 1 : Nat) : Int)) * (2 : Rat) ^ x.toExpInt = (2 : Rat) ^ x.ex.toInt := by
    rw [Rat.zpow_mul_zpow (by grind)]
    have heq : ((su - 1 : Nat) : Int) + x.toExpInt = x.ex.toInt := by
      rw [hexp]; omega
    rw [heq]
  have key : (2 : Rat) ^ x.ex.toInt ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [← h1]
    apply Rat.mul_le_mul_of_nonneg_right
    · rw [Rat.zpow_natCast]
      have : ((2 ^ (su - 1) : Nat) : Rat) ≤ (x.sig.toNat : Rat) := by
        exact_mod_cast hle
      simpa [Rat.natCast_pow] using this
    · exact Rat.le_of_lt hpos
  have h3 : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (2 : Rat) ^ x.ex.toInt :=
    Rat.two_pow_le_two_pow_of_le (by omega)
  grind

/-- The absolute value of an unpacked float is its significand value times its scaled exponent. -/
theorem UnpackedFloat.abs_toRat'_eq (x : UnpackedFloat eu su) :
    (x.toRat' prec).abs = (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt prec := by
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt prec := Rat.two_pow_pos _
  have hsignn : (0 : Rat) ≤ (x.sig.toNat : Rat) := by exact_mod_cast Nat.zero_le _
  have hnonneg : (0 : Rat) ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt prec :=
    Rat.mul_nonneg hsignn (Rat.le_of_lt hpos)
  rw [UnpackedFloat.toRat', Rat.abs]
  cases hsgn : x.sign
  · simp [Bool.toSign]
    intros hlt
    grind
  · simp [Bool.toSign]
    grind

/-- For a nonzero unpacked float, the sign bit records whether the value is negative. -/
theorem UnpackedFloat.sign_eq_decide_toRat'_lt_zero (x : UnpackedFloat eu su)
    (hx0 : x.toRat' ≠ 0) :
    x.sign = decide (x.toRat' < 0) := by
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsig : x.sig.toNat ≠ 0 := by
    intro h
    apply hx0
    simp [UnpackedFloat.toRat', UnpackedFloat.toSigNat, h]
  have hsignat : (0 : Rat) < (x.sig.toNat : Rat) := by
    exact_mod_cast Nat.pos_of_ne_zero hsig
  have hprod : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt :=
    Rat.mul_positive hsignat hpos
  rw [UnpackedFloat.toRat']
  cases hsgn : x.sign
  · simp [Bool.toSign]
    grind
  · simp [Bool.toSign]
    grind

/-- An early-underflowing float is strictly smaller in magnitude than
half the minimum subnormal of the target format. -/
theorem UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hunder : x.blastIsEarlyUnderflowNonneg ep sp = true) :
    (x.toRat').abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1) := by
  have hunder' : x.ex.toInt < minSubnormalExp ep sp - 1 := by
    have := UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x
    grind
  rw [UnpackedFloat.abs_toRat'_eq]
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsiglt : x.sig.toNat < 2 ^ su := x.sig.isLt
  have h1 : (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt
      < ((2 : Rat) ^ ((su : Nat) : Int)) * (2 : Rat) ^ x.toExpInt := by
    rw [Rat.mul_lt_mul_cancel_right_of_lt hpos]
    rw [Rat.zpow_natCast]
    have : ((x.sig.toNat : Nat) : Rat) < ((2 ^ su : Nat) : Rat) := by exact_mod_cast hsiglt
    simpa [Rat.natCast_pow] using this
  have h2 : ((2 : Rat) ^ ((su : Nat) : Int)) * (2 : Rat) ^ x.toExpInt
      = (2 : Rat) ^ (((su : Nat) : Int) + x.toExpInt) :=
    Rat.zpow_mul_zpow (by grind) _ _
  have h3 : ((su : Nat) : Int) + x.toExpInt ≤ minSubnormalExp ep sp - 1 := by
    simp [UnpackedFloat.toExpInt]
    omega
  have h4 : (2 : Rat) ^ (((su : Nat) : Int) + x.toExpInt) ≤ (2 : Rat) ^ (minSubnormalExp ep sp - 1) :=
    Rat.two_pow_le_two_pow_of_le h3
  grind

/-- A nonnegative rational strictly below the smallest subnormal of `(ep, sp)` has lower
approximant `+0` (anything `≤ r` is a nonpositive float, since the least positive representable
is `minSubnormal > r`). -/
theorem isLawfulLower_Number_getZero_of_nonneg_of_lt (ep sp : Nat)
    (he : 1 < ep) (hs : 0 < sp) (r : Rat) (hnn : 0 ≤ r)
    (hlt : r < (PackedFloat.minSubnormalNumber ep sp false).toRat) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number r) (PackedFloat.getZero ep sp false) := by
  have hgz : (PackedFloat.getZero ep sp false).toExtRat = ExtRat.Number 0 := by
    rw [PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero] <;> grind)]
  constructor
  · show (PackedFloat.getZero ep sp false).toExtRat ≤ ExtRat.Number r
    rw [hgz]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]; exact hnn
  · intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number r := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']; exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso; rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'; simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        exfalso; rw [PackedFloat.toExtRat'_getInfinity hs] at hy'; simp at hy'
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp [PackedFloat.sign_getInfinity])
          (by simp [PackedFloat.sign_getZero])
          (by simp [PackedFloat.isNaN_getInfinity_eq_false] <;> grind)
          (by simp [PackedFloat.isNaN_getZero] <;> grind)
    | zeroCase sign =>
      cases sign
      case false => exact PackedFloat.le_refl _
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp [PackedFloat.sign_getZero])
          (by simp [PackedFloat.sign_getZero]) (by simp [PackedFloat.isNaN_getZero] <;> grind)
          (by simp [PackedFloat.isNaN_getZero] <;> grind)
    | numCase n hn =>
      by_cases hnsign : n.sign
      · exact PackedFloat.le_of_nonneg_of_neg n _ hnsign (by simp [PackedFloat.sign_getZero])
          (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn)
          (by simp [PackedFloat.isNaN_getZero] <;> grind)
      · exfalso
        simp only [Bool.not_eq_true] at hnsign
        have hnNaN : ¬ n.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn
        have hnzero : ¬ n.isZero := by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hn
        have hminNaN : ¬ (PackedFloat.minSubnormalNumber ep sp false).isNaN :=
          PackedFloat.not_isNaN_minSubnormalNumber ep sp false (by grind) hs
        have hminfin : (PackedFloat.minSubnormalNumber ep sp false).isNormOrNonzeroSubnorm :=
          PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hs
        have hnotlt : ¬ (n < PackedFloat.minSubnormalNumber ep sp false) := by
          rw [PackedFloat.isZero_iff_lt_minSubnormalNumber_of_isNaN_of_nonneg n he hs hnNaN hnsign]
          exact hnzero
        have hge : PackedFloat.minSubnormalNumber ep sp false ≤ n := by
          apply Classical.byContradiction
          intro hcon
          exact hnotlt (PackedFloat.lt_of_not_le _ _ (by grind) hcon)
        have hgeR : (PackedFloat.minSubnormalNumber ep sp false).toRat ≤ n.toRat := by
          have hmin := PackedFloat.toExtRat'_le_toExtRat'_of_le (by grind) hs _ _ hminNaN hnNaN hge
          rw [PackedFloat.toExtRat'_eq_toRat_of hminfin, PackedFloat.toExtRat'_eq_toRat_of hn,
            ExtRat.ExtRat.num_le_num_iff] at hmin
          simpa using hmin
        have hnle : n.toRat ≤ r := by
          rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
          simpa only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] using hy'
        grind

/-- The lower approximant of a nonnegative tiny rational is `+0`. -/
theorem smtLibLower_eq_getZero_of_nonneg_of_lt (ep S : Nat) (he : 1 < ep) (hS : 0 < S)
    (r : Rat) (hnn : 0 ≤ r) (hlt : r < (PackedFloat.minSubnormalNumber ep S false).toRat) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep S)
      = PackedFloat.getZero ep S false := by
  refine eq_of_IsLawfulLower_of_IsLawfulLower ep S (ExtRat.Number r) _ _ ?_ ?_ ?_ ?_
  · simpa using not_isNaN_lower_of_ne_NaN ep S (by grind) hS (ExtRat.Number r) (by simp)
  · simp [PackedFloat.isNaN_getZero] <;> grind
  · exact lsLawfulLower_smtLibLower ep S (by grind) hS (ExtRat.Number r)
  · exact isLawfulLower_Number_getZero_of_nonneg_of_lt ep S he hS r hnn hlt

/-- The upper approximant of a positive tiny rational is the smallest subnormal. -/
theorem smtLibUpper_eq_minSub_of_pos_of_lt (ep S : Nat) (he : 1 < ep) (hS : 0 < S)
    (r : Rat) (hpos : 0 < r) (hlt : r < (PackedFloat.minSubnormalNumber ep S false).toRat) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep S)
      = PackedFloat.minSubnormalNumber ep S false := by
  refine eq_of_IsLawfulUpper_of_IsLawfulUpper ep S (ExtRat.Number r) _ _ ?_ ?_ ?_ ?_
  · simpa using not_isNaN_upper_of_ne_NaN ep S (by grind) hS (ExtRat.Number r) (by simp)
  · simpa using PackedFloat.not_isNaN_minSubnormalNumber ep S false (by grind) hS
  · exact isLawfulUpper_smtLibUpper ep S (by grind) hS (ExtRat.Number r)
  · exact isLawfulUpper_minSubnormalNumber_of_pos_of_le he hS r hpos (Rat.le_of_lt hlt)

private theorem neg_getZero_false (ep S : Nat) :
    -(PackedFloat.getZero ep S false) = PackedFloat.getZero ep S true := by
  simp [PackedFloat.neg_def, PackedFloat.neg, PackedFloat.getZero]

private theorem neg_minSub_false (ep S : Nat) :
    -(PackedFloat.minSubnormalNumber ep S false) = PackedFloat.minSubnormalNumber ep S true := by
  simp [PackedFloat.neg_def, PackedFloat.neg, PackedFloat.minSubnormalNumber]

/-- The upper approximant of a nonpositive tiny rational is `-0`. -/
theorem smtLibUpper_eq_getZero_of_nonpos_of_gt (ep S : Nat) (he : 1 < ep) (hS : 0 < S)
    (r : Rat) (hnp : r ≤ 0) (hgt : -(PackedFloat.minSubnormalNumber ep S false).toRat < r) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep S)
      = PackedFloat.getZero ep S true := by
  rw [smtLibUpper_eq_neg_smtLibLower_neg ep S (by grind) hS (ExtRat.Number r) (by simp),
    show (-(ExtRat.Number r)) = ExtRat.Number (-r) by simp [ExtRat.neg],
    smtLibLower_eq_getZero_of_nonneg_of_lt ep S he hS (-r) (by grind) (by grind),
    neg_getZero_false]

/-- The lower approximant of a negative tiny rational is `-minSubnormal`. -/
theorem smtLibLower_eq_minSub_of_neg_of_gt (ep S : Nat) (he : 1 < ep) (hS : 0 < S)
    (r : Rat) (hneg : r < 0) (hgt : -(PackedFloat.minSubnormalNumber ep S false).toRat < r) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep S)
      = PackedFloat.minSubnormalNumber ep S true := by
  rw [smtLibLower_eq_neg_smtLibUpper_neg ep S (by grind) hS (ExtRat.Number r) (by simp),
    show (-(ExtRat.Number r)) = ExtRat.Number (-r) by simp [ExtRat.neg],
    smtLibUpper_eq_minSub_of_pos_of_lt ep S he hS (-r) (by grind) (by grind),
    neg_minSub_false]

/--
Rounding any number whose absolute value is strictly smaller than *half the
minimum subnormal* of the target format produces a zero, whose sign is the
sign of the number itself.

NOTE (statement corrected): the original statement assumed only
`r.abs < 2 ^ minNormalExp ep` and an arbitrary `sign`, which is FALSE:
* any representable subnormal `r` (e.g. `r = 2 ^ minSubnormalExp ep sp`)
  satisfies that bound but rounds to itself (nonzero);
* for nonzero `r` the sign of the resulting zero is forced by the sign of
  `r` (e.g. positive tiny `r` rounds to `+0` even when `sign = true`).
The corrected hypotheses require `|r| < 2 ^ (minSubnormalExp ep sp - 1)`
(strictly below half the smallest subnormal, so RNE rounds to zero) and
`sign = decide (r < 0)`.
-/
theorem roundRNE_eq_zero_of_lt_minNormalExp
  (he : 1 < ep)
  (hs : 0 < sp)
  (r : Rat)
  (hsign : sign = decide (r < 0))
  (hr : r.abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1)) :
  ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
        (ExtRat.Number r)) = PackedFloat.getZero ep sp sign := by
  have he' : 0 < ep := by grind
  have hsp1 : 0 < sp + 1 := by omega
  -- The two relevant subnormal magnitudes: `minSub` at precision `sp` and `sp+1`.
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
  -- Bounds on `r` from `|r| < minSub_{sp+1}`.
  have hbnd : r < (2 : Rat) ^ (minSubnormalExp ep sp - 1)
      ∧ -(2 : Rat) ^ (minSubnormalExp ep sp - 1) < r := by
    simp only [Rat.abs_def_lt] at hr; split at hr <;> grind
  have hrlt1 : r < (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat := by
    rw [hA]; exact hbnd.1
  have hrgt1 : -(PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat < r := by
    rw [hA]; exact hbnd.2
  have hrlt : r < (PackedFloat.minSubnormalNumber ep sp false).toRat := by grind
  have hrgt : -(PackedFloat.minSubnormalNumber ep sp false).toRat < r := by grind
  -- `toExtRat` of the building blocks.
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
    rw [← neg_minSub_false ep S, PackedFloat.toRat_neg]
  by_cases hr0 : r = 0
  · subst hr0; exact roundRNE_zero he'
  have hnotnan : ¬ (SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number r)) := by simp
  have hnotzero : ¬ (SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r)) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hr0]
  by_cases hrpos : 0 < r
  · -- `r > 0`: `lowerHalf` holds, no tie, so RNE rounds down to `+0`.
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
    have hTB : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq, SmtLibSemantics.smtLibV_lower_eq,
        SmtLibSemantics.smtLibV_upper_eq, hLsp, hLsp1, hUsp, hUsp1]
      rw [hgz, hgz, hms _ _ hs, hms _ _ hsp1]
      have h1 : ¬ ((ExtRat.Number 0 : ExtRat) < ExtRat.Number 0) := by simp
      have h2 : (ExtRat.Number (PackedFloat.minSubnormalNumber ep (sp + 1) false).toRat
          < ExtRat.Number (PackedFloat.minSubnormalNumber ep sp false).toRat) := by simp [hAB]
      intro hcontra
      rw [hcontra] at h1
      exact h1 h2
    have hRL : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lower (ExtRat.Number r) = PackedFloat.getZero ep sp false := by
      rw [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq, hLsp]
    rw [SmtLibSemantics.RoundMethod.roundRNE]
    rw [if_neg hnotnan,
      if_neg (by intro h; exact absurd hLH (by simpa using h.2.1)),
      if_neg (by intro h; exact hTB h.2.1),
      if_neg (by intro h; exact hTB h.2.1),
      if_pos ⟨hnotzero, hLH⟩, hRL, hsignF]
  · -- `r < 0`: neither `lowerHalf` nor tie, so RNE rounds up to `-0`.
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
    rw [SmtLibSemantics.RoundMethod.roundRNE]
    rw [if_neg hnotnan, if_pos ⟨hnotzero, by simp [hLH], by simp [hTB]⟩, hRU, hsignT]

/-- The normalized RNE blast-rounder output is `Packable`: each branch is a `blastUpper`/
`blastLower` (already a normalize fixed point, so `Packable` via L6/L7) or `mkNaN` (vacuous). -/
theorem UnpackedFloat.blastSmtLibRoundRNE_normalize_Packable
    (hep : 1 < ep) (hs : 0 < sp) (hsu : sp + 2 ≤ su)
    (z : UnpackedFloat (exponentWidth ep sp) su) (hznorm : z.normalize = z)
    (hnotEU : z.blastIsEarlyUnderflowNonneg ep sp = false)
    (hnotEO : z.blastIsEarlyOverflowNonneg ep sp = false) :
    (z.blastSmtLibRoundRNE ep sp).normalize.Packable := by
  have heu : exponentWidth ep sp ≤ exponentWidth ep sp := Nat.le_refl _
  have hU : (z.blastUpper ep sp).normalize.Packable := by
    rw [UnpackedFloat.blastUpper_normalize_eq_self hep hs heu hsu z hznorm hnotEU hnotEO]
    exact UnpackedFloat.blastUpper_Packable hep hs hsu z hznorm hnotEU hnotEO
  have hL : (z.blastLower ep sp).normalize.Packable := by
    rw [UnpackedFloat.blastLower_normalize_eq_self hep hs heu hsu z hznorm hnotEU hnotEO]
    exact UnpackedFloat.blastLower_Packable hep hs hsu z hznorm hnotEU hnotEO
  have hN : (EUnpackedFloat.mkNaN : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).normalize.Packable := by
    apply EUnpackedFloat.Packable_of_state_ne_Number
    rw [EUnpackedFloat.state_normalize]; simp
  unfold UnpackedFloat.blastSmtLibRoundRNE
  split
  · exact hU
  · split
    · exact hU
    · split
      · exact hL
      · split
        · exact hL
        · exact hN

/-- `blastSmtLibRound` (RNE) output is always `Packable`. -/
theorem UnpackedFloat.blastSmtLibRound_Packable_of_RNE
    (hep : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RNE).Packable := by
  have he : 1 < ep := by grind
  rw [UnpackedFloat.blastSmtLibRound]
  by_cases hzero : x.isZero = true
  · rw [if_pos hzero]
    exact EUnpackedFloat.mkZero_Packable he hs x.sign
  · rw [if_neg hzero]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
    · rw [if_pos hover]
      exact EUnpackedFloat.Packable_of_state_ne_Number (by
        simp [blastRounderSpecialCaseOverflow])
    · rw [if_neg hover]
      by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
      · rw [if_pos hunder]
        rw [show blastRounderSpecialCaseUnderflow (tep := ep) (tsp := sp) .RNE x.sign
            = EUnpackedFloat.mkZero x.sign from rfl]
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
        show ((x.truncateFittingExponent ep sp).blastSmtLibRoundRNE ep sp).normalize.Packable
        exact UnpackedFloat.blastSmtLibRoundRNE_normalize_Packable hep hs hsu
          (x.truncateFittingExponent ep sp) htnorm htunder htover

/-# `blastSmtLibRound` matches `smtLibRound` for RNE rounding mode. -/

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.

This is what I'm working on right now.

TODO: Refactor proof to case split on x.isZero, and then derive that y.isZero from this.
-/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RNE  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE
        sign (ExtRat.Number r)) := by
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  simp [UnpackedFloat.toRat_eq_toRat']
  by_cases hzero : x.isZero
  · simp [hzero, hs]
    rw [roundRNE_zero]
    · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
      · grind only
    · grind only
  · by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
    · simp [hover]
      -- rw [blastIsEarlyOverflowNonneg_eq_decide he hs heu x] at hover
      -- simp at hover
      simp [blastRounderSpecialCaseOverflow]
      have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
      simp [hx0]
      rw [roundRNE_eq_infinity_of_maxNormalExp_lt]
      · apply EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign
        · simp
        · grind
        · simp
      · simp [he]
      · simp [hs]
      · -- the sign argument matches the sign of the rational value
        exact UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
      · -- from hover
        exact UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm hzero hover
    · simp [hover]
      -- rw [blastIsEarlyOverflowNonneg_eq_decide he hs heu x] at hover
      -- simp at hover
      by_cases hx0 : x.toRat' = 0
      · simp [hx0]
        rw [roundRNE_zero]
        · apply EUnpackedFloat.Rel_of_Rel_of_isZero_of_isZero_of_eq_sign
          · simp
          · simp; grind only
          · simp
        · grind
      · simp [hx0]
        by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp
        · simp [hunder]
          -- rw [blastIsEarlyUnderflowNonneg_eq_decide he hs heu x] at hunder
          simp [blastRounderSpecialCaseUnderflow]
          -- need a lemma that says that 'round' on smaller than minSubnormal values gives zero.
          rw [roundRNE_eq_zero_of_lt_minNormalExp]
          · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
            · grind only
          · simp [he]
          · simp [hs]
          · -- the sign argument matches the sign of the rational value
            exact UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
          · -- from hunder
            exact UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder
        · simp [hunder]
          -- rw [blastIsEarlyUnderflowNonneg_eq_decide he hs heu x] at hunder
          -- -- simp at hunder
          rw [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRNE]
          simp
          -- The rounding predicates are applied to `x.truncateFittingExponent`, which is nonzero and
          -- normalized; supply its `msb`, normalization, and (early) under/overflow flags.
          have hsig : x.sig ≠ 0#su := by simpa [UnpackedFloat.isZero] using hzero
          have htnorm := normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
            he hs heu hsu x hzero hxnorm
          have htmsb : (x.truncateFittingExponent ep sp).sig.msb = true :=
            (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
          have htover : (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
            rw [blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x
              (by simpa using hover) (by simpa using hunder)]
            simpa using hover
          have htunder : (x.truncateFittingExponent ep sp).blastIsEarlyUnderflowNonneg ep sp = false := by
            rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs (Nat.le_refl _)
                (x.truncateFittingExponent ep sp),
              toInt_ex_truncateFittingExponent he hs heu x (by simpa using hover) (by simpa using hunder),
              ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x]
            simpa using hunder
          by_cases hnrd : (x.truncateFittingExponent ep sp).needsRounding ep sp = true
          · rw [blastIsLowerHalf_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover]
            simp only [decide_eq_false_iff_not, decide_eq_true_eq]
            rw [blastIsTieBreak_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover, hnrd, Bool.true_and]
            simp only [decide_eq_false_iff_not, decide_eq_true_eq]
            rw [blastIsEvenUpper_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover]
            simp only [Bool.decide_eq_true]
            rw [blastIsEvenLower_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover]
            simp only [Bool.decide_eq_true]
            rw [SmtLibSemantics.RoundMethod.roundRNE]
            simp [hx0]
            rw [toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg he hs heu (by grind only) (by grind only)]
            -- use that blastUpper rel smtLiBupper, blastLower rel smtLibLower.
            -- this should just be pure proof automation!
            split
            next h1 =>
              rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self he hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
              rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
              exact blastUpper_Rel_smtLibUpper he hs hsu heu x hxnorm (by simpa using hover)
            next h1 =>
              split
              next h2 =>
                rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self he hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                exact blastUpper_Rel_smtLibUpper he hs hsu heu x hxnorm (by simpa using hover)
              next h2 =>
                split
                next h3 =>
                  rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self he hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                  rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                  exact blastLower_Rel_smtLibLower he hs hsu heu x hxnorm (by simpa using hover)
                next h3 =>
                  split
                  next h4 =>
                    rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self he hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                    rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                    exact blastLower_Rel_smtLibLower he hs hsu heu x hxnorm (by simpa using hover)
                  next h4 =>
                    apply EUnpackedFloat.Rel_of_state_eq_NaN_of_isNaN
                    · simp
                    · grind
          · -- needsRounding = false (representable): `blastIsLowerHalf = true`, `blastIsTieBreak = false`,
            -- so the circuit rounds to `blastLower`; the SMT round also yields the representable value.
            have hnrd' : (x.truncateFittingExponent ep sp).needsRounding ep sp = false := by grind
            rw [blastIsLowerHalf_eq_true_of_not_needsRounding _ hnrd',
              blastIsTieBreak_eq_false_of_not_needsRounding _ hnrd']
            simp only [if_false, if_true, Bool.false_eq_true, Bool.true_eq_false, false_and]
            -- Convenient `= false` forms of the early under/overflow flags.
            have hoverF : x.blastIsEarlyOverflowNonneg ep sp = false := by simpa using hover
            have hunderF : x.blastIsEarlyUnderflowNonneg ep sp = false := by simpa using hunder
            have hsig : x.sig ≠ 0#su := by simpa [UnpackedFloat.isZero] using hzero
            have hxmsb : x.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
            have hxnr : x.needsRounding ep sp = false := by
              rw [← needsRounding_truncateFittingExponent he hs heu x hoverF hunderF]; exact hnrd'
            -- A representable, normalized, non-(early)underflow value does not underflow.
            have hundSF : ∀ (y : UnpackedFloat eu su), y.sign = false → y.sig.msb = true →
                y.needsRounding ep sp = false → y.blastIsEarlyUnderflowNonneg ep sp = false →
                y.blastIsUnderflowNonneg ep sp = false := by
              intro y hysign hymsb hynr hyunderF
              rcases Bool.eq_false_or_eq_true (y.blastIsUnderflowNonneg ep sp) with h | h
              · obtain ⟨hoff, hdiffLower, hdiffUpper, _, _⟩ :=
                  boundary_facts he hs heu hsu y hysign hymsb h hyunderF
                have hcontra := needsRounding_eq_true_of_off_eq_succ_of_msb (by grind) hs heu hsu y
                  hdiffLower hdiffUpper hoff hymsb
                rw [hcontra] at hynr; simp at hynr
              · exact h
            -- The representable value: `lower (x).toRat = x.toRat'` (sign-generic).
            have hlowToRat : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')
                : PackedFloat ep sp).toRat = x.toRat' := by
              by_cases hsign : x.sign = false
              · have hund := hundSF x hsign hxmsb hxnr hunderF
                rw [smtLibLower_lower_toRat_eq_blastRoundTowardZero he hs heu hsu x hsign hxnorm hund hoverF,
                    UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding he hs heu hsu x
                      hsign hund hoverF hxnr]
              · have hsignt : x.sign = true := by grind
                have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hsignt]
                have hnnorm : (-x).normalize = -x :=
                  UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
                have hnmsb : (-x).sig.msb = true := by rw [UnpackedFloat.neg_sig]; exact hxmsb
                have hnunderF : (-x).blastIsEarlyUnderflowNonneg ep sp = false := by
                  rw [blastIsEarlyUnderflowNonneg_neg]; exact hunderF
                have hnoverF : (-x).blastIsEarlyOverflowNonneg ep sp = false := by
                  rw [blastIsEarlyOverflowNonneg_neg]; exact hoverF
                have hnnr : (-x).needsRounding ep sp = false := hxnr
                have hnund := hundSF (-x) hnsign hnmsb hnnr hnunderF
                have hlowNeg : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat')
                    : PackedFloat ep sp).toRat = (-x).toRat' := by
                  rw [smtLibLower_lower_toRat_eq_blastRoundTowardZero he hs heu hsu (-x) hnsign hnnorm
                        hnund hnoverF,
                      UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding he hs heu hsu
                        (-x) hnsign hnund hnoverF hnnr]
                have hnegval : (-(ExtRat.Number x.toRat')) = ExtRat.Number ((-x).toRat') := by
                  rw [ExtRat.ExtRat.neg_number]; congr 1; exact (UnpackedFloat.toRat'_neg x).symm
                rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp),
                    hnegval, PackedFloat.toRat_neg,
                    upper_toRat_eq_of_lower_toRat_eq (by grind) hs (-x).toRat'
                      (by rw [UnpackedFloat.toRat'_neg]; simpa using hx0) hlowNeg]
                rw [UnpackedFloat.toRat'_neg]; grind
            -- Finiteness and `upper = lower` at the representable value.
            have hfin := isNormOrNonzeroSubnorm_lower_of_toRat_eq (by grind) hs x.toRat' hx0 hlowToRat
            have hUeqL := upper_eq_lower_of_lower_isNormOrNonzeroSubnorm (by grind) hs x.toRat' hfin hlowToRat
            -- The SMT `lowerHalf` predicate holds (round-toward-zero is exact).
            have hLHtrue : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') := by
              have h1 := blastIsLowerHalf_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
                htnorm htmsb htunder htover
              rw [blastIsLowerHalf_eq_true_of_not_needsRounding _ hnrd',
                toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
                  he hs heu (by grind only) (by grind only)] at h1
              exact of_decide_eq_true h1.symm
            have hnotnan : ¬ SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number x.toRat') := by simp
            have hnotzero : ¬ SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number x.toRat') := by
              simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hx0]
            -- Rewrite the (collapsed) circuit `blastLower` of the truncate into `blastLower` of `x`.
            rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self he hs heu hsu x hzero
                hxnorm hunderF hoverF]
            rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind)
                (by grind) (by grind)]
            -- `roundRNE` collapses to `lower` at a representable value.
            have hRNEeq : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
                SmtLibSemantics.smtLibV).roundRNE x.sign (ExtRat.Number x.toRat')
                = SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') := by
              rw [SmtLibSemantics.RoundMethod.roundRNE, if_neg hnotnan]
              simp only [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibRoundMethod.upper_eq,
                SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq, hUeqL]
              repeat' (first | rfl | split)
              all_goals (exfalso; grind)
            rw [hRNEeq]
            exact UnpackedFloat.blastLower_Rel_smtLibLower he hs hsu heu x hxnorm hoverF

/--
info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE

/-- **Upper finiteness from circuit state.** For a normalized, nonnegative, nonzero float that does
not *early*-overflow, if the bit-blasted upper rounder `blastUpperNonneg` is a finite `Number`
(its late-overflow `mkInfinity` branch was not taken), then the SMT-LIB `upper` is finite
(`isNormOrNonzeroSubnorm`). Cloned from the `blastUpperNonneg_Rel_smtLibUpper_in_range`/`_boundary`
keystones, using `state = Number` to exclude the overflow branch. -/
theorem UnpackedFloat.isNormOrNonzeroSubnorm_smtLibUpper_of_blastUpperNonneg_state_Number
    (he : 1 < ep) (hsp : 0 < sp) (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hxmsb : x.sig.msb = true)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hst : (x.blastUpperNonneg ep sp).state = State.Number) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
  have he' : 0 < ep := by grind
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hxmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  by_cases hu : x.blastIsUnderflowNonneg ep sp = true
  · -- Subnormal boundary: `upper = minSubnormalNumber`.
    have hexlt : x.ex.toInt < minSubnormalExp ep sp := by
      rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hu; simpa using hu
    have hle : x.toRat' ≤ (PackedFloat.minSubnormalNumber ep sp false).toRat := by
      have h1 := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x (by grind) hxsign
      rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
      have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
        simp only [minSubnormalExp, maxSubnormalExp]; grind
      have hmono : (2 : Rat) ^ (x.ex.toInt + 1) ≤ 2 ^ (minNormalExp ep - sp) :=
        Rat.two_pow_le_two_pow_of_le (by omega)
      grind
    have hupperLawful := isLawfulUpper_minSubnormalNumber_of_pos_of_le (by grind) hsp x.toRat' hxpos hle
    have hfinMin : (PackedFloat.minSubnormalNumber ep sp false).isNormOrNonzeroSubnorm :=
      PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hsp
    have hUnan : ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
      simpa using not_isNaN_upper_of_ne_NaN ep sp he' hsp _ (by simp)
    have hMinnan : ¬ (PackedFloat.minSubnormalNumber ep sp false).isNaN := by
      simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfinMin
    have heq : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.minSubnormalNumber ep sp false :=
      eq_of_IsLawfulUpper_of_IsLawfulUpper ep sp (ExtRat.Number x.toRat') _ _ hUnan hMinnan
        (isLawfulUpper_smtLibUpper ep sp he' hsp _) hupperLawful
    rw [heq]; exact hfinMin
  · simp only [Bool.not_eq_true] at hu
    -- In-range: the successor does not underflow.
    have hnnu : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp = false := by
      have hmono := UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux (by grind) hsp heu x hnotover
      have hxu : minSubnormalExp ep sp ≤ x.ex.toInt := by
        rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hu; simpa using hu
      rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu]
      simp only [decide_eq_false_iff_not]; omega
    -- `state = Number` excludes the late-overflow (`mkInfinity`) branch.
    have hnoO : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
      rcases Bool.eq_false_or_eq_true
        ((x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp) with h | h
      · exfalso
        unfold UnpackedFloat.blastUpperNonneg at hst
        rw [UnpackedFloat.isZero_eq_false_of_msb x hxmsb] at hst
        simp only [hnnu, h, Bool.false_eq_true, if_false, if_true] at hst
        simp [EUnpackedFloat.mkInfinity] at hst
      · exact h
    have hfinL := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range he hsp heu hsu x hxsign hxnorm hu hnotover
    by_cases hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false
    · -- `lower = maxNormal`: if rounding, the successor overflows (contradiction); else `upper = lower`.
      obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _, _⟩ :=
        UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
          (by grind) hsp heu hsu x hxsign hxnorm hu hnotover
      have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
        eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
          (by simpa using not_isNaN_lower_of_ne_NaN ep sp he' hsp _ (by simp)) hpfLower
          (lsLawfulLower_smtLibLower ep sp he' hsp _)
      have hlowToRat' : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
          = (x.blastRoundTowardZero ep sp).toRat' := by rw [← hpflow]; exact hToRat.symm
      by_cases hnr : x.needsRounding ep sp = true
      · exfalso
        have hne : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
            ≠ x.toRat' := by
          rw [hlowToRat']; intro he2
          have := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
            (by grind) hsp heu hsu x hxsign hu hnotover).mp he2
          rw [this] at hnr; simp at hnr
        have hle := lower_toRat_le he' hsp x.toRat' hfinL
        have hlowlt : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
            < x.toRat' := by grind
        rw [hmaxL] at hlowlt
        have := UnpackedFloat.blastIsEarlyOverflow_next_of_maxNormalNumber_lt
          he hsp heu hsu x hxsign hxnorm hnotover hu hlowlt
        rw [this] at hnoO; simp at hnoO
      · simp only [Bool.not_eq_true] at hnr
        have hrepr : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
            = x.toRat' := by
          rw [hlowToRat']
          exact (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
            (by grind) hsp heu hsu x hxsign hu hnotover).mpr hnr
        rw [upper_eq_lower_of_lower_isNormOrNonzeroSubnorm he' hsp x.toRat' hfinL hrepr]
        exact hfinL
    · exact isNormOrNonzeroSubnorm_smtLibUpper_of_sign_false_of_ne_maxNormal
        he hsp heu hsu x hxsign hxnorm hu hnotover hmaxL

/-- **Lower finiteness** for a normalized nonzero float that does not early-overflow, given the
circuit `blastLower` is a finite `Number`. For nonnegative `z`, round-toward-zero never overflows
(finite unconditionally); for negative `z`, it reflects to `upper` of `-z`, finite by the upper
keystone using the (neg-transported) circuit state. -/
theorem UnpackedFloat.not_isInfinite_smtLibLower_of_blastLower_state_Number
    (he : 1 < ep) (hsp : 0 < sp) (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (z : UnpackedFloat eu su) (hznorm : z.normalize = z) (hzmsb : z.sig.msb = true)
    (hnotover : z.blastIsEarlyOverflowNonneg ep sp = false)
    (hst : (z.blastLower ep sp).state = State.Number) :
    ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number z.toRat') : PackedFloat ep sp).isInfinite := by
  have he' : 1 < ep := by grind
  by_cases hsign : z.sign = false
  · -- Nonnegative: round-toward-zero is always finite.
    by_cases hu : z.blastIsUnderflowNonneg ep sp = true
    · have hexlt : z.ex.toInt < minSubnormalExp ep sp := by
        rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hu; simpa using hu
      have hxpos : 0 < z.toRat' := by
        have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false z (by grind) hsign hzmsb
        have h2 : (0 : Rat) < 2 ^ (z.ex.toInt) := Rat.two_pow_pos _
        grind
      have hlt : z.toRat' < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
        have h1 := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false z (by grind) hsign
        rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
        have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
          simp only [minSubnormalExp, maxSubnormalExp]; grind
        have hmono : (2 : Rat) ^ (z.ex.toInt + 1) ≤ 2 ^ (minNormalExp ep - sp) :=
          Rat.two_pow_le_two_pow_of_le (by omega)
        grind
      rw [smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he' hsp z.toRat' (Rat.le_of_lt hxpos) hlt]
      simp [PackedFloat.isInfinite_getZero] <;> grind
    · simp only [Bool.not_eq_true] at hu
      simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
        (UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range he hsp heu hsu z hsign hznorm hu hnotover)
  · -- Negative: reflect to `upper` of `-z` (nonnegative).
    simp only [Bool.not_eq_false] at hsign
    have hns : (-z).sign = false := by simp [UnpackedFloat.neg_sign, hsign]
    have hnnorm : (-z).normalize = -z := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq z hznorm
    have hnmsb : (-z).sig.msb = true := by rw [UnpackedFloat.neg_sig]; exact hzmsb
    have hnover : (-z).blastIsEarlyOverflowNonneg ep sp = false := by
      rw [blastIsEarlyOverflowNonneg_neg]; exact hnotover
    have hstU : ((-z).blastUpperNonneg ep sp).state = State.Number := by
      rw [UnpackedFloat.blastLower, if_pos hsign, UnpackedFloat.blastLowerNeg,
        EUnpackedFloat.neg_state] at hst
      exact hst
    have hfinU := UnpackedFloat.isNormOrNonzeroSubnorm_smtLibUpper_of_blastUpperNonneg_state_Number
      he hsp hsu heu (-z) hns hnnorm hnmsb hnover hstU
    rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp (by grind) hsp (ExtRat.Number z.toRat') (by simp),
      show (-(ExtRat.Number z.toRat')) = ExtRat.Number (-z.toRat') by simp [ExtRat.neg],
      show (-z.toRat') = (-z).toRat' by rw [UnpackedFloat.toRat'_neg],
      PackedFloat.isInfinite_neg]
    simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfinU

/-- **Upper finiteness** (any sign), dual of `not_isInfinite_smtLibLower_of_blastLower_state_Number`:
nonnegative is the away-direction handled by the upper keystone (needs circuit state); negative is
toward-zero, reflected to `lower` of `-z` (finite unconditionally). -/
theorem UnpackedFloat.not_isInfinite_smtLibUpper_of_blastUpper_state_Number
    (he : 1 < ep) (hsp : 0 < sp) (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (z : UnpackedFloat eu su) (hznorm : z.normalize = z) (hzmsb : z.sig.msb = true)
    (hnotover : z.blastIsEarlyOverflowNonneg ep sp = false)
    (hst : (z.blastUpper ep sp).state = State.Number) :
    ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number z.toRat') : PackedFloat ep sp).isInfinite := by
  have he' : 1 < ep := by grind
  by_cases hsign : z.sign = false
  · -- Nonnegative: away-direction; use the upper keystone with the circuit state.
    have hstU : (z.blastUpperNonneg ep sp).state = State.Number := by
      rw [UnpackedFloat.blastUpper, if_neg (by simp [hsign])] at hst; exact hst
    simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
      (UnpackedFloat.isNormOrNonzeroSubnorm_smtLibUpper_of_blastUpperNonneg_state_Number
        he hsp hsu heu z hsign hznorm hzmsb hnotover hstU)
  · -- Negative: toward-zero; reflect to `lower` of `-z`.
    simp only [Bool.not_eq_false] at hsign
    have hns : (-z).sign = false := by simp [UnpackedFloat.neg_sign, hsign]
    have hnnorm : (-z).normalize = -z := UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq z hznorm
    have hnmsb : (-z).sig.msb = true := by rw [UnpackedFloat.neg_sig]; exact hzmsb
    have hnover : (-z).blastIsEarlyOverflowNonneg ep sp = false := by
      rw [blastIsEarlyOverflowNonneg_neg]; exact hnotover
    -- lower of nonnegative `-z` is finite regardless of circuit state.
    have hfinL : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-z).toRat') : PackedFloat ep sp).isInfinite := by
      by_cases hu : (-z).blastIsUnderflowNonneg ep sp = true
      · have hexlt : (-z).ex.toInt < minSubnormalExp ep sp := by
          rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hu; simpa using hu
        have hxpos : 0 < (-z).toRat' := by
          have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false (-z) (by grind) hns hnmsb
          have h2 : (0 : Rat) < 2 ^ ((-z).ex.toInt) := Rat.two_pow_pos _
          grind
        have hlt : (-z).toRat' < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
          have h1 := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false (-z) (by grind) hns
          rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
          have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
            simp only [minSubnormalExp, maxSubnormalExp]; grind
          have hmono : (2 : Rat) ^ ((-z).ex.toInt + 1) ≤ 2 ^ (minNormalExp ep - sp) :=
            Rat.two_pow_le_two_pow_of_le (by omega)
          grind
        rw [smtLibLower_eq_getZero_of_nonneg_of_lt ep sp he' hsp (-z).toRat' (Rat.le_of_lt hxpos) hlt]
        simp [PackedFloat.isInfinite_getZero] <;> grind
      · simp only [Bool.not_eq_true] at hu
        simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm
          (UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range he hsp heu hsu (-z) hns hnnorm hu hnover)
    rw [smtLibUpper_eq_neg_smtLibLower_neg ep sp (by grind) hsp (ExtRat.Number z.toRat') (by simp),
      show (-(ExtRat.Number z.toRat')) = ExtRat.Number (-z.toRat') by simp [ExtRat.neg],
      show (-z.toRat') = (-z).toRat' by rw [UnpackedFloat.toRat'_neg],
      PackedFloat.isInfinite_neg]
    exact hfinL

/-- **SMT-LIB round result is finite (RNE).** When the bit-blasted rounder output is a finite
`Number`, the SMT-LIB round of the (nonzero, normalized) input is neither NaN nor infinite. The
proof mirrors `toExtRat_round_Rel_smtLibRound_of_RNE`'s operational branch structure, pinning the
round result to a concrete finite value in each branch (`getZero`, `lower`, `upper`) and using the
circuit `state = Number` to exclude late overflow and the unreachable `mkNaN` tie branch. -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RNE
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true) :
    (x.blastSmtLibRound ep sp .RNE : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE
            sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE
            sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  subst r sign
  have hzero : x.isZero = false := UnpackedFloat.isZero_eq_false_of_msb x hmsb
  have hx0 : x.toRat' ≠ 0 := by
    grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
  simp only [SmtLibSemantics.RoundMethod.round_RNE_eq, UnpackedFloat.toRat_eq_toRat']
  -- Reduce the circuit-state hypothesis through `blastSmtLibRound`'s branches.
  rw [UnpackedFloat.blastSmtLibRound, if_neg (by simp [hzero])] at hstate
  by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
  · -- Early overflow ⟹ circuit is `mkInfinity` (state `Infinity`): the hypothesis is false.
    rw [if_pos hover,
      show blastRounderSpecialCaseOverflow (tep := ep) (tsp := sp) .RNE x.sign
        = EUnpackedFloat.mkInfinity x.sign from rfl] at hstate
    simp [EUnpackedFloat.mkInfinity] at hstate
  · rw [if_neg (by simpa using hover)] at hstate
    by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp = true
    · -- Early underflow ⟹ round result is `getZero`, which is finite.
      rw [roundRNE_eq_zero_of_lt_minNormalExp he hs x.toRat'
          (UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0)
          (UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder)]
      refine ⟨?_, ?_⟩
      · simp [PackedFloat.isNaN_getZero] <;> grind
      · simp [PackedFloat.isInfinite_getZero] <;> grind
    · -- Main branch: round result collapses to `upper`/`lower`; finiteness from the helpers.
      rw [if_neg (by simpa using hunder)] at hstate
      simp only [Bool.not_eq_true] at hover hunder
      have htnorm := normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
        he hs heu hsu x (by grind) hxnorm
      have hsigne : x.sig ≠ 0#su := by simpa [UnpackedFloat.isZero] using hzero
      have htmsb : (x.truncateFittingExponent ep sp).sig.msb = true :=
        (UnpackedFloat.normalize_eq_self_iff x hsigne).mp hxnorm
      have htover : (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp = false := by
        rw [blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x hover hunder]; exact hover
      have htunder : (x.truncateFittingExponent ep sp).blastIsEarlyUnderflowNonneg ep sp = false := by
        rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs (Nat.le_refl _),
          toInt_ex_truncateFittingExponent he hs heu x hover hunder,
          ← UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x]
        exact hunder
      have hztoRat : (x.truncateFittingExponent ep sp).toRat' = x.toRat' :=
        toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
          he hs heu hover hunder
      -- `hstate : (z.blastSmtLibRoundRNE).state = Number`, with `z := truncateFittingExponent`.
      simp only [UnpackedFloat.blastSmtLibRoundAux, EUnpackedFloat.state_normalize] at hstate
      -- Finiteness of `upper` / `lower` at `x.toRat'`, from the (about-to-be-extracted) piece state.
      have hUfin : ((x.truncateFittingExponent ep sp).blastUpper ep sp).state = State.Number →
          ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isInfinite := by
        intro hsU
        have := UnpackedFloat.not_isInfinite_smtLibUpper_of_blastUpper_state_Number
          he hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hsU
        rwa [hztoRat] at this
      have hLfin : ((x.truncateFittingExponent ep sp).blastLower ep sp).state = State.Number →
          ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isInfinite := by
        intro hsL
        have := UnpackedFloat.not_isInfinite_smtLibLower_of_blastLower_state_Number
          he hs hsu (Nat.le_refl _) (x.truncateFittingExponent ep sp) htnorm htmsb htover hsL
        rwa [hztoRat] at this
      have hUnan : ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
        simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hs _ (by simp)
      have hLnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
        simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp)
      -- Align the circuit predicates to the SMT predicates, then case split.
      rw [UnpackedFloat.blastSmtLibRoundRNE,
        blastIsLowerHalf_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
          htnorm htmsb htunder htover,
        blastIsEvenUpper_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
          htnorm htmsb htunder htover,
        blastIsEvenLower_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
          htnorm htmsb htunder htover,
        blastIsTieBreak_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
          htnorm htmsb htunder htover,
        hztoRat] at hstate
      have hx0' : ¬ SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number x.toRat') := by
        simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hx0]
      rw [SmtLibSemantics.RoundMethod.roundRNE, if_neg (show ¬ SmtLibSemantics.ExtendedNumber.isNaN
        (ExtRat.Number x.toRat') by simp)]
      by_cases hnrd : (x.truncateFittingExponent ep sp).needsRounding ep sp = true
      · -- Genuine rounding: `blastIsTieBreak = decide tieBreak`.
        -- After `rw [hnrd, Bool.true_and] at hstate`, `hstate` is the 5-way circuit `if`-chain
        --   (blastUpper | blastUpper | blastLower | blastLower | mkNaN).state = .Number
        -- over `decide (lowerHalf ..)`, `decide (tieBreak ..)`, `decide (isEven (upper ..))`,
        -- `decide (isEven (lower ..))`, and the goal is the matching SMT round `if`-chain.
        -- TODO(continue): case-split both the goal `if`-chain and `hstate` on the same
        -- decidable conditions; in each leaf the round result is pinned to `upper`/`lower`
        -- (finiteness via `hUfin`/`hLfin` + `hUnan`/`hLnan`) and the circuit piece state is
        -- read off from `hstate`; the `mkNaN` leaf contradicts `hstate` (state ≠ .Number).
        rw [hnrd, Bool.true_and] at hstate
        -- The SMT round if-chain and the circuit if-chain (`hstate`) run over the SAME four
        -- decidable conditions; case on them so both reduce in lockstep. In each surviving leaf the
        -- round result is `upper`/`lower` (finite via the helpers + the circuit piece state from
        -- `hstate`); the `getNaN`/`mkNaN` leaf makes `hstate` (state `.NaN = .Number`) absurd.
        by_cases hlh : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat') <;>
          by_cases htb : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') <;>
          cases hEU : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven ((SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)) <;>
          cases hEL : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven ((SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)) <;>
          simp_all only [hx0', SmtLibSemantics.smtLibRoundMethod.upper_eq,
            SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_upper_eq,
            SmtLibSemantics.smtLibV_lower_eq, decide_eq_true_eq, not_false_eq_true, true_and, and_true, and_false,
            false_and, if_true, if_false, ite_true, ite_false, decide_true, decide_false,
            Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.true_and,
            Bool.false_and, not_true, not_false_iff, EUnpackedFloat.state_mkNaN, reduceCtorEq] <;>
          first
            | exact ⟨hUnan, hUfin hstate⟩
            | exact ⟨hLnan, hLfin hstate⟩
      · -- `needsRounding = false` (representable): `blastIsTieBreak = false`, `lowerHalf = true`,
        -- so the circuit collapses to `blastLower`; `smtLibUpper = smtLibLower` there, so the SMT
        -- round result is `lower` (finite). Mirrors the representable case of the `Rel` theorem.
        have hnrd' : (x.truncateFittingExponent ep sp).needsRounding ep sp = false := by grind
        have hoverF : x.blastIsEarlyOverflowNonneg ep sp = false := by simpa using hover
        have hunderF : x.blastIsEarlyUnderflowNonneg ep sp = false := by simpa using hunder
        have hsig : x.sig ≠ 0#su := by simpa [UnpackedFloat.isZero] using hzero
        have hxmsb : x.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
        have hxnr : x.needsRounding ep sp = false := by
          rw [← needsRounding_truncateFittingExponent he hs heu x hoverF hunderF]; exact hnrd'
        have hundSF : ∀ (y : UnpackedFloat eu su), y.sign = false → y.sig.msb = true →
            y.needsRounding ep sp = false → y.blastIsEarlyUnderflowNonneg ep sp = false →
            y.blastIsUnderflowNonneg ep sp = false := by
          intro y hysign hymsb hynr hyunderF
          rcases Bool.eq_false_or_eq_true (y.blastIsUnderflowNonneg ep sp) with h | h
          · obtain ⟨hoff, hdiffLower, hdiffUpper, _, _⟩ :=
              boundary_facts he hs heu hsu y hysign hymsb h hyunderF
            have hcontra := needsRounding_eq_true_of_off_eq_succ_of_msb (by grind) hs heu hsu y
              hdiffLower hdiffUpper hoff hymsb
            rw [hcontra] at hynr; simp at hynr
          · exact h
        have hlowToRat : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')
            : PackedFloat ep sp).toRat = x.toRat' := by
          by_cases hsign : x.sign = false
          · have hund := hundSF x hsign hxmsb hxnr hunderF
            rw [smtLibLower_lower_toRat_eq_blastRoundTowardZero he hs heu hsu x hsign hxnorm hund hoverF,
                UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding he hs heu hsu x
                  hsign hund hoverF hxnr]
          · have hsignt : x.sign = true := by grind
            have hnsign : (-x).sign = false := by simp [UnpackedFloat.neg_sign, hsignt]
            have hnnorm : (-x).normalize = -x :=
              UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
            have hnmsb : (-x).sig.msb = true := by rw [UnpackedFloat.neg_sig]; exact hxmsb
            have hnunderF : (-x).blastIsEarlyUnderflowNonneg ep sp = false := by
              rw [blastIsEarlyUnderflowNonneg_neg]; exact hunderF
            have hnoverF : (-x).blastIsEarlyOverflowNonneg ep sp = false := by
              rw [blastIsEarlyOverflowNonneg_neg]; exact hoverF
            have hnund := hundSF (-x) hnsign hnmsb hxnr hnunderF
            have hlowNeg : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number (-x).toRat')
                : PackedFloat ep sp).toRat = (-x).toRat' := by
              rw [smtLibLower_lower_toRat_eq_blastRoundTowardZero he hs heu hsu (-x) hnsign hnnorm
                    hnund hnoverF,
                  UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding he hs heu hsu
                    (-x) hnsign hnund hnoverF hxnr]
            have hnegval : (-(ExtRat.Number x.toRat')) = ExtRat.Number ((-x).toRat') := by
              rw [ExtRat.ExtRat.neg_number]; congr 1; exact (UnpackedFloat.toRat'_neg x).symm
            rw [smtLibLower_eq_neg_smtLibUpper_neg ep sp (by grind) hs (ExtRat.Number x.toRat') (by simp),
                hnegval, PackedFloat.toRat_neg,
                upper_toRat_eq_of_lower_toRat_eq (by grind) hs (-x).toRat'
                  (by rw [UnpackedFloat.toRat'_neg]; simpa using hx0) hlowNeg]
            rw [UnpackedFloat.toRat'_neg]; grind
        have hfin := isNormOrNonzeroSubnorm_lower_of_toRat_eq (by grind) hs x.toRat' hx0 hlowToRat
        have hUeqL := upper_eq_lower_of_lower_isNormOrNonzeroSubnorm (by grind) hs x.toRat' hfin hlowToRat
        -- collapse the circuit `hstate` to `(blastLower …).state = .Number`.
        have hlhdec : decide ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
            SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')) = true := by
          have h1 := blastIsLowerHalf_eq he hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
            htnorm htmsb htunder htover
          rw [blastIsLowerHalf_eq_true_of_not_needsRounding _ hnrd', hztoRat] at h1
          exact h1.symm
        rw [hnrd', Bool.false_and] at hstate
        simp only [hlhdec, decide_true, Bool.not_true, Bool.false_and, Bool.and_false,
          Bool.false_eq_true, if_false, ite_false, Bool.not_false, Bool.true_and, if_true,
          ite_true] at hstate
        have hLfin' := hLfin hstate
        have hLnan' := hLnan
        simp only [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibRoundMethod.upper_eq,
          SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq, hUeqL, hx0',
          not_false_eq_true, true_and, and_true, and_false, false_and, if_true, if_false,
          ite_true, ite_false]
        refine ⟨?_, ?_⟩ <;> (repeat' (first | assumption | split)) <;>
          first
            | exact hLnan'
            | exact hLfin'
            | (exfalso; simp_all)

end Fp
