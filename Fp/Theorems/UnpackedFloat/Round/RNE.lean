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
`hsign : sign = decide (r < 0)` and `hep : 2 < ep` were ADDED: without
`hsign` the conclusion is false for, e.g., positive `r` and `sign = true`
(the result `+∞` does not depend on `sign` for nonzero `r`).
-/
theorem roundRNE_eq_infinity_of_maxNormalExp_lt
  (he : 1 < ep)
  (hep : 2 < ep)
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
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq, hL, hL1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_toRat_of hfinN, PackedFloat.toExtRat'_eq_toRat_of hfinN1]
      simp only [ExtRat.Number.injEq]
      grind
    have hTB : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq,
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
      simp [Rat.abs, hneg]
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
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq, hL, hL1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1]
    have hTB : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq,
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
  sorry

/-# `blastSmtLibRound` matches `smtLibRound` for RNE rounding mode. -/

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.

This is what I'm working on right now.

TODO: Refactor proof to case split on x.isZero, and then derive that y.isZero from this.
-/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
    (he : 1 < ep)
    (hep : 2 < ep)
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
      · simp [hep]
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
          rw [blastIsLowerHalf_eq (by grind only) (by grind only)]
          simp only [decide_eq_false_iff_not, decide_eq_true_eq]
          rw [blastIsTieBreak_eq (by grind only) (by grind only)]
          simp only [decide_eq_false_iff_not, decide_eq_true_eq]
          rw [blastIsEvenUpper_eq (by grind only) (by grind only)]
          simp only [Bool.decide_eq_true]
          rw [blastIsEvenLower_eq (by grind only) (by grind only)]
          simp only [Bool.decide_eq_true]
          rw [SmtLibSemantics.RoundMethod.roundRNE]
          simp [hx0]
          rw [toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg he hs heu (by grind only) (by grind only)]
          -- use that blastUpper rel smtLiBupper, blastLower rel smtLibLower.
          -- this should just be pure proof automation!
          split
          case neg.isTrue h1 =>
            rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
            rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
            exact blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm (by simpa using hover)
          case neg.isFalse h1 =>
            split
            case isTrue h2 =>
              rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
              rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
              exact blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm (by simpa using hover)
            case isFalse h2 =>
              split
              case isTrue h3 =>
                rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                exact blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm (by simpa using hover)
              case isFalse h3 =>
                split
                case isTrue h4 =>
                  rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                  rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                  exact blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm (by simpa using hover)
                case isFalse h4 =>
                  apply EUnpackedFloat.Rel_of_state_eq_NaN_of_isNaN
                  · simp
                  · grind


end Fp
