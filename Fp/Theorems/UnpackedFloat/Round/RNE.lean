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
    unfold Rat.abs at hr; split at hr <;> grind
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
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq, hLsp, hLsp1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [hgz, hgz]
    have hTB : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq,
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
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq, hLsp, hLsp1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [hms _ _ hs, hms _ _ hsp1, hmt _ hs, hmt _ hsp1]
      simp only [ExtRat.Number.injEq]
      grind
    have hTB : ¬ (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq,
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
          · rw [blastIsLowerHalf_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover]
            simp only [decide_eq_false_iff_not, decide_eq_true_eq]
            rw [blastIsTieBreak_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover, hnrd, Bool.true_and]
            simp only [decide_eq_false_iff_not, decide_eq_true_eq]
            rw [blastIsEvenUpper_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover]
            simp only [Bool.decide_eq_true]
            rw [blastIsEvenLower_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
              htnorm htmsb htunder htover]
            simp only [Bool.decide_eq_true]
            rw [SmtLibSemantics.RoundMethod.roundRNE]
            simp [hx0]
            rw [toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg he hs heu (by grind only) (by grind only)]
            -- use that blastUpper rel smtLiBupper, blastLower rel smtLibLower.
            -- this should just be pure proof automation!
            split
            next h1 =>
              rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
              rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
              exact blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm (by simpa using hover)
            next h1 =>
              split
              next h2 =>
                rw [UnpackedFloat.blastUpper_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                exact blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm (by simpa using hover)
              next h2 =>
                split
                next h3 =>
                  rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                  rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                  exact blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm (by simpa using hover)
                next h3 =>
                  split
                  next h4 =>
                    rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero hxnorm (by simpa using hunder) (by simpa using hover)]
                    rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                    exact blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm (by simpa using hover)
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
                  boundary_facts hep hs heu hsu y hysign hymsb h hyunderF
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
              have h1 := blastIsLowerHalf_eq hep hs (Nat.le_refl _) hsu (x.truncateFittingExponent ep sp)
                htnorm htmsb htunder htover
              rw [blastIsLowerHalf_eq_true_of_not_needsRounding _ hnrd',
                toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
                  he hs heu (by grind only) (by grind only)] at h1
              exact of_decide_eq_true h1.symm
            have hnotnan : ¬ SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number x.toRat') := by simp
            have hnotzero : ¬ SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number x.toRat') := by
              simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]; simp [hx0]
            -- Rewrite the (collapsed) circuit `blastLower` of the truncate into `blastLower` of `x`.
            rw [UnpackedFloat.blastLower_truncateFittingExponent_normalize_eq_self hep hs heu hsu x hzero
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
            exact UnpackedFloat.blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm hoverF

/--
info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE

end Fp
