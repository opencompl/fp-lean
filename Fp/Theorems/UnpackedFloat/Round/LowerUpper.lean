import Fp.Theorems.UnpackedFloat.Round.TruncateFittingExponent

namespace Fp


/-# `blastLowerNonneg` matches `lower` -/



/--
Helper: Reduce `result.Rel (smtLibLower.lower (Number r))` to producing a
witness `pf` that is a lawful lower with matching `toRat'` and `sign`.
-/
theorem EUnpackedFloat.Rel_smtLibLower_of_witness
    (he : 0 < ep) (hs : 0 < sp)
    (r : Rat)
    (result : EUnpackedFloat eu su)
    (hres : result.state = .Number)
    (pf : PackedFloat ep sp)
    (hpfNotNaN : ¬ pf.isNaN)
    (hpfLower : SmtLibSemantics.IsLawfulLower (ExtRat.Number r) pf)
    (hToRat : result.num.toRat' sp = pf.toRat)
    (hSign  : result.num.sign  = pf.sign) :
    result.Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp) := by
  -- The smtLib lower is also a lawful lower; by uniqueness it equals `pf`.
  have hSmtLower : SmtLibSemantics.IsLawfulLower (ExtRat.Number r)
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp) :=
    lsLawfulLower_smtLibLower ep sp he hs _
  have hSmtNotNaN : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp).isNaN := by
    have := not_isNaN_lower_of_ne_NaN ep sp he hs (ExtRat.Number r) (by simp)
    grind only
  have hpf_eq : pf = SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) := by
    apply eq_of_IsLawfulLower_of_IsLawfulLower
    · exact hpfNotNaN
    · exact hSmtNotNaN
    · exact hpfLower
    · exact hSmtLower
  apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
  · simp [hres]
  · refine UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign _ _ ?_ ?_
    · rw [hToRat, hpf_eq]
    · rw [hSign, hpf_eq]

  /--
info: 'Fp.EUnpackedFloat.Rel_smtLibLower_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EUnpackedFloat.Rel_smtLibLower_of_witness

/--
Helper: Reduce `result.Rel (smtLibUpper.upper (Number r))` to producing a
witness `pf` that is a lawful upper with matching `toRat'` and `sign`.
(Upper analog of `EUnpackedFloat.Rel_smtLibLower_of_witness`.)
-/
theorem EUnpackedFloat.Rel_smtLibUpper_of_witness
    (he : 0 < ep) (hs : 0 < sp)
    (r : Rat)
    (result : EUnpackedFloat eu su)
    (hres : result.state = .Number)
    (pf : PackedFloat ep sp)
    (hpfNotNaN : ¬ pf.isNaN)
    (hpfUpper : SmtLibSemantics.IsLawfulUpper (ExtRat.Number r) pf)
    (hToRat : result.num.toRat' sp = pf.toRat)
    (hSign  : result.num.sign  = pf.sign) :
    result.Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp) := by
  -- The smtLib upper is also a lawful upper; by uniqueness it equals `pf`.
  have hSmtUpper : SmtLibSemantics.IsLawfulUpper (ExtRat.Number r)
      (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp) :=
    isLawfulUpper_upper ep sp he hs _
  have hSmtNotNaN : ¬ (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp).isNaN := by
    have := not_isNaN_upper_of_ne_NaN ep sp he hs (ExtRat.Number r) (by simp)
    grind only
  have hpf_eq : pf = SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) := by
    apply eq_of_IsLawfulUpper_of_IsLawfulUpper
    · exact hpfNotNaN
    · exact hSmtNotNaN
    · exact hpfUpper
    · exact hSmtUpper
  apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
  · simp [hres]
  · refine UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign _ _ ?_ ?_
    · rw [hToRat, hpf_eq]
    · rw [hSign, hpf_eq]

/--
info: 'Fp.EUnpackedFloat.Rel_smtLibUpper_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EUnpackedFloat.Rel_smtLibUpper_of_witness

/-- A normalized float that does not underflow is nonzero, so its significand msb is set.
(A zero would have `ex = intMin`, whose value `-2^(eu-1)` is below `minSubnormalExp`, i.e.
underflow — contradicting `hnotunder`.) -/
theorem UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false) :
    x.sig.msb = true := by
  have hsig0 : x.sig ≠ 0#su := by
    intro h0
    have hmk : x = UnpackedFloat.mkZero x.sign := by
      have h := hxnorm; rw [UnpackedFloat.normalize] at h
      simpa only [h0, beq_self_eq_true, cond_true] using h.symm
    have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
      have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
    have heupos : 0 < eu := by have := @zero_lt_exponentWidth ep sp; grind
    have hexval : x.ex.toInt = -2 ^ (eu - 1) := by
      have hmod : (2 : Nat) ^ (eu - 1) % 2 ^ eu = 2 ^ (eu - 1) :=
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_of_lt (by grind) (by grind))
      rw [hmk, UnpackedFloat.ex_mkZero, BitVec.toInt_intMin, hmod]
      push_cast; grind
    have hlt := neg_two_pow_exponentWidth_lt_minSubnormalExp (e := ep) (s := sp) he hs
    have hpow : (2 : Int) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) := by
      have h1 : (2 : Nat) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) :=
        Nat.pow_le_pow_right (by grind) (by grind)
      have hc1 : ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int) = (2 : Int) ^ (exponentWidth ep sp - 1) := by
        push_cast; rfl
      have hc2 : ((2 ^ (eu - 1) : Nat) : Int) = (2 : Int) ^ (eu - 1) := by push_cast; rfl
      grind
    grind
  exact (UnpackedFloat.normalize_eq_self_iff x hsig0).mp hxnorm

/-! ### Binade bounds (shared API) -/

/-- A nonnegative packed float lies strictly below the top of its binade:
`pf.toRat < 2 ^ (toRatExp + 1)` (since `toRatSig < 2`). -/
theorem PackedFloat.toRat_lt_two_pow_toRatExp_succ_of_sign_false {e s : Nat}
    (pf : PackedFloat e s) (hsign : pf.sign = false) :
    pf.toRat < 2 ^ (pf.toRatExp + 1) := by
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  rw [PackedFloat.toRat, hsign, hsg, Rat.one_mul]
  have h2 := pf.toRatSig_lt_two
  have hpow : (0 : Rat) < 2 ^ pf.toRatExp := Rat.two_pow_pos _
  rw [← Rat.mul_self_zpow_eq_zpow_succ (a := (2 : Rat)) (n := pf.toRatExp) (by grind)]
  exact (Rat.mul_lt_mul_cancel_right_of_lt hpow).mpr h2

/-- The rational exponent of any packed float is at least `minNormalExp` (subnormals
all share that exponent; normals have `ex.toNat ≥ 1` since `isNorm` forbids `ex = 0`). -/
theorem PackedFloat.minNormalExp_le_toRatExp {e s : Nat} (pf : PackedFloat e s) (he : 0 < e) :
    minNormalExp e ≤ pf.toRatExp := by
  rw [PackedFloat.toRatExp, minNormalExp]
  split
  · case isTrue hnorm =>
    have hne : pf.ex ≠ BitVec.zero e := by
      simp only [PackedFloat.isNorm, Bool.and_eq_true, bne_iff_ne] at hnorm; exact hnorm.2
    have : 1 ≤ pf.ex.toNat := by
      rcases Nat.eq_zero_or_pos pf.ex.toNat with h | h
      · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h) hne
      · exact h
    grind
  · case isFalse _ => grind

/-- A nonnegative unpacked float whose significand msb is set is at least `2 ^ ex`
(the bottom of its binade). -/
theorem UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false {e s : Nat}
    (uf : UnpackedFloat e s) (hs : 0 < s) (hsign : uf.sign = false) (hmsb : uf.sig.msb = true) :
    (2 : Rat) ^ uf.ex.toInt ≤ uf.toRat' := by
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  rw [UnpackedFloat.toRat', hsign, hsg, Rat.one_mul, UnpackedFloat.toExpInt,
    UnpackedFloat.toNat_toSigNat_eq]
  have hge : 2 ^ (s - 1) ≤ uf.sig.toNat := by
    rw [BitVec.msb_eq_decide] at hmsb; simpa using hmsb
  have hgeR : (2 : Rat) ^ (s - 1 : Nat) ≤ (uf.sig.toNat : Rat) := by exact_mod_cast hge
  have hpow : (0 : Rat) < 2 ^ (-(↑(s - 1) - uf.ex.toInt)) := Rat.two_pow_pos _
  have hfac : (2 : Rat) ^ uf.ex.toInt
      = (2 : Rat) ^ (s - 1 : Nat) * 2 ^ (-(↑(s - 1) - uf.ex.toInt)) := by
    rw [← Rat.zpow_natCast (2 : Rat) (s - 1), Rat.zpow_mul_zpow (by grind)]
    congr 1; grind
  rw [hfac]
  exact Rat.mul_le_mul_of_nonneg_right hgeR (Rat.le_of_lt hpow)

/-- A nonnegative unpacked float is strictly below the top of its binade: `toRat' < 2^(ex+1)`
(holds for *any* significand since `sig.toNat < 2^s`). -/
theorem UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false {e s : Nat}
    (uf : UnpackedFloat e s) (hs : 0 < s) (hsign : uf.sign = false) :
    uf.toRat' < (2 : Rat) ^ (uf.ex.toInt + 1) := by
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  rw [UnpackedFloat.toRat', hsign, hsg, Rat.one_mul, UnpackedFloat.toExpInt,
    UnpackedFloat.toNat_toSigNat_eq]
  have hlt : (uf.sig.toNat : Rat) < (2 : Rat) ^ (s : Nat) := by
    have := uf.sig.isLt; exact_mod_cast this
  have hpow : (0 : Rat) < 2 ^ (-(↑(s - 1) - uf.ex.toInt)) := Rat.two_pow_pos _
  have hfac : (2 : Rat) ^ (uf.ex.toInt + 1)
      = (2 : Rat) ^ (s : Nat) * 2 ^ (-(↑(s - 1) - uf.ex.toInt)) := by
    rw [← Rat.zpow_natCast (2 : Rat) s, Rat.zpow_mul_zpow (by grind)]
    congr 1
    rw [Int.natCast_sub (show 1 ≤ s by grind)]; push_cast; grind
  rw [hfac]
  exact (Rat.mul_lt_mul_cancel_right_of_lt hpow).mpr hlt

/-- A nonnegative unpacked float has nonnegative value. -/
theorem UnpackedFloat.toRat'_nonneg_of_sign_false {e s : Nat}
    (uf : UnpackedFloat e s) (hsign : uf.sign = false) :
    0 ≤ uf.toRat' prec := by
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  rw [UnpackedFloat.toRat', hsign, hsg, Rat.one_mul, UnpackedFloat.toNat_toSigNat_eq]
  have h1 : (0 : Rat) ≤ (uf.sig.toNat : Rat) := by exact_mod_cast Nat.zero_le _
  have h2 : (0 : Rat) < 2 ^ uf.toExpInt prec := Rat.two_pow_pos _
  exact Rat.mul_nonneg h1 (Rat.le_of_lt h2)

/-- `minSubnormalNumber` is a nonzero subnormal (hence normal-or-nonzero-subnormal). -/
theorem PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber (e s : Nat) (sign : Bool)
    (he : 0 < e) (hs : 0 < s) :
    (PackedFloat.minSubnormalNumber e s sign).isNormOrNonzeroSubnorm := by
  apply PackedFloat.isNormOrSubnorm_of_isSubnorm
  rw [PackedFloat.isNonzeroSubnorm_minSubnormalNumber_eq_decide]
  simp [he, hs]

/-- `minSubnormalNumber` is not NaN. -/
theorem PackedFloat.not_isNaN_minSubnormalNumber (e s : Nat) (sign : Bool)
    (he : 0 < e) (hs : 0 < s) :
    ¬ (PackedFloat.minSubnormalNumber e s sign).isNaN := by
  simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm
    (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber e s sign he hs)

/-! ## Branch (1): underflow

When `x` is positive but smaller in magnitude than the smallest representable
subnormal (i.e. `blastIsUnderflowNonneg`), the greatest representable PF ≤ x
is `+0`. -/

/--
Spec-side: when `x` underflows the target format, `+0` is a lawful lower
for `Number x.toRat'`.

This is hard: it requires knowing `x.toRat' < (minSubnormal target).toRat`
and that no negative PF can be `> x`'s value (since `x ≥ 0`).
-/
theorem isLawfulLower_Number_getZero_of_underflowNonneg
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : 0 < su)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hunder : x.blastIsUnderflowNonneg ep sp = true) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat')
      (PackedFloat.getZero ep sp false) := by
  have hnn : 0 ≤ x.toRat' := UnpackedFloat.toRat'_nonneg_of_sign_false x hxsign
  -- `x.toRat' < minSubnormalNumber.toRat = 2^minSubnormalExp`.
  have hlt : x.toRat' < (PackedFloat.minSubnormalNumber ep sp false).toRat := by
    rw [PackedFloat.toExtRat_minSubnormal_eq ep sp he hs]
    have hub := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x hsu hxsign
    have hexub : x.ex.toInt + 1 ≤ minNormalExp ep - (sp : Int) := by
      rw [UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu] at hunder
      simp only [decide_eq_true_eq] at hunder
      have : minSubnormalExp ep sp = minNormalExp ep - sp := by
        simp only [minSubnormalExp, maxSubnormalExp]; grind
      grind
    have hmono := Rat.two_pow_le_two_pow_of_le hexub
    grind
  have hgz : (PackedFloat.getZero ep sp false).toExtRat = ExtRat.Number 0 := by
    rw [PackedFloat.toExtRat_eq_toExtRat',
      PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero] <;> grind)]
  constructor
  · -- `getZero ≤ x` in the embedding: `0 ≤ x.toRat'`.
    show (PackedFloat.getZero ep sp false).toExtRat ≤ ExtRat.Number x.toRat'
    rw [hgz]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]; exact hnn
  · -- anything `≤ x` is at most `+0` (positives are `≥ minSubnormal > x.toRat'`).
    intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number x.toRat' := by
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
        -- `¬(n < minSubnormal)` (since `¬ n.isZero`) ⇒ `minSubnormal ≤ n`.
        have hnotlt : ¬ (n < PackedFloat.minSubnormalNumber ep sp false) := by
          rw [PackedFloat.isZero_iff_lt_minSubnormalNumber_of_isNaN_of_nonneg n he hs hnNaN hnsign]
          exact hnzero
        have hge : PackedFloat.minSubnormalNumber ep sp false ≤ n := by
          apply Classical.byContradiction
          intro hcon
          exact hnotlt (PackedFloat.lt_of_not_le _ _ (by grind) hcon)
        -- transport to `toRat`: `minSubnormal.toRat ≤ n.toRat`.
        have hgeR : (PackedFloat.minSubnormalNumber ep sp false).toRat ≤ n.toRat := by
          have hmin := PackedFloat.toExtRat'_le_toExtRat'_of_le (by grind) hs _ _ hminNaN hnNaN hge
          rw [PackedFloat.toExtRat'_eq_toRat_of hminfin, PackedFloat.toExtRat'_eq_toRat_of hn,
            ExtRat.ExtRat.num_le_num_iff] at hmin
          simpa using hmin
        have hnle : n.toRat ≤ x.toRat' := by
          rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
          simpa only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] using hy'
        grind

theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_underflow
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : 0 < su)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hunder : x.blastIsUnderflowNonneg ep sp = true) :
    (EUnpackedFloat.mkNumber (UnpackedFloat.mkZero false) :
      EUnpackedFloat eu (sp+1)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := PackedFloat.getZero ep sp false)
      (he := by grind) (hs := hs)
  · simp
  · simp; grind only
  · exact isLawfulLower_Number_getZero_of_underflowNonneg he hs heu hsu x hxsign hunder
  · -- `(mkZero false).num.toRat' = 0 = (getZero ep sp false).toRat`
    simp only [EUnpackedFloat.num_mkNumber]
    rw [UnpackedFloat.toRat'_mkZero,
        PackedFloat.toRat_eq_Zero_of_isZero _ (by simp [PackedFloat.isZero_getZero]; grind)]
  · -- `(mkZero false).num.sign = false = (getZero ep sp false).sign`
    simp [UnpackedFloat.mkZero, PackedFloat.sign_getZero]

/-! ### `maxNormalNumber` facts (shared by the overflow branch) -/

/-- `maxNormalNumber` is not NaN: its exponent is `allOnes - 1`, never `allOnes`
    (when `0 < ep`). -/
theorem PackedFloat.not_isNaN_maxNormalNumber (ep sp : Nat) (sign : Bool) (hep : 0 < ep) :
    ¬ (PackedFloat.maxNormalNumber ep sp sign).isNaN := by
  -- The exponent of `maxNormalNumber` is `allOnes - 1`, which differs from `allOnes`
  -- whenever `0 < ep`. `isNaN` requires `ex = allOnes`, so this case is excluded.
  simp [PackedFloat.maxNormalNumber, PackedFloat.isNaN]
  intros hcontra
  rw [BitVec.sub_eq_iff_eq_add] at hcontra
  simp at hcontra
  grind

/-- `maxNormalNumber` is a normal number when `1 < e`. -/
theorem PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber'
    {e s : Nat} (he : 1 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).isNormOrNonzeroSubnorm := by
  have h := PackedFloat.isNorm_maxNormalNumber_of_lt_e e s he sign
  simp only [PackedFloat.isNormOrNonzeroSubnorm]
  simp only [PackedFloat.isNorm] at h
  grind

/-- Negating the positive `maxNormalNumber` gives the negative one. -/
theorem PackedFloat.neg_maxNormalNumber_false' {ep sp : Nat} :
    - PackedFloat.maxNormalNumber ep sp false = PackedFloat.maxNormalNumber ep sp true := rfl

/-- The value of `maxNormalNumber` is strictly below `2 ^ (maxNormalExp + 1)`. -/
theorem PackedFloat.toRat_maxNormalNumber_lt_two_pow
    {ep sp : Nat} (hep : 2 < ep) (hs : 0 < sp) :
    (PackedFloat.maxNormalNumber ep sp false).toRat < (2 : Rat) ^ (maxNormalExp ep + 1) := by
  rw [PackedFloat.toRat, PackedFloat.toRatSig_maxNormalNumber ep sp hep,
    PackedFloat.toRatExp_maxNormalNumber ep sp hep]
  simp [Bool.toSign]
  have h2 : (2 : Rat) * (2 : Rat) ^ maxNormalExp ep = (2 : Rat) ^ (maxNormalExp ep + 1) :=
    Rat.mul_self_zpow_eq_zpow_succ (by grind)
  rw [← h2, Rat.sub_mul]
  have hpos : (0 : Rat) < 2 ^ maxNormalExp ep := Rat.two_pow_pos _
  have hsub : (0 : Rat) < 2 ^ (-(sp : Int)) := Rat.two_pow_pos _
  have : (0 : Rat) < 2 ^ (-(sp : Int)) * 2 ^ maxNormalExp ep := Rat.mul_positive hsub hpos
  grind

/-- The value of the positive `maxNormalNumber` is nonnegative. -/
theorem PackedFloat.toRat_maxNormalNumber_nonneg
    {ep sp : Nat} (he : 1 < ep) :
    (0 : Rat) ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
  have h := PackedFloat.sign_iff_toRat_neg
    (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp) he false)
  rw [PackedFloat.sign_maxNormalNumber] at h
  have h3 : ¬ ((PackedFloat.maxNormalNumber ep sp false).toRat < 0) := by
    simpa using h.symm
  grind

/-- The max normal value strictly increases with the significand width. -/
theorem PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ
    {ep sp : Nat} (hep : 2 < ep) (hs : 0 < sp) :
    (PackedFloat.maxNormalNumber ep sp false).toRat
      < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat := by
  rw [PackedFloat.toRat, PackedFloat.toRat,
    PackedFloat.toRatSig_maxNormalNumber ep sp hep,
    PackedFloat.toRatExp_maxNormalNumber ep sp hep,
    PackedFloat.toRatSig_maxNormalNumber ep (sp + 1) hep,
    PackedFloat.toRatExp_maxNormalNumber ep (sp + 1) hep]
  simp [Bool.toSign]
  have hpos : (0 : Rat) < 2 ^ maxNormalExp ep := Rat.two_pow_pos _
  rw [Rat.sub_mul, Rat.sub_mul]
  have hppos : (0 : Rat) < 2 ^ (-((sp : Int) + 1)) := Rat.two_pow_pos _
  have hstep : (2 : Rat) * (2 : Rat) ^ (-((sp : Int) + 1)) = 2 ^ (-((sp : Int) + 1) + 1) :=
    Rat.mul_self_zpow_eq_zpow_succ (by grind)
  have hexp : (-((sp : Int) + 1) + 1) = -(sp : Int) := by grind
  rw [hexp] at hstep
  have hlt : (2 : Rat) ^ (-((sp : Int) + 1)) < 2 ^ (-(sp : Int)) := by
    rw [← hstep]
    grind
  have h1 : (2 : Rat) ^ (-((sp : Int) + 1)) * 2 ^ maxNormalExp ep
      < 2 ^ (-(sp : Int)) * 2 ^ maxNormalExp ep := by
    rw [Rat.mul_lt_mul_cancel_right_of_lt hpos]
    exact hlt
  grind

/-- For `R` at or above `maxNormalNumber`, the greatest float `≤ R` is
`maxNormalNumber` itself. -/
theorem lower_Number_eq_maxNormalNumber_of_toRat_le
    {ep sp : Nat} (hep : 1 < ep) (hep0 : 0 < ep) (hsp : 0 < sp) (R : Rat)
    (hmax : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ R) :
    lower ep sp hep0 hsp (ExtRat.Number R) = PackedFloat.maxNormalNumber ep sp false := by
  have hfin := PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp) hep false
  have hnan := PackedFloat.not_isNaN_maxNormalNumber ep sp false hep0
  symm
  apply eq_lower_of_IsLawfulLower ep sp hep0 hsp _ _ (by simp)
  constructor
  · -- `maxNormalNumber ≤ R` in the embedding
    show (PackedFloat.maxNormalNumber ep sp false).toExtRat ≤ ExtRat.Number R
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfin]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
    exact hmax
  · -- anything `≤ R` is at most `maxNormalNumber`
    intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number R := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']
      exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'
      simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        exfalso
        rw [PackedFloat.toExtRat'_getInfinity hsp] at hy'
        simp at hy'
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp)
          (by simp [PackedFloat.sign_maxNormalNumber]) (by simp [hsp]) hnan
    | zeroCase sign =>
      cases sign
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp [PackedFloat.sign_getZero])
          (by simp [PackedFloat.sign_maxNormalNumber]) (by simp [hsp] <;> grind) hnan
      case false =>
        apply PackedFloat.le_of_toExtRat'_le_toExtRat' hep0 hsp
          (PackedFloat.getZero ep sp false) (PackedFloat.maxNormalNumber ep sp false)
          (by simp [hsp] <;> grind) hnan
        · intro h1 h2 h3
          simp [PackedFloat.sign_getZero] at h3
        · intro h1 _ _
          exfalso
          have h2 := PackedFloat.not_isZero_of_isNormOrSubnorm hfin
          simp at h2
          simp [h2] at h1
        · rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [hsp] <;> grind),
            PackedFloat.toExtRat'_eq_toRat_of hfin]
          simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
          exact PackedFloat.toRat_maxNormalNumber_nonneg hep
    | numCase n hn =>
      by_cases hsign : n.sign
      · exact PackedFloat.le_of_nonneg_of_neg _ _ hsign
          (by simp [PackedFloat.sign_maxNormalNumber])
          (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn) hnan
      · apply PackedFloat.le_maxNormalNumber_of_isNormOrNonzeroSubnorm_of_nonneg _ hep hn
        simpa using hsign

/-! ## Branch (2): overflow

When `x.toRat'` exceeds `maxNormalNumber`, the greatest representable PF ≤ x
is `maxNormalNumber ep sp false` (since +∞ would be > x in the embedding,
and there is no PF strictly between maxNormal and +∞). -/

/--
Spec-side: when `x` overflows the target format positively, `maxNormalNumber`
is a lawful lower for `Number x.toRat'`.

Proof: overflow forces `2^(maxNormalExp+1) ≤ x.toRat'` while
`maxNormalNumber.toRat < 2^(maxNormalExp+1)`, so `maxNormalNumber.toRat ≤ x.toRat'`;
then the greatest float `≤ x.toRat'` is `maxNormalNumber`
(`lower_Number_eq_maxNormalNumber_of_toRat_le`), and `lower` is lawful. -/
theorem isLawfulLower_Number_maxNormalNumber_of_overflowNonneg
    (hep : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hover  : x.blastIsEarlyOverflowNonneg ep sp = true) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat')
      (PackedFloat.maxNormalNumber ep sp false) := by
  -- overflow ⇒ ¬underflow ⇒ (normalized) msb set ⇒ nonzero.
  have hnotunder : x.blastIsUnderflowNonneg ep sp = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu]
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu] at hover
    have : minSubnormalExp ep sp ≤ maxNormalExp ep := by
      simp only [minSubnormalExp, maxSubnormalExp, minNormalExp, maxNormalExp]; grind
    simp only [decide_eq_true_eq] at hover; grind
  have hmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
    (by grind) hs heu x hxnorm hnotunder
  have hzero : ¬ x.isZero := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true]
    intro h0
    rw [h0, BitVec.msb_eq_getMsbD_zero] at hmsb
    simp at hmsb
  have hsu0 : 0 < su := by
    rcases Nat.eq_zero_or_pos su with h | h
    · subst h; rw [BitVec.msb_eq_getMsbD_zero] at hmsb; simp at hmsb
    · exact h
  -- `maxNormalNumber.toRat ≤ x.toRat'`, via the binade lower bound `2^x.ex ≤ x.toRat'`
  -- and the overflow fact `maxNormalExp < x.ex.toInt`.
  have hle : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ x.toRat' := by
    have h1 := PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
    have hexlb : maxNormalExp ep + 1 ≤ x.ex.toInt := by
      rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu] at hover
      simp only [decide_eq_true_eq] at hover; grind
    have hxlb := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x hsu0 hxsign hmsb
    have hmono := Rat.two_pow_le_two_pow_of_le hexlb
    grind
  -- `lower (Number x.toRat') = maxNormalNumber`, and `lower` is lawful.
  have heq := lower_Number_eq_maxNormalNumber_of_toRat_le (by grind) (by grind) hs x.toRat' hle
  have hlaw := IsLawfulLower_lower ep sp (by grind) hs (ExtRat.Number x.toRat')
  rw [heq] at hlaw
  exact hlaw

/--
The unpacked `maxNormal` and packed `maxNormalNumber` agree under `toRat`.
-/
theorem UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber
    {eu su ep sp : Nat}
    {sign : Bool}
    (hsp : 0 < sp)
    (hsu : sp + 1 ≤ su)
    (hep : 2 < ep)
    (heu : exponentWidth ep sp ≤ eu) :
    (UnpackedFloat.maxNormal eu su ep sp sign).toRat' (sp)
      = (PackedFloat.maxNormalNumber ep sp sign).toRat := by
  rw [UnpackedFloat.maxNormal, UnpackedFloat.toRat']
  simp [UnpackedFloat.toExpInt]
  rw [PackedFloat.toRat]
  rw [PackedFloat.toRatSig_maxNormalNumber]
  rw [PackedFloat.toRatExp_maxNormalNumber]
  rw [Nat.mod_eq_of_lt]
  · rw [Int.bmod_eq_of_le]
    · simp
      rw [Int.neg_sub]
      rw [Rat.zpow_sub_eq_zpow_mul_zpow (by grind)]
      rw [Rat.natCast_sub_of_le (by grind)]
      push_cast
      have : ((2 : Rat) ^ (sp + 1) - 1) * (2 : Rat) ^ (-sp : Int) = (2 - (2 : Rat) ^ (-sp : Int)) := by
        rw [Rat.sub_mul]
        simp only [Rat.one_mul]
        norm_cast
        rw [Nat.pow_succ]
        simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat]
        have := Rat.zpow_mul_zpow (show 2 ≠ 0 by grind) sp (-sp)
        simp only [Rat.zpow_natCast] at this
        grind only
      rw [← this]
      grind
    · simp [maxNormalExp]
      grind
    · simp [maxNormalExp]
      norm_cast
      apply Nat.lt_trans <| bias_lt_two_pow_exponent_sub_one ep
      apply Nat.pow_lt_pow_of_lt
      · grind
      · have := self_lt_exponentWidth ep sp (by grind) (by grind)
        grind
  · rw [Nat.pow_add]
    have : 2 ^ (sp + 1) ≤ 2 ^ su := by
      apply Nat.pow_le_pow_of_le
      · grind
      · grind
    have : 2 * 2 ^ sp ≤ 2 ^ su := by
      grind
    grind
  · grind
  · grind

/--
info: 'Fp.UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber

theorem UnpackedFloat.mkNumber_maxNormal_Rel_smtLibLower_of_overflow
    (hep : 2 < ep)
    (hsp : 0 < sp)
    (x : UnpackedFloat eu su)
    (hsu : sp + 1 ≤ sm)
    (heu : exponentWidth ep sp ≤ em)
    (heu' : exponentWidth ep sp ≤ eu)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (EUnpackedFloat.mkNumber (UnpackedFloat.maxNormal em sm ep sp false)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := PackedFloat.maxNormalNumber ep sp false)
      (by grind) (by grind)
  · simp
  · exact PackedFloat.not_isNaN_maxNormalNumber ep sp false (by grind)
  · exact isLawfulLower_Number_maxNormalNumber_of_overflowNonneg (by grind) (by grind) heu' x hxsign hxnorm hover
  · -- `num.toRat'` of the unpacked `maxNormal` equals `toRat` of the packed `maxNormalNumber`.
    simp only [EUnpackedFloat.num_mkNumber]
    apply UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber
    · grind
    · grind
    · grind
    · grind
  · -- sign is `false` on both sides
    simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]

/--
info: 'Fp.UnpackedFloat.mkNumber_maxNormal_Rel_smtLibLower_of_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.mkNumber_maxNormal_Rel_smtLibLower_of_overflow

/-! ## Branch (3): normal range — `blastRoundTowardZero` is a lawful lower

When `x` is in the normal range (no under/overflow), the bit-blasted
round-toward-zero `next := blastRoundTowardZero x ep sp` produces an
`UnpackedFloat (exponentWidth ep sp) (sp+1)` whose value is the greatest PF representable
in `(ep, sp)` that is ≤ `x.toRat'`.

To use the helper we need *some* `PackedFloat ep sp` `pf` such that
  • `IsLawfulLower (Number x.toRat') pf`
  • `next.toRat' = pf.toRat`
  • `next.sign  = pf.sign`

Such a `pf` exists because `next` is by construction representable in the
target format (its exponent and significand are within `(ep, sp)` bounds in
this branch); we don't have a single named constructor for it, so we
existentially extract one. -/

/-
Key facts:

- the packed float will be the one given by 'blastLowerNonneg.pack'
- pack preserves the toRat, nor does it change the sign
- we need a lemma that says that it's a lawful lower if the 'toRat' is equal, and then distance
  btween 'pf.toRat' and 'x.toRat' is less than 1 ulp of 'pf' (which is the same as 1 ulp of 'blastRoundTowardZero x').
  This needs a separate lemma or two.
- These key facts establish the existence of the 'pf'.
- TODO: maybe worth it to replace the existential with the concrete pf we know.
-/
/-- (M) Full not-underflow ⇒ early not-underflow.

`blastIsEarlyUnderflowNonneg` is the coarser test (exponent strictly below the
subnormal range), so it is subsumed by `blastIsUnderflowNonneg`. This lets the
`truncateFittingExponent` invariance lemmas — which are stated with the `Early`
form — apply under the hypothesis the keystone is actually given.

Proof: discharge via `blastUnderflowNonneg_eq_decide` and
`blastIsEarlyUnderflowNonneg_eq_decide` + `grind` on the exponent bounds. -/
theorem UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false) :
    x.blastIsEarlyUnderflowNonneg ep sp = false := by
  -- `not-underflow` says `minSubnormalExp ≤ x.ex.toInt`; since `minSubnormalExp - 1`
  -- is strictly smaller, `early-underflow` (testing `< minSubnormalExp - 1`) is false.
  rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu]
  rw [UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu] at hnotunder
  simp only [decide_eq_false_iff_not] at hnotunder ⊢
  grind

/--
info: 'Fp.UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg

/-- (U) The sub-ulp gap — the heart of round-toward-zero correctness.

The bits discarded by `blastRoundTowardZero` are worth strictly less than one ulp
of the *target* grid, so the rounded value plus one ulp strictly overshoots `x`.
The ulp exponent is `x.ex.toInt - sp + off` where `off = (minNormalExp ep - x.ex.toInt).toNat`
is the subnormal shift: in the normal range `off = 0` (ulp `2^(ex-sp)`), in the
subnormal range `off = minNormalExp - ex` (ulp `2^(minNormalExp-sp)`, the subnormal
quantum). The inequality is strict even when `x` is already representable.

Proof: factor out the common weight `2^(ex-(su-1))`; the goal reduces to
`x.sig.toNat < cleared.sig.toNat + 2^L` with `L = lsbIndex.toNat = (su-(sp+1))+off`,
which holds because `blastClearSignificand` zeroes exactly the low `L` bits and
`extractMsb'` then re-reads `cleared / 2^(su-(sp+1))`. -/
theorem UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    x.toRat' <
      (x.blastRoundTowardZero ep sp).toRat'
        + (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
  -- Exponent / guard-index bounds from "no early over/underflow".
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  -- `L = guardBitIndex + 1 = (su-(sp+1)) + off`, `m = su-(sp+1) ≤ L`.
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  -- Clearing rounds the significand down to a multiple of `2^L`; `extractMsb'` re-reads
  -- `cleared / 2^m`, and since `m ≤ L` this recovers `cleared` exactly.
  have hcl := UnpackedFloat.blastClearSignificand_sig_toNat_eq x ep sp
  have hdvd : 2 ^ (su - (sp + 1)) ∣ (x.blastClearSignificand ep sp).sig.toNat := by
    rw [hcl]; exact Nat.two_pow_dvd_div_mul_two_pow x.sig.toNat (by grind)
  have hrm : (x.blastRoundTowardZero ep sp).sig.toNat * 2 ^ (su - (sp + 1))
      = (x.blastClearSignificand ep sp).sig.toNat := by
    rw [sig_blastRoundTowardZero, BitVec.toNat_extractMsb'_zero _ (by grind)]
    exact Nat.div_mul_cancel hdvd
  -- The core Nat gap: `x.sig.toNat < cleared.sig.toNat + 2^L`.
  have hnatN : x.sig.toNat
      < (x.blastClearSignificand ep sp).sig.toNat
          + 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) := by
    rw [hcl, hLeq]
    have hk : 0 < 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) :=
      Nat.two_pow_pos _
    have h1 := Nat.div_add_mod x.sig.toNat
      (2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))))
    have h2 := Nat.mod_lt x.sig.toNat hk
    grind
  have hnat : (x.sig.toNat : Rat)
      < (x.blastClearSignificand ep sp).sig.toNat
          + (2 : Rat) ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) := by
    exact_mod_cast hnatN
  -- Expand both `toRat'` and factor the common weight `C = 2^(ex - (su-1))`.
  rw [UnpackedFloat.toRat', UnpackedFloat.toRat', sign_blastRoundTowardZero, hxsign,
    UnpackedFloat.toExpInt, UnpackedFloat.toExpInt, ex_blastRoundTowardZero,
    UnpackedFloat.toNat_toSigNat_eq, UnpackedFloat.toNat_toSigNat_eq]
  have hCpos : (0 : Rat) < 2 ^ (x.ex.toInt - ((su : Int) - 1)) := Rat.two_pow_pos _
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  -- rewrite the three scaled terms onto the base weight `C = 2^(ex-(su-1))`.
  have hround : (Bool.toSign false : Rat) * (x.blastRoundTowardZero ep sp).sig.toNat
        * 2 ^ (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
      = (x.blastClearSignificand ep sp).sig.toNat * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    have hrmR : (↑(x.blastRoundTowardZero ep sp).sig.toNat : Rat) * 2 ^ (su - (sp + 1))
        = ↑(x.blastClearSignificand ep sp).sig.toNat := by exact_mod_cast hrm
    have hexp : (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
        = (↑(su - (sp + 1)) : Int) + (x.ex.toInt - ((su : Int) - 1)) := by
      rw [Int.natCast_sub (show sp + 1 ≤ su by grind)]
      have e1 : ((sp + 1) - 1 : Nat) = sp := by grind
      rw [e1]; push_cast; grind
    rw [hexp, ← Rat.zpow_mul_zpow (by grind), Rat.zpow_natCast, hsg, ← hrmR]
    grind
  have hulp : (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
      = (2 : Rat) ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)))
          * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    rw [← Rat.zpow_natCast (2 : Rat) ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))),
      Rat.zpow_mul_zpow (by grind)]
    congr 1
    push_cast [Int.natCast_sub (show sp + 1 ≤ su by grind)]; grind
  have hx : (Bool.toSign false : Rat) * x.sig.toNat * 2 ^ (-((↑(su - 1) : Int) - x.ex.toInt))
      = (x.sig.toNat : Rat) * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    have hexp : (-((↑(su - 1) : Int) - x.ex.toInt)) = x.ex.toInt - ((su : Int) - 1) := by
      rw [Int.natCast_sub (show 1 ≤ su by grind)]; push_cast; grind
    rw [hexp, hsg]; grind
  rw [hround, hulp, hx]
  -- `x.sig.toNat * C < cleared.sig.toNat * C + (2^L) * C`, cancel `C > 0`.
  have hmul := (Rat.mul_lt_mul_cancel_right_of_lt hCpos).mpr hnat
  grind

/--
info: 'Fp.UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp

/-- (GLB) A non-NaN nonnegative packed float that is `≤ R` and lies within one ulp
below `R` is the greatest lower bound of `R`.

Reusable spec-side lemma. Proof: `constructor`.
  * clause 1 (`embed pf ≤ R`): from `hle` via `toExtRat'_eq_toRat_of` + `num_le_num_iff`.
  * clause 2 (`∀ pf', embed pf' ≤ R → pf' ≤ pf`): case-split `pf'` with
    `PackedFloat.kindCasesNaNInfZeroNum`; NaN and `+∞` are excluded by `embed ≤ R`,
    the negative kinds are `≤` the nonnegative `pf`, and for the positive-finite case
    a `pf < pf'` would force `pf.toRat + ulp ≤ pf'.toRat ≤ R` (via
    `toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false`), contradicting `hlt`.
Mirror the body of `lower_Number_eq_maxNormalNumber_of_toRat_le`. -/
theorem PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp
    (he : 1 < ep) (hs : 0 < sp)
    (R : Rat) (pf : PackedFloat ep sp)
    (hsign : pf.sign = false)
    (hfin : pf.isNormOrNonzeroSubnorm)
    (hle : pf.toRat ≤ R)
    (hlt : R < pf.toRat + (2 : Rat) ^ (-(sp : Int)) * 2 ^ pf.toRatExp) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number R) pf := by
  have hpfNaN : ¬ pf.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfin
  constructor
  · -- `pf ≤ R` in the embedding.
    show pf.toExtRat ≤ ExtRat.Number R
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfin]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
    exact hle
  · -- Any representable `y` with embedded value `≤ R` is at most `pf`.
    intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number R := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']; exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'
      simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        -- `+∞` cannot be `≤ Number R`.
        exfalso
        rw [PackedFloat.toExtRat'_getInfinity hs] at hy'
        simp at hy'
      case true =>
        -- `-∞ ≤` the nonnegative `pf`.
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp) hsign (by simp [hs]) hpfNaN
    | zeroCase sign =>
      -- `±0 ≤` the nonnegative `pf`.
      exact PackedFloat.getZero_le_of_nonneg (by grind) hs pf hsign hpfNaN
    | numCase n hn =>
      have hnNaN : ¬ n.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn
      by_cases hnsign : n.sign
      · -- `n` negative, `pf` nonnegative.
        exact PackedFloat.le_of_nonneg_of_neg n pf hnsign hsign hnNaN hpfNaN
      · -- `n` nonnegative: the one-ulp gap above `pf` rules out `pf < n ≤ R`.
        simp only [Bool.not_eq_true] at hnsign
        apply Classical.byContradiction
        intro hcon
        have hltn : pf < n := PackedFloat.lt_of_not_le n pf (by grind) hcon
        have hulp := PackedFloat.toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false
          (by grind) hs pf n hsign hnsign
          (by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hfin)
          (by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hn)
          hpfNaN hnNaN
          (by simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hfin)
          (by simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hn)
          hltn
        have hnR : n.toRat ≤ R := by
          rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
          simpa only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] using hy'
        grind

/--
info: 'Fp.PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp

/-- Upper (least-upper-bound) analog of `isLawfulLower_of_toRat_le_of_lt_add_ulp`.
If `pf` is a nonneg finite float, `0 < R ≤ pf.toRat`, and every nonneg finite float
strictly below `pf` has value `< R` (i.e. no representable lies in `[R, pf)`),
then `pf` is the lawful upper (least upper bound) of `R`.

The `0 < R` hypothesis is necessary: a positive `pf` can only be the least upper bound
of a positive `R` (for `R ≤ 0`, `+0` would be a smaller upper bound). It makes the
`±∞` / `±0` / negative cases vacuous. -/
theorem PackedFloat.isLawfulUpper_of_le_toRat_of_no_float_between
    (he : 1 < ep) (hs : 0 < sp)
    (R : Rat) (pf : PackedFloat ep sp)
    (hsign : pf.sign = false)
    (hfin : pf.isNormOrNonzeroSubnorm)
    (hRpos : 0 < R)
    (hle : R ≤ pf.toRat)
    (hbetween : ∀ (y : PackedFloat ep sp), y.sign = false → y.isNormOrNonzeroSubnorm →
        y.toRat < pf.toRat → y.toRat < R) :
    SmtLibSemantics.IsLawfulUpper (ExtRat.Number R) pf := by
  have hpfNaN : ¬ pf.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfin
  have hpfZero : ¬ pf.isZero := by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hfin
  have hpfInf : ¬ pf.isInfinite := by
    simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hfin
  constructor
  · -- `Number R ≤ pf` in the embedding.
    show ExtRat.Number R ≤ pf.toExtRat
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfin]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
    exact hle
  · -- Any representable `y` with `R ≤` its embedded value is at least `pf`.
    intro y hy
    have hy' : ExtRat.Number R ≤ y.toExtRat' := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']; exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'
      simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        -- `pf ≤ +∞`.
        exact (PackedFloat.le_getInfinity_false_of_not_isNaN hs pf).mpr hpfNaN
      case true =>
        -- `Number R ≤ -∞` is impossible.
        exfalso
        rw [PackedFloat.toExtRat'_getInfinity hs] at hy'
        simp at hy'
    | zeroCase sign =>
      -- `Number R ≤ ±0` forces `R ≤ 0`, contradicting `0 < R`.
      exfalso
      rw [PackedFloat.toExtRat'_eq_zero_of_isZero (PackedFloat.getZero ep sp sign)
        (by simp only [PackedFloat.isZero_getZero]; grind)] at hy'
      simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] at hy'
      grind
    | numCase n hn =>
      have hnNaN : ¬ n.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn
      have hnZero : ¬ n.isZero := by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hn
      have hnInf : ¬ n.isInfinite := by
        simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hn
      by_cases hnsign : n.sign
      · -- `n` negative ⇒ `n.toRat < 0 < R`, contradicting `R ≤ n.toRat`.
        exfalso
        rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
        simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] at hy'
        have hneg : n.toRat < 0 := by
          have := PackedFloat.sign_iff_toRat_neg hn; grind
        grind
      · -- `n` nonneg: the no-float-between hypothesis rules out `R ≤ n < pf`.
        simp only [Bool.not_eq_true] at hnsign
        apply Classical.byContradiction
        intro hcon
        have hltn : n < pf := PackedFloat.lt_of_not_le pf n (by grind) hcon
        have hnlt : n.toRat < pf.toRat :=
          PackedFloat.toRat_lt_toRat_of_lt (by grind) hs n pf hnZero hpfZero hnNaN hpfNaN hnInf hpfInf hltn
        have hnR : R ≤ n.toRat := by
          rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
          simpa only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] using hy'
        have := hbetween n hnsign hn hnlt
        grind

/--
info: 'Fp.PackedFloat.isLawfulUpper_of_le_toRat_of_no_float_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms PackedFloat.isLawfulUpper_of_le_toRat_of_no_float_between

/-- Round-toward-zero never increases the (nonnegative) value: `round ≤ x`.
The rounded value equals the cleared significand re-read at precision `sp`, and clearing
only drops low bits. -/
theorem UnpackedFloat.blastRoundTowardZero_toRat'_le_toRat'
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastRoundTowardZero ep sp).toRat' ≤ x.toRat' := by
  have hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false :=
    UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg he hs heu x hnotunder
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  -- `round.sig.toNat * 2^m = cleared.sig.toNat ≤ x.sig.toNat`.
  have hdvd : 2 ^ (su - (sp + 1)) ∣ (x.blastClearSignificand ep sp).sig.toNat := by
    rw [UnpackedFloat.blastClearSignificand_sig_toNat_eq]
    exact Nat.two_pow_dvd_div_mul_two_pow x.sig.toNat (by grind)
  have hrm : (x.blastRoundTowardZero ep sp).sig.toNat * 2 ^ (su - (sp + 1))
      = (x.blastClearSignificand ep sp).sig.toNat := by
    rw [sig_blastRoundTowardZero, BitVec.toNat_extractMsb'_zero _ (by grind)]
    exact Nat.div_mul_cancel hdvd
  have hcllen : (x.blastClearSignificand ep sp).sig.toNat ≤ x.sig.toNat :=
    UnpackedFloat.blastClearSignificand_sig_toNat_le x ep sp
  -- expand both `toRat'` onto the base weight `C = 2^(ex - (su-1))`.
  rw [UnpackedFloat.toRat', UnpackedFloat.toRat', sign_blastRoundTowardZero, hxsign,
    UnpackedFloat.toExpInt, UnpackedFloat.toExpInt, ex_blastRoundTowardZero,
    UnpackedFloat.toNat_toSigNat_eq, UnpackedFloat.toNat_toSigNat_eq]
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  have hCpos : (0 : Rat) < 2 ^ (x.ex.toInt - ((su : Int) - 1)) := Rat.two_pow_pos _
  have hround : (Bool.toSign false : Rat) * (x.blastRoundTowardZero ep sp).sig.toNat
        * 2 ^ (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
      = (x.blastClearSignificand ep sp).sig.toNat * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    have hrmR : (↑(x.blastRoundTowardZero ep sp).sig.toNat : Rat) * 2 ^ (su - (sp + 1))
        = ↑(x.blastClearSignificand ep sp).sig.toNat := by exact_mod_cast hrm
    have hexp : (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
        = (↑(su - (sp + 1)) : Int) + (x.ex.toInt - ((su : Int) - 1)) := by
      rw [Int.natCast_sub (show sp + 1 ≤ su by grind)]
      have e1 : ((sp + 1) - 1 : Nat) = sp := by grind
      rw [e1]; push_cast; grind
    rw [hexp, ← Rat.zpow_mul_zpow (by grind), Rat.zpow_natCast, hsg, ← hrmR]; grind
  have hx : (Bool.toSign false : Rat) * x.sig.toNat * 2 ^ (-((↑(su - 1) : Int) - x.ex.toInt))
      = (x.sig.toNat : Rat) * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    have hexp : (-((↑(su - 1) : Int) - x.ex.toInt)) = x.ex.toInt - ((su : Int) - 1) := by
      rw [Int.natCast_sub (show 1 ≤ su by grind)]; push_cast; grind
    rw [hexp, hsg]; grind
  rw [hround, hx]
  have hle : (↑(x.blastClearSignificand ep sp).sig.toNat : Rat) ≤ x.sig.toNat := by
    exact_mod_cast hcllen
  exact (Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hCpos))

/-- `blastRoundTowardZero`'s value, expanded onto the base weight `C = 2^(ex - (su-1))`:
it equals `cleared.sig.toNat · C`. (Extracted from the `≤` proof's `hround` step; the
`blastSuccessorAwayFromZero` bound mirrors this with `cleared.sig.toNat + 2^(g+1)`.) -/
theorem UnpackedFloat.blastRoundTowardZero_toRat'_eq_clearSignificand_mul
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastRoundTowardZero ep sp).toRat'
      = (x.blastClearSignificand ep sp).sig.toNat
          * (2 : Rat) ^ (x.ex.toInt - ((su : Int) - 1)) := by
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  have hdvd : 2 ^ (su - (sp + 1)) ∣ (x.blastClearSignificand ep sp).sig.toNat := by
    rw [UnpackedFloat.blastClearSignificand_sig_toNat_eq]
    exact Nat.two_pow_dvd_div_mul_two_pow x.sig.toNat (by grind)
  have hrm : (x.blastRoundTowardZero ep sp).sig.toNat * 2 ^ (su - (sp + 1))
      = (x.blastClearSignificand ep sp).sig.toNat := by
    rw [sig_blastRoundTowardZero, BitVec.toNat_extractMsb'_zero _ (by grind)]
    exact Nat.div_mul_cancel hdvd
  rw [UnpackedFloat.toRat', sign_blastRoundTowardZero, hxsign,
    UnpackedFloat.toExpInt, ex_blastRoundTowardZero, UnpackedFloat.toNat_toSigNat_eq]
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  have hrmR : (↑(x.blastRoundTowardZero ep sp).sig.toNat : Rat) * 2 ^ (su - (sp + 1))
      = ↑(x.blastClearSignificand ep sp).sig.toNat := by exact_mod_cast hrm
  have hexp : (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
      = (↑(su - (sp + 1)) : Int) + (x.ex.toInt - ((su : Int) - 1)) := by
    rw [Int.natCast_sub (show sp + 1 ≤ su by grind)]
    have e1 : ((sp + 1) - 1 : Nat) = sp := by grind
    rw [e1]; push_cast; grind
  rw [hexp, ← Rat.zpow_mul_zpow (by grind), Rat.zpow_natCast, hsg, ← hrmR]; grind

/--
info: 'Fp.UnpackedFloat.blastRoundTowardZero_toRat'_eq_clearSignificand_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastRoundTowardZero_toRat'_eq_clearSignificand_mul

/-- A nonnegative unpacked float's value expanded onto the base weight `2^(ex-(su-1))`. -/
theorem UnpackedFloat.toRat'_eq_sig_toNat_mul (x : UnpackedFloat eu su)
    (hxsign : x.sign = false) (hsu1 : 1 ≤ su) :
    x.toRat' = x.sig.toNat * (2 : Rat) ^ (x.ex.toInt - ((su : Int) - 1)) := by
  rw [UnpackedFloat.toRat', hxsign, UnpackedFloat.toExpInt, UnpackedFloat.toNat_toSigNat_eq]
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  rw [hsg]
  have hexp : (-(((su - 1 : Nat) : Int) - x.ex.toInt)) = (x.ex.toInt - ((su : Int) - 1)) := by
    rw [Int.natCast_sub hsu1]; push_cast; grind
  rw [hexp]; grind

/--
info: 'Fp.UnpackedFloat.toRat'_eq_sig_toNat_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.toRat'_eq_sig_toNat_mul

/-- Forward: if no rounding is needed, truncating toward zero preserves the value. -/
theorem UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (h : x.needsRounding ep sp = false) :
    (x.blastRoundTowardZero ep sp).toRat' = x.toRat' := by
  rw [UnpackedFloat.blastRoundTowardZero_toRat'_eq_clearSignificand_mul he hs heu hsu x hxsign
      hnotunder hnotover,
    UnpackedFloat.toRat'_eq_sig_toNat_mul x hxsign (by grind)]
  have hsig : (x.blastClearSignificand ep sp).sig = x.sig :=
    UnpackedFloat.blastClearSignificand_sig_eq_of_not_needsRounding x ep sp h
  rw [hsig]

/--
info: 'Fp.UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding

/-- Backward: if truncating toward zero preserves the value, no rounding was needed. -/
theorem UnpackedFloat.not_needsRounding_of_blastRoundTowardZero_toRat'_eq_toRat'
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (h : (x.blastRoundTowardZero ep sp).toRat' = x.toRat') :
    x.needsRounding ep sp = false := by
  rw [UnpackedFloat.blastRoundTowardZero_toRat'_eq_clearSignificand_mul he hs heu hsu x hxsign
      hnotunder hnotover,
    UnpackedFloat.toRat'_eq_sig_toNat_mul x hxsign (by grind)] at h
  have hW : (2 : Rat) ^ (x.ex.toInt - ((su : Int) - 1)) ≠ 0 := Rat.two_pow_ne_zero _
  have hcast : ((x.blastClearSignificand ep sp).sig.toNat : Rat) = (x.sig.toNat : Rat) := by
    grind
  have hnat : (x.blastClearSignificand ep sp).sig.toNat = x.sig.toNat := by exact_mod_cast hcast
  have hsig : (x.blastClearSignificand ep sp).sig = x.sig := BitVec.toNat_inj.mp hnat
  exact UnpackedFloat.not_needsRounding_of_blastClearSignificand_sig_eq x ep sp hsig

/--
info: 'Fp.UnpackedFloat.not_needsRounding_of_blastRoundTowardZero_toRat'_eq_toRat'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.not_needsRounding_of_blastRoundTowardZero_toRat'_eq_toRat'

/-- **A nonnegative in-range float is exactly representable at the target precision iff it
needs no rounding** (guard and sticky bits both zero): truncating toward zero preserves the
value iff `needsRounding = false`. -/
theorem UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastRoundTowardZero ep sp).toRat' = x.toRat' ↔ x.needsRounding ep sp = false :=
  ⟨UnpackedFloat.not_needsRounding_of_blastRoundTowardZero_toRat'_eq_toRat' he hs heu hsu x hxsign
     hnotunder hnotover,
   UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding he hs heu hsu x hxsign
     hnotunder hnotover⟩

/--
info: 'Fp.UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding

/-- `blastSuccessorAwayFromZero`'s value, expanded onto the base weight `C = 2^(ex-(su-1))`:
it equals `(cleared.sig.toNat + 2^(g+1)) · C` (where `g = guardBitIndex.toNat`), i.e. one
ulp above `blastRoundTowardZero`. Both the no-carry and carry cases give the same value. -/
theorem UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_clearSignificand_mul
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastSuccessorAwayFromZero ep sp).toRat'
      = ((x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1))
          * (2 : Rat) ^ (x.ex.toInt - ((su : Int) - 1)) := by
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  have hgsu : (x.guardBitIndex ep sp).toNat + 1 < su := by rw [hLeq]; grind
  have hmle : su - (sp + 1) ≤ (x.guardBitIndex ep sp).toNat + 1 := by rw [hLeq]; grind
  -- Abbreviations: g+1 (guard index), cleared significand value `cl`, rounded value `S = cl + 2^(g+1)`.
  -- `lsbMask` value.
  have hlsb : (BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).toNat
      = 2 ^ ((x.guardBitIndex ep sp).toNat + 1) :=
    BitVec.toNat_zeroExtend_oneHotBV_shiftLeft_one (x.guardBitIndex ep sp) hgsu
  have hcllt : (x.blastClearSignificand ep sp).sig.toNat < 2 ^ su :=
    (x.blastClearSignificand ep sp).sig.isLt
  have hg1lt : 2 ^ ((x.guardBitIndex ep sp).toNat + 1) < 2 ^ su :=
    Fp.Nat.two_pow_lt_two_pow_of_lt hgsu
  have hpow1 : 2 ^ (su + 1) = 2 ^ su + 2 ^ su := by rw [Nat.pow_succ]; omega
  -- `SUM.toNat = S`.
  have hsum : (BitVec.zeroExtend (su + 1) (x.blastClearSignificand ep sp).sig
        + BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).toNat
      = (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, hlsb,
      Nat.mod_eq_of_lt (by omega : (x.blastClearSignificand ep sp).sig.toNat < 2 ^ (su + 1)),
      Nat.mod_eq_of_lt (by omega)]
  -- `S` is divisible by `2^(su-(sp+1))` (so `extractMsb'` recovers it).
  have hclform : (x.blastClearSignificand ep sp).sig.toNat
      = x.sig.toNat / 2 ^ ((x.guardBitIndex ep sp).toNat + 1)
          * 2 ^ ((x.guardBitIndex ep sp).toNat + 1) :=
    UnpackedFloat.blastClearSignificand_sig_toNat_eq x ep sp
  have hcldvd : 2 ^ ((x.guardBitIndex ep sp).toNat + 1) ∣ (x.blastClearSignificand ep sp).sig.toNat := by
    rw [hclform]; exact Nat.dvd_mul_left _ _
  have hSdvd : 2 ^ (su - (sp + 1))
      ∣ ((x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1)) := by
    apply Nat.dvd_add
    · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hmle) hcldvd
    · exact Nat.pow_dvd_pow 2 hmle
  -- `S ≤ 2^su` (consecutive multiples of `2^(g+1)`): needed for the carry case to pin `S = 2^su`.
  have hSle : (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) ≤ 2 ^ su := by
    obtain ⟨q, hq⟩ := hcldvd
    have hsplit : 2 ^ su
        = 2 ^ ((x.guardBitIndex ep sp).toNat + 1) * 2 ^ (su - ((x.guardBitIndex ep sp).toNat + 1)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hqlt : q < 2 ^ (su - ((x.guardBitIndex ep sp).toNat + 1)) := by
      apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ ((x.guardBitIndex ep sp).toNat + 1))
      rw [← hq, ← hsplit]; exact hcllt
    have hmul : 2 ^ ((x.guardBitIndex ep sp).toNat + 1) * (q + 1) ≤ 2 ^ su := by
      rw [hsplit]; exact Nat.mul_le_mul_left _ (by omega)
    rw [hq, ← Nat.mul_succ]; exact hmul
  simp only [UnpackedFloat.blastSuccessorAwayFromZero, UnpackedFloat.toRat',
    UnpackedFloat.toExpInt, UnpackedFloat.toNat_toSigNat_eq, clearSignificand_sign,
    clearSignificand_ex, hxsign]
  -- `SUM.msb` is the overflow predicate `2^su ≤ S`.
  have hmsb : (BitVec.zeroExtend (su + 1) (x.blastClearSignificand ep sp).sig
        + BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).msb
      = decide (2 ^ su ≤ (x.blastClearSignificand ep sp).sig.toNat
          + 2 ^ ((x.guardBitIndex ep sp).toNat + 1)) := by
    rw [BitVec.msb_eq_decide, hsum]; simp
  rw [hmsb]
  by_cases hov : 2 ^ su ≤ (x.blastClearSignificand ep sp).sig.toNat
      + 2 ^ ((x.guardBitIndex ep sp).toNat + 1)
  · -- carry: significand overflowed, exponent incremented.  `S = 2^su`.
    have hSeq : (x.blastClearSignificand ep sp).sig.toNat
        + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) = 2 ^ su := Nat.le_antisymm hSle hov
    simp only [hov, decide_true, if_true]
    have hleadext : ((BitVec.leadingOne su).extractMsb' 0 (sp + 1)).toNat = 2 ^ sp := by
      have he2 : (su - 1) - (su - (sp + 1)) = sp := by omega
      rw [BitVec.toNat_extractMsb'_zero _ (by omega), BitVec.toNat_leadingOne (by omega),
        Nat.pow_div (by omega) (by omega), he2]
    have hexI : (x.ex + 1#eu).toInt = x.ex.toInt + 1 := by
      have hew1 : 1 < exponentWidth ep sp := one_lt_exponentWidth
      have heu1 : 1 < eu := by omega
      have hbias : bias ep + 1 < 2 ^ (exponentWidth ep sp - 1) :=
        bias_plus_one_lt_two_pow_exponentWidth_minus_one ep sp he hs
      have hminS := neg_two_pow_exponentWidth_lt_minSubnormalExp (e := ep) (s := sp) he hs
      have hmaxN : maxNormalExp ep = (bias ep : Int) := rfl
      have hpowle : (2 : Int) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) := by
        have h1 : (2 : Nat) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hc1 : ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int)
            = (2 : Int) ^ (exponentWidth ep sp - 1) := by push_cast; rfl
        have hc2 : ((2 ^ (eu - 1) : Nat) : Int) = (2 : Int) ^ (eu - 1) := by push_cast; rfl
        omega
      have hcastBias : ((bias ep : Nat) : Int) + 1 < (2 : Int) ^ (exponentWidth ep sp - 1) := by
        have hb : ((bias ep + 1 : Nat) : Int) < ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int) := by
          exact_mod_cast hbias
        push_cast at hb; omega
      have h2pow : ∀ n : Nat, 0 < n → (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
        intro n hn
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
        rw [Int.pow_succ]; simp; omega
      have h2eu : (2 : Int) ^ eu = 2 * 2 ^ (eu - 1) := h2pow eu (by omega)
      rw [BitVec.toInt_add, BitVec.toInt_one_of_lt heu1, Int.bmod_eq_of_le] <;> push_cast <;> omega
    rw [hleadext, hexI]
    have hSeqR : ((x.blastClearSignificand ep sp).sig.toNat : Rat)
        + (2 : Rat) ^ ((x.guardBitIndex ep sp).toNat + 1) = (2 : Rat) ^ su := by exact_mod_cast hSeq
    have hfs : ((false.toSign : Int) : Rat) = 1 := by simp [Bool.toSign]
    rw [hSeqR, hfs, Rat.one_mul,
      show ((sp + 1 - 1 : Nat) : Int) = (sp : Int) by push_cast; omega]
    push_cast
    simp only [← Rat.zpow_natCast]
    rw [Rat.zpow_mul_zpow (by grind), Rat.zpow_mul_zpow (by grind)]
    congr 1; push_cast; omega
  · -- no carry: `S < 2^su`, exponent unchanged.
    have hSlt : (x.blastClearSignificand ep sp).sig.toNat
        + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) < 2 ^ su := by omega
    simp only [hov, decide_false]
    rw [if_neg (by decide), if_neg (by decide),
      BitVec.toNat_extractMsb'_zero _ (by omega), BitVec.toNat_setWidth, hsum,
      Nat.mod_eq_of_lt hSlt]
    have hfs : ((false.toSign : Int) : Rat) = 1 := by simp [Bool.toSign]
    have hVRnat : ((x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1))
          / 2 ^ (su - (sp + 1)) * 2 ^ (su - (sp + 1))
        = (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) :=
      Nat.div_mul_cancel hSdvd
    have hVR : (↑(((x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1))
            / 2 ^ (su - (sp + 1))) : Rat) * 2 ^ (su - (sp + 1))
        = ↑(x.blastClearSignificand ep sp).sig.toNat + (2 : Rat) ^ ((x.guardBitIndex ep sp).toNat + 1) := by
      exact_mod_cast hVRnat
    have hexp : (-((↑(sp + 1 - 1) : Int) - x.ex.toInt))
        = (↑(su - (sp + 1)) : Int) + (x.ex.toInt - ((su : Int) - 1)) := by
      rw [Int.natCast_sub (show sp + 1 ≤ su by grind)]
      have e1 : ((sp + 1 - 1) : Nat) = sp := by grind
      rw [e1]; push_cast; grind
    rw [hfs, Rat.one_mul, hexp, ← Rat.zpow_mul_zpow (by grind), Rat.zpow_natCast, ← hVR]
    grind

/--
info: 'Fp.UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_clearSignificand_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_clearSignificand_mul

/-- `blastSuccessorAwayFromZero` is exactly one ulp above `blastRoundTowardZero`
(same `ulp` as the `blastRoundTowardZero` gap lemma). -/
theorem UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastSuccessorAwayFromZero ep sp).toRat'
      = (x.blastRoundTowardZero ep sp).toRat'
        + (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  rw [blastSuccessorAwayFromZero_toRat'_eq_clearSignificand_mul he hs heu hsu x hxsign hnotunder hnotover,
    blastRoundTowardZero_toRat'_eq_clearSignificand_mul he hs heu hsu x hxsign hnotunder hnotover]
  have hulp : (2 : Rat) ^ ((x.guardBitIndex ep sp).toNat + 1)
        * (2 : Rat) ^ (x.ex.toInt - ((su : Int) - 1))
      = (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
    rw [← Rat.zpow_natCast (2 : Rat) ((x.guardBitIndex ep sp).toNat + 1),
      Rat.zpow_mul_zpow (by grind)]
    congr 1
    rw [hLeq, Int.natCast_add, Int.natCast_sub (show sp + 1 ≤ su by grind)]
    push_cast; omega
  rw [Rat.add_mul, hulp]

/--
info: 'Fp.UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp

/-- (B1) `blastSuccessorAwayFromZero` is strictly above the input: `x < successor`. -/
theorem UnpackedFloat.toRat'_lt_blastSuccessorAwayFromZero_toRat'
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    x.toRat' < (x.blastSuccessorAwayFromZero ep sp).toRat' := by
  rw [blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp he hs heu hsu x hxsign hnotunder hnotover]
  exact UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp he hs heu hsu x hxsign hxnorm hnotunder hnotover

/-- (B2) `blastSuccessorAwayFromZero` is at most one ulp above the input. -/
theorem UnpackedFloat.blastSuccessorAwayFromZero_toRat'_le_toRat'_add_ulp
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastSuccessorAwayFromZero ep sp).toRat'
      ≤ x.toRat' + (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
  rw [blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp he hs heu hsu x hxsign hnotunder hnotover]
  have := UnpackedFloat.blastRoundTowardZero_toRat'_le_toRat' he hs heu hsu x hxsign hnotunder hnotover
  grind

/-- The width-adjusted round-toward-zero of a normalized, in-range nonnegative float is
itself normalized (needed for `Packable`).

The rounded significand's msb equals the input's (set) msb: `blastClearSignificand` and
`extractMsb' 0 (sp+1)` both keep the top bit (`guardBitIndex < su - 1`), and the input is
nonzero since `ex ≥ minSubnormalExp > (intMin).toInt`. -/
theorem UnpackedFloat.normalize_truncateFittingExponent_blastRoundTowardZero_eq_self
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastRoundTowardZero ep sp).normalize
      = (x.truncateFittingExponent ep sp).blastRoundTowardZero ep sp := by
  have hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false :=
    UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg he hs heu x hnotunder
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hglt : (x.guardBitIndex ep sp).toNat < su - 1 := by grind
  have hxmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
    he hs heu x hxnorm hnotunder
  apply UnpackedFloat.normalize_eq_self_of_msb_eq_true
  -- msb of the round = top bit of the cleared significand = `x`'s (set) msb.
  rw [sig_blastRoundTowardZero,
    sig_blastClearSignificand_truncateFittingExponent he hs heu x hnotover hnotearlyunder,
    BitVec.msb_eq_getMsbD_zero, BitVec.getLsbD_extractMsb']
  simp only [Nat.add_zero, Nat.zero_add, show (0 : Nat) < sp + 1 by grind,
    show (0 : Nat) < su by grind, decide_true, Bool.and_true, Bool.true_and,
    ← BitVec.msb_eq_getMsbD_zero, UnpackedFloat.blastClearSignificand, BitVec.msb_and]
  -- `(x.sig &&& mask).msb = x.sig.msb && mask.msb`, and `mask.msb = true`.
  rw [hxmsb, Bool.true_and, BitVec.msb_eq_getMsbD_zero, BitVec.getMsbD_not]
  simp only [show (0 : Nat) < su by grind, Nat.sub_zero, decide_true, Bool.true_and,
    BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_or, BitVec.getlsbD_oneHotBV,
    BitVec.getLsbD_orderEncode]
  grind

theorem UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)   -- ADDED (needed by `truncateFittingExponent`)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    ∃ pf : PackedFloat ep sp,
      ¬ pf.isNaN ∧
      SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat') pf ∧
      (x.blastRoundTowardZero ep sp).toRat' = pf.toRat ∧
      (x.blastRoundTowardZero ep sp).sign  = pf.sign ∧
      pf.toRatExp = x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int) ∧
      pf.isNormOrNonzeroSubnorm := by
  -- (M) Full not-underflow ⇒ early not-underflow, so the `truncateFittingExponent`
  -- invariance lemmas (stated with the `Early` form) apply.
  have hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false :=
    UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg
      he hs heu x hnotunder
  -- Width-adjust into the packable exponent width `exponentWidth ep sp`, then round.
  -- (`blastRoundTowardZero` keeps the input exponent width, so we adjust first.)
  let r : UnpackedFloat (exponentWidth ep sp) (sp + 1) :=
    (x.truncateFittingExponent ep sp).blastRoundTowardZero ep sp
  -- Shared facts: `r` agrees with the width-`eu` round on sign, significand and
  -- exponent value (the `truncateFittingExponent` invariances).
  have hrsign : r.sign = false := by
    simp only [r, sign_blastRoundTowardZero, sign_truncateFittingExponent, hxsign]
  have hrsig : r.sig = (x.blastRoundTowardZero ep sp).sig := by
    simp only [r, sig_blastRoundTowardZero]
    rw [sig_blastClearSignificand_truncateFittingExponent he hs heu x hnotover hnotearlyunder]
  have hrex : r.ex.toInt = (x.blastRoundTowardZero ep sp).ex.toInt := by
    simp only [r, ex_blastRoundTowardZero]
    exact toInt_ex_truncateFittingExponent he hs heu x hnotover hnotearlyunder
  -- the two rounds have equal `toRat'` at every precision.
  have hrtoRat : ∀ w, r.toRat' w = (x.blastRoundTowardZero ep sp).toRat' w := fun w =>
    UnpackedFloat.toRat'_eq_toRat'_of_parts
      (by rw [hrsign, sign_blastRoundTowardZero, hxsign]) hrsig hrex w
  -- (P) `r` is `Packable`: (1) normalized (rounding keeps the top significand bit),
  -- (2) `ex ≤ maxNormalExp` (from `hnotover`), (3) subnormal divisibility — the bits
  -- `blastClearSignificand` zeroes are exactly the divisibility witness.
  -- Index machinery (as in U) feeding the `Packable` divisibility/exponent conditions.
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  have hrexX : r.ex.toInt = x.ex.toInt := by rw [hrex, ex_blastRoundTowardZero]
  -- `r.sig.toNat = x.sig.toNat / 2^L * 2^off`, hence divisible by `2^off` (the gap-closer).
  have hrsigval : r.sig.toNat
      = x.sig.toNat / 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)))
          * 2 ^ (minNormalExp ep - x.ex.toInt).toNat := by
    rw [hrsig, sig_blastRoundTowardZero, BitVec.toNat_extractMsb'_zero _ (by grind),
      UnpackedFloat.blastClearSignificand_sig_toNat_eq, hLeq,
      Nat.div_mul_two_pow_add_div_two_pow]
  have hPack : r.Packable := by
    refine ⟨?_, ?_, ?_⟩
    · -- (1) normalized — extracted as a named lemma.
      exact UnpackedFloat.normalize_truncateFittingExponent_blastRoundTowardZero_eq_self
        he hs heu hsu x hxsign hxnorm hnotunder hnotover
    · -- (2) `ex ≤ maxNormalExp`.
      rw [hrexX]; exact hoverE
    · -- (3) subnormal divisibility — `2^off ∣ r.sig.toNat`.
      right
      rw [hrexX, hrsigval]
      exact ⟨x.sig.toNat / 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))),
        Nat.mul_comm _ _⟩
  -- `r` is nonzero (msb set ⇒ `x.sig ≥ 2^(su-1) ≥ 2^L`, so the high quotient is positive).
  have hrsigne : r.sig ≠ 0#(sp + 1) := by
    have hxmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
      he hs heu x hxnorm hnotunder
    have hge : 2 ^ (su - 1) ≤ x.sig.toNat := by
      rw [BitVec.msb_eq_decide] at hxmsb; simpa using hxmsb
    have hdivpos : 0 < x.sig.toNat / 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) := by
      apply Nat.div_pos _ (Nat.two_pow_pos _)
      exact Nat.le_trans (Nat.pow_le_pow_right (by grind) (by grind)) hge
    intro h0
    have hz : r.sig.toNat = 0 := by rw [h0]; simp
    rw [hrsigval] at hz
    have := Nat.mul_pos hdivpos (Nat.two_pow_pos (minNormalExp ep - x.ex.toInt).toNat)
    grind
  -- `pf = pack r` is a normal / nonzero-subnormal float (gives ¬isNaN and GLB's `hfin`).
  have hfin : (EUnpackedFloat.mkNumber r).pack.isNormOrNonzeroSubnorm := by
    have hexpb : r.ex.toInt ≤ maxNormalExp ep := hPack.2.1
    have hpacked : (EUnpackedFloat.mkNumber r).pack
        = EUnpackedFloat.packNumber' r.sign r.sig r.ex := by
      rw [EUnpackedFloat.pack_eq_pack', EUnpackedFloat.pack']
      have hz : (EUnpackedFloat.mkNumber r).isZero = false := by
        rw [EUnpackedFloat.isZero_mkNumber]; simp [UnpackedFloat.isZero, hrsigne]
      simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber, hz,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    have hnotNaN : ¬ (EUnpackedFloat.mkNumber r).pack.isNaN := by
      rw [hpacked, EUnpackedFloat.not_isNaN_packNumber' hs he _ _ _ hexpb]; simp
    have hnotInf : ¬ (EUnpackedFloat.mkNumber r).pack.isInfinite := by
      rw [hpacked]
      have hne := EUnpackedFloat.packNumber'.exPacked_ne_allOnes hs he r.ex hexpb
      simp only [PackedFloat.isInfinite, EUnpackedFloat.packNumber']; grind
    have hnotZero : ¬ (EUnpackedFloat.mkNumber r).pack.isZero := by
      intro hz0
      have h0 := PackedFloat.toRat_eq_Zero_of_isZero _ hz0
      rw [EUnpackedFloat.toRat_pack_mkNumber_eq_toRat he hs r hPack,
        UnpackedFloat.toRat_eq_toRat'] at h0
      have := (UnpackedFloat.toRat'_isZero r).mpr h0
      simp [UnpackedFloat.isZero, hrsigne] at this
    exact PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero
      hnotNaN hnotInf hnotZero
  have hpfRat : (EUnpackedFloat.mkNumber r).pack.toRat = (x.blastRoundTowardZero ep sp).toRat' := by
    rw [EUnpackedFloat.toRat_pack_mkNumber_eq_toRat he hs r hPack, UnpackedFloat.toRat_eq_toRat']
    exact hrtoRat _
  have hpfsign : (EUnpackedFloat.mkNumber r).pack.sign = false := by
    rw [EUnpackedFloat.sign_pack]
    simp only [EUnpackedFloat.isNaN_mkNumber, Bool.false_eq_true, if_false,
      EUnpackedFloat.sign, EUnpackedFloat.num_mkNumber, hrsign]
  have hrmsb : r.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff r hrsigne).mp hPack.1
  -- The packed exponent equals `max(x.ex, minNormalExp) = x.ex + subnormal-shift`.
  have hexpeq : (EUnpackedFloat.mkNumber r).pack.toRatExp
      = x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int) := by
    have hpfRatR : (EUnpackedFloat.mkNumber r).pack.toRat = r.toRat' := by
      rw [EUnpackedFloat.toRat_pack_mkNumber_eq_toRat he hs r hPack, UnpackedFloat.toRat_eq_toRat']
    -- `2^x.ex ≤ pf.toRat < 2^(x.ex+1)`.
    have hlow : (2 : Rat) ^ x.ex.toInt ≤ (EUnpackedFloat.mkNumber r).pack.toRat := by
      rw [hpfRatR, ← hrexX]
      exact UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false r (by grind) hrsign hrmsb
    have hub : (EUnpackedFloat.mkNumber r).pack.toRat < 2 ^ (x.ex.toInt + 1) := by
      rw [hpfRat]
      have h1 := UnpackedFloat.blastRoundTowardZero_toRat'_le_toRat'
        he hs heu hsu x hxsign hnotunder hnotover
      have h2 := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x (by grind) hxsign
      grind
    have hexB : minNormalExp ep ≤ (EUnpackedFloat.mkNumber r).pack.toRatExp :=
      PackedFloat.minNormalExp_le_toRatExp _ (by grind)
    have hhigh := PackedFloat.toRat_lt_two_pow_toRatExp_succ_of_sign_false
      (EUnpackedFloat.mkNumber r).pack hpfsign
    -- `x.ex ≤ toRatExp` (from `2^x.ex ≤ pf.toRat < 2^(toRatExp+1)`).
    have hexA : x.ex.toInt ≤ (EUnpackedFloat.mkNumber r).pack.toRatExp := by
      apply Classical.byContradiction
      intro hlt
      have hstep : (EUnpackedFloat.mkNumber r).pack.toRatExp + 1 ≤ x.ex.toInt := by grind
      have := Rat.two_pow_le_two_pow_of_le hstep
      grind
    -- `toRatExp ≤ max(x.ex, minNormalExp)`.
    have hrev : (EUnpackedFloat.mkNumber r).pack.toRatExp
        ≤ x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int) := by
      by_cases hnorm : (EUnpackedFloat.mkNumber r).pack.isNorm
      · have hlb := PackedFloat.two_pow_toRatExp_le_toRat_of_isNorm_of_sign_false _ hnorm hpfsign
        have hltexp : (EUnpackedFloat.mkNumber r).pack.toRatExp ≤ x.ex.toInt := by
          apply Classical.byContradiction
          intro hlt
          have hstep : x.ex.toInt + 1 ≤ (EUnpackedFloat.mkNumber r).pack.toRatExp := by grind
          have := Rat.two_pow_le_two_pow_of_le hstep
          grind
        grind
      · have hsub : (EUnpackedFloat.mkNumber r).pack.toRatExp = minNormalExp ep := by
          simp only [PackedFloat.toRatExp, hnorm, Bool.false_eq_true, if_false, minNormalExp]
        rw [hsub]; grind
    grind
  refine ⟨(EUnpackedFloat.mkNumber r).pack, ?_, ?_, ?_, ?_, hexpeq, hfin⟩
  · -- ¬ isNaN, from `isNormOrNonzeroSubnorm`.
    simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfin
  · -- IsLawfulLower via the GLB lemma.
    have hpfsign : (EUnpackedFloat.mkNumber r).pack.sign = false := by
      rw [EUnpackedFloat.sign_pack]
      simp only [EUnpackedFloat.isNaN_mkNumber, Bool.false_eq_true, if_false,
        EUnpackedFloat.sign, EUnpackedFloat.num_mkNumber, hrsign]
    apply PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp he hs _ _ hpfsign hfin
    · -- `pf.toRat = round.toRat' ≤ x.toRat'`.
      rw [hpfRat]
      exact UnpackedFloat.blastRoundTowardZero_toRat'_le_toRat'
        he hs heu hsu x hxsign hnotunder hnotover
    · -- `x.toRat' < pf.toRat + ulp`: from (U), bridging the unpacked ulp `2^(ex-sp+off)`
      -- to the packed ulp `2^(-sp)·2^(pf.toRatExp)` via `x.ex + off ≤ pf.toRatExp`.
      rw [hpfRat]
      have hU := UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp
        he hs heu hsu x hxsign hxnorm hnotunder hnotover
      have hexpbridge : x.ex.toInt + ((minNormalExp ep - x.ex.toInt).toNat : Int)
          ≤ (EUnpackedFloat.mkNumber r).pack.toRatExp := by
        -- `pf.toRat = r.toRat'`, with `r` in the same binade: `2^x.ex ≤ pf.toRat < 2^(pf.toRatExp+1)`.
        have hpfRatR : (EUnpackedFloat.mkNumber r).pack.toRat = r.toRat' := by
          rw [EUnpackedFloat.toRat_pack_mkNumber_eq_toRat he hs r hPack,
            UnpackedFloat.toRat_eq_toRat']
        have hrmsb : r.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff r hrsigne).mp hPack.1
        -- (lower) `2^x.ex ≤ pf.toRat`.
        have hlow : (2 : Rat) ^ x.ex.toInt ≤ (EUnpackedFloat.mkNumber r).pack.toRat := by
          rw [hpfRatR, ← hrexX]
          exact UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false r (by grind) hrsign hrmsb
        -- (upper) `pf.toRat < 2^(pf.toRatExp+1)`.
        have hhigh := PackedFloat.toRat_lt_two_pow_toRatExp_succ_of_sign_false
          (EUnpackedFloat.mkNumber r).pack hpfsign
        -- combine: `2^x.ex < 2^(pf.toRatExp+1)` ⇒ `x.ex ≤ pf.toRatExp`.
        have hexA : x.ex.toInt ≤ (EUnpackedFloat.mkNumber r).pack.toRatExp := by
          apply Classical.byContradiction
          intro hlt
          have hstep : (EUnpackedFloat.mkNumber r).pack.toRatExp + 1 ≤ x.ex.toInt := by grind
          have := Rat.two_pow_le_two_pow_of_le hstep
          grind
        have hexB : minNormalExp ep ≤ (EUnpackedFloat.mkNumber r).pack.toRatExp :=
          PackedFloat.minNormalExp_le_toRatExp _ (by grind)
        -- `x.ex + off = max(x.ex, minNormalExp)`, bounded by both.
        grind
      have hbridge : (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
          ≤ 2 ^ (-(sp : Int)) * 2 ^ ((EUnpackedFloat.mkNumber r).pack.toRatExp) := by
        rw [Rat.zpow_mul_zpow (by grind)]
        apply Rat.two_pow_le_two_pow_of_le
        grind
      grind
  · -- value: `pf.toRat = r.toRat = r.toRat' = (x.blastRoundTowardZero ep sp).toRat'`.
    rw [EUnpackedFloat.toRat_pack_mkNumber_eq_toRat he hs r hPack,
      UnpackedFloat.toRat_eq_toRat']
    exact (hrtoRat _).symm
  · -- sign: both sides are `false`.
    rw [sign_blastRoundTowardZero, hxsign, EUnpackedFloat.sign_pack]
    simp only [EUnpackedFloat.isNaN_mkNumber, Bool.false_eq_true, if_false,
      EUnpackedFloat.sign, EUnpackedFloat.num_mkNumber, hrsign]

/--
info: 'Fp.UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero

/-- `lower (Number x.toRat')` is finite (normal or nonzero subnormal) when `x` is a nonnegative
in-range normalized float. Obtained by pinning the keystone's witness `pf = lower` (uniqueness)
and transferring its `isNormOrNonzeroSubnorm`. -/
theorem UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range
    (he : 2 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm := by
  obtain ⟨pf, hpfNotNaN, hpfLower, _, _, _, hfin⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hsp _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hsp _)
  rw [← hpflow]; exact hfin

/--
info: 'Fp.UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range

/-- The successor (away from zero) of a finite, nonnegative, non-`maxNormal` float is again
finite (normal or nonzero subnormal): it stays positive (`= toRat + ulp`), so it is neither
zero nor infinite, and the successor preserves non-NaN. -/
theorem PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal
    (he : 1 < e) (hs : 0 < s) (x : PackedFloat e s)
    (hxsign : x.sign = false) (hfin : x.isNormOrNonzeroSubnorm)
    (hmax : x ≠ PackedFloat.maxNormalNumber e s false) :
    x.successorAwayFromZero.isNormOrNonzeroSubnorm := by
  have hnan : ¬ x.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfin
  have hinf : ¬ x.isInfinite := by simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfin
  have hxpos : 0 < x.toRat := by
    have hne : x.toRat ≠ 0 := PackedFloat.toRat_ne_zero hfin
    have hnn : ¬ (x.toRat < 0) := by
      have := PackedFloat.sign_iff_toRat_neg hfin; grind
    grind
  have hval := PackedFloat.toRat_successorAwayFromZero_eq x hnan hinf (by rw [hxsign]; exact hmax) he hs
  have hsuccpos : 0 < x.successorAwayFromZero.toRat := by
    rw [hval, hxsign]
    have hulp : (0 : Rat) < (2 : Rat) ^ (-(s : Int)) * 2 ^ x.toRatExp := by
      have h1 : (0 : Rat) < (2 : Rat) ^ (-(s : Int)) := by grind only [Fp.Rat.two_pow_pos]
      have h2 : (0 : Rat) < (2 : Rat) ^ x.toRatExp := by grind only [Fp.Rat.two_pow_pos]
      grind
    have : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
    rw [this]; grind
  refine PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero ?_ ?_ ?_
  · simpa [PackedFloat.isNaN_successorAwayFromZero hs] using hnan
  · intro h; have := PackedFloat.toRat_eq_zero_of_isInfinite _ h; grind
  · intro h; have := PackedFloat.toRat_eq_Zero_of_isZero _ h; grind

/--
info: 'Fp.PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal

/-- Incrementing `x.ex` by one does not wrap, provided `x` does not early-overflow
(`x.ex.toInt ≤ maxNormalExp ≪ 2^(eu-1)`). Extracted from the successor-value proof. -/
theorem UnpackedFloat.toInt_ex_add_one_of_not_blastIsEarlyOverflow
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.ex + 1#eu).toInt = x.ex.toInt + 1 := by
  have hexhi : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hlo := x.ex.le_toInt
  have hew1 : 1 < exponentWidth ep sp := one_lt_exponentWidth
  have heu1 : 1 < eu := by omega
  have hbias : bias ep + 1 < 2 ^ (exponentWidth ep sp - 1) :=
    bias_plus_one_lt_two_pow_exponentWidth_minus_one ep sp he hs
  have hminS := neg_two_pow_exponentWidth_lt_minSubnormalExp (e := ep) (s := sp) he hs
  have hmaxN : maxNormalExp ep = (bias ep : Int) := rfl
  have hpowle : (2 : Int) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) := by
    have h1 : (2 : Nat) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hc1 : ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int)
        = (2 : Int) ^ (exponentWidth ep sp - 1) := by push_cast; rfl
    have hc2 : ((2 ^ (eu - 1) : Nat) : Int) = (2 : Int) ^ (eu - 1) := by push_cast; rfl
    omega
  have hcastBias : ((bias ep : Nat) : Int) + 1 < (2 : Int) ^ (exponentWidth ep sp - 1) := by
    have hb : ((bias ep + 1 : Nat) : Int) < ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int) := by
      exact_mod_cast hbias
    push_cast at hb; omega
  have h2pow : ∀ n : Nat, 0 < n → (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    rw [Int.pow_succ]; simp; omega
  have h2eu : (2 : Int) ^ eu = 2 * 2 ^ (eu - 1) := h2pow eu (by omega)
  rw [BitVec.toInt_add, BitVec.toInt_one_of_lt heu1, Int.bmod_eq_of_le] <;> push_cast <;> omega

/--
info: 'Fp.UnpackedFloat.toInt_ex_add_one_of_not_blastIsEarlyOverflow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.toInt_ex_add_one_of_not_blastIsEarlyOverflow

/-- **Successor exponent monotonicity** (linchpin): the auxiliary successor never decreases the
exponent, given no early-overflow (so the `+1` carry does not wrap). -/
theorem UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    x.ex.toInt ≤ (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt := by
  unfold UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux
  split
  · -- needsRounding: next = blastSuccessorAwayFromZero
    simp only [UnpackedFloat.blastSuccessorAwayFromZero]
    split
    · -- carry: ex = clearSignificand.ex + 1 = x.ex + 1
      simp only [clearSignificand_ex]
      rw [UnpackedFloat.toInt_ex_add_one_of_not_blastIsEarlyOverflow he hs heu x hnotover]
      omega
    · -- no carry: ex = clearSignificand.ex = x.ex
      simp only [clearSignificand_ex]; omega
  · -- ¬needsRounding: next = blastRoundTowardZero, ex = x.ex
    rw [ex_blastRoundTowardZero]; omega

/--
info: 'Fp.UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux

/-- Companion upper bound: the auxiliary successor raises the exponent by at most one. -/
theorem UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt ≤ x.ex.toInt + 1 := by
  unfold UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux
  split
  · simp only [UnpackedFloat.blastSuccessorAwayFromZero]
    split
    · simp only [clearSignificand_ex]
      rw [UnpackedFloat.toInt_ex_add_one_of_not_blastIsEarlyOverflow he hs heu x hnotover]; omega
    · simp only [clearSignificand_ex]; omega
  · rw [ex_blastRoundTowardZero]; omega

/--
info: 'Fp.UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one

/-- **Underflow connection**: if the successor underflows, `x.toRat'` is at most the smallest
positive subnormal. (Via monotonicity: `next.ex < minSubnormalExp ⇒ x.ex < minSubnormalExp ⇒
x.toRat' < 2^(x.ex+1) ≤ 2^minSubnormalExp = minSubnormal.toRat`.) -/
theorem UnpackedFloat.toRat'_le_minSubnormalNumber_of_blastIsUnderflow_next
    (he : 2 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotEarlyOver : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hunder : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp = true) :
    x.toRat' ≤ (PackedFloat.minSubnormalNumber ep sp false).toRat := by
  rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
  have hmono := UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux (by grind) hsp heu x hnotEarlyOver
  have hub := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x (by grind) hxsign
  have hexub : x.ex.toInt + 1 ≤ minNormalExp ep - (sp : Int) := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hunder
    simp only [decide_eq_true_eq] at hunder
    have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
      simp only [minSubnormalExp, maxSubnormalExp]; grind
    grind
  have hmono2 := Rat.two_pow_le_two_pow_of_le hexub
  grind

/--
info: 'Fp.UnpackedFloat.toRat'_le_minSubnormalNumber_of_blastIsUnderflow_next' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.toRat'_le_minSubnormalNumber_of_blastIsUnderflow_next

/-- The packed-format underflow representative `minSubnormalForPackedFloat` (significand
`leadingOne`, exponent `minSubnormalExp`) has value exactly `minSubnormalNumber.toRat`, i.e.
`2 ^ minSubnormalExp`. This is the value produced on the circuit's underflow branch. -/
theorem UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber
    (ep sp eu : Nat) (he : 1 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) :
    (UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp false).toRat'
      = (PackedFloat.minSubnormalNumber ep sp false).toRat := by
  have hsign : (UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp false).sign = false := by
    simp [UnpackedFloat.minSubnormalForPackedFloat]
  rw [UnpackedFloat.toRat'_eq_sig_toNat_mul _ hsign (by omega)]
  have hsig : (UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp false).sig.toNat
      = 2 ^ sp := by
    simp only [UnpackedFloat.minSubnormalForPackedFloat]
    rw [BitVec.toNat_zeroExtend_of_le _ (by omega), BitVec.toNat_leadingOne (by omega),
      Nat.add_sub_cancel]
  have hex : (UnpackedFloat.minSubnormalForPackedFloat eu (sp + 1) ep sp false).ex.toInt
      = minSubnormalExp ep sp := by
    simp only [UnpackedFloat.minSubnormalForPackedFloat]
    exact toInt_ofInt_minSubnormalExp_eq_minSubnormalExp_of_le he hsp heu
  rw [hsig, hex, PackedFloat.toExtRat_minSubnormal_eq ep sp he hsp]
  have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hcast : ((2 ^ sp : Nat) : Rat) = (2 : Rat) ^ (sp : Int) := by
    rw [Rat.zpow_natCast]; norm_cast
  rw [hcast, Rat.zpow_mul_zpow (by grind)]
  congr 1
  push_cast
  omega

/--
info: 'Fp.UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber

/-- Closed form of `maxNormal.toRat`: `2^(maxNormalExp+1) - 2^(maxNormalExp - sp)`. -/
theorem PackedFloat.toRat_maxNormalNumber_false_eq (ep sp : Nat) (he : 2 < ep) :
    (PackedFloat.maxNormalNumber ep sp false).toRat
      = 2 ^ (maxNormalExp ep + 1) - 2 ^ (maxNormalExp ep - (sp : Int)) := by
  rw [PackedFloat.toRat, PackedFloat.toRatSig_maxNormalNumber ep sp he,
    PackedFloat.toRatExp_maxNormalNumber ep sp he, PackedFloat.sign_maxNormalNumber]
  rw [show (Bool.toSign false : Rat) = 1 by simp [Bool.toSign], Rat.one_mul]
  have e1 : (2 : Rat) ^ (-(sp : Int)) * 2 ^ (maxNormalExp ep) = 2 ^ (maxNormalExp ep - (sp : Int)) := by
    rw [Rat.zpow_mul_zpow (by grind)]; congr 1; omega
  have e2 : (2 : Rat) * 2 ^ (maxNormalExp ep) = 2 ^ (maxNormalExp ep + 1) := by
    rw [Rat.zpow_add_one (show (2 : Rat) ≠ 0 by grind), Rat.mul_comm]
  rw [Rat.sub_mul, e1, e2]

/--
info: 'Fp.PackedFloat.toRat_maxNormalNumber_false_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PackedFloat.toRat_maxNormalNumber_false_eq

/-- A nonnegative width-`(sp+1)` float at exponent `maxNormalExp` is at most `maxNormal`
(its significand fits in `sp+1` bits, so `toRat' = sig·2^(maxNormalExp-sp) ≤ maxNormal`). -/
theorem UnpackedFloat.toRat'_le_maxNormalNumber_of_sign_false_of_ex_eq_maxNormalExp
    (he : 2 < ep) (hsp : 0 < sp)
    (uf : UnpackedFloat eu (sp + 1)) (hsign : uf.sign = false) (hex : uf.ex.toInt = maxNormalExp ep) :
    uf.toRat' ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
  have hexp : uf.ex.toInt - (((sp + 1 : Nat) : Int) - 1) = maxNormalExp ep - (sp : Int) := by
    rw [hex]; push_cast; omega
  rw [UnpackedFloat.toRat'_eq_sig_toNat_mul uf hsign (by omega), hexp,
    PackedFloat.toRat_maxNormalNumber_false_eq ep sp he]
  have hC : (0 : Rat) ≤ 2 ^ (maxNormalExp ep - (sp : Int)) := Rat.le_of_lt (Rat.two_pow_pos _)
  have h2M1 : (2 : Rat) ^ (maxNormalExp ep + 1)
      = 2 ^ (sp + 1) * 2 ^ (maxNormalExp ep - (sp : Int)) := by
    rw [← Rat.zpow_natCast (2 : Rat) (sp + 1), Rat.zpow_mul_zpow (by grind)]
    congr 1; push_cast; omega
  have hsigle : ((uf.sig.toNat : Rat) + 1) ≤ 2 ^ (sp + 1) := by
    have h := uf.sig.isLt
    have : (uf.sig.toNat : Rat) + 1 ≤ ((2 ^ (sp + 1) : Nat) : Rat) := by exact_mod_cast (by omega)
    push_cast at this; exact this
  have hkey := Rat.mul_le_mul_of_nonneg_right hsigle hC
  rw [h2M1]
  rw [Rat.add_mul, Rat.one_mul] at hkey
  grind

/--
info: 'Fp.UnpackedFloat.toRat'_le_maxNormalNumber_of_sign_false_of_ex_eq_maxNormalExp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.toRat'_le_maxNormalNumber_of_sign_false_of_ex_eq_maxNormalExp

/-- **Converse overflow connection**: if `x.toRat' > maxNormal` (and `x` is in range), the
successor early-overflows. (The successor `> x > maxNormal`, but a non-overflowing successor
would sit at exponent `maxNormalExp`, hence `≤ maxNormal` — contradiction.) -/
theorem UnpackedFloat.blastIsEarlyOverflow_next_of_maxNormalNumber_lt
    (he : 2 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hlt : (PackedFloat.maxNormalNumber ep sp false).toRat < x.toRat') :
    (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp = true := by
  have hxhi : x.ex.toInt ≤ maxNormalExp ep := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hsp heu] at hnotover
    simpa using hnotover
  have hub := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x (by grind) hxsign
  have hmaxge : (2 : Rat) ^ (maxNormalExp ep) ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
    rw [PackedFloat.toRat_maxNormalNumber_false_eq ep sp he]
    have h1 : (2 : Rat) ^ (maxNormalExp ep + 1) = 2 * 2 ^ (maxNormalExp ep) := by
      rw [Rat.zpow_add_one (show (2 : Rat) ≠ 0 by grind), Rat.mul_comm]
    have h2 : (2 : Rat) ^ (maxNormalExp ep - (sp : Int)) ≤ 2 ^ (maxNormalExp ep) :=
      Rat.two_pow_le_two_pow_of_le (by omega)
    grind
  have hxex : x.ex.toInt = maxNormalExp ep := by
    have hxlo : maxNormalExp ep ≤ x.ex.toInt := by
      apply Classical.byContradiction
      intro hc
      have hle : x.ex.toInt + 1 ≤ maxNormalExp ep := by omega
      have := Rat.two_pow_le_two_pow_of_le hle
      grind
    omega
  -- roundTZ ≤ maxNormal, hence (needsRounding ⇒) lower < x.
  have hrtle : (x.blastRoundTowardZero ep sp).toRat' ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
    apply UnpackedFloat.toRat'_le_maxNormalNumber_of_sign_false_of_ex_eq_maxNormalExp he hsp
    · rw [sign_blastRoundTowardZero]; exact hxsign
    · rw [ex_blastRoundTowardZero]; exact hxex
  have hnr : x.needsRounding ep sp = true := by
    apply Classical.byContradiction
    intro hc
    simp only [Bool.not_eq_true] at hc
    have heq := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding
      (by grind) hsp heu hsu x hxsign hnotunder hnotover hc)
    grind
  -- next = successor; assume ¬next.over and derive a contradiction.
  apply Classical.byContradiction
  intro hcon
  simp only [Bool.not_eq_true] at hcon
  have hlt_next := UnpackedFloat.toRat'_lt_blastSuccessorAwayFromZero_toRat'
    (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  have hnexteq : x.blastSuccessorAwayFromZeroNonnegAux ep sp = x.blastSuccessorAwayFromZero ep sp := by
    rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_pos hnr]
  have hmono := UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux (by grind) hsp heu x hnotover
  have hcomp := UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one (by grind) hsp heu x hnotover
  have hnextexle : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt ≤ maxNormalExp ep := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hsp heu] at hcon
    simpa using hcon
  have hnextex : (x.blastSuccessorAwayFromZero ep sp).ex.toInt = maxNormalExp ep := by
    rw [← hnexteq]; omega
  have hnextle : (x.blastSuccessorAwayFromZero ep sp).toRat'
      ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
    apply UnpackedFloat.toRat'_le_maxNormalNumber_of_sign_false_of_ex_eq_maxNormalExp he hsp
    · rw [sign_blastSuccessorAwayFromZero]; exact hxsign
    · exact hnextex
  grind

/--
info: 'Fp.UnpackedFloat.blastIsEarlyOverflow_next_of_maxNormalNumber_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastIsEarlyOverflow_next_of_maxNormalNumber_lt

/-- If the successor early-overflows (while `x` itself does not), then `x.ex = maxNormalExp`:
`maxNormalExp < next.ex ≤ x.ex + 1` and `x.ex ≤ maxNormalExp` pin it exactly. -/
theorem UnpackedFloat.ex_eq_maxNormalExp_of_blastIsEarlyOverflow_next
    (he : 1 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotEarlyOver : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hover : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp = true) :
    x.ex.toInt = maxNormalExp ep := by
  have hcomp := UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one he hsp heu x hnotEarlyOver
  have hnextover : maxNormalExp ep < (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hsp heu] at hover
    simpa using hover
  have hxhi : x.ex.toInt ≤ maxNormalExp ep := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hsp heu] at hnotEarlyOver
    simpa using hnotEarlyOver
  omega

/--
info: 'Fp.UnpackedFloat.ex_eq_maxNormalExp_of_blastIsEarlyOverflow_next' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.ex_eq_maxNormalExp_of_blastIsEarlyOverflow_next

/-- When the successor's exponent increments (the significand carried), its value is exactly the
binade boundary `2^(x.ex+1)`. (Carry pins `cleared.sig + 2^(g+1) = 2^su`, so
`next.toRat' = 2^su · 2^(x.ex-(su-1)) = 2^(x.ex+1)`.) -/
theorem UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_ex_succ_of_ex_succ
    (he : 1 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hexsucc : (x.blastSuccessorAwayFromZero ep sp).ex.toInt = x.ex.toInt + 1) :
    (x.blastSuccessorAwayFromZero ep sp).toRat' = (2 : Rat) ^ (x.ex.toInt + 1) := by
  -- Reconstruct the carry analysis (mirrors `_eq_clearSignificand_mul`).
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by
    have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
      simp only [minSubnormalExp, maxSubnormalExp]; grind
    grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  have hgsu : (x.guardBitIndex ep sp).toNat + 1 < su := by rw [hLeq]; grind
  have hlsb : (BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).toNat
      = 2 ^ ((x.guardBitIndex ep sp).toNat + 1) :=
    BitVec.toNat_zeroExtend_oneHotBV_shiftLeft_one (x.guardBitIndex ep sp) hgsu
  have hcllt : (x.blastClearSignificand ep sp).sig.toNat < 2 ^ su :=
    (x.blastClearSignificand ep sp).sig.isLt
  have hg1lt : 2 ^ ((x.guardBitIndex ep sp).toNat + 1) < 2 ^ su :=
    Fp.Nat.two_pow_lt_two_pow_of_lt hgsu
  have hsum : (BitVec.zeroExtend (su + 1) (x.blastClearSignificand ep sp).sig
        + BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).toNat
      = (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, hlsb,
      Nat.mod_eq_of_lt (by omega : (x.blastClearSignificand ep sp).sig.toNat < 2 ^ (su + 1)),
      Nat.mod_eq_of_lt (by omega)]
  have hcldvd : 2 ^ ((x.guardBitIndex ep sp).toNat + 1) ∣ (x.blastClearSignificand ep sp).sig.toNat := by
    rw [UnpackedFloat.blastClearSignificand_sig_toNat_eq x ep sp]; exact Nat.dvd_mul_left _ _
  have hSle : (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) ≤ 2 ^ su := by
    obtain ⟨q, hq⟩ := hcldvd
    have hsplit : 2 ^ su
        = 2 ^ ((x.guardBitIndex ep sp).toNat + 1) * 2 ^ (su - ((x.guardBitIndex ep sp).toNat + 1)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hqlt : q < 2 ^ (su - ((x.guardBitIndex ep sp).toNat + 1)) := by
      apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ ((x.guardBitIndex ep sp).toNat + 1))
      rw [← hq, ← hsplit]; exact hcllt
    have hmul : 2 ^ ((x.guardBitIndex ep sp).toNat + 1) * (q + 1) ≤ 2 ^ su := by
      rw [hsplit]; exact Nat.mul_le_mul_left _ (by omega)
    rw [hq, ← Nat.mul_succ]; exact hmul
  have hmsb : (BitVec.zeroExtend (su + 1) (x.blastClearSignificand ep sp).sig
        + BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).msb
      = decide (2 ^ su ≤ (x.blastClearSignificand ep sp).sig.toNat
          + 2 ^ ((x.guardBitIndex ep sp).toNat + 1)) := by
    rw [BitVec.msb_eq_decide, hsum]; simp
  -- The exponent increments iff the significand carried (`2^su ≤ S`).
  have hexform : (x.blastSuccessorAwayFromZero ep sp).ex
      = if (BitVec.zeroExtend (su + 1) (x.blastClearSignificand ep sp).sig
            + BitVec.zeroExtend (su + 1) (x.guardBitIndex ep sp).oneHotBV <<< 1).msb
        then x.ex + 1#eu else x.ex := by
    simp only [UnpackedFloat.blastSuccessorAwayFromZero, clearSignificand_ex]
  have hcarry : (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) = 2 ^ su := by
    by_cases hov : 2 ^ su ≤ (x.blastClearSignificand ep sp).sig.toNat + 2 ^ ((x.guardBitIndex ep sp).toNat + 1)
    · omega
    · exfalso
      rw [hexform, hmsb, if_neg (by simp [hov])] at hexsucc
      omega
  rw [UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_clearSignificand_mul he hs heu hsu x hxsign
    hnotunder hnotover]
  have hcarryR : ((x.blastClearSignificand ep sp).sig.toNat : Rat)
      + 2 ^ ((x.guardBitIndex ep sp).toNat + 1) = 2 ^ su := by exact_mod_cast hcarry
  rw [hcarryR, ← Rat.zpow_natCast (2 : Rat) su, Rat.zpow_mul_zpow (by grind)]
  congr 1
  push_cast; omega

/--
info: 'Fp.UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_ex_succ_of_ex_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_ex_succ_of_ex_succ

/-- Subnormal-aware companion to `blastSuccessorAwayFromZero_toRat'_eq_two_pow_ex_succ_of_ex_succ`:
whenever the successor's exponent strictly increments (the rounding carried into a higher
exponent), its value is exactly `2 ^ (x.ex + 1)`. Unlike the normal-range version this needs
no `¬under`/`¬over` hypotheses — the carry forces `sig = leadingOne` directly from the circuit
definition — so it applies at the subnormal underflow boundary. -/
theorem UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_of_ex_succ
    (ep sp : Nat) (hsu : sp + 1 ≤ su) (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hexsucc : (x.blastSuccessorAwayFromZero ep sp).ex.toInt = x.ex.toInt + 1) :
    (x.blastSuccessorAwayFromZero ep sp).toRat' = (2 : Rat) ^ (x.ex.toInt + 1) := by
  have hsign : (x.blastSuccessorAwayFromZero ep sp).sign = false := by
    simp only [UnpackedFloat.blastSuccessorAwayFromZero, clearSignificand_sign, hxsign]
  have hsigN : (x.blastSuccessorAwayFromZero ep sp).sig.toNat = 2 ^ sp := by
    -- The exponent incremented, so the significand carried (`sigDidOverflow = true`),
    -- whence `sig = (leadingOne su).extractMsb' 0 (sp + 1)`, of value `2 ^ sp`.
    have hne : (x.blastSuccessorAwayFromZero ep sp).ex ≠ x.ex := by
      intro h; rw [h] at hexsucc; omega
    simp only [UnpackedFloat.blastSuccessorAwayFromZero, clearSignificand_ex,
      clearSignificand_sign] at hne ⊢
    split at hne
    · split
      · rw [BitVec.toNat_extractMsb'_zero _ (by omega), BitVec.toNat_leadingOne (by omega),
          Nat.pow_div (by omega) (by omega)]
        congr 1; omega
      · simp_all
    · simp_all
  rw [UnpackedFloat.toRat'_eq_sig_toNat_mul _ hsign (by omega), hsigN, hexsucc]
  have hcast : ((2 ^ sp : Nat) : Rat) = (2 : Rat) ^ (sp : Int) := by
    rw [Rat.zpow_natCast]; norm_cast
  rw [hcast, Rat.zpow_mul_zpow (by grind)]
  congr 1; push_cast; omega

/--
info: 'Fp.UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_of_ex_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_of_ex_succ

/-- **Overflow connection**: if the successor early-overflows (while `x` does not), then
`x.toRat' > maxNormal`. With `x.ex = maxNormalExp`, the carry forces
`blastSuccessorAwayFromZero x = 2^(maxNormalExp+1)`, so `roundTZ = maxNormal` (= `next - ulp`),
and `needsRounding` gives `roundTZ < x`. -/
theorem UnpackedFloat.lt_toRat'_of_blastIsEarlyOverflow_next
    (he : 2 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false)
    (hnotEarlyOver : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hover : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp = true) :
    (PackedFloat.maxNormalNumber ep sp false).toRat < x.toRat' := by
  have hxex := UnpackedFloat.ex_eq_maxNormalExp_of_blastIsEarlyOverflow_next (by grind) hsp heu x hnotEarlyOver hover
  have hxnotunder : x.blastIsUnderflowNonneg ep sp = false := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu]
    have hle : minSubnormalExp ep sp ≤ maxNormalExp ep := by
      simp only [minSubnormalExp, maxSubnormalExp, minNormalExp, maxNormalExp]; grind
    simp only [decide_eq_false_iff_not]; omega
  have hmono := UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux (by grind) hsp heu x hnotEarlyOver
  have hcomp := UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one (by grind) hsp heu x hnotEarlyOver
  have hnextover : maxNormalExp ep < (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hsp heu] at hover; simpa using hover
  have hnextex : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt = x.ex.toInt + 1 := by omega
  have hnr : x.needsRounding ep sp = true := by
    apply Classical.byContradiction
    intro hc
    simp only [Bool.not_eq_true] at hc
    rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_neg (by simp [hc]),
      ex_blastRoundTowardZero] at hnextex
    omega
  have hbsex : (x.blastSuccessorAwayFromZero ep sp).ex.toInt = x.ex.toInt + 1 := by
    have heq : x.blastSuccessorAwayFromZeroNonnegAux ep sp = x.blastSuccessorAwayFromZero ep sp := by
      rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_pos hnr]
    rw [← heq]; exact hnextex
  have hbsval := UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_ex_succ_of_ex_succ
    (by grind) hsp heu hsu x hxsign hxnotunder hnotEarlyOver hbsex
  have hadd := UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp
    (by grind) hsp heu hsu x hxsign hxnotunder hnotEarlyOver
  have hsubshift : (minNormalExp ep - x.ex.toInt).toNat = 0 := by
    rw [hxex]
    have hbp : 0 < bias ep := bias_pos_of_one_lt ep (by grind)
    have hneg : minNormalExp ep - maxNormalExp ep < 0 := by
      simp only [minNormalExp, maxNormalExp]; omega
    omega
  -- `maxNormal + ulp = 2^(x.ex+1)` (pure value arithmetic at `x.ex = maxNormalExp`).
  have hmaxval : (PackedFloat.maxNormalNumber ep sp false).toRat
      + (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
        = 2 ^ (x.ex.toInt + 1) := by
    have hexp : x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int)
        = maxNormalExp ep - (sp : Int) := by rw [hsubshift, hxex]; simp
    rw [hexp, hxex, PackedFloat.toRat, PackedFloat.toRatSig_maxNormalNumber ep sp (by grind),
      PackedFloat.toRatExp_maxNormalNumber ep sp (by grind)]
    simp only [PackedFloat.sign_maxNormalNumber]
    rw [show (Bool.toSign false : Rat) = 1 by simp [Bool.toSign], Rat.one_mul]
    have e1 : (2 : Rat) ^ (-(sp : Int)) * 2 ^ (maxNormalExp ep) = 2 ^ (maxNormalExp ep - (sp : Int)) := by
      rw [Rat.zpow_mul_zpow (by grind)]; congr 1; omega
    have e2 : (2 : Rat) * 2 ^ (maxNormalExp ep) = 2 ^ (maxNormalExp ep + 1) := by
      rw [Rat.zpow_add_one (show (2 : Rat) ≠ 0 by grind), Rat.mul_comm]
    rw [Rat.sub_mul, e1, e2]; grind
  have hrtval : (x.blastRoundTowardZero ep sp).toRat' = (PackedFloat.maxNormalNumber ep sp false).toRat := by
    grind
  have hrtle := UnpackedFloat.blastRoundTowardZero_toRat'_le_toRat' (by grind) hsp heu hsu x hxsign hxnotunder hnotEarlyOver
  have hrtne : (x.blastRoundTowardZero ep sp).toRat' ≠ x.toRat' := by
    intro heq
    have hnn := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
      (by grind) hsp heu hsu x hxsign hxnotunder hnotEarlyOver).mp heq
    rw [hnn] at hnr; simp at hnr
  rw [← hrtval]
  grind

/--
info: 'Fp.UnpackedFloat.lt_toRat'_of_blastIsEarlyOverflow_next' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.lt_toRat'_of_blastIsEarlyOverflow_next

theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ e) (hsu : sp + 2 ≤ s)   -- ADDED (forwarded to the keystone)
    (x : UnpackedFloat e s)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (EUnpackedFloat.mkNumber (x.blastRoundTowardZero ep sp) :
      EUnpackedFloat e (sp+1)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      he hs heu hsu x hxsign hxnorm hnotunder hnotover
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := pf) (he := by grind) (hs := hs)
  · simp
  · exact hpfNotNaN
  · exact hpfLower
  · simpa using hToRat
  · simpa using hSign

/-- Main theorem: the bit-blasted lower-rounding circuit for nonnegative floats
    matches the SMT-LIB greatest lower bound. The proof unfolds
    `blastLowerNonneg` and dispatches to one of the three branch lemmas.

    Requires `x.normalize = x` (i.e. `x` is already in normalized form) so that
    the normal-range branch can identify `blastRoundTowardZero x` with a packed
    float — without normalization, multiple unpacked representations share the
    same value and the bit-level "extract top sp+1 bits" step does not commute
    with `toRat'`. -/
theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower (he : 2 < ep) (hsp : 0 < sp)
  (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
  (x : UnpackedFloat eu su)
  (hxsign : x.sign = false)
  (hxnorm : x.normalize = x) :
  (x.blastLowerNonneg ep sp).Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  unfold UnpackedFloat.blastLowerNonneg
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · simp [hunder]
    exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_underflow (by grind only) hsp heu (by grind) x hxsign hunder
  · simp only [Bool.not_eq_true] at hunder
    simp [hunder]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
    · simp [hover]
      -- The witness lemma must be instantiated at `em := eu` (not `exponentWidth ep sp`):
      -- `blastLowerNonneg` returns an `EUnpackedFloat eu (sp+1)`, so the goal mentions
      -- `UnpackedFloat.maxNormal eu (sp+1) ep sp false`.
      have := mkNumber_maxNormal_Rel_smtLibLower_of_overflow (x := x) (ep := ep) (sp := sp) (sm := sp + 1) (em := eu)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
      exact this
    · simp only [Bool.not_eq_true] at hover
      simp [hover]
      exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal (by grind only) hsp heu hsu x hxsign hxnorm hunder hover

/--
info: 'Fp.UnpackedFloat.blastLowerNonneg_Rel_smtLibLower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastLowerNonneg_Rel_smtLibLower

/-! ## Not perfectly approximable ⇒ `upper r = (lower r).successorAwayFromZero`

When `r` is strictly bracketed (`lower < r < upper`), the upper round is the immediate
successor (away from zero) of the lower round. This is roadmap step 4. -/

/-- For two finite floats, the float ordering matches the rational ordering of their values. -/
theorem lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm
    (he : 0 < e) (hs : 0 < s) (x y : PackedFloat e s)
    (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm) :
    x < y ↔ x.toRat < y.toRat := by
  rw [PackedFloat.lt_iff_toExtRat'_lt_toExtRat'_of_not_isZero_or_not_isZero he hs x y
      (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hx)
      (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hy)
      (Or.inl (by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hx)),
    PackedFloat.toExtRat'_eq_toRat_of hx, PackedFloat.toExtRat'_eq_toRat_of hy]
  rw [ExtRat.num_lt_num_iff]
  simp

/--
info: 'Fp.lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm

/-- If `r` is not perfectly approximable, `upper r` is the successor (away from zero) of
`lower r`. We take finiteness of `lower r` and of its successor (the latter fails only when
`lower r = maxNormal`, i.e. on overflow) plus `lower r`'s sign, all available in range. -/
theorem upper_eq_lower_successorAwayFromZero_of_ne
    (he : 1 < e) (hs : 0 < s) (r : Rat) (hrpos : 0 < r)
    (hfinL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).isNormOrNonzeroSubnorm)
    (hfinSucc : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero.isNormOrNonzeroSubnorm)
    (hsignL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).sign = false)
    (hne : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).toRat ≠ r) :
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat e s)
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero := by
  have he' : 0 < e := by grind
  have hLnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).isNaN := by
    simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfinL
  have hLinf : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).isInfinite := by
    simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfinL
  have hSnan : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero.isNaN := by
    simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfinSucc
  have hLlt_r := lower_toRat_lt_of_ne he' hs r hfinL hne
  have hLltS := PackedFloat.self_lt_successorAwayFromZero he hs
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s) hsignL hLnan hLinf
  have hSsign :
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero.sign
        = false := by simp [hsignL]
  -- The successor is a lawful upper of `r`.
  have hLawful : SmtLibSemantics.IsLawfulUpper (ExtRat.Number r)
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero := by
    apply PackedFloat.isLawfulUpper_of_le_toRat_of_no_float_between he hs r _ hSsign hfinSucc hrpos
    · -- `r ≤ successor.toRat`: else the successor would be a lower bound ≤ `lower`, contradicting `lower < successor`.
      apply Classical.byContradiction
      intro hcon
      have hlowuniv := (lsLawfulLower_smtLibLower e s he' hs (ExtRat.Number r)).2
      have hembed : SmtLibSemantics.RoundableEmbed.embed
          ((SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero)
            ≤ (ExtRat.Number r) := by
        simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
          PackedFloat.toExtRat'_eq_toRat_of hfinSucc]
        rw [ExtRat.ExtRat.num_le_num_iff]
        simp; grind
      have hSleL := hlowuniv _ hembed
      have hLleS := PackedFloat.le_of_lt hLltS
      exact PackedFloat.ne_of_lt hLltS (PackedFloat.le_antisymm_of_ne_NaN hLleS hSleL hLnan hSnan)
    · -- No float lies strictly between `r` and `successor`.
      intro y hysign hyfin hylt
      apply Classical.byContradiction
      intro hcon
      have hLlty : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s) < y := by
        rw [lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm he' hs _ _ hfinL hyfin]; grind
      have hyltS : y <
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat e s).successorAwayFromZero := by
        rw [lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm he' hs _ _ hyfin hfinSucc]; exact hylt
      exact PackedFloat.elim_self_lt_lt_successor he hs _ y hsignL hysign hLnan
        (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hyfin) hLinf hLlty hyltS
  rw [smtLibUpper_eq_upper e s he' hs (ExtRat.Number r) (by simp)]
  exact (eq_upper_of_IsLawfulUpper e s he' hs (ExtRat.Number r) _ (by simp) hLawful).symm

/--
info: 'Fp.upper_eq_lower_successorAwayFromZero_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms upper_eq_lower_successorAwayFromZero_of_ne

/-- Underflow spec: a tiny positive `r` (`0 < r ≤ minSubnormal`) rounds up to the smallest
positive subnormal. There is no nonzero float below `minSubnormalNumber`, so the LUB lemma's
"no float between" obligation is vacuous. (Mirrors the existing overflow spec
`upper_Number_eq_getInfinity_of_maxNormalNumber_lt`.) -/
theorem isLawfulUpper_minSubnormalNumber_of_pos_of_le
    (he : 1 < ep) (hsp : 0 < sp) (r : Rat) (hrpos : 0 < r)
    (hle : r ≤ (PackedFloat.minSubnormalNumber ep sp false).toRat) :
    SmtLibSemantics.IsLawfulUpper (ExtRat.Number r) (PackedFloat.minSubnormalNumber ep sp false) := by
  apply PackedFloat.isLawfulUpper_of_le_toRat_of_no_float_between he hsp r _
    (by simp [PackedFloat.sign_minSubnormalNumber])
    (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hsp)
    hrpos hle
  intro y hysign hyfin hylt
  exfalso
  have hynan : ¬ y.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hyfin
  have hyltfloat : y < PackedFloat.minSubnormalNumber ep sp false := by
    rw [lt_iff_toRat_lt_of_isNormOrNonzeroSubnorm (by grind) hsp y _ hyfin
      (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hsp)]
    exact hylt
  have hyzero := (PackedFloat.isZero_iff_lt_minSubnormalNumber_of_isNaN_of_nonneg y he hsp hynan hysign).mp hyltfloat
  have hynz := PackedFloat.not_isZero_of_isNormOrSubnorm hyfin
  simp [hyzero] at hynz

/--
info: 'Fp.isLawfulUpper_minSubnormalNumber_of_pos_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLawfulUpper_minSubnormalNumber_of_pos_of_le

/-! ## Bridge: the unpacked successor value equals the packed successor of `lower`

The crux connecting the bit-blasted circuit to the spec: the unpacked
`blastSuccessorAwayFromZero x` has the same value as the packed
`(lower (Number x.toRat')).successorAwayFromZero`. Both are `lower.toRat + 1 ulp`; the
unpacked ulp `2^(x.ex - sp + shift)` matches the packed ulp `2^(-sp)·2^(lower.toRatExp)`
because the keystone pins `lower.toRatExp = x.ex + shift`. -/
theorem UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_lower_successorAwayFromZero_toRat
    (he : 2 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false)
    (hfinL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm) :
    (x.blastSuccessorAwayFromZero ep sp).toRat'
      = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).successorAwayFromZero.toRat := by
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, hexpeq, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hsp _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hsp _)
  have hpfsign : pf.sign = false := by rw [← hSign, sign_blastRoundTowardZero, hxsign]
  have hpfInf : ¬ pf.isInfinite := by
    rw [hpflow]; simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfinL
  have hpfmax : pf ≠ PackedFloat.maxNormalNumber ep sp pf.sign := by
    rw [hpfsign, hpflow]; exact hmaxL
  -- The unpacked ulp equals the packed ulp (via the keystone's exponent equality).
  have hulp : (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
      = pf.sign.toSign * ((2 : Rat) ^ (-(sp : Int)) * 2 ^ pf.toRatExp) := by
    rw [hpfsign, hexpeq]
    have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
    rw [hsg, Rat.one_mul, Rat.zpow_mul_zpow (by grind)]
    congr 1
    grind
  rw [← hpflow,
    PackedFloat.toRat_successorAwayFromZero_eq pf hpfNotNaN hpfInf hpfmax (by grind) hsp,
    UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_blastRoundTowardZero_add_ulp
      (by grind) hsp heu hsu x hxsign hnotunder hnotover,
    hToRat, hulp]

/--
info: 'Fp.UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_lower_successorAwayFromZero_toRat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_lower_successorAwayFromZero_toRat

/-- **Upper keystone, Case B** (normal branch, `needsRounding = true`).

When `x` needs rounding, `blastSuccessorAwayFromZeroNonnegAux` returns
`blastSuccessorAwayFromZero x`, whose value (by the bridge) equals
`(lower (Number x.toRat')).successorAwayFromZero.toRat = (upper (Number x.toRat')).toRat`
(step 4). The witness is `upper (Number x.toRat')` itself. -/
theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_needsRounding
    (he : 2 < ep) (hsp : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hxpos : 0 < x.toRat')
    (hfinL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNormOrNonzeroSubnorm)
    (hfinSucc : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).successorAwayFromZero.isNormOrNonzeroSubnorm)
    (hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      ≠ PackedFloat.maxNormalNumber ep sp false)
    (hnr : x.needsRounding ep sp = true) :
    (EUnpackedFloat.mkNumber (x.blastSuccessorAwayFromZero ep sp) : EUnpackedFloat eu (sp + 1)).Rel
      (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  -- Pin `lower`, and derive its sign and non-approximability.
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hsp _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hsp _)
  have hsignL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).sign
      = false := by rw [← hpflow, ← hSign, sign_blastRoundTowardZero, hxsign]
  have hne : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
      ≠ x.toRat' := by
    rw [← hpflow, ← hToRat]
    intro hcontra
    have hnotneeds := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
      (by grind) hsp heu hsu x hxsign hnotunder hnotover).mp hcontra
    rw [hnotneeds] at hnr
    simp at hnr
  -- `upper = lower.succ` (step 4) and `blastSucc.toRat' = lower.succ.toRat` (bridge).
  have hupeq := upper_eq_lower_successorAwayFromZero_of_ne (e := ep) (s := sp)
    (by grind) hsp x.toRat' hxpos hfinL hfinSucc hsignL hne
  have hbridge := UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_lower_successorAwayFromZero_toRat
    he hsp heu hsu x hxsign hxnorm hnotunder hnotover hmaxL hfinL
  have hval : (x.blastSuccessorAwayFromZero ep sp).toRat'
      = (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat := by
    rw [hupeq]; exact hbridge
  have hsgn : (x.blastSuccessorAwayFromZero ep sp).sign
      = (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp).sign := by
    rw [sign_blastSuccessorAwayFromZero, hxsign, hupeq, PackedFloat.sign_successorAwayFromZero, hsignL]
  apply EUnpackedFloat.Rel_smtLibUpper_of_witness
    (pf := (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp))
    (he := by grind) (hs := hsp)
  · simp
  · simpa using not_isNaN_upper_of_ne_NaN ep sp (by grind) hsp _ (by simp)
  · exact isLawfulUpper_upper ep sp (by grind) hsp (ExtRat.Number x.toRat')
  · simpa using hval
  · simpa using hsgn

/--
info: 'Fp.UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_needsRounding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_needsRounding

/-# `blastUpperNonneg` matches `upper` -/

/-- **Case A** (normal branch, no rounding): when `x` needs no rounding, the upper-rounding
circuit's normal branch relates to `upper`. (Recovered onto this branch; PR #26 landed it on a
non-main branch.) -/
theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_not_needsRounding
    (he : 2 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hxpos : 0 < x.toRat')
    (hnr : x.needsRounding ep sp = false) :
    (EUnpackedFloat.mkNumber (x.blastRoundTowardZero ep sp) : EUnpackedFloat eu (sp + 1)).Rel
      (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  have hround : (x.blastRoundTowardZero ep sp).toRat' = x.toRat' :=
    UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_of_not_needsRounding
      (by grind) hsp heu hsu x hxsign hnotunder hnotover hnr
  have hpfval : pf.toRat = x.toRat' := by rw [← hToRat, hround]
  have hlowLawful :
      SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat')
        (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    lsLawfulLower_smtLibLower ep sp (by grind) hsp (ExtRat.Number x.toRat')
  have hlowNotNaN :
      ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN := by
    simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hsp (ExtRat.Number x.toRat') (by simp)
  have hpflow :
      pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _
      hpfNotNaN hlowNotNaN hpfLower hlowLawful
  have hlowToRat :
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        = x.toRat' := by rw [← hpflow]; exact hpfval
  have hfin := isNormOrNonzeroSubnorm_lower_of_toRat_eq (e := ep) (s := sp)
    (by grind) hsp x.toRat' (by grind) hlowToRat
  have hupeq := upper_eq_lower_of_lower_isNormOrNonzeroSubnorm (e := ep) (s := sp)
    (by grind) hsp x.toRat' hfin hlowToRat
  have hpfupper : SmtLibSemantics.IsLawfulUpper (ExtRat.Number x.toRat') pf := by
    rw [hpflow, ← hupeq]
    exact isLawfulUpper_upper ep sp (by grind) hsp (ExtRat.Number x.toRat')
  apply EUnpackedFloat.Rel_smtLibUpper_of_witness (pf := pf) (he := by grind) (hs := hsp)
  · simp
  · exact hpfNotNaN
  · exact hpfupper
  · simpa using hToRat
  · simpa using hSign

/--
info: 'Fp.UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_not_needsRounding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_not_needsRounding

/-- **Wrapper dispatch** (in-range, no underflow): assembles the leaf cases. With `¬x.under`,
the successor never underflows so the underflow branch is dead; the overflow branch uses the
overflow connection + spec, and the normal branch routes to Case A / Case B. `hmaxL`
(`lower ≠ maxNormal`) is the one residual obligation (discharged by a converse-overflow argument). -/
theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_in_range
    (he : 2 < ep) (hsp : 0 < sp) (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false) :
    (x.blastUpperNonneg ep sp).Rel
      (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  have he' : 0 < ep := by grind
  have hmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg (by grind) hsp heu x hxnorm hnotunder
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  have hfinL := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp he' hsp _ (by simp)) hpfLower
      (lsLawfulLower_smtLibLower ep sp he' hsp _)
  have hsignL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).sign = false := by
    rw [← hpflow, ← hSign, sign_blastRoundTowardZero, hxsign]
  have hlowToRat' : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
      = (x.blastRoundTowardZero ep sp).toRat' := by rw [← hpflow]; exact hToRat.symm
  have hnnu : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp = false := by
    have hmono := UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux (by grind) hsp heu x hnotover
    have hxu : minSubnormalExp ep sp ≤ x.ex.toInt := by
      rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hnotunder
      simpa using hnotunder
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu]
    simp only [decide_eq_false_iff_not]; omega
  unfold UnpackedFloat.blastUpperNonneg
  simp only [hnnu, Bool.false_eq_true, if_false]
  by_cases ho : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp = true
  · -- Overflow branch: `mkInfinity false`.
    simp only [ho, if_true]
    have hupinf : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.getInfinity ep sp false := by
      rw [smtLibUpper_eq_upper ep sp he' hsp _ (by simp)]
      exact upper_Number_eq_getInfinity_of_maxNormalNumber_lt he' hsp x.toRat'
        (UnpackedFloat.lt_toRat'_of_blastIsEarlyOverflow_next (by grind) hsp heu hsu x hxsign hnotover ho)
    apply EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign
    · simp [EUnpackedFloat.mkInfinity]
    · rw [hupinf]; simp [PackedFloat.isInfinite_getInfinity, hsp]
    · rw [hupinf]; simp [EUnpackedFloat.mkInfinity, EUnpackedFloat.sign, PackedFloat.sign_getInfinity]
  · -- Normal branch: `mkNumber next` → Case A / Case B.
    simp only [ho, Bool.false_eq_true, if_false]
    by_cases hr : x.needsRounding ep sp = true
    · -- Case B: derive `lower ≠ maxNormal` here (else the converse forces `next.over`).
      have hmaxL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
          ≠ PackedFloat.maxNormalNumber ep sp false := by
        intro heqmax
        have hle := lower_toRat_le he' hsp x.toRat' hfinL
        have hne : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
            ≠ x.toRat' := by
          rw [hlowToRat']
          intro he2
          have := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
            (by grind) hsp heu hsu x hxsign hnotunder hnotover).mp he2
          rw [this] at hr; simp at hr
        have hlowlt : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
            < x.toRat' := by grind
        rw [heqmax] at hlowlt
        exact ho (UnpackedFloat.blastIsEarlyOverflow_next_of_maxNormalNumber_lt
          he hsp heu hsu x hxsign hxnorm hnotover hnotunder hlowlt)
      have hfinSucc := PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal
        (by grind) hsp _ hsignL hfinL hmaxL
      have heq : x.blastSuccessorAwayFromZeroNonnegAux ep sp = x.blastSuccessorAwayFromZero ep sp := by
        rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_pos hr]
      rw [heq]
      exact UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_needsRounding
        (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover hxpos hfinL hfinSucc hmaxL hr
    · simp only [Bool.not_eq_true] at hr
      have heq : x.blastSuccessorAwayFromZeroNonnegAux ep sp = x.blastRoundTowardZero ep sp := by
        rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_neg (by simp [hr])]
      rw [heq]
      exact UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_normal_of_not_needsRounding
        (by grind) hsp heu hsu x hxsign hxnorm hnotunder hnotover hxpos hr

/-- **Subnormal underflow boundary.** When `x` underflows (`x.ex < minSubnormalExp`) but does not
*early*-underflow (so `x.ex = minSubnormalExp - 1`), `x.toRat'` lies in `(0, minSubnormalNumber)`,
hence `upper x.toRat' = minSubnormalNumber`. The circuit rounds `x` up to `minSubnormalNumber`
either through its underflow branch (`minSubnormalForPackedFloat`) or through a carry into
`minSubnormalExp` (the successor); both witnesses have value `minSubnormalNumber.toRat`. -/
theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper_boundary
    (he : 2 < ep) (hsp : 0 < sp) (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxmsb : x.sig.msb = true)
    (hunder : x.blastIsUnderflowNonneg ep sp = true)
    (hnotEU : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.blastUpperNonneg ep sp).Rel
      (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  have he' : 0 < ep := by grind
  -- The exponent sits exactly at the boundary: `minSubnormalExp - 1`.
  have hexlt : x.ex.toInt < minSubnormalExp ep sp := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hunder
    simpa using hunder
  have hexge : minSubnormalExp ep sp - 1 ≤ x.ex.toInt := by
    rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (by grind) hsp heu] at hnotEU
    simp only [decide_eq_false_iff_not, Int.not_lt] at hnotEU; omega
  have hexeq : x.ex.toInt = minSubnormalExp ep sp - 1 := by omega
  have hms : minSubnormalExp ep sp = minNormalExp ep - sp := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  -- `¬EarlyOverflow` (needed by the successor exponent bounds).
  have hmaxN : minSubnormalExp ep sp ≤ maxNormalExp ep := by
    have hb := bias_pos_of_one_lt ep (by grind)
    rw [minSubnormalExp_eq_neg_bias_minus_s_minus_one (by grind)]; simp only [maxNormalExp]; omega
  have hnotover : x.blastIsEarlyOverflowNonneg ep sp = false := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hsp heu]
    simp only [decide_eq_false_iff_not, Int.not_lt]; omega
  -- `0 < x.toRat' < minSubnormalNumber`.
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hxmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  have hle : x.toRat' ≤ (PackedFloat.minSubnormalNumber ep sp false).toRat := by
    have h1 := UnpackedFloat.toRat'_lt_two_pow_ex_succ_of_sign_false x (by grind) hxsign
    rw [hexeq, show minSubnormalExp ep sp - 1 + 1 = minNormalExp ep - sp by omega] at h1
    rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
    exact Rat.le_of_lt h1
  have hupper : SmtLibSemantics.IsLawfulUpper (ExtRat.Number x.toRat')
      (PackedFloat.minSubnormalNumber ep sp false) :=
    isLawfulUpper_minSubnormalNumber_of_pos_of_le (by grind) hsp x.toRat' hxpos hle
  have hmsNaN : ¬ (PackedFloat.minSubnormalNumber ep sp false).isNaN := by
    simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm
      (PackedFloat.isNormOrNonzeroSubnorm_minSubnormalNumber ep sp false (by grind) hsp)
  -- Dispatch on the circuit's flags.
  unfold UnpackedFloat.blastUpperNonneg
  by_cases hnu : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp = true
  · -- Underflow branch: `minSubnormalForPackedFloat`.
    simp only [hnu, if_true]
    apply EUnpackedFloat.Rel_smtLibUpper_of_witness
      (pf := PackedFloat.minSubnormalNumber ep sp false) (he := he') (hs := hsp)
    · simp
    · exact hmsNaN
    · exact hupper
    · simp only [EUnpackedFloat.num_mkNumber]
      exact UnpackedFloat.toRat'_minSubnormalForPackedFloat_eq_toRat_minSubnormalNumber
        ep sp eu (by grind) hsp heu
    · simp [EUnpackedFloat.num_mkNumber, UnpackedFloat.minSubnormalForPackedFloat,
        PackedFloat.sign_minSubnormalNumber]
  · simp only [Bool.not_eq_true] at hnu
    by_cases hno : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp = true
    · -- Overflow branch is vacuous: the carry reaches at most `minSubnormalExp ≤ maxNormalExp`.
      exfalso
      have hub := UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one
        (by grind) hsp heu x hnotover
      rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hsp heu] at hno
      simp only [decide_eq_true_eq] at hno; omega
    · simp only [Bool.not_eq_true] at hno
      simp only [hnu, hno, Bool.false_eq_true, if_false]
      -- Normal branch: the successor carried into `minSubnormalExp`, value `2^minSubnormalExp`.
      have hlb := UnpackedFloat.ex_le_ex_blastSuccessorAwayFromZeroNonnegAux
        (by grind) hsp heu x hnotover
      have hub := UnpackedFloat.ex_blastSuccessorAwayFromZeroNonnegAux_le_ex_add_one
        (by grind) hsp heu x hnotover
      have hnnu : minSubnormalExp ep sp ≤ (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt := by
        rw [UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hsp heu] at hnu
        simpa using hnu
      have hnextex : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt = x.ex.toInt + 1 := by omega
      have hnr : x.needsRounding ep sp = true := by
        apply Classical.byContradiction; intro h
        simp only [Bool.not_eq_true] at h
        rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_neg (by simp [h]),
          ex_blastRoundTowardZero] at hnextex
        omega
      have hAux : x.blastSuccessorAwayFromZeroNonnegAux ep sp = x.blastSuccessorAwayFromZero ep sp := by
        rw [UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux, if_pos hnr]
      rw [hAux] at hnextex ⊢
      have hval : (x.blastSuccessorAwayFromZero ep sp).toRat' = (2 : Rat) ^ (x.ex.toInt + 1) :=
        UnpackedFloat.blastSuccessorAwayFromZero_toRat'_eq_two_pow_of_ex_succ
          ep sp (by grind) x hxsign hnextex
      apply EUnpackedFloat.Rel_smtLibUpper_of_witness
        (pf := PackedFloat.minSubnormalNumber ep sp false) (he := he') (hs := hsp)
      · simp
      · exact hmsNaN
      · exact hupper
      · simp only [EUnpackedFloat.num_mkNumber]
        rw [PackedFloat.toExtRat_minSubnormal_eq ep sp (by grind) hsp]
        have hval' : (x.blastSuccessorAwayFromZero ep sp).toRat' sp = (2 : Rat) ^ (x.ex.toInt + 1) := hval
        rw [hval']
        congr 1; omega
      · simp only [EUnpackedFloat.num_mkNumber, PackedFloat.sign_minSubnormalNumber,
          UnpackedFloat.blastSuccessorAwayFromZero, clearSignificand_sign, hxsign]

theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper (he : 1 < ep) (hs : 0 < sp)
  (x : UnpackedFloat eu su)
  (hxsign : x.sign = false) :
  (x.blastUpperNonneg ep sp).Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastUpperNonneg]
  sorry


/-# `blastLower` matches `lower` -/

theorem UnpackedFloat.blastLower_Rel_smtLibLower (hep : 2 < ep)
  (hsp : 0 < sp)
  (hsu : sp + 2 ≤ su)
  (heu : exponentWidth ep sp ≤ eu)
  (x : UnpackedFloat eu su)
  (hxnorm : x.normalize = x) :
  (x.blastLower ep sp).Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastLower]
  by_cases hsign : x.sign
  · simp [hsign]
    simp [UnpackedFloat.blastLowerNeg]
    rw [smtLibLower_eq_neg_smtLibUpper_neg]
    · apply EUnpackedFloat.neg_Rel_neg
      simp
      rw [show - x.toRat' = (-x).toRat' by simp]
      apply UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper
      · grind
      · grind
      · simp [hsign]
    · grind only
    · grind only
    · grind only
  · simp [hsign]
    apply UnpackedFloat.blastLowerNonneg_Rel_smtLibLower
    · grind only
    · grind only
    · grind
    · grind
    · grind only
    · grind only

/-# `blastUpper` matches `upper` -/


theorem UnpackedFloat.blastUpper_Rel_smtLibUpper (hep : 2 < ep) (hsp : 0 < sp)
    (hsu : sp + 2 ≤ su)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x) :
    (x.blastUpper ep sp).Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastUpper]
  by_cases hsign : x.sign
  · simp [hsign]
    simp [UnpackedFloat.blastUpperNeg]
    rw [smtLibUpper_eq_neg_smtLibLower_neg]
    · apply EUnpackedFloat.neg_Rel_neg
      simp
      rw [show - x.toRat' = (-x).toRat' by simp]
      apply UnpackedFloat.blastLowerNonneg_Rel_smtLibLower
      · grind
      · grind
      · grind
      · grind
      · simp; grind only
      · exact normalize_neg_eq_neg_of_normalize_eq x hxnorm
    · grind only
    · grind only
    · grind only
  · simp [hsign]
    apply UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper
    · grind only
    · grind only
    · simp [hsign]

end Fp
