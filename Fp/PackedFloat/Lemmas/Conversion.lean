import Fp.PackedFloat.Lemmas.Classification

/-!
## Basic conversion lemmas about `PackedFloat`

Bounds and monotonicity of `toRatSig`/`toRatExp`, injectivity of the rational
denotation, and `toExtRat`/`toExtRat'` facts.
-/

namespace PackedFloat

/--
Subnormal numbers are smaller than '2^minNormalExp'.
-/
@[simp, grind .]
theorem toRatSig_mul_toRatExp_lt_two_pow_minNormalExp_of_isNonzeroSubnorm {x : PackedFloat e s}
    (hx : x.isNonzeroSubnorm) :
      x.toRatSig * (2 : Rat) ^ x.toRatExp < (2 : Rat) ^ minNormalExp e := by
  rw [toRatExp_eq_of_not_isNorm]
  apply Rat.lt_mul_self_of_lt_one
  · grind only [zero_le_twoNumberRatSig, !toRatSig_lt_ite, → not_isSubnorm_of_isNorm,
    Rat.natCast_eq_zero_iff, = Bool.toNat.eq_1]
  · grind only [Fp.Rat.two_pow_pos]
  · grind only [→ not_isNorm_of_isSubnorm]



@[simp, grind .]
theorem two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm
    {x : PackedFloat e s}
    (hx : x.isNorm) :
    (2 : Rat) ^ minNormalExp e ≤ x.toRatSig * (2 : Rat) ^ x.toRatExp  := by
  rw [x.toRatExp_eq_of_isNorm (by grind only)]
  norm_cast
  -- rw [Rat.zpow_sub_eq_zpow_mul_zpow]
  have : 1 ≤ x.toRatSig := by grind only [one_le_toRatSig_of_isNorm]
  rw [minNormalExp]
  have : x.ex ≠ 0 := by grind only [ex_ne_zero_if_isNorm, = BitVec.ofNat_eq_ofNat,
    = BitVec.zero_eq]
  norm_cast
    -- 2 ^ - (bias e - 1) ≤ 2 ^ (- bias e)
  have : (2 : Rat) ^ ((- ((bias e - 1) : Nat)) : Int) ≤ (2 : Rat) ^ (((x.ex.toNat: Int) - (bias e : Int)) : Int) := by
    norm_cast
    apply Rat.two_pow_le_two_pow_of_le
    grind
  apply Rat.le_mul_of_one_le_of_le
  · grind only
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · grind only

/--
write being isNorm in terms of an arithmetic condition in terms of
the rational values of the significand and exponent.
-/
theorem isNorm_iff_toRatSig_times_toRatExp_ge
    {x : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) :
    x.isNorm ↔ decide ((2 : Rat) ^ minNormalExp e ≤ x.toRatSig * (2 : Rat) ^ x.toRatExp) := by
  simp only [decide_eq_true_eq]
  constructor
  · apply two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm
  · apply Classical.byContradiction
    intros h
    simp at h
    have := x.toRatSig_mul_toRatExp_lt_two_pow_minNormalExp_of_isNonzeroSubnorm (by grind)
    grind only

/--
This is true because we can separate out the
cases of normal and subnormal based on values,
and the largest subnormal is smaller than the smallest normal.
-/
@[simp, grind .]
theorem isNorm_eq_of_toRat_eq {x y : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
    (heq : x.toRat = y.toRat) :
    (x.isNorm = y.isNorm) := by
  have hsign : x.sign = y.sign := by
    apply PackedFloat.sign_eq_of_toRat_eq hx hy heq
  have h' := heq
  simp [toRat] at h'
  rw [hsign] at h'
  have : x.toRatSig * 2 ^ x.toRatExp = y.toRatSig * 2 ^ y.toRatExp := by
    rw [← Rat.mul_cancel_left (x := x.sign.toSign)]
    · grind
    · simp
  have xval := x.isNorm_iff_toRatSig_times_toRatExp_ge (by grind)
  have yval := y.isNorm_iff_toRatSig_times_toRatExp_ge (by grind)
  rcases hxnorm : x.isNorm
  · simp [hxnorm] at this xval
    rcases hynorm : y.isNorm
    · simp only
    · simp only [hynorm, two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm, decide_true,
      Bool.false_eq_true] at this yval ⊢
      grind only [two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm]
  · simp [hxnorm] at this xval
    rcases hynorm : y.isNorm
    · simp [hynorm] at this yval ⊢
      grind only [two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm]
    · simp only


@[simp, grind .]
theorem sig_eq_and_ex_eq_of_toRat_eq {x y : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
    (heq : x.toRat = y.toRat) :
    x.sign = y.sign ∧ x.sig = y.sig ∧ x.ex = y.ex := by
  have hNormState := PackedFloat.isNorm_eq_of_toRat_eq hx hy heq
  have hSignEq : x.sign = y.sign := by
    apply PackedFloat.sign_eq_of_toRat_eq hx hy heq
  simp [toRat] at heq
  rw [hSignEq] at heq
  simp [hSignEq]
  have : x.toRatSig  * 2 ^ x.toRatExp = y.toRatSig * 2 ^ y.toRatExp := by
    rw [← Rat.mul_cancel_left (x := x.sign.toSign)]
    · grind
    · simp
  have xsigNeZero : x.toRatSig ≠ 0 := by grind only [toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
  have ySigNeZero : y.toRatSig ≠ 0 := by grind only [toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
  by_cases hxnorm : x.isNorm
  · have := mul_two_pow_inj
      x.toRatSig
      y.toRatSig
      x.toRatExp
      y.toRatExp
      (by grind only)
      (by grind only [one_le_toRatSig_of_isNorm])
      (by grind only [one_le_toRatSig_of_isNorm])
      (by grind only [toRatSig_lt_two])
    -- now I need to know that 'toRatSig', 'toRatExp' are equal.
    have hSigEq := sig_eq_of_toRatSig_eq_toRatSig
       (x := x) (y := y) (by grind) (by grind)
    simp [hSigEq]
    have hExpEq := exp_eq_of_toRatExp_eq
      (x := x) (y := y) (by grind) (by grind) (by grind) (by grind)
    simp [hExpEq]
  · have xSubnorm : x.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    have ySubnorm : y.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    have expEq : x.toRatExp = y.toRatExp := by
      simp [x.toRatExp_eq_of_not_isNorm (by grind only)]
      simp [y.toRatExp_eq_of_not_isNorm (by grind only)]
    have sigEq : x.toRatSig = y.toRatSig := by
      rw [← Rat.mul_cancel_right (x := 2 ^ x.toRatExp)]
      · rw [expEq]
        grind only
      · grind only [Rat.two_pow_int_ne_zero]
    have : x.sig = y.sig := by
      rw [x.toRatSig_eq_of_not_isNorm (by grind only)] at sigEq
      rw [y.toRatSig_eq_of_not_isNorm (by grind only)] at sigEq
      have hTwoPowNeZero : (2 : Rat) ^ s ≠ 0 := by norm_cast; grind only [usr Nat.pow_pos]
      rw [Rat.div_cancel hTwoPowNeZero] at sigEq
      simp at sigEq
      apply BitVec.eq_of_toNat_eq
      assumption
    simp [this]
    rw [exp_eq_of_isNonzeroSubnorm (by grind only)]
    rw [exp_eq_of_isNonzeroSubnorm (by grind only)]

theorem eq_of_toExtRat'_eq (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero)
    (h : x.toExtRat' = y.toExtRat') : x = y := by
  simp [PackedFloat.toExtRat'] at h
  have hExtRateq := h
  simp [hx, hy] at h
  by_cases hxinf : x.isInfinite
  · simp [hxinf] at h
    by_cases hyinf : y.isInfinite
    · simp [hyinf] at h
      grind only [PackedFloat.eq_getInfinity_iff_isInfinity, → eq_mkInfinity_of_isInfinite,
        !isInfinite_getInfinity, #5505cb0d9cd21b53]
    · by_cases hyinf : y.isInfinite
      · simp [hyinf] at h
        grind only
      · simp [hyinf] at h
  · simp [hxinf] at h
    by_cases hyinf : y.isInfinite
    · simp [hyinf] at h
    · simp [hyinf] at h
      have :=
        PackedFloat.sig_eq_and_ex_eq_of_toRat_eq (x := x) (y := y)
        (by grind only [= isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero])
        (by grind only [= isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero])
        (by grind)
      apply PackedFloat.ext <;> grind only


/--
info: 'PackedFloat.eq_of_toExtRat'_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_of_toExtRat'_eq


@[grind ., grind =]
theorem isNaN_iff_toExtRat'_eq_NaN (x : PackedFloat e s) (hs : 0 < s) :
    x.isNaN ↔ x.toExtRat' = .NaN := by
  constructor
  · intros h
    simp [h]
  · intros hx
    induction x using PackedFloat.classification <;> grind

@[simp]
theorem PackedFloat.zero_le_toExtRat'_iff (x : PackedFloat e s) :
    ExtRat.Number 0 ≤ x.toExtRat' ↔ (¬ x.isNaN ∧ (x.isZero ∨ x.sign = false)) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp
      · simp; grind only [→ PackedFloat.not_isZero_of_isInfinite]
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind

@[simp]
theorem PackedFloat.le_zero_toExtRat'_iff (x : PackedFloat e s) :
    x.toExtRat' ≤ .Number 0 ↔ (¬ x.isNaN ∧ (x.isZero ∨ x.sign = true)) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp
        grind only [→ not_isZero_of_isInfinite]
      · simp
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind


@[simp]
theorem PackedFloat.lt_zero_toExtRat'_iff (x : PackedFloat e s) :
    x.toExtRat' < .Number 0 ↔ (¬ x.isNaN ∧ ¬ x.isZero ∧ x.sign = true) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp
      · simp; grind only [→ not_isZero_of_isInfinite]
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind
/--
info: 'PackedFloat.PackedFloat.lt_zero_toExtRat'_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PackedFloat.lt_zero_toExtRat'_iff


@[simp]
theorem PackedFloat.zero_lt_toExtRat'_iff (x : PackedFloat e s) :
    .Number 0 < x.toExtRat' ↔ (¬ x.isNaN ∧ ¬ x.isZero ∧ x.sign = false) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp; grind only [→ not_isZero_of_isInfinite]
      · simp;
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind

@[simp]
theorem eq_getInfinity_iff_toExtRat'_eq_Infinity (x : PackedFloat e s)
    (sign : Bool)
    (hs : 0 < s := by solve | simp | grind) :
    x.toExtRat' = ExtRat.Infinity sign ↔ x  = PackedFloat.getInfinity e s sign := by
  grind only [= toExtRat'_eq_Infinity_of_isInfinite, = toExtRat'_eq_NaN_of_isNaN,
    = toExtRat'_eq_zero_of_isZero, = toExtRat'_eq_toRat_of,
    !toExtRat'_getInfinity, !isInfinite_getInfinity, eq_getInfinity_iff_isInfinity,
    = isNaN_iff_toExtRat'_eq_NaN, = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero, #8ef6]

end PackedFloat
