import Fp.PackedFloat.Lemmas.Classification

/-!
## Basic conversion lemmas about `PackedFloat`

Bounds and monotonicity of `toRatSig`/`toRatExp`, injectivity of the rational
denotation, and `toExtRat`/`toExtRat'` facts.
-/

namespace PackedFloat

@[simp]
theorem toExtDyadic_eq_NaN_of_isNaN (pf : PackedFloat e s) (hp : pf.isNaN) :
    pf.toExtDyadic = .NaN := by
  simp [toExtDyadic, hp]

@[simp]
theorem toExtDyadic_eq_Infinity_of_isInfinite (pf : PackedFloat e s) (hp : pf.isInfinite) :
    pf.toExtDyadic = .Infinity pf.sign := by
  simp only [toExtDyadic, hp, BitVec.setWidth'_eq, Int.natCast_add, cond_true]
  grind [not_isNaN_of_isInfinite]

@[simp]
theorem toRatSig_neg (pf : PackedFloat e s) : (- pf).toRatSig = pf.toRatSig := by
  simp [toRatSig]

/--
This gives precise bounds on `toRatSig` as being bounded above by one, when it's a nonzero subnormal.
-/
@[simp]
theorem toRatSig_plus_le_one_of_isNonzeroSubnorm (pf : PackedFloat e s)
  (hnorm : pf.isNonzeroSubnorm) :
    pf.toRatSig  + 1 / 2 ^ s ≤ 1 := by
  simp [toRatSig]
  simp [show ¬ pf.isNorm by grind only [→ not_isNorm_of_isSubnorm]]
  have : pf.sig.toNat < 2 ^ s := by
    grind only [usr BitVec.isLt]
  suffices ((pf.sig.toNat : Rat) + 1) / 2 ^ s ≤ 1 by
    grind only    -- grind?
  apply Rat.div_le_of_le_mul
  · grind only [Rat.pow_pos]
  · norm_cast; simp; grind only

/--
This gives precise bounds on `toRatSig` as being bounded above by one, when it's a nonzero subnormal.
-/
@[simp]
theorem toRatSig_le_one_sub_of_isNonzeroSubnorm (pf : PackedFloat e s)
  (hnorm : pf.isNonzeroSubnorm) :
    pf.toRatSig  ≤ 1 - 1 / 2 ^ s := by
  have := toRatSig_plus_le_one_of_isNonzeroSubnorm pf hnorm
  grind only

/--
This gives precise bounds on `toRatSig` as being bounded above by two.
-/
@[simp]
theorem toRatSig_plus_le_two_of_isNorm (pf : PackedFloat e s) (hnorm : pf.isNorm) :
    pf.toRatSig  + 1 / 2 ^ s ≤ 2 := by
  simp [toRatSig, hnorm]

  suffices (pf.sig.toNat : Rat) / 2 ^ s + 1 / 2 ^ s ≤ (1 : Rat) by
    grind only
  have : pf.sig.toNat < 2 ^ s := by
    grind only [usr BitVec.isLt]
  suffices ((pf.sig.toNat : Rat) + 1) / 2 ^ s ≤ 1 by
    grind only    -- grind?
  apply Rat.div_le_of_le_mul
  · grind only [Rat.pow_pos]
  · norm_cast; simp; grind only

/--
Gives imprecise  but quantitiatve bounds on `toRatSig` as being bounded above by two,
when it's nonzero. More precise bounds are given by
`toRatSig_le_two_sub_of_isNorm` and `lt_twoRatSig_of_sig_ne_zero`.
-/
@[simp]
theorem toRatSig_plus_le_two_of_isNormOrNonzeroSubnorm
    (pf : PackedFloat e s) (hnorm : pf.isNormOrNonzeroSubnorm) :
    pf.toRatSig  + 1 / 2 ^ s ≤ 2 := by
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
  · suffices pf.toRatSig + 1 / 2^s ≤ 1 by grind
    have : pf.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    simp [this]


/--
This gives precise bounds on `toRatSig` as being bounded above by two
-/
@[simp]
theorem toRatSig_le_two_sub_of_isNorm (pf : PackedFloat e s) (hnorm : pf.isNorm) :
    pf.toRatSig  ≤ 2 - 1 / 2 ^ s := by
  have := toRatSig_plus_le_two_of_isNorm pf hnorm
  grind only


/--
`1/2^s` is a lower bound on 'toRatSig` when it's nonzero.
-/
theorem lt_twoRatSig_of_sig_ne_zero (pf : PackedFloat e s)
    (hsig : pf.sig ≠ 0#_) :
    (1 : Rat) / 2^s ≤  pf.toRatSig := by
  rw [PackedFloat.toRatSig]
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
    apply Rat.le_add_of_le_of_nonneg
    · norm_cast
      apply Rat.div_le_self_of_nonneg_of_one_le
      · grind
      · grind
    · grind only [Fp.Rat.div_nonneg, Rat.pow_nonneg]
  · simp [hnorm]
    rw [Rat.div_le_div_self]
    · apply Classical.byContradiction
      intros hcontra
      simp at hcontra
      norm_cast at hcontra
      grind only [= BitVec.ofNat_toNat, = BitVec.getElem_zero, = BitVec.getElem_setWidth,
        = BitVec.getLsbD_eq_getElem, #4929]
    · grind only [Rat.pow_pos]

/--
If we have two floating point numbers
whose significands are ordered, and whose normality is the same,
then their `toRatSig` are ordered in the same way, up to a gap of `1/2^s`.
This gives us the 'gap' between floating point numbers.
-/
theorem toRatSig_add_le_toRatSig_of_lt_of_isNorm_eq_isNorm
    (x y : PackedFloat e s)
    (hnorm : x.isNorm = y.isNorm)
    (hsig : x.sig < y.sig) :
    x.toRatSig + (1 : Rat) / 2^s ≤ y.toRatSig := by
  rw [PackedFloat.toRatSig, PackedFloat.toRatSig]
  by_cases hnorm : x.isNorm
  · by_cases hnorm' : y.isNorm
    · simp only [hnorm, ↓reduceIte, hnorm']
      rw [Rat.add_assoc]
      simp only [Rat.div_add_eq_div_add_div, Rat.add_le_iff_le']
      rw [Rat.div_le_cancel]
      · suffices x.sig.toNat < y.sig.toNat from by
          norm_cast
        rw [← BitVec.lt_def]
        simp [hsig]
      · grind only [Rat.pow_pos]
    · grind only
  · by_cases hnorm' : y.isNorm
    · grind only
    · simp [hnorm, hnorm']
      rw [Rat.div_le_cancel]
      · suffices x.sig.toNat < y.sig.toNat from by
          norm_cast
        rw [← BitVec.lt_def]
        simp [hsig]
      · grind


/--
A subnormal number's signifiand interpretation is
smaller than a normal number's, by the same gap of `1/2^s`.
-/
theorem toRatSig_add_one_div_two_pow_lt_toRatSig_of_eq_isNorm_of_not_eq_isNorm
    (x y : PackedFloat e s)
    (hxnorm : x.isNonzeroSubnorm)
    (hynorm : y.isNorm)
    (hsig : x.sig < y.sig) :
    x.toRatSig + (1 : Rat) / 2^s ≤ y.toRatSig := by
  rw [PackedFloat.toRatSig, PackedFloat.toRatSig]
  simp only [show x.isNorm = false by grind, Bool.false_eq_true, ↓reduceIte, Rat.zero_add,
    Rat.div_add_eq_div_add_div, hynorm]
  rw [Rat.add_div_eq_add_div']
  · rw [Rat.div_le_cancel]
    · norm_cast
      simp only [Nat.one_mul]
      have : 1 ≤ 2^s := by grind
      have : x.sig.toNat < y.sig.toNat := by
        rw [← BitVec.lt_def]
        simp [hsig]
      grind only
    · grind only [Rat.pow_pos]
  · grind only [Rat.two_pow_nat_ne_zero]

@[grind .]
theorem one_le_toRatSig_of_isNorm {e s} (pf : PackedFloat e s) (hnorm : pf.isNorm) :
  1 ≤ pf.toRatSig := by
  simp [toRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : (1 + pf.sig.toNat / 2^s) ≥ 0 := by grind
  grind

/-- `PackedFloat.toRatSig` is nonnegative. -/
@[simp, grind .]
theorem nonneg_toRatSig (pf : PackedFloat e s) : 0 ≤ pf.toRatSig := by
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
    Rat.pow_nonneg]
  have : (0 + pf.sig.toNat / 2^s) ≥ 0 := by grind only
  have : pf.sig.toNat / 2^s ≥ 0 := by grind only
  have : pf.sig.toNat ≥ 0 := by grind only
  simp only [toRatSig, Rat.zero_add, ge_iff_le]
  grind only

/-- Alias for `PackedFloat.nonneg_toRatSig` -/
theorem zero_le_toRatSig (pf : PackedFloat e s) : 0 ≤ pf.toRatSig :=
  nonneg_toRatSig pf

@[grind .]
theorem zero_le_twoNumberRatSig {e s} (pf : PackedFloat e s) :
  0 ≤ pf.toRatSig := by
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
    Rat.pow_nonneg]
  have : (0 + pf.sig.toNat / 2^s) ≥ 0 := by grind only
  have : pf.sig.toNat / 2^s ≥ 0 := by grind only
  have : pf.sig.toNat ≥ 0 := by grind only
  simp only [toRatSig, Rat.zero_add, ge_iff_le]
  grind only

theorem toRatSig_eq_of_isNorm {e s} {pf : PackedFloat e s} (hnorm : pf.isNorm) :
  pf.toRatSig = 1 + pf.sig.toNat / 2 ^ s := by
  simp [toRatSig, hnorm]

theorem toRatSig_eq_of_not_isNorm {e s} {pf : PackedFloat e s} (hnorm : ¬ pf.isNorm) :
  pf.toRatSig = pf.sig.toNat / 2 ^ s := by
  simp [toRatSig, hnorm]

@[grind ., simp]
theorem toRatSig_lt_one_of_not_isNorm {e s} (pf : PackedFloat e s) (hnorm : ¬ pf.isNorm) :
  pf.toRatSig < 1 := by
  simp [toRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : pf.sig.toNat < 2^s := by grind
  apply Rat.div_lt_iff .. |>.mpr
  · simp
    norm_cast
  · grind => instantiate only [Rat.pow_pos]

@[simp]
theorem toRatSig_lt_two_of_not_isNorm {e s} (pf : PackedFloat e s) (hnorm : pf.isNorm):
  pf.toRatSig < 2 := by
  simp [toRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : pf.sig.toNat < 2^s := by grind
  suffices (pf.sig.toNat : Rat) / (2 : Rat) ^ s < 1 from by
    grind
  apply Rat.div_lt_iff .. |>.mpr
  · simp
    norm_cast
  · grind => instantiate only [Rat.pow_pos]

@[grind! .]
theorem toRatSig_lt_ite {e s} (pf : PackedFloat e s) :
  pf.toRatSig < 1 + pf.isNorm.toNat := by
  by_cases hnorm : pf.isNorm
  · simp [hnorm]; grind [toRatSig_lt_two_of_not_isNorm pf hnorm]
  · simp [hnorm];

@[grind .]
theorem toRatSig_lt_two {e s} (pf : PackedFloat e s) :
  pf.toRatSig < 2 := by
  have := toRatSig_lt_ite pf
  by_cases hnorm : pf.isNorm
  · grind [toRatSig_lt_two_of_not_isNorm pf hnorm]
  · grind [toRatSig_lt_one_of_not_isNorm pf hnorm]

/--
Amongst packed floats
the rational exponent is monotone in the exponent if the numbers are
both normal or both subnormal.
-/
theorem toRatExp_le_toRatExp_of_ex_le_ex_of_isNorm (x y : PackedFloat e s)
  (hle : x.ex ≤ y.ex) (hnorm : x.isNorm = y.isNorm) :
  x.toRatExp ≤ y.toRatExp := by
  rw [toRatExp, toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    have : x.ex.toNat ≤ y.ex.toNat := by grind only [BitVec.le_def]
    grind only
  · simp [hnorm, show ¬ y.isNorm by grind only]

/--
Amongst packed floatswith the same normality, the rational exponent is strictly monotone in the exponent.
-/
theorem toRatExp_lt_toRatExp_of_ex_lt_ex_of_isNorm (x y : PackedFloat e s)
  (hle : x.ex < y.ex) (hnorm : x.isNorm = y.isNorm)
  (hx : x.isNormOrNonzeroSubnorm)
  (hy : y.isNormOrNonzeroSubnorm):
  x.toRatExp < y.toRatExp := by
  rw [toRatExp, toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    have : x.ex.toNat < y.ex.toNat := by grind only [BitVec.lt_def]
    grind only
  · have := x.exp_eq_of_isNonzeroSubnorm
    simp [this] at hle
    have := y.exp_eq_of_isNonzeroSubnorm
    simp [this] at hle

theorem toRatExp_le_toRatExp (x y : PackedFloat e s)
  -- (hx : x.isNormOrNonzeroSubnorm)
  (hy : y.isNormOrNonzeroSubnorm)
  (hle : x.ex ≤ y.ex) :
  x.toRatExp ≤ y.toRatExp := by
  rw [toRatExp, toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    by_cases hnorm' : y.isNorm
    · simp [hnorm']
      have : x.ex.toNat ≤ y.ex.toNat := by grind only [BitVec.le_def]
      grind only
    · -- 'x' is normal, 'y' is subnormal.
      have hxex := x.ex_ne_zero_if_isNorm
      have hyex := y.exp_eq_of_isNonzeroSubnorm
      simp [hyex] at hle
      simp at hxex
      grind only
  · simp [hnorm]
    by_cases hnorm' : y.isNorm
    · simp [hnorm']
      simp [PackedFloat.isNorm] at hnorm hnorm'
      grind only [ex_ne_zero_if_isNorm, BitVec.eq_zero_iff_toNat_eq, = BitVec.zero_eq, #41d9]
    · simp [hnorm']

@[grind .]
theorem zero_lt_ex_of_isNorm {e s} {pf : PackedFloat e s}
  (hnorm : pf.isNorm) :
    0#_ < pf.ex := by
  simp [isNorm] at hnorm
  rw [BitVec.lt_def]
  simp
  have : pf.ex.toNat = 0 ∨ 0 < pf.ex.toNat  := by grind
  rcases this with (this | hpos)
  · have : pf.ex.toNat ≠ 0 := by grind only [ex_ne_zero_if_isNorm, BitVec.eq_zero_iff_toNat_eq,
    = BitVec.zero_eq]
    grind only
  · grind only

/--
If the packed floats have the same exponent bits,
then the rational exponent they compute is equal.
-/
@[simp]
theorem toRatExp_eq_of_ex_eq (x y : PackedFloat e s) (h : x.ex = y.ex) :
  x.toRatExp = y.toRatExp := by
  simp [toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    by_cases hnorm' : y.isNorm
    · simp [hnorm']
      simp [h]
    · simp [hnorm']
      simp [PackedFloat.isNorm] at hnorm hnorm'
      grind only
  · simp [hnorm]
    intros hynorm
    simp [PackedFloat.isNorm] at hnorm hynorm
    grind only

theorem toRatExp_eq_of_not_isNorm {e s} {pf : PackedFloat e s} (hnorm : ¬ pf.isNorm) :
  pf.toRatExp = -(bias e - 1 : Nat) := by
  simp [toRatExp, hnorm]

theorem toRatExp_eq_of_isNorm {e s} {pf : PackedFloat e s} (hnorm : pf.isNorm) :
  pf.toRatExp = pf.ex.toNat - bias e := by
  simp [toRatExp, hnorm]

@[simp]
theorem toRatExp_neg {pf : PackedFloat e s} :
    (- pf).toRatExp = pf.toRatExp := by
  simp [toRatExp]

@[simp]
theorem toRat_neg {e s} (pf : PackedFloat e s) :
    (-pf).toRat = - pf.toRat := by
  simp [toRat]
  grind only

@[simp]
theorem toRatSig_eq_zero_of_isZero {e s} (pf : PackedFloat e s) (hzero : pf.isZero := by grind) :
  pf.toRatSig = 0 := by
  simp [toRatSig]
  have hnorm : ¬ pf.isNorm := by grind
  simp [hnorm]
  have : pf.sig = 0#s := by grind
  simp only [this, BitVec.toNat_ofNat, Nat.zero_mod, Rat.natCast_ofNat]
  grind

@[grind . ]
theorem sig_ne_zero_of_isNormOrNonzeroSubnorm_of_not_isNorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) (hnorm : ¬ pf.isNorm) :
    pf.sig ≠ 0#s := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at h
  grind

@[simp]
theorem toRatSig_ne_zero_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
  pf.toRatSig ≠ 0 := by
  simp [toRatSig]
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
    have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
      Rat.pow_nonneg]
    simp only [ne_eq]
    grind
  · simp [hnorm]
    have := sig_ne_zero_of_isNormOrNonzeroSubnorm_of_not_isNorm h (hnorm := by grind)
    have : pf.sig.toNat ≠ 0 := by grind
    have : (pf.sig.toNat : Rat) ≠ 0 := by
      grind only [Rat.natCast_eq_zero_iff]
    grind only [Fp.Rat.div_pos, Rat.pow_pos]

@[simp, grind .]
theorem toRatSig_pos_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
  0 < pf.toRatSig := by
  have : pf.toRatSig ≠ 0 := by exact toRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : pf.toRatSig ≥ 0 := by exact zero_le_toRatSig pf
  grind

@[simp, grind =]
theorem toRat_eq_Zero_of_isZero {e s} (pf : PackedFloat e s) (hp : pf.isZero) :
    pf.toRat = 0 := by
  rw [toRat]
  have : pf.toRatSig = 0 := by exact toRatSig_eq_zero_of_isZero pf hp
  grind

@[simp, grind =]
theorem toRatSig_eq_zero_of_isInfinite {e s} (pf : PackedFloat e s) (hinf : pf.isInfinite) :
    pf.toRatSig = 0 := by
  simp [toRatSig]
  have hnorm : ¬ pf.isNorm := by grind [isNorm, isInfinite]
  simp [hnorm]
  have : pf.sig = 0#s := by grind [isInfinite]
  simp only [this, BitVec.toNat_ofNat, Nat.zero_mod, Rat.natCast_ofNat]
  grind

@[simp, grind =]
theorem toRat_eq_zero_of_isInfinite {e s} (pf : PackedFloat e s) (hinf : pf.isInfinite) :
    pf.toRat = 0 := by
  rw [toRat]
  have : pf.toRatSig = 0 := toRatSig_eq_zero_of_isInfinite pf hinf
  grind

@[simp, grind =]
theorem toRat_getZero {e s} (h : 0 < e) (sign : Bool) :
    (PackedFloat.getZero e s sign).toRat = 0 := by
  apply toRat_eq_Zero_of_isZero
  simp [h]


theorem toRat_ne_zero {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
    pf.toRat ≠ 0 := by
  simp [toRat]
  have : pf.sign.toSign ≠ 0 := by grind only [Bool.toSign, #26b7]
  have : pf.toRatSig ≠ 0 := by exact toRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : (2 : Rat) ^ (pf.toRatExp) > 0 := by grind only [Fp.Rat.two_pow_pos]
  grind only

@[simp, grind →, grind =]
theorem sign_iff_toRat_neg {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
    pf.sign = decide (pf.toRat < 0) := by
  rw  [toRat]
  have : pf.toRatSig ≠ 0 := by
    exact toRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : 0 ≤ pf.toRatSig := by exact zero_le_toRatSig pf
  have : (2 : Rat) ^ pf.toRatExp > 0 := by grind only [Fp.Rat.two_pow_pos]
  by_cases hsign : pf.sign <;> simp [hsign] <;> grind

@[simp, grind =, grind =_]
theorem isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s}
    (h : pf.isNormOrNonzeroSubnorm) (he : 0 < e) :
    pf.isZero ↔ pf.toRat = 0 := by
  constructor
  · grind only [→ not_isZero_of_isNormOrSubnorm]
  · intros hzero
    simp [isZero]
    simp [show ¬ e = 0 by grind]
    simp [toRat] at hzero
    have hsign_ne_zero : pf.sign.toSign ≠ (0 : Rat) := by
      simp
    have hcontra : pf.toRatSig * 2 ^ pf.toRatExp = 0 := by
      grind
    have : (2 : Rat) ^ pf.toRatExp ≠ 0 := by
      grind only [Rat.two_pow_ne_zero]
    grind only [toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]


@[simp, grind =]
theorem toExtRat'_eq_toRat_of {pf : PackedFloat e s} (hp : pf.isNormOrNonzeroSubnorm := by grind) :
    pf.toExtRat' =
        .Number pf.toRat := by
  have hnan : pf.isNaN = false := by
    grind [isNaN, isNormOrNonzeroSubnorm]
  have hinf : pf.isInfinite = false := by
    grind [isInfinite, isNormOrNonzeroSubnorm]
  have hzero : pf.isZero = false := by
    grind [isZero, isNormOrNonzeroSubnorm]
  simp [toExtRat', hnan, hinf, toRat]


@[simp, grind =]
theorem toExtRat'_eq_zero_of_isZero (pf : PackedFloat e s) (hp : pf.isZero) :
    pf.toExtRat' = .Number 0 := by
  have hnan : pf.isNaN = false := by
    grind [isNaN, isZero]
  have hinf : pf.isInfinite = false := by
    grind [isInfinite, isZero]
  simp only [toExtRat', hnan, hinf, cond_false, ExtRat.Number.injEq]
  grind

@[simp, grind =]
theorem toExtRat'_eq_NaN_of_isNaN (pf : PackedFloat e s) (hp : pf.isNaN) :
    pf.toExtRat' = .NaN := by
  simp [toExtRat', hp]

@[simp, grind =]
theorem toExtRat'_eq_NaN_iff_isNaN (pf : PackedFloat e s) : pf.toExtRat' = .NaN ↔ pf.isNaN := by
  constructor
  · intros h
    simp [toExtRat'] at h
    grind only [#47ab]
  · intros h
    simp [toExtRat', h]

@[simp, grind =]
theorem toExtRat'_eq_Infinity_of_isInfinite (pf : PackedFloat e s) (hp : pf.isInfinite) :
    pf.toExtRat' = .Infinity pf.sign := by
  rw [toExtRat', hp]
  grind [not_isNaN_of_isInfinite]


@[simp, grind! .] -- aggressive?
theorem toExtRat'_getInfinity {sign : Bool} (hs : 0 < s := by grind) :
    (PackedFloat.getInfinity e s sign).toExtRat' = .Infinity sign := by
  have : (PackedFloat.getInfinity e s sign).isInfinite = true := by
    grind
  simp [hs]

@[simp, grind! .]
theorem isNaN_mkNaN : (PackedFloat.getNaN e s).isNaN = true := by
  simp [getNaN, isNaN]
  grind

@[simp]
theorem toExtRat'_mkNaN :
    (PackedFloat.getNaN e s).toExtRat' = .NaN := by
  rw [toExtRat']
  simp

@[simp, grind! .]
theorem toExtRat'_getZero (sign : Bool) (he : 0 < e := by grind) :
    (PackedFloat.getZero e s sign).toExtRat' = .Number 0 := by
  rw [toExtRat']
  simp [show ¬ e = 0 by grind]
  simp [he]

/--
x is infinite iff it is equal to the infinity value with the same sign.
TODO: mark this 'simp'.
-/
@[grind .]
theorem eq_getInfinity_iff_isInfinity (hs : 0 < s)
    {x : PackedFloat e s} :
    (x.isInfinite) ↔ x = .getInfinity e s x.sign := by
  simp [getInfinity, isInfinite]
  grind [PackedFloat]


@[simp, grind .]
theorem PackedFloat.sign_eq_of_toRat_eq {x y : PackedFloat e s}
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (heq : x.toRat = y.toRat) : x.sign = y.sign := by
  by_cases hxsign : x.sign <;> grind only [→ sign_iff_toRat_neg]

theorem mul_two_pow_inj (base0 base1 : Rat)
    (pow0 pow1 : Int) (h : base0 * (2 : Rat) ^ pow0 = base1 * (2 : Rat) ^ pow1)
    (hLtBase0 : 1 ≤ base0)
    (hLtBase1 : 1 ≤ base1)
    (hBase0Lt : base0 < 2)
    (hBase1Lt : base1 < 2) :
    base0 = base1 ∧ pow0 = pow1 := by
  by_cases hle : pow0 ≤ pow1
  · apply mul_two_pow_inj_aux <;> grind only
  · have hgt : pow1 < pow0 := by grind only
    have := mul_two_pow_inj_aux base1 base0 pow1 pow0 h.symm hLtBase1 hLtBase0 hBase1Lt (by grind only)
    grind only

/--
Show that the exponents are equal
if their interpretation as Rats are equal.
-/
theorem exp_eq_of_toRatExp_eq
  (x y : PackedFloat e s)
  (h : x.toRatExp = y.toRatExp)
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (hnorm : x.isNorm = y.isNorm) : x.ex = y.ex := by
simp [toRatExp] at h
by_cases hxnorm : x.isNorm
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : (x.ex.toNat : Int) = (y.ex.toNat : Int) := by grind only
  simp only [Int.natCast_inj] at this
  apply BitVec.eq_of_toNat_eq
  grind
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : x.isNonzeroSubnorm := by grind
  simp [this]
  have : y.isNonzeroSubnorm := by grind
  simp [this]

/--
Show that the significands are equal
if their interpretation as Rats are equal.
-/
theorem sig_eq_of_toRatSig_eq_toRatSig
  {x y : PackedFloat e s}
  (h : x.toRatSig = y.toRatSig)
  (hnorm : x.isNorm = y.isNorm) : x.sig = y.sig := by
simp [toRatSig] at h
by_cases hxnorm : x.isNorm
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : (2 ^ s : Rat) ≠ 0 := by
    apply Rat.ne_zero_of_zero_lt
    grind only [Rat.pow_pos]
  have : (x.sig.toNat : Rat) = (y.sig.toNat : Rat) := by
   grind only
  simp only [Rat.natCast_inj] at this
  apply BitVec.eq_of_toNat_eq
  grind
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : (2 ^ s : Rat) ≠ 0 := by grind
  have : (x.sig.toNat : Rat) = (y.sig.toNat : Rat) := by
    grind only
  simp only [Rat.natCast_inj] at this
  apply BitVec.eq_of_toNat_eq
  grind




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
