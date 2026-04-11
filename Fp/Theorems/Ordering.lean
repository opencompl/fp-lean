import Fp.Theorems.Packing
import Fp.Utils
import Fp.Theorems.Negation

namespace PackedFloat

@[simp]
private theorem Rat.neg_one_mul_le_neg_one_mul_iff {a b : Rat} : -1 * a ≤ -1 * b ↔ b ≤ a := by
  grind

/--
if `a.ex ≤ b.ex`,
then `a.toRatExp ≤ b.toRatExp`..
-/
theorem PackedFloat.toRatExp_le_toRatExp_of_le (a b : PackedFloat e s)
    (hbnan : ¬ b.isNaN)
    (hbinf : ¬ b.isInfinite)
    (hbzero : ¬ b.isZero)
    (hle : a.ex ≤ b.ex)
    : a.toRatExp ≤ b.toRatExp := by
  simp [PackedFloat.toRatExp]
  by_cases ha : a.isNorm
  · simp [ha]
    by_cases hb : b.isNorm
    · simp [hb]
      rw [← BitVec.le_def]
      apply hle
    · simp [hb]
      have haexp := a.ex_ne_zero_if_isNorm
      simp at haexp
      have : b.isNonzeroSubnorm = true := by grind only [=
          isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
        = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
        isNormOrSubnorm_eq_isNorm_or_isSubnorm]
      have := b.exp_eq_of_isNonzeroSubnorm
      rw [this] at hle
      simp at hle
      grind only
  · by_cases hb : b.isNorm
    · simp [ha]
      simp [hb]
      grind
    · simp [hb, ha]

/-
theorem PackedFloat.toRatExp_lt_toRatExp_of_lt (a b : PackedFloat e s)
    (he : 0 < e)
    (hanan : ¬ a.isNaN)
    (hainf : ¬ a.isInfinite)
    (hazero : ¬ a.isZero)
    (hbnan : ¬ b.isNaN)
    (hbinf : ¬ b.isInfinite)
    (hbzero : ¬ b.isZero)
    (hle : a.ex < b.ex)
    : a.toRatExp < b.toRatExp := by
  simp [PackedFloat.toRatExp]
  by_cases ha : a.isNorm
  · simp [ha]
    by_cases hb : b.isNorm
    · simp [hb]
      rw [← BitVec.lt_def]
      apply hle
    · simp [hb]
      have haexp := a.ex_ne_zero_if_isNorm
      simp at haexp
      have : b.isNonzeroSubnorm = true := by grind only [=
          isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
        = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
        isNormOrSubnorm_eq_isNorm_or_isSubnorm]
      have := b.exp_eq_of_isNonzeroSubnorm
      rw [this] at hle
      simp at hle
  · by_cases hb : b.isNorm
    · simp [ha]
      simp [hb]
      have haexp := a.exp_eq_of_isNonzeroSubnorm
      have hbexp := b.ex_ne_zero_if_isNorm
      simp at haexp hbexp
      have : 0 < b.ex.toNat := by exact BitVec.toNat_pos_of_ne_zero hbexp
      have hbias : bias e = 0 ∨ 0 < bias e  := by grind
      rcases hbias with (hbias | hbias)
      · simp [hbias]
        grind
      · rw [show (((bias e - 1) : Nat) : Int) = bias e - 1 by grind]
        rw [Int.neg_sub]
        simp
        sorry
    · simp [hb, ha]
      have := b.exp_eq_of_isNonzeroSubnorm
      have := a.exp_eq_of_isNonzeroSubnorm
      grind only
-/

@[simp]
theorem PackedFloat.toRatExp_eq_toRatExp_of_ex_eq_ex (a b : PackedFloat e s)
    (ha : a.isNormOrNonzeroSubnorm)
    (hb : b.isNormOrNonzeroSubnorm)
    (heq : a.ex = b.ex)
    : a.toRatExp = b.toRatExp := by
  simp [PackedFloat.toRatExp]
  by_cases ha : a.isNorm
  · simp [ha]
    by_cases hb : b.isNorm
    · simp [hb]
      grind only
    · simp [hb]
      have haexp := a.ex_ne_zero_if_isNorm
      have hbexp := b.exp_eq_of_isNonzeroSubnorm
      simp at haexp
      grind only
  · simp [ha]
    intros hb
    have haexp := a.exp_eq_of_isNonzeroSubnorm
    have hbexp := b.exp_eq_of_isNonzeroSubnorm
    rw [hbexp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Int.cast_ofNat_Int, Int.zero_sub, Int.neg_inj]
    grind only [ex_ne_zero_if_isNorm, = BitVec.zero_eq]


/--
Amongst normal numbers, the ordering by `toRatExp` agrees with the ordering by exponent.
-/
theorem PackedFloat.toRatExp_lt_toRatExp_of_lt_of_isNorm (a b : PackedFloat e s)
    (hanorm : a.isNorm)
    (hbnorm : b.isNorm)
    (hle : a.ex < b.ex)
    : a.toRatExp < b.toRatExp := by
  simp [PackedFloat.toRatExp]
  simp [hanorm]
  simp [hbnorm]
  rw [← BitVec.lt_def]
  apply hle

/--
the 'toRatSig' is in the same order as that of the 'sig'
interpreted as a 2s complement unsigned number.
-/
@[simp]
theorem PackedFloat.toRatSig_le_toRatSig_of_le_of_isNorm_eq_isNorm
  (x y : PackedFloat e s)
  (hxy : x.isNorm = y.isNorm)
  (hle : x.sig ≤ y.sig) : x.toRatSig ≤ y.toRatSig := by
  simp [PackedFloat.toRatSig]
  rw [hxy]
  by_cases hynorm : y.isNorm
  · simp [hynorm]
    rw [Rat.div_le_div_self]
    · exact Rat.natCast_le_natCast.mpr hle
    · grind only [Rat.pow_pos]
  · simp [hynorm]
    have : x.sig.toNat ≤ y.sig.toNat :=  BitVec.le_def.mp hle
    apply Rat.div_le_div_self .. |>.mpr
    · norm_cast
    · grind only [Rat.pow_pos]

/--
The exponent of a subnormal number is always less than or equal to the exponent of a normal number.
-/
@[simp, grind .]
theorem PackedFloat.ex_le_ex_of_isNonzeroSubnorm_of_not_isNorm (x y : PackedFloat e s)
    (hxnorm : x.isNonzeroSubnorm)
    (hynorm : y.isNorm) : x.ex ≤ y.ex := by
  have hxexp := x.exp_eq_of_isNonzeroSubnorm
  have := y.ex_ne_zero_if_isNorm
  simp at this
  have : x.ex.toNat = 0 := by grind only [= BitVec.toNat_zero]
  have : y.ex.toNat ≠ 0 := by grind only [BitVec.toNat_inj]
  rw [BitVec.le_def]
  grind

@[grind .]
theorem PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm (x : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hxero : ¬ x.isZero)
    (hxsubnorm : ¬ x.isNonzeroSubnorm) : x.isNorm := by
  grind only [= isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
    = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
    isNormOrSubnorm_eq_isNorm_or_isSubnorm]

/--
The interpretation of the exponent of a subnormal number is always less than or equal to the exponent of a normal number.
-/
@[simp, grind .]
theorem PackedFloat.toRatExp_le_toRatExp_of_isNonzeroSubnorm_of_not_isNorm (x y : PackedFloat e s)
    (hxnorm : ¬ x.isNorm)
    (hynorm : y.isNorm) : x.toRatExp ≤ y.toRatExp := by
  simp [PackedFloat.toRatExp]
  have hxexp := x.toRatExp_eq_of_not_isNorm (by grind only)
  simp [show ¬ x.isNorm by grind]
  simp [show y.isNorm by grind]
  have hyexp := y.toRatExp_eq_of_isNorm (by grind only)
  by_cases hbias : bias e = 0
  · simp [hbias]
  · rw [Int.natCast_sub (by grind only)]
    norm_cast
    rw [Int.neg_sub]
    simp only [Int.sub_le_sub_right_iff, ge_iff_le]
    have := y.ex_ne_zero_if_isNorm -- TODO: rephrase to be in terms of simp-nf
    simp at this
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    have yzero : y.ex.toNat = 0 := by grind only
    have yzero' : y.ex = 0 := by
      rw [← BitVec.toNat_inj]
      simp [yzero]
    grind only



theorem Rat.zpow_succ {q : Rat} (hq : q ≠ 0) {a : Int} : q ^ (a + 1) = q ^ a * q := by
  exact Rat.zpow_add_one hq a

/--
The heart of showing that the ordering by `toRat'`
agrees with packed float ordering, where we show that
if the packed floats are ordered by `(exponent, significand)` (in lex ordering),
then their `toRat'` are ordered by the usual ordering on rationals.
See that this reduction only talks about the nonnegative cases.
Case splitting on signs will handle the general case.

TODO: can we drop `isZero`?
-/
theorem toExtRat'_le_toExtRat'_of_le_of_number
    {e s : Nat}
    (x y : PackedFloat e s)
    (hxzero : ¬x.isZero = true)
    (hyzero : ¬y.isZero = true)
    (hxnan : ¬x.isNaN = true)
    (hynan : ¬y.isNaN = true)
    (hxinf : ¬x.isInfinite = true)
    (hyinf : ¬y.isInfinite = true)
    (hxy' : x.ex.toNat < y.ex.toNat ∨ x.ex = y.ex ∧ x.sig.toNat ≤ y.sig.toNat)
    : x.toRatSig * 2 ^ x.toRatExp ≤ y.toRatSig * 2 ^ y.toRatExp := by
  by_cases hxsubnorm : x.isNonzeroSubnorm
  · -- x subnorm
    have hxexp := x.toRatExp_eq_of_not_isNorm (by grind)
    have hxex := x.exp_eq_of_isNonzeroSubnorm
    by_cases hysubnorm : y.isNonzeroSubnorm
    · -- x subnorm, y subnorm.
      have hyexp := y.toRatExp_eq_of_not_isNorm (by grind)
      have hyex := y.exp_eq_of_isNonzeroSubnorm
      rw [hxexp, hyexp]
      rw [Rat.mul_le_mul_cancel_right_of_lt]
      simp [hxex, hyex] at hxy'
      · apply PackedFloat.toRatSig_le_toRatSig_of_le_of_isNorm_eq_isNorm
        · grind
        · exact BitVec.le_def.mpr hxy'
      · grind only [Fp.Rat.two_pow_pos]
    · -- x subnorm, y norm.
      -- compare exponents and show that one is dominated by the other.
      have hexpLe : x.toRatExp ≤ y.toRatExp := by
        apply PackedFloat.toRatExp_le_toRatExp_of_isNonzeroSubnorm_of_not_isNorm
        · grind only [→ not_isNorm_of_isSubnorm]
        · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
      have : (2 : Rat) ^ x.toRatExp ≤ 2 ^ y.toRatExp := by
        grind only [Rat.two_pow_le_two_pow_of_le]
      apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
      · apply Rat.le_trans (b := 1)
        · grind only [Rat.le_of_lt, → not_isNorm_of_isSubnorm, toRatSig_lt_one_of_not_isNorm]
        · grind only [= isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
          one_le_toRatSig_of_isNorm, = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
          isNormOrSubnorm_eq_isNorm_or_isSubnorm]
      · grind only
      · grind only [zero_le_twoNumberRatSig]
      · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · -- x norml.
    by_cases hysubnorm : y.isNonzeroSubnorm
    · -- x normal, y subnormale, x ≤ y. impossible, since x is normal and x ≤ y.
      have := y.exp_eq_of_isNonzeroSubnorm
      rw [this] at hxy'
      simp at hxy'
      have : x.ex ≠ 0#e := by
        have := x.ex_ne_zero_if_isNorm
        simp at this
        grind only
      grind only
    · -- x normal, y normal, x ≤ y
      rcases hxy' with (hlexp | hleSig)
      · -- x.exp < y.exp,
        have := x.toRatSig_lt_two
        have := x.one_le_toRatSig_of_isNorm (by grind)
        have := y.toRatSig_lt_two
        have := y.one_le_toRatSig_of_isNorm (by grind)
        apply Rat.le_trans (b := 2 * ((2 : Rat) ^ x.toRatExp))
        · apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
          · grind only
          · grind only
          · grind only
          · grind only [Fp.Rat.two_pow_pos]
        · rw [show y.toRatExp = (y.toRatExp - 1) + 1 by grind only]
          rw [Rat.zpow_succ (by grind only)]
          apply Rat.le_trans (b := (y.toRatSig * 2)* 2 ^ (y.toRatExp - 1))
          · apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
            · grind only
            · apply Rat.two_pow_le_two_pow_of_le
              suffices x.toRatExp < y.toRatExp from by grind only
              apply PackedFloat.toRatExp_lt_toRatExp_of_lt_of_isNorm
              · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
              · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
              · grind only [BitVec.lt_def]
              -- apply PackedFloat.toRatExp_le_toRatExp_of_le
            · grind only [zero_le_twoNumberRatSig]
            · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
          · grind only
      · -- x.exp = y.exp
        obtain ⟨hexpEq, hsigLe⟩ := hleSig
        rw [x.toRatExp_eq_of_ex_eq (h := hexpEq)]
        apply Rat.mul_le_mul_cancel_right_of_lt .. |>.mpr
        · apply PackedFloat.toRatSig_le_toRatSig_of_le_of_isNorm_eq_isNorm
          · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          · rw [BitVec.le_def]; grind only
        · grind only [Fp.Rat.two_pow_pos]

/--
info: 'PackedFloat.toExtRat'_le_toExtRat'_of_le_of_number' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms toExtRat'_le_toExtRat'_of_le_of_number

/--
The `x.isInfinite` branch of `toExtRat'_le_toExtRat'_of_le`:
if `x` is infinite and `x ≤ y`, then `x.toExtRat' ≤ y.toExtRat'`.
-/
theorem toExtRat'_le_toExtRat'_of_le_of_isInfinite (_he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : x.isInfinite)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  rw [PackedFloat.toExtRat']
  have hxy' := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hxy'
  simp [hxnan, hynan] at hxy'
  simp [hxnan] at ⊢
  simp [hxinf]
  by_cases hxsign : x.sign
  · simp [hxsign, hynan]
  · simp at hxsign
    simp [hxsign]
    have := PackedFloat.eq_getInfinity_iff_isInfinity hs |>.mp hxinf
    simp [hxsign] at this
    subst this
    simp [hs] at hxy
    subst hxy
    simp [hs]

/--
The `y.isInfinite` subcase of `toExtRat'_le_toExtRat'_of_le_of_not_isInfinite`:
if `x` is not infinite, `y` is infinite, and `x ≤ y`, then `x.toExtRat' ≤ y.toExtRat'`.
-/
theorem toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_isInfinite
    (_he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (_hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite) (hyinf : y.isInfinite)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  rw [PackedFloat.toExtRat']
  have hxy' := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hxy'
  simp [hxnan, hynan] at hxy'
  simp [hxnan] at ⊢
  simp [hxinf]
  rw [PackedFloat.toExtRat']
  simp [hyinf, hynan]
  by_cases hysign : y.sign
  · simp [hysign]
    have := PackedFloat.eq_getInfinity_iff_isInfinity hs |>.mp hyinf
    simp [hysign] at this
    subst this
    simp [hs] at hxy
    grind only
  · simp [hysign]

set_option maxHeartbeats 9999999 in
/--
The `x.sign` subcase of `toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite`:
neither `x` nor `y` infinite, `x` negative, and `x ≤ y`, then `x.toExtRat' ≤ y.toExtRat'`.
-/
theorem toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite_of_sign
    (_he : 0 < e) (_hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite) (hyinf : ¬ y.isInfinite)
    (hxsign : x.sign)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  rw [PackedFloat.toExtRat']
  have hxy' := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hxy'
  simp [hxnan, hynan] at hxy'
  simp [hxnan] at ⊢
  simp [hxinf]
  rw [PackedFloat.toExtRat']
  simp [hyinf, hynan]
  rw [PackedFloat.toRat, PackedFloat.toRat]
  simp [hxsign]
  -- x -ve
  by_cases hysign : y.sign
  · -- x -ve, y -ve
    simp [hysign]
    simp [hxsign, hysign] at hxy'
    rw [Rat.mul_assoc, Rat.mul_assoc]
    simp only [Rat.neg_one_mul_le_neg_one_mul_iff]
    apply toExtRat'_le_toExtRat'_of_le_of_number <;> grind only
  · -- x -ve, y +ve
    simp [hysign]
    simp [hxsign, hysign] at hxy'
    have := x.zero_le_twoNumberRatSig
    have := y.zero_le_twoNumberRatSig
    have := Rat.zpow_nonneg (a := 2) (h := by decide) (n := y.toRatExp)
    have := Rat.zpow_nonneg (a := 2) (h := by decide) (n := x.toRatExp)
    simp only [ge_iff_le]
    apply Rat.le_trans (b := 0)
    · grind =>
      instantiate only [Rat.le_of_lt, toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
      instantiate only [Fp.Rat.two_pow_pos, → Rat.mul_pos,
        = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero]
    · grind => instantiate only [Rat.mul_nonneg]
    -- grind?

/--
The `¬ x.sign` subcase of `toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite`:
neither `x` nor `y` infinite, `x` non-negative, and `x ≤ y`, then `x.toExtRat' ≤ y.toExtRat'`.
-/
theorem toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite_of_not_sign
    (_he : 0 < e) (_hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite) (hyinf : ¬ y.isInfinite)
    (hxsign : ¬ x.sign)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  rw [PackedFloat.toExtRat']
  have hxy' := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hxy'
  simp [hxnan, hynan] at hxy'
  simp [hxnan] at ⊢
  simp [hxinf]
  rw [PackedFloat.toExtRat']
  simp [hyinf, hynan]
  rw [PackedFloat.toRat, PackedFloat.toRat]
  -- x +ve
  simp at hxsign
  simp [hxsign]
  by_cases hysign : y.sign
  · -- x+ve, y -ve
    simp [hxsign, hysign] at hxy'
  · -- x+ve, y +ve
    simp at hysign
    simp [hysign]
    simp [hxsign, hysign] at hxy'
    apply toExtRat'_le_toExtRat'_of_le_of_number
    · grind only
    · assumption
    · assumption
    · assumption
    · grind only
    · grind only
    · grind only

/--
The `¬ y.isInfinite` subcase of `toExtRat'_le_toExtRat'_of_le_of_not_isInfinite`:
if neither `x` nor `y` is infinite and `x ≤ y`, then `x.toExtRat' ≤ y.toExtRat'`.
-/
theorem toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite
    (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite) (hyinf : ¬ y.isInfinite)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  by_cases hxsign : x.sign
  · exact toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite_of_sign
      he hs x y hxzero hyzero hxnan hynan hxinf hyinf hxsign hxy
  · exact toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite_of_not_sign
      he hs x y hxzero hyzero hxnan hynan hxinf hyinf hxsign hxy

/--
The `¬ x.isInfinite` branch of `toExtRat'_le_toExtRat'_of_le`:
if `x` is not infinite and `x ≤ y`, then `x.toExtRat' ≤ y.toExtRat'`.
-/
theorem toExtRat'_le_toExtRat'_of_le_of_not_isInfinite (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  by_cases hyinf : y.isInfinite
  · exact toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_isInfinite
      he hs x y hxzero hyzero hxnan hynan hxinf hyinf hxy
  · exact toExtRat'_le_toExtRat'_of_le_of_not_isInfinite_of_not_isInfinite
      he hs x y hxzero hyzero hxnan hynan hxinf hyinf hxy

/--
TODO: split into separate proofs based on
 - nan
 - signs.
The packed float '≤' relationship captures ordering by `toRat'`.
-/
@[simp]
theorem toExtRat'_le_toExtRat'_of_le (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  by_cases hxinf : x.isInfinite
  · exact toExtRat'_le_toExtRat'_of_le_of_isInfinite he hs x y hxzero hyzero hxnan hynan hxinf hxy
  · exact toExtRat'_le_toExtRat'_of_le_of_not_isInfinite he hs x y hxzero hyzero hxnan hynan hxinf hxy

/--
Two packed floats that are ordered by `≤` are ordered by `toRat`, if they are numbers.
TODO: can we drop `isZero`?
-/
@[simp]
theorem toRat_le_toRat_of_le (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero)
    (hyzero : ¬ y.isZero)
    (hxnan : ¬ x.isNaN)
    (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hyinf : ¬ y.isInfinite)
    (hxy : x ≤ y) : x.toRat ≤ y.toRat := by
  have := toExtRat'_le_toExtRat'_of_le he hs x y hxzero hyzero hxnan hynan hxy
  simp [PackedFloat.toExtRat', hxnan, hxinf, hynan, hyinf] at this
  exact this



@[simp]
theorem PackedFloat.one_le_ex_of_isNorm (x : PackedFloat e s) (hxnorm : x.isNorm) (he : 0 < e) :
   1#e ≤ x.ex := by
  have hxexp := x.ex_ne_zero_if_isNorm
  simp at hxexp
  have : x.ex.toNat ≠ 0 := by grind only [BitVec.toNat_pos_of_ne_zero hxexp]
  rw [BitVec.le_def]
  simp [he]
  grind only

/--
exponents of normal numbers are ordered by the packed float ordering, amongst
nonnegative numbers.
-/
theorem Packedfloat.ex_le_ex_of_le_of_nonneg (x y : PackedFloat e s)
  (_hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (hxsign : x.sign = false) (hysign : y.sign = false)
  (hle : x ≤ y) : x.ex ≤ y.ex := by
  rw [← PackedFloat.le_def, PackedFloat.le] at hle
  simp at hle
  simp [show ¬ x.isNaN by grind,
        show ¬ y.isNaN by grind, hxsign, hysign] at hle
  have : x.ex.toNat ≤ y.ex.toNat := by grind only [BitVec.le_def]
  rw [BitVec.le_def]
  exact this


/--
amongst nonnegative numbers,
normal numbers are always greater than subnormal numbers,
-/
theorem not_le_of_isNorm_of_isNonzeroSubnorm_of_nonneg
    (x y : PackedFloat e s)
    (hxsign : x.sign = false)
    (hysign : y.sign = false)
    (hxnorm : x.isNorm)
    (hynonzerosubnorm : y.isNonzeroSubnorm) : ¬ x ≤ y := by
  intros hcontra
  have hxexp := x.ex_ne_zero_if_isNorm
  have hyexp := y.exp_eq_of_isNonzeroSubnorm
  simp only [BitVec.zero_eq, bne_iff_ne, ne_eq] at hxexp hyexp
  have hxnonzero : x.ex.toNat ≠ 0 := by grind only [BitVec.toNat_pos_of_ne_zero hxexp]
  have hyzero : y.ex.toNat = 0 := by grind only [BitVec.toNat_zero]
  have : x.ex ≥ y.ex := by
    simp
    rw [BitVec.le_def]
    grind only
  have : x.ex ≤ y.ex := by
    apply Packedfloat.ex_le_ex_of_le_of_nonneg
    · grind only [→ isNormOrSubnorm_of_isNorm]
    · grind only [→ isNormOrSubnorm_of_isSubnorm]
    · grind only
    · grind only
    · grind only
  have : x.ex = y.ex := by grind only
  grind only


/--
We can show that the significands of two packed floats are ordered by the packed float ordering,
amongst those with the same sign and exponent, and that are not NaN, and not infinite.
-/
theorem PackedFloat.sig_lt_sig_of_lt_of_of_exp_eq_exp_of_sign_eq_false
  (x y : PackedFloat e s)
  (hxy : x < y)
  (hxnan : ¬ x.isNaN)
  (hynan : ¬ y.isNaN)
  (hexpEq : x.ex = y.ex)
  (hxsign : x.sign = false)
  (hysign : y.sign = false) : x.sig < y.sig := by
  rw [← PackedFloat.lt_def, PackedFloat.lt] at hxy
  obtain ⟨hle, hne⟩ := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hle
  simp at hle
  simp [hxnan, hynan, hxsign, hysign] at hle
  rcases hle with (hleExp | hleSig)
  · have : x.ex = y.ex := by grind only [← BitVec.le_def]
    rw [this] at hexpEq
    grind only
  · have : x.sig.toNat ≤ y.sig.toNat := by grind only
    have : x.sig.toNat ≠ y.sig.toNat := by
      intros hcontra
      apply hne
      ext
      · grind only
      · grind only
      · grind only [BitVec.toNat_inj]
    apply BitVec.lt_of_le_ne
    · grind only [BitVec.le_def]
    · grind only



/--
Packed floats are less than each other if the tuple (exponent, significand)
is lex ordered.
-/
theorem le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg (a b : PackedFloat e s)
  (hasign : a.sign = false) (hbsign : b.sign = false) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  a ≤ b ↔ a.ex.toNat < b.ex.toNat ∨ (a.ex.toNat = b.ex.toNat ∧ a.sig.toNat ≤ b.sig.toNat) := by
  rw [← PackedFloat.le_def]
  simp [PackedFloat.le, hasign, hbsign, hanan, hbnan]
  grind only [BitVec.toNat_inj, #c695bb6e572d0f9f]

/--
Packed floats are less than each other if the tuple (exponent, significand)
is lex ordered, amongst negative numbers.
-/
theorem le_of_ex_le_ex_or_sig_le_sig_of_neg_of_neg (a b : PackedFloat e s)
  (hasign : a.sign = true) (hbsign : b.sign = true) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  a ≤ b ↔ b.ex.toNat < a.ex.toNat ∨ (b.ex.toNat = a.ex.toNat ∧ b.sig.toNat ≤ a.sig.toNat) := by
  rw [← PackedFloat.le_def]
  simp [PackedFloat.le, hasign, hbsign, hanan, hbnan]
  grind only [BitVec.toNat_inj, #8f52c9ba759470ab]

@[simp, grind .]
theorem le_of_nonneg_of_neg (a b : PackedFloat e s)
  (hasign : a.sign = true) (hbsign : b.sign = false) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  a ≤ b := by
  rw [← PackedFloat.le_def]
  simp [PackedFloat.le, hasign, hbsign, hanan, hbnan]

@[simp, grind .]
theorem not_le_of_neg_of_nonneg (a b : PackedFloat e s)
  (hasign : a.sign = false) (hbsign : b.sign = true) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  ¬ a ≤ b := by
  rw [← PackedFloat.le_def]
  simp [PackedFloat.le, hasign, hbsign, hanan, hbnan]

theorem lt_of_ex_lt_ex_or_sig_lt_sig_of_nonneg_of_nonneg (a b : PackedFloat e s)
  (hasign : a.sign = false) (hbsign : b.sign = false) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  a < b ↔ a.ex.toNat < b.ex.toNat ∨ (a.ex.toNat = b.ex.toNat ∧ a.sig.toNat < b.sig.toNat) := by
  rw [← PackedFloat.lt_def]
  simp [PackedFloat.lt, hasign, hbsign, hanan, hbnan]
  by_cases hex : a.ex.toNat < b.ex.toNat
  · simp [hex]
    intros hcontra
    subst hcontra
    grind only
  · simp [hex]
    by_cases hex' : a.ex = b.ex
    · simp [hex']
      by_cases hsig : a.sig.toNat < b.sig.toNat
      · simp [hsig]
        grind only
      · simp [hsig]
        by_cases hsig' : a.sig = b.sig
        · simp [hsig']
          ext <;> grind only
        · intros hsig
          grind only [BitVec.toNat_inj]
    · simp [show a.ex.toNat ≠ b.ex.toNat by grind only [BitVec.toNat_inj]]

theorem PackedFloat.lt_of_ex_lt_ex_or_sig_lt_sig_of_neg_of_neg (a b : PackedFloat e s)
  (hasign : a.sign = true) (hbsign : b.sign = true) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  a < b ↔ b.ex.toNat < a.ex.toNat ∨ (b.ex.toNat = a.ex.toNat ∧ b.sig.toNat < a.sig.toNat) := by
  rw [← PackedFloat.lt_def]
  simp [PackedFloat.lt, hasign, hbsign, hanan, hbnan]
  by_cases hex : b.ex.toNat < a.ex.toNat
  · simp [hex]
    intros hcontra
    subst hcontra
    grind only
  · simp only [hex, false_or]
    by_cases hex' : a.ex = b.ex
    · simp only [hex', true_and]
      by_cases hsig : b.sig.toNat < a.sig.toNat
      · simp only [hsig, iff_true]
        grind only
      · simp only [hsig, iff_false]
        by_cases hsig' : a.sig = b.sig
        · simp only [hsig', Nat.le_refl, true_and, Decidable.not_not]
          ext <;> grind only
        · intros hsig
          grind only [BitVec.toNat_inj]
    · simp only [show a.ex.toNat ≠ b.ex.toNat by grind only [BitVec.toNat_inj], false_and,
      false_iff, not_and, Nat.not_lt]
      intros hex
      have : a.ex = b.ex := by grind only [BitVec.toNat_inj]
      grind only

@[simp, grind . ]
theorem PackedFloat.lt_of_neg_of_nonneg (a b : PackedFloat e s)
  (hasign : a.sign = true)
  (hbsign : b.sign = false) (hanan : ¬ a.isNaN) (hbnan : ¬ b.isNaN) :
  a < b ↔ (a ≠ b) := by
  rw [← PackedFloat.lt_def]
  simp [PackedFloat.lt, hasign, hbsign, hanan, hbnan]

@[simp, grind .]
theorem PackedFloat.not_lt_of_nonneg_of_neg (a b : PackedFloat e s)
  (hasign : a.sign = false)
  (hbsign : b.sign = true) (hanan : ¬ a.isNaN) :
  ¬ a < b := by
  rw [← PackedFloat.lt_def]
  simp [PackedFloat.lt, hasign, hbsign, hanan]

/-
This shows that the packed floats packed floats are always at least a distance
of 2^-e. This gives us the discreteness of the ordering
that lets us define 'lower' and 'upper',
and show that 'lower' and 'upper' are always some distance apart.

-- x < y => x + 1 ≤ y
-/
theorem toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxsign : x.sign = false)
    (hysign : y.sign = false)
    (hxzero : ¬ x.isZero)
    (hyzero : ¬ y.isZero)
    (hxnan : ¬ x.isNaN)
    (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hyinf : ¬ y.isInfinite)
    (hlt : x < y) :
    x.toRat + (2 : Rat)^(-(s : Int)) * 2 ^ x.toRatExp ≤ y.toRat := by
  have hxle := PackedFloat.le_of_lt hlt
  by_cases hx : x.isNorm
  · -- x norm
    by_cases hy : y.isNorm
    · -- xnorm, y norm, x ≤ y
      simp [PackedFloat.toRat, PackedFloat.toRat, hxsign, hysign]
      have hxyrat := PackedFloat.toRat_le_toRat_of_le he hs x y hxzero hyzero hxnan hynan hxinf hyinf (by grind only)
      rw [← PackedFloat.lt_def, PackedFloat.lt] at hlt
      obtain ⟨hle, hne⟩ := hlt
      rw [← PackedFloat.le_def, PackedFloat.le] at hle
      simp [hxsign, hysign, hxnan, hynan] at hle
      rcases hle with (hleExp | hleSig)
      · rw [← Rat.add_mul]
        rw [← Rat.one_div_zpow_eq_zpow_neg]
        simp only [Rat.zpow_natCast, ge_iff_le]
        rw [show y.toRatExp = (y.toRatExp - 1) + 1 by grind only]
        rw [Rat.zpow_succ (by grind only)]
        suffices (x.toRatSig + 1 / 2 ^ s) * 2 ^ x.toRatExp ≤ (2 * y.toRatSig) * (2 ^ (y.toRatExp - 1)) by grind only
        apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
        · have := x.one_le_toRatSig_of_isNorm (by grind)
          have := x.toRatSig_lt_two
          have := y.toRatSig_lt_two
          have := y.one_le_toRatSig_of_isNorm (by grind)
          apply Rat.le_trans (b := 2)
          · have := x.toRatSig_le_two_sub_of_isNorm (by grind)
            grind only
          · suffices 2 * 1 ≤ 2 * y.toRatSig by
              simp
              grind only
            apply Rat.mul_le_mul_of_nonneg_left
            · grind only
            · grind only
        · apply Rat.two_pow_le_two_pow_of_le
          suffices x.toRatExp < y.toRatExp from by grind only
          apply PackedFloat.toRatExp_lt_toRatExp_of_lt_of_isNorm
          · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          · grind only [BitVec.lt_def]
          -- apply PackedFloat.toRatExp_le_toRatExp_of_le
        · have := x.nonneg_toRatSig
          have : 0 ≤ (1 : Rat) / 2 ^ s := by
            grind only [Fp.Rat.inv_nonneg, Rat.pow_nonneg]
          grind only
        · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
      · -- exp equal
        obtain ⟨hexpEq, hleSig'⟩ := hleSig
        have : x.toRatExp = y.toRatExp := by
          grind only [x.toRatExp_eq_of_ex_eq]
        rw [this]
        have hleSig'' : x.sig ≤ y.sig := by
            grind only [BitVec.le_def]
        have hsigNe : x.sig ≠ y.sig := by grind only [=> not_isNaN_iff_ex_ne_or_sig_ne,
          le_antisymm_of_ne_NaN, le_eq_of_sign_eq_false_of_sign_eq_false]
        have hsigLt : x.sig < y.sig := by grind only
        suffices (x.toRatSig + 1 / 2 ^ s) * 2 ^  y.toRatExp ≤ y.toRatSig * 2 ^ y.toRatExp by
          rw [Rat.zpow_neg_natCast_eq_one_div_zpow]
          grind only
        apply Rat.mul_le_mul_cancel_right_of_lt .. |>.mpr
        · -- ⊢  x.toRatSig + 2 ^ -s ≤ y.toRatSig
          apply PackedFloat.toRatSig_add_le_toRatSig_of_lt_of_isNorm_eq_isNorm
          · grind only
          · grind only
        · grind only [Fp.Rat.two_pow_pos]
    · -- x norm, y subnorm, x ≤ y:  This is impossible when restricted to nonnegative numbers.
      have : ¬ (x ≤ y) := by
        apply not_le_of_isNorm_of_isNonzeroSubnorm_of_nonneg
        · grind only
        · grind only
        · grind only
        · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
      grind only
  · -- x subnormal
    have : x.isNonzeroSubnorm := by grind
    by_cases hy : y.isNorm
    · -- x subnorm, y norm, x ≤ y: This is trivial when restricted to nonnegative numbers.
      simp only [toRat, hxsign, toSign_false, Rat.intCast_ofNat, Rat.one_mul,
        Rat.zpow_neg_natCast_eq_one_div_zpow, hysign, ge_iff_le]
      rw [← Rat.add_mul]
      have : x.toRatExp ≤ y.toRatExp := by
        exact PackedFloat.toRatExp_le_toRatExp_of_isNonzeroSubnorm_of_not_isNorm x y hx hy
      have : x.toRatSig + 1 / 2 ^ s ≤  1 := by
        apply toRatSig_plus_le_one_of_isNonzeroSubnorm x (by grind only)
      have : 0 ≤ x.toRatSig := by
        exact zero_le_twoNumberRatSig x
      have : 0 ≤ (1 : Rat) / 2 ^ s := by
        grind only [Fp.Rat.inv_nonneg, Rat.pow_nonneg]
      have : 1 ≤ y.toRatSig := by
        apply y.one_le_toRatSig_of_isNorm (by grind only)
      have : x.toRatSig + 1 / 2 ^ s ≤ y.toRatSig := by
        grind only
      apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
      · grind only
      · apply Rat.two_pow_le_two_pow_of_le
        · grind only
      · grind only
      · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]

    · -- x subnorm, y subnorm, x ≤ y: This will be possible by the analysis.
      simp only [toRat, hxsign, toSign_false, Rat.intCast_ofNat, Rat.one_mul,
        Rat.zpow_neg_natCast_eq_one_div_zpow, hysign, ge_iff_le]
      rw [← Rat.add_mul]
      have hxex := x.exp_eq_of_isNonzeroSubnorm
      have hyex := y.exp_eq_of_isNonzeroSubnorm
      have hxexp := x.toRatExp_eq_of_not_isNorm (by grind)
      have hyexp := y.toRatExp_eq_of_not_isNorm (by grind)
      have hxyexp : x.toRatExp = y.toRatExp := by
        simp [hxexp, hyexp]
      simp [hxyexp]
      suffices (x.toRatSig + 1 / 2 ^ s)  ≤ y.toRatSig by
        apply Rat.mul_le_mul_cancel_right_of_lt .. |>.mpr
        · exact this
        · grind only [Fp.Rat.two_pow_pos]
      apply toRatSig_add_le_toRatSig_of_lt_of_isNorm_eq_isNorm
      · grind only
      · apply PackedFloat.sig_lt_sig_of_lt_of_of_exp_eq_exp_of_sign_eq_false
        · grind only
        · grind only
        · grind only
        · grind only
        · grind only
        · grind only

/--
info: 'PackedFloat.toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false


/--
All nonnegative subnormals are less than the max subnormal number.
-/
theorem PackedFloat.le_maxSubnormalNumber_of_isSubnormal_of_nonneg (x : PackedFloat e s)
    (he : 0 < e) (hs : 0 < s)
    (hxsubnorm : x.isNonzeroSubnorm ∨ x.isZero) (hxsign : x.sign = false) :
    x ≤ PackedFloat.maxSubnormalNumber e s false := by
  rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg]
  · simp
    constructor
    · rcases hxsubnorm
      · have := x.exp_eq_of_isNonzeroSubnorm
        grind only [= BitVec.toNat_zero]
      · have := x.ex_eq_of_isZero
        grind only [= BitVec.toNat_zero]
    · grind only [!Nat.two_pow_pos, usr BitVec.isLt]
  · grind only
  · simp
  · grind only [→ not_isNaN_of_isSubnorm, → not_isNaN_of_isZero]
  · simp
    grind only [→ not_isSubnorm_of_isNaN, isNonzeroSubnorm_maxSubnormalNumber_eq_decide]

/--
The max subnormal number is less than or equal to the min normal number
-/
theorem PackedFloat.maxSubnormalNumber_le_minNormalNumber_of_nonneg (he : 1 < e) (hs : 0 < s):
  (PackedFloat.maxSubnormalNumber e s false ≤ PackedFloat.minNormalNumber e s false) := by
  rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg]
  · simp
    grind only [= Nat.mod_eq_of_lt, !Nat.two_pow_pos, usr Nat.div_pow_of_pos, #56f6]
  · simp
  · simp
  · have := isNonzeroSubnorm_maxSubnormalNumber_eq_decide e s false
    grind only [→ not_isNaN_of_isSubnorm]
  · have := isNorm_minNormalNumber_eq_decide e s false
    grind only [→ not_isNaN_of_isNorm]

/--
The exponent of a nonzero number is not all ones,
which is reserved for infinity/NaN.
-/
@[simp]
theorem ex_ne_of_isNormOrNonzeroSubnorm (x : PackedFloat e s)
    (hxnorm : x.isNormOrNonzeroSubnorm) :
    x.ex ≠ BitVec.allOnes e := by
  simp [PackedFloat.isNormOrNonzeroSubnorm] at hxnorm
  grind only

/--
The exponent of a nonzero number is ≤ 2^e-2.
Recall that the full exponent is reserved for infinity/NaN.
-/
@[simp, grind .]
theorem toNat_ex_le_of_isNormOrNonzeroSubnorm (x : PackedFloat e s)
    (hxnorm : x.isNormOrNonzeroSubnorm) :
    x.ex.toNat ≤ 2^e - 2 := by
  have := x.ex_ne_of_isNormOrNonzeroSubnorm hxnorm
  have : x.ex.toNat ≠ 2^e - 1 := by
    intros hcontra
    apply this
    apply BitVec.eq_of_toNat_eq
    simp; grind
  have : x.ex.toNat ≤ 2 ^ e - 1 := by grind only [!Nat.two_pow_pos, usr BitVec.isLt]
  grind only [!Nat.two_pow_pos, usr BitVec.isLt, #11341de38214aa15]

/--
The exponent of a nonzero number is ≤ the exponent of the max normal number.
-/
theorem ex_le_ex_maxNormalNumber_of_isNormOrNonzeroSubnorm
    (x : PackedFloat e s) (he : 1 < e)
    (hxnorm : x.isNormOrNonzeroSubnorm) :
    x.ex ≤ (PackedFloat.maxNormalNumber e s false).ex := by
  simp only [ex_maxNormalNumber, BitVec.ofNat_eq_ofNat]
  rw [BitVec.le_def]
  rw [BitVec.toNat_sub_of_le]
  · simp
    rw [Nat.mod_eq_of_lt]
    · apply toNat_ex_le_of_isNormOrNonzeroSubnorm x hxnorm
    · grind => instantiate approx
  · rw [BitVec.le_def]
    simp
    grind only [!Nat.two_pow_pos, = Nat.mod_eq_of_lt, one_lt_two_pow_iff]

/--
all numbers that are nonnegative and normal are less than or equal to the max normal number.
-/
theorem le_maxNormalNumber_of_isNormOrNonzeroSubnorm_of_nonneg (x : PackedFloat e s)
    (he : 1 < e)
    (hxnorm : x.isNormOrNonzeroSubnorm) (hxsign : x.sign = false) :
    x ≤ PackedFloat.maxNormalNumber e s false := by
  rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg]
  · have : x.ex.toNat ≤ (maxNormalNumber e s false).ex.toNat := by
      apply PackedFloat.ex_le_ex_maxNormalNumber_of_isNormOrNonzeroSubnorm
      · grind only
      · grind only
    by_cases hex : x.ex.toNat = (maxNormalNumber e s false).ex.toNat
    · simp [hex]
      grind only [usr BitVec.isLt, !Nat.two_pow_pos]
    · left
      grind only
  · grind only
  · simp
  · simp; grind only [→ not_isNaN_of_isNormOrSubnorm]
  · simp
    have := isNorm_maxNormalNumber_eq_decide e s false
    grind only [→ not_isNaN_of_isNorm]

/--
only number that is not strictly less than +infinity is NaN
-/
@[simp, grind =]
theorem lt_getInfinity_iff (x : PackedFloat e s) (hs : 0 < s) : x < getInfinity e s false ↔ (¬ x.isNaN ∧ x ≠ getInfinity e s false) := by
  constructor
  · intros h
    by_cases hnan : x.isNaN
    · simp only [hnan, lt_iff_ne_and_isNaN_of_isNaN, isNaN_getInfinity_eq_false,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero_eq,
      ne_eq] at h
      grind only
    · simp only [hnan, Bool.false_eq_true, not_false_eq_true, ne_eq, true_and] at ⊢
      grind only [ne_of_lt]
  · intros h
    apply lt_of_le_of_ne
    · grind only [=> le_getInfinity_false_of_not_isNaN]
    · grind only

/--
zero is less than or equal to all other nonneg numbers.
-/
@[grind .]
theorem getZero_le_of_nonneg {e s : Nat} {sign : Bool}
    (he : 0 < e) (hs : 0 < s)
    (x : PackedFloat e s)
    (hsign : x.sign = false)
    (hnan : ¬ x.isNaN) :
    PackedFloat.getZero e s sign ≤ x := by
  rcases sign with rfl | rfl
  · rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg]
    · simp [he, hs]
      grind only
    · simp [hs]
    · simp [hsign]
    · simp; grind
    · grind only
  · apply le_of_nonneg_of_neg
    · simp
    · simp [hsign]
    · grind only [= isNaN_iff_toExtRat'_eq_NaN, !toExtRat'_getZero]
    · grind only

@[grind .]
theorem getZero_lt_of_nonneg_of_not_isZero {e s : Nat} {sign : Bool}
  (he : 0 < e) (hs : 0 < s)
  (x : PackedFloat e s)
  (hsign : x.sign = false)
  (hnan : ¬ x.isNaN)
  (hzero : ¬ x.isZero) :
  PackedFloat.getZero e s sign < x := by
  apply PackedFloat.lt_of_le_of_ne
  · grind only [getZero_le_of_nonneg]
  · grind only [isZero_getZero]

@[grind .]
theorem isZero_lt_of_nonneg_of_not_isZero {e s : Nat}
  (he : 0 < e) (hs : 0 < s)
  (z x : PackedFloat e s)
  (hz : z.isZero)
  (hsign : x.sign = false)
  (hnan : ¬ x.isNaN)
  (hzero : ¬ x.isZero) :
  z < x := by
  have := z.eq_mkZero_of_isZero hz
  obtain ⟨zsign, rfl⟩ := this
  grind only [getZero_lt_of_nonneg_of_not_isZero]


/--
If one is strictly greater than `maxNormal`, then one equals `+∞`.
-/
theorem eq_getInfinity_of_lt_maxNormalNumber_of_isNaN_of_nonneg (x : PackedFloat e s)
  (he : 1 < e) (hs : 0 < s)
  (hx : ¬ x.isNaN)
  (hxsign : x.sign = false) :
  PackedFloat.maxNormalNumber e s false < x ↔ x = PackedFloat.getInfinity e s false := by
  constructor
  · intros hx
    apply Classical.byContradiction
    intros hcontra
    have : ¬ x.isInfinite := by grind only [eq_getInfinity_iff_isInfinity]
    by_cases hxzero : x.isZero
    · have : x ≤ PackedFloat.maxNormalNumber e s false := by
        apply PackedFloat.le_of_lt
        apply isZero_lt_of_nonneg_of_not_isZero
        · grind only
        · grind only
        · grind only
        · simp
        · grind only [= lt_iff_ne_and_isNaN_of_isNaN]
        · grind only [→ not_isNorm_of_isZero, isNorm_maxNormalNumber_eq_decide]
      grind only [ne_of_lt, = lt_iff_ne_and_isNaN_of_isNaN, le_antisymm_of_ne_NaN, le_of_lt]
    · have : x ≤ PackedFloat.maxNormalNumber e s false := by
        apply le_maxNormalNumber_of_isNormOrNonzeroSubnorm_of_nonneg
        · grind only
        · grind only [= isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero]
        · grind only
      grind only [ne_of_lt, = lt_iff_ne_and_isNaN_of_isNaN, le_antisymm_of_ne_NaN, le_of_lt]
  · intros hx
    subst hx
    grind only [→ not_isNorm_of_isNaN, !isInfinite_getInfinity, = lt_getInfinity_iff,
      → not_isInfinite_of_isNorm, isNorm_maxNormalNumber_eq_decide]

/--
A nonnegative number that is less than the min subnormal number is zero.
-/
theorem isZero_iff_lt_minSubnormalNumber_of_isNaN_of_nonneg (x : PackedFloat e s)
  (he : 1 < e) (hs : 0 < s)
  (hxnan : ¬ x.isNaN)
  (hxsign : x.sign = false) :
  x < PackedFloat.minSubnormalNumber e s false ↔ x.isZero := by
  constructor
  · intros hx
    rw [PackedFloat.lt_of_ex_lt_ex_or_sig_lt_sig_of_nonneg_of_nonneg] at hx
    · simp at hx
      rw [Nat.mod_eq_of_lt] at hx
      · rw [PackedFloat.isZero_iff_ex_eq_zero_and_sig_eq_zero]
        constructor
        · apply BitVec.eq_of_toNat_eq
          simp
          grind only
        · apply BitVec.eq_of_toNat_eq
          simp
          grind
        · grind only
      · simp; grind only
    · grind only
    · grind only [PackedFloat.not_lt_of_nonneg_of_neg]
    · grind only
    · grind only [= lt_iff_ne_and_isNaN_of_isNaN']
  · intros hx
    apply PackedFloat.lt_of_le_of_ne
    · rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg]
      · simp [hx]
      · simp [hxsign]
      · simp
      · grind only
      · grind only [→ not_isSubnorm_of_isNaN, isNonzeroSubnorm_minSubnormalNumber_eq_decide]
    · grind only [→ not_isSubnorm_of_isZero, isNonzeroSubnorm_minSubnormalNumber_eq_decide]


theorem le_of_toRat_le_toRat (x y : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (hy : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hyinf : ¬ y.isInfinite )
    (hxy : x.toRat ≤ y.toRat) : x ≤ y := by
  sorry

/--
For nonnegative numbers, the ordering of the packed floats
is consistent with the ordering of the extended rationals.
-/
theorem le_of_toExtRat'_le_toExtRat'_of_nonneg_of_nonneg
    (hs : 0 < s)
    (x y : PackedFloat e s) (hx : ¬ x.isNaN) (hy : ¬ y.isNaN)
    (hxsign : x.sign = false) (hysign : y.sign = false)
    (hxy : x.toExtRat' ≤ y.toExtRat') : x ≤ y := by
  simp [toExtRat', hx, hy, hxsign, hysign] at hxy
  by_cases hxinf : x.isInfinite
  · simp [hxinf] at hxy
    have hxinf := x.eq_getInfinity_iff_isInfinity hs |>.mp hxinf
    simp only [hxsign] at hxinf
    subst hxinf
    by_cases hyinf : y.isInfinite
    · simp [hyinf] at hxy
      have hyinf := y.eq_getInfinity_iff_isInfinity hs |>.mp hyinf
      simp only [hysign] at hyinf
      subst hyinf
      grind only [le_refl]
    · grind only
  · simp [hxinf] at hxy
    by_cases hyinf : y.isInfinite
    · simp [hyinf] at hxy
      have hyinf := y.eq_getInfinity_iff_isInfinity hs |>.mp hyinf
      simp only [hysign] at hyinf
      subst hyinf
      simp [hs, hx]
    · simp [hyinf] at hxy
      apply le_of_toRat_le_toRat
      · grind only
      · grind only
      · grind only
      · grind only
      · grind only

@[grind .]
theorem not_eq_of_not_le (x y : PackedFloat e s)
  (hnan : x.isNaN = y.isNaN) (hxy : ¬ x ≤ y) : x ≠ y := by
  apply Classical.byContradiction
  intros hcontra
  simp only [ne_eq, Decidable.not_not] at hcontra
  subst hcontra
  grind only [le_refl]

@[grind ., simp]
theorem lt_of_not_le (x y : PackedFloat e s) (hxnan : x.isNaN = y.isNaN)
  (hxy : ¬ x ≤ y) : y < x := by
  have := PackedFloat.le_total_of_isNaN_eq_isNaN x y (by grind only)
  rcases this with hxy | hxy
  · grind only
  · have : ¬ x = y := by grind only
    apply lt_of_le_of_ne
    · grind only
    · grind only

/--
Packed floats that are negative are less than or equal to packed floats that are nonnegative.
-/
theorem toRat_le_toRat_of_neg_of_nonneg
    (x y : PackedFloat e s) (hxsign : x.sign = true) (hysign : y.sign = false) :
    x.toRat ≤ y.toRat := by
  simp [PackedFloat.toRat, hxsign, hysign]
  have : 0 ≤ x.toRatSig := by grind only [nonneg_toRatSig]
  have : 0 ≤ (2 : Rat) ^ x.toRatExp := by grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  have : 0 ≤ y.toRatSig := by grind only [nonneg_toRatSig]
  have : 0 ≤ (2 : Rat) ^ y.toRatExp := by grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  have : 0 ≤ y.toRatSig * (2 : Rat) ^ y.toRatExp := by
    apply Rat.mul_nonneg
    · grind only
    · grind only
  have : 0 ≤ x.toRatSig * (2 : Rat) ^ x.toRatExp := by
    apply Rat.mul_nonneg
    · grind only
    · grind only
  grind only




theorem toExtRat'_le_toExtRat'_of_neg_of_nonneg (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hy : ¬ y.isNaN)
    (hxsign : x.sign = true) (hysign : y.sign = false) :
    x.toExtRat' ≤ y.toExtRat' := by
  simp [toExtRat', hx, hy]
  by_cases hxinf : x.isInfinite
  · simp only [Bool.not_eq_true] at hx
    simp only [hxinf, hxsign, cond_true, ExtRat.ExtRat.inf_true_le_iff, ne_eq, decide_not, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    by_cases hyinf : y.isInfinite
    · simp [hyinf]
    · simp [hyinf]
  · simp only [Bool.not_eq_true] at hx
    simp [hxinf, hxsign]
    by_cases hyinf : y.isInfinite
    · simp only [Bool.not_eq_true] at hy
      simp [hyinf, hysign]
    · simp only [Bool.not_eq_true] at hy
      simp only [hyinf, hysign, decide_eq_true_eq,
        cond_false, ExtRat.ExtRat.num_le_num_iff]
      apply PackedFloat.toRat_le_toRat_of_neg_of_nonneg
      · grind only
      · grind only

/--
For nonnegative numbers, the ordering of the packed floats
is consistent with the ordering of the extended rationals.
We disallow zero as we could have `x=+0`, `y=-0`.
The rational numbers will give `x:0 ≤ y:0`, but the
packed floats will give `x:0 ≤ y:0` is false, since `+0 ≤ -0` is false.
-/
theorem le_of_toExtRat'_le_toExtRat'
    (hs : 0 < s) (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hy : ¬ y.isNaN)
    (hxzero : ¬ x.isZero)
    (hyzero : ¬ y.isZero)
    (hxy : x.toExtRat' ≤ y.toExtRat') : x ≤ y := by
  by_cases hxsign : x.sign
  · -- x -ve
    by_cases hysign : y.sign
    · -- -ve
      suffices - y ≤ - x by
        grind only [= le_neg_iff_le_neg, = neg_neg']
      apply le_of_toExtRat'_le_toExtRat'_of_nonneg_of_nonneg
      · grind only
      · simp
        grind only
      · simp
        grind only
      · simp
        grind only
      · simp
        grind
      · simp
        exact ExtRat.neg_le_neg hxy
    · -- +ve
      grind only [le_of_nonneg_of_neg]
  · -- x +ve
    by_cases hysign : y.sign
    · -- y -ve
      simp only [Bool.not_eq_true] at hx hxsign
      have := toExtRat'_le_toExtRat'_of_neg_of_nonneg  y x
        (by grind only) (by grind only) (by grind only) (by grind only)
      have : x.toExtRat' = y.toExtRat' := by grind only
      have : x = y := by
        apply eq_of_toExtRat'_eq
        · grind only
        · grind only
        · grind only
        · grind only
        · grind only
      subst this
      simp
    · apply le_of_toExtRat'_le_toExtRat'_of_nonneg_of_nonneg
      · grind only
      · grind only
      · grind only
      · grind only
      · grind only
      · grind only


end PackedFloat
