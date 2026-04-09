import Fp.Basic
import Fp.Packing

namespace PackedFloat

theorem Rat.zpow_sub {q : Rat} (hq : q ≠ 0) {a b : Int} : q ^ (a - b) = q ^ a * q ^ (-b) := by
  rw [Int.sub_eq_add_neg]
  rw [Rat.zpow_add hq]

@[simp]
theorem toExtRat_eq_toExtRat' {pf : PackedFloat e s}
  : pf.toExtRat = pf.toExtRat' := by
  cases hNaN : pf.isNaN <;>
  cases hInf : pf.isInfinite <;>
  cases hZero : pf.isZero <;>
  cases hNorm : pf.isNorm <;>
  all_goals simp only [toExtRat, toExtDyadic, ExtDyadic.toExtRat, toExtRat', hNaN, hInf, hZero, hNorm, cond_true,
    cond_false, Dyadic.toRat_zero, toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, Bool.false_eq_true, if_false, if_true]
  all_goals simp only [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, ExtRat.Number.injEq,
    Int.neg_add, Int.neg_sub, Bool.apply_cond]
  -- all_goals (simp only [PackedFloat.toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, if_true, if_false, hNorm, Bool.false_eq_true])
  all_goals (try simp only [BitVec.toInt_setWidth'_of_lt (Nat.lt_succ_self (s + 1)), Rat.intCast_natCast, BitVec.toInt_neg_eq_of_msb (BitVec.msb_setWidth'_of_lt (Nat.lt_succ_self (s + 1))), BitVec.toNat_cons', Bool.toNat, cond_false, cond_true, Nat.zero_shiftLeft, Nat.one_shiftLeft, Nat.zero_add, Int.natCast_add, Rat.intCast_neg, Rat.intCast_add, Rat.natCast_pow, Rat.natCast_ofNat])
  all_goals (cases pf.sign <;> simp only [cond_false, cond_true, Bool.toSign, if_true, Bool.false_eq_true, if_false, Rat.intCast_ofNat, Rat.intCast_neg, Rat.zero_add, Rat.one_mul, Rat.neg_mul])
  all_goals (rewrite [Rat.div_def])
  all_goals (try rewrite [← Rat.zpow_natCast, ← Rat.zpow_neg])
  all_goals (push_cast)
  · simp only [Int.neg_add]
    simp only [Rat.zpow_add (q := 2) (hq := by decide)]
    grind
  · simp only [Int.neg_add]
    simp only [Rat.zpow_add (q := 2) (hq := by decide)]
    grind
  · simp only [Rat.add_mul]
    ac_nf
    norm_cast
    congr 1
    · simp only [← Rat.zpow_add (q := 2) (hq := by decide)]
      congr 1
      grind only
    · rw [Rat.zpow_add (q := 2) (hq := by decide)]
      grind only
  · -- TODO: disgusting, write a solver for this that does power-of-2 simplification.
    simp only [Rat.add_mul]
    simp only [Rat.zpow_add (q := 2) (hq := by decide)]
    simp only [Rat.zpow_sub (q := 2) (hq := by decide)]
    simp only [Rat.one_mul]
    simp only [← Rat.zpow_add (q := 2) (hq := by decide)]
    norm_cast
    congr 2
    · congr 1
      grind only
    · rw [Rat.zpow_add (q := 2) (hq := by decide)]
      grind only
  · grind only [→ eq_mkZero_of_isZero, Rat.natCast_eq_zero_iff, = sig_getZero,
    = BitVec.ofNat_eq_ofNat, = BitVec.toNat_zero, #a5422ce67b0854c8]
  · grind only [→ eq_mkZero_of_isZero, Rat.natCast_eq_zero_iff, = sig_getZero,
    = BitVec.ofNat_eq_ofNat, = BitVec.toNat_zero, #a5422ce67b0854c8]
  · grind only [→ not_isNorm_of_isZero]
  · grind only [→ not_isNorm_of_isZero]

@[simp]
theorem toExtRat_minSubnormal_eq (e s : Nat) (he : 1 < e) (hs : 0 < s):
    (PackedFloat.minSubnormalNumber e s false).toRat =
    (2 : Rat) ^ (minNormalExp e - s)  := by -- I should NOT need a + 1?
  rw [toRat]
  simp [sign_minSubnormalNumber]
  simp [toRatExp]
  simp [toRatSig]
  have := isNonzeroSubnorm_minSubnormalNumber_eq_of_lt e s false he hs
  have : (minSubnormalNumber e s false).isNorm = false := by grind only [→ not_isNorm_of_isSubnorm]
  simp [this]
  rw [show 1 % (2 ^ s) = 1 by grind only [= Nat.mod_eq_of_lt, !Nat.two_pow_pos,
    usr Nat.div_pow_of_pos]]
  simp only [Rat.natCast_ofNat]
  rw[Rat.one_div_zpow_natCast_eq_zpow_neg]
  rw [Rat.zpow_mul_zpow]
  · congr 1
    simp [minNormalExp]
    norm_cast
    generalize hb : - (((bias e - 1 ) : Nat) : Int) = b
    rw [Int.sub_eq_add_neg]
    grind only
  · decide

theorem toRat_minSubnormal_le_toRat_of_isNonzeroSubnorm (x : PackedFloat e s)
    (hxsign : x.sign = false)
    (hxsubnorm : x.isNonzeroSubnorm)
    (he : 1 < e)
    (hs : 0 < s) :
    (PackedFloat.minSubnormalNumber e s false).toRat ≤ x.toRat := by
  simp [he, hs]
  rw [toRat]
  simp [hxsign]
  have := x.lt_twoRatSig_of_sig_ne_zero (by grind only [→ not_isNorm_of_isSubnorm,
    → isNormOrSubnorm_of_isSubnorm, sig_ne_zero_of_isNormOrNonzeroSubnorm_of_not_isNorm])
  have := x.toRatExp_eq_of_not_isNorm (by grind only [→ not_isNorm_of_isSubnorm])
  rw [this]
  apply Rat.le_trans (b := (1 / (2 : Rat) ^ s) * (2 : Rat) ^ (minNormalExp e - 1))
  · sorry
  · sorry


theorem toExtRat_maxSubnormal_eq (e s : Nat) (he : 1 < e) (hs : 0 < s):
    (PackedFloat.maxSubnormalNumber e s false).toRat =
    (2 : Rat) ^ (minNormalExp e - s) * ((2 : Rat) ^ s - 1) := by
  rw [toRat]
  simp [sign_maxSubnormalNumber]
  simp [toRatExp]
  simp [toRatSig]
  have := isNonzeroSubnorm_maxSubnormalNumber_eq_of_lt e s false he hs
  have : (maxSubnormalNumber e s false).isNorm = false := by grind only [→ not_isNorm_of_isSubnorm]
  simp only [this]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Rat.div_def]
  simp only [Rat.inv_zpow_natCast_eq_zpow_neg]
  rw [Rat.mul_assoc]
  have h1 : (((2 ^ s - 1) : Nat) : Rat) = (2 : Rat) ^ s - 1 := by
    have : 0 < 2 ^ s := by grind only [!Nat.two_pow_pos]
    rw [Rat.natCast_sub_of_le (by grind only)]
    grind only
  -- ⊢ ↑(2 ^ s - 1) * (2 ^ (-↑s) * 2 ^ (-↑(bias e - 1))) = 2 ^ (minNormalExp e - ↑s) * (2 ^ s - 1)
  have h2 : (2 : Rat) ^ (- (s : Int)) * (2 : Rat) ^ (- (((bias e - 1) : Nat) : Int)) =
    (2 : Rat) ^ (minNormalExp e - s) := by
    rw [Rat.zpow_mul_zpow]
    · apply congrArg
      simp [minNormalExp]
      grind only
    · grind only
  grind only

theorem toRat_le_toRat_maxSubnormal_of_isNonzeroSubnorm (x : PackedFloat e s)
    (hxsign : x.sign = false)
    (hxsubnorm : x.isNonzeroSubnorm)
    (he : 1 < e)
    (hs : 0 < s) :
    x.toRat ≤ (PackedFloat.maxSubnormalNumber e s false).toRat := by
  sorry


theorem toRat_maxNormalNumber_eq :
  (PackedFloat.maxNormalNumber e s false).toRat = (2 : Rat) ^ (maxNormalExp e - 1) * ((2 : Rat) ^ s - 1) := by
  rw [toRat]
  rw [sign_maxNormalNumber]
  simp
  sorry

/--
Numbers that are strictly larger than the max normal number is positive infinity.
-/
theorem toExtRat_maxNormal_lt_toExtRat_iff_eq_getinfinity (x : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (he : 1 < e) (hs : 0 < s) :
    (PackedFloat.maxNormalNumber e s false).toExtRat < x.toExtRat ↔ x = PackedFloat.getInfinity e s false := by
  sorry

/--
Numbers that are strictly smaller than the negative max normal number is negative infinity.
-/
theorem toExtRat_lt_toExtRat_maxNormal_iff_eq_getInfinity (x : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (he : 1 < e) (hs : 0 < s) :
    x.toExtRat < (PackedFloat.maxNormalNumber e s true).toExtRat ↔ x = PackedFloat.getInfinity e s true := by
  sorry

end PackedFloat
