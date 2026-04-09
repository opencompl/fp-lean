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

end PackedFloat
