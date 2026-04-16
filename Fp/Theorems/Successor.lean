import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing
import Fp.Theorems.Negation
import Fp.Theorems.Ordering

namespace Fp
namespace PackedFloat

/--
successorAwayFromZero of NaN is NaN
-/
@[simp, grind .]
theorem successorAwayFromZero_eq_of_isNaN (pf : PackedFloat e s) (hNaN : pf.isNaN) :
    pf.successorAwayFromZero = pf := by
  simp  [PackedFloat.successorAwayFromZero, hNaN]

/--
successorAwayFromZero of ∞ is ∞
-/
@[simp, grind .]
theorem successorAwayFromZero_eq_of_isInfinite (pf : PackedFloat e s)
    (hInf : pf.isInfinite) :
    pf.successorAwayFromZero = pf := by
  simp  [PackedFloat.successorAwayFromZero, hInf]
  grind only [PackedFloat.eq_getInfinity_iff_isInfinity, → PackedFloat.eq_mkInfinity_of_isInfinite,
    → PackedFloat.unpack_eq_NaN_of_isNaN, !PackedFloat.unpack_getInfinity,
    !PackedFloat.isInfinite_getInfinity, !PackedFloat.isInfinite_unpack_eq_isInfinite, #532a]

/--
successorAwayFromZero of max normal number is +∞.
-/
@[simp, grind .]
theorem successorAwayFromZero_maxNormal_eq (he : 1 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).successorAwayFromZero =
    PackedFloat.getInfinity e s sign := by
  simp only [PackedFloat.successorAwayFromZero]
  have : ¬ (PackedFloat.maxNormalNumber e s sign).isNaN := by
    grind
  simp [this]

@[simp]
theorem sign_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.exSucc x).sign = x.sign := by
  simp [PackedFloat.successorAwayFromZero.exSucc]

@[simp]
theorem sig_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.exSucc x).sig = 0#s := by
  simp [PackedFloat.successorAwayFromZero.exSucc]


theorem ex_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.exSucc x).ex = x.ex + 1#_ := by
  simp [PackedFloat.successorAwayFromZero.exSucc]


theorem isNorm_of_le_isNorm_of_not_inf (x : PackedFloat e s)
    (hinf : x.isNorm) (hxy : x ≤ y) (hy : ¬ y.isInfinite): y.isNorm := by
  sorry

theorem toRatSig_successorAwayFromZero_exSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.exSucc x).toRatSig = 1 := by
  simp [PackedFloat.toRatSig, PackedFloat.successorAwayFromZero.exSucc]
  sorry

@[simp]
theorem sign_sucessorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.sigSucc x).sign = x.sign := by
  simp [PackedFloat.successorAwayFromZero.sigSucc]

@[simp]
theorem ex_sucessorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.sigSucc x).ex = x.ex := by
  simp [PackedFloat.successorAwayFromZero.sigSucc]

theorem sig_sucessorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.sigSucc x).sig = x.sig + 1#_ := by
  simp [PackedFloat.successorAwayFromZero.sigSucc]

@[simp]
theorem isNorm_successorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.sigSucc x).isNorm = x.isNorm := by
  simp [PackedFloat.successorAwayFromZero.sigSucc, PackedFloat.isNorm]

@[simp]
theorem toRatExp_successorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (PackedFloat.successorAwayFromZero.sigSucc x).toRatExp = x.toRatExp := by
  simp [PackedFloat.toRatExp, PackedFloat.successorAwayFromZero.sigSucc, PackedFloat.toRatExp, PackedFloat.isNorm]

@[simp]
theorem toRatSig_successorAwayFromZero_sigSucc (x : PackedFloat e s) (hs : 0 < s)
    (hx : x.sig ≠ BitVec.allOnes s) :
    (PackedFloat.successorAwayFromZero.sigSucc x).toRatSig =
    x.toRatSig + (1 : Rat) / 2 ^ s := by
  simp [PackedFloat.toRatSig]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    rw [PackedFloat.sig_sucessorAwayFromZero_sigSucc]
    rw [BitVec.toNat_add_of_lt]
    · simp [hs]
      grind
    · simp [hs]
      grind only [!Nat.two_pow_pos, BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
  · simp [hnorm]
    rw [PackedFloat.sig_sucessorAwayFromZero_sigSucc]
    rw [BitVec.toNat_add_of_lt]
    · simp [hs]
    · simp [hs]
      grind only [!Nat.two_pow_pos, BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]

end PackedFloat

@[simp]
theorem BitVec.toNat_allOnes_sub_one_eq_twoPow_sub_two (n : Nat) (hn : 0 < n) :
    BitVec.toNat (BitVec.allOnes n - 1#n) = 2 ^ n - 2 := by
  rw [BitVec.toNat_sub_of_le]
  · simp [hn]
    grind
  · rw [BitVec.le_def]
    simp [hn]
    grind

@[simp]
theorem BitVec.one_le_allOnes (n : Nat) : 1#n ≤ BitVec.allOnes n := by
  rw [BitVec.le_def]
  simp
  grind

@[simp]
theorem BitVec.sub_le_iff_le_add (a b c : BitVec n)
    (hle' : c ≤ a)
    (hbc : b.toNat + c.toNat < 2^n) : a - c ≤ b ↔ a ≤ b + c := by
  rw [BitVec.le_def]
  rw [BitVec.le_def]
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_add_of_lt]
    · grind
    · grind
  · grind


/--
The successor is away by the right amount.
-/
theorem PackedFloat.toRat_successorAwayFromZero_eq
    (x : PackedFloat e s)
    (hxNaN : ¬ x.isNaN)
    (hxInf : ¬ x.isInfinite)
    (hxMaxNormal : x ≠ PackedFloat.maxNormalNumber e s x.sign) -- this is needed to avoid the case where successorAwayFromZero is ∞
    (he : 0 < e)
    (hs : 0 < s) :
    x.successorAwayFromZero.toRat = x.toRat + x.sign.toSign * ((2 : Rat) ^ (- (s : Int)) * 2 ^ (x.toRatExp)) := by
  simp [PackedFloat.successorAwayFromZero, hxNaN, hxInf]
  split
  case isTrue hsig =>
    split
    case isTrue hexp =>
      have : x = PackedFloat.maxNormalNumber e s x.sign := by
        apply PackedFloat.ext
        · simp
        · simp
          rw [BitVec.le_def] at hexp
          rw [BitVec.toNat_sub_of_le] at hexp
          · simp [he] at hexp
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_allOnes_sub_one_eq_twoPow_sub_two]
            · grind
            · simp [he]
          · simp
        · simp [hs, hsig]
      grind only
    case isFalse hexp =>
      simp [PackedFloat.toRat]
      rw [Rat.mul_assoc, Rat.mul_assoc]
      rw [← Rat.mul_add]
      apply Rat.mul_cancel_left .. |>.mpr
      · sorry
      · simp only [ne_eq, Rat.intCast_eq_zero_iff, Bool.toSign_ne_zero, not_false_eq_true]
  case isFalse hsig =>
    simp [PackedFloat.toRat]
    rw [Rat.mul_assoc, Rat.mul_assoc]
    rw [← Rat.mul_add]
    apply Rat.mul_cancel_left .. |>.mpr
    · simp [hs, hsig]
      rw [Rat.add_mul]
      rw [Rat.div_zpow_natCast_eq_zpow_neg]
      grind only
    · simp

end Fp
