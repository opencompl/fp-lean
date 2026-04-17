import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing
import Fp.Theorems.Negation
import Fp.Theorems.Ordering

namespace PackedFloat

/--
successorAwayFromZero of NaN is NaN
-/
@[simp, grind .]
theorem successorAwayFromZero_eq_of_isNaN (pf : PackedFloat e s) (hNaN : pf.isNaN) :
    pf.successorAwayFromZero = pf := by
  simp  [successorAwayFromZero, hNaN]

/--
successorAwayFromZero of ∞ is ∞
-/
@[simp, grind .]
theorem successorAwayFromZero_eq_of_isInfinite (pf : PackedFloat e s)
    (hInf : pf.isInfinite) :
    pf.successorAwayFromZero = pf := by
  simp  [successorAwayFromZero, hInf]
  grind only [eq_getInfinity_iff_isInfinity, → eq_mkInfinity_of_isInfinite,
    → unpack_eq_NaN_of_isNaN, !unpack_getInfinity,
    !isInfinite_getInfinity, !isInfinite_unpack_eq_isInfinite, #532a]

/--
successorAwayFromZero of max normal number is +∞.
-/
@[simp, grind .]
theorem successorAwayFromZero_maxNormal_eq (he : 1 < e) (sign : Bool) :
    (maxNormalNumber e s sign).successorAwayFromZero =
    getInfinity e s sign := by
  simp only [successorAwayFromZero]
  have : ¬ (maxNormalNumber e s sign).isNaN := by
    grind
  simp [this]

@[simp]
theorem sign_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (successorAwayFromZero.exSucc x).sign = x.sign := by
  simp [successorAwayFromZero.exSucc]

@[simp]
theorem sig_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (successorAwayFromZero.exSucc x).sig = 0#s := by
  simp [successorAwayFromZero.exSucc]


theorem ex_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (successorAwayFromZero.exSucc x).ex = x.ex + 1#_ := by
  simp [successorAwayFromZero.exSucc]

/--
the exponent interpreted as a natural number is the original exponent plus one.
-/
theorem toNat_ex_sucessorAwayFromZero_exSucc_eq_add_one
    (x : PackedFloat e s)
    (hex : x.ex ≠ BitVec.allOnes e):
    (successorAwayFromZero.exSucc x).ex.toNat = x.ex.toNat + 1 := by
  simp [successorAwayFromZero.exSucc]
  grind only [!Nat.two_pow_pos, = Nat.mod_eq_of_lt, BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]

/--
the successor that increments the exponent always creates a normal number,
as the exponent is at least 1.
-/
theorem isNorm_successorAwayFromZero_exSucc
    (he : 0 < e) (x : PackedFloat e s)
    (hex : x.ex < BitVec.allOnes e - 1#e) :
    (successorAwayFromZero.exSucc x).isNorm = true := by
  simp [successorAwayFromZero.exSucc, isNorm]
  constructor
  · intros hcontra
    rw [← hcontra] at hex
    rw [BitVec.lt_def] at hex
    rw [BitVec.toNat_sub_of_le] at hex
    · rw [BitVec.toNat_add_of_lt] at hex
      · simp [he] at hex
      · simp [he]; grind only [= BitVec.toNat_add, = BitVec.toNat_ofNat, = BitVec.toNat_one,
        usr BitVec.isLt, = BitVec.toNat_allOnes]
    · grind only [BitVec.toNat_inj, = BitVec.toNat_sub, BitVec.eq_allOnes_iff_toNat_eq,
      = BitVec.toNat_ofNat, = BitVec.toNat_one, usr BitVec.isLt, = BitVec.toNat_allOnes,
      #1a9affbe9de0fbf2, #7d3276f4fb79b018, #a7353b0b482378e0]
  · intros hcontra
    have : x.ex.toNat < (2^e - 1) - 1 := by
      rw [BitVec.lt_def] at hex
      rw [BitVec.toNat_sub_of_le] at hex
      · simp [he] at hex
        grind
      · simp
    obtain hcontra := BitVec.toNat_inj .. |>.mpr hcontra
    rw [BitVec.toNat_add_of_lt] at hcontra
    · simp [he] at hcontra
    · simp [he]; grind only [= BitVec.toNat_add, usr BitVec.isLt, = BitVec.toNat_one]


/--
the significand when overflowing the exponent is set to 1..
-/
theorem toRatSig_successorAwayFromZero_exSucc
    (he : 0 < e) (x : PackedFloat e s) (hex : x.ex < BitVec.allOnes e - 1#e) :
    (successorAwayFromZero.exSucc x).toRatSig = 1 := by
  simp [toRatSig]
  have := isNorm_successorAwayFromZero_exSucc he x hex
  simp [this]
  grind only

@[simp]
theorem sign_sucessorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (successorAwayFromZero.sigSucc x).sign = x.sign := by
  simp [successorAwayFromZero.sigSucc]

@[simp]
theorem ex_sucessorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (successorAwayFromZero.sigSucc x).ex = x.ex := by
  simp [successorAwayFromZero.sigSucc]

theorem sig_sucessorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (successorAwayFromZero.sigSucc x).sig = x.sig + 1#_ := by
  simp [successorAwayFromZero.sigSucc]

@[simp]
theorem isNorm_successorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (successorAwayFromZero.sigSucc x).isNorm = x.isNorm := by
  simp [successorAwayFromZero.sigSucc, isNorm]

@[simp]
theorem toRatExp_successorAwayFromZero_sigSucc (x : PackedFloat e s) :
    (successorAwayFromZero.sigSucc x).toRatExp = x.toRatExp := by
  simp [toRatExp, successorAwayFromZero.sigSucc, toRatExp, isNorm]


theorem BitVec.add_one_eq_zero_iff_eq_allOnes (x : BitVec s) :
    x + 1#_ = 0#_ ↔ x = BitVec.allOnes s := by
  constructor
  · intro h
    have := BitVec.toNat_inj .. |>.mpr h
    simp at this
    have : x.toNat = 2^s - 1 := by grind
    apply BitVec.eq_of_toNat_eq
    simp
    rw [this]
  · intros h
    subst h
    apply BitVec.eq_of_toNat_eq
    simp
    have : 0 < 2^s := by grind only [!Nat.two_pow_pos]
    have : (2^s - 1) + 1 = 2^s := by grind
    rw [this]
    simp only [Nat.mod_self]

/--
the significand interpreted as a natural number is the original significand plus one.
-/
@[simp]
theorem toNat_sig_successorAwayFromZero_sigSucc_eq_toNat_add_one (x : PackedFloat e s)
    (hx : x.sig ≠ BitVec.allOnes s) :
    (successorAwayFromZero.sigSucc x).sig.toNat =
    x.sig.toNat + 1 := by
  simp [successorAwayFromZero.sigSucc]
  grind only [!Nat.two_pow_pos, = Nat.mod_eq_of_lt, BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]



@[simp]
theorem toRatSig_successorAwayFromZero_sigSucc (x : PackedFloat e s)
    (hx : x.sig ≠ BitVec.allOnes s) :
    (successorAwayFromZero.sigSucc x).toRatSig =
    x.toRatSig + (1 : Rat) / 2 ^ s := by
  simp [toRatSig]
  rw [toNat_sig_successorAwayFromZero_sigSucc_eq_toNat_add_one x hx]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    grind
  · simp [hnorm]


/--
The successor is away by the right amount.
-/
theorem toRat_successorAwayFromZero_eq
    (x : PackedFloat e s)
    (hxNaN : ¬ x.isNaN)
    (hxInf : ¬ x.isInfinite)
    (hxMaxNormal : x ≠ maxNormalNumber e s x.sign) -- this is needed to avoid the case where successorAwayFromZero is ∞
    (he : 0 < e)
    (hs : 0 < s) :
    x.successorAwayFromZero.toRat =
      x.toRat + x.sign.toSign * ((2 : Rat) ^ (- (s : Int)) * 2 ^ (x.toRatExp)) := by
  simp [successorAwayFromZero, hxNaN, hxInf]
  split
  case isTrue hsig =>
    split
    case isTrue hexp =>
      have : x = maxNormalNumber e s x.sign := by
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
      simp [toRat]
      rw [Rat.mul_assoc, Rat.mul_assoc]
      rw [← Rat.mul_add]
      apply Rat.mul_cancel_left .. |>.mpr
      · simp at hexp
        -- This is the painful case, because we may go from maxSubnormal to minNormal.
        -- we know that sig is all ones.
        -- if exp is 0, then we are max subnormal.
        -- otherwise, we are normal, and successor is also normal.
        by_cases hex : x.ex = 0#e
        · have : x.isZeroOrSubnorm := by simp [isZeroOrSubnorm, hex]
          have : x.isNonzeroSubnorm := by simp [isNonzeroSubnorm, hex, hsig]; grind only [=
              allOnes_eq_zero_eq_decide,
            = zero_ne_allOnes_eq_decide]
          have := x.toRatExp_eq_of_not_isNorm (by grind)
          simp [this]
          have := x.toRatSig_eq_of_not_isNorm (by grind)
          rw [this]
          rw [hsig]
          simp [hs]
          generalize hy : successorAwayFromZero.exSucc x = y
          have := isNorm_successorAwayFromZero_exSucc he x hexp
          have hex := y.toRatExp_eq_of_isNorm (by grind only)
          rw [hex]
          have : y.toRatSig = 1 := by
            subst y
            apply toRatSig_successorAwayFromZero_exSucc
            · grind only
            · grind only
          rw [this]
          simp only [Rat.one_mul]
          -- needs more analysis...
          sorry
        · have : x.isNorm := by grind only [exp_eq_of_isNonzeroSubnorm,
          ex_eq_of_isZero,
          PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          sorry
      · simp only [ne_eq, Rat.intCast_eq_zero_iff, Bool.toSign_ne_zero, not_false_eq_true]
  case isFalse hsig =>
    simp [toRat]
    rw [Rat.mul_assoc, Rat.mul_assoc]
    rw [← Rat.mul_add]
    apply Rat.mul_cancel_left .. |>.mpr
    · simp [hs, hsig]
      rw [Rat.add_mul]
      rw [Rat.div_zpow_natCast_eq_zpow_neg]
      grind only
    · simp

theorem successor_exp_lt_or_sig_lt (x : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (hxinf : ¬ x.isInfinite) :
    x.ex < (successorAwayFromZero x).ex ∨
      ((successorAwayFromZero x).ex = x.ex ∧ (x.sig < (successorAwayFromZero x).sig)) := by
  simp [successorAwayFromZero]
  simp [hxnan, hxinf]
  by_cases hsig : x.sig = BitVec.allOnes s
  · simp only [hsig, ↓reduceIte, BitVec.one_le_allOnes, BitVec.not_allOnes_lt, and_false, or_false]
    by_cases hexp : BitVec.allOnes e - 1#e ≤ x.ex
    · simp [hexp]
      sorry
    · simp [hexp]
      sorry
  · simp only [hsig, ↓reduceIte, ex_sucessorAwayFromZero_sigSucc, BitVec.lt_irrefl, true_and,
    false_or]
    rw [BitVec.lt_def]
    simp [hsig]


/--
successor is the closest number that is greater than the original number
so if x < y, then successor of x is ≤ y.
-/
theorem lt_iff_le_of_successor_of_nonneg_of_nonneg (x : PackedFloat e s) (y : PackedFloat e s)
    (hxsign : x.sign = false) (hysign : y.sign = false)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN) :
    x < y ↔ x.successorAwayFromZero ≤ y := by
  sorry

/--
Any number between 'x' and its successor must be 'x' or the successor.
-/
theorem eq_self_or_successor_of_le_of_le (x : PackedFloat e s) (y : PackedFloat e s)
    (hxsign : x.sign = false) (hysign : y.sign = false)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN) :
    (x ≤ y ∧ y ≤  x.successorAwayFromZero) ↔ (y = x ∨ y = x.successorAwayFromZero) := by
  sorry

/-
Either upper = lower, or upper = successor(lower)
-/
