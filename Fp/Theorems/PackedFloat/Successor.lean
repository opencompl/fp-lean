import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.PackedFloat.Negation
import Fp.Theorems.PackedFloat.Ordering

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
    → unpack_eq_NaN_of_isNaN, !unpack_getInfinity, !isInfinite_getInfinity,
    !isInfinite_unpack_eq_isInfinite, #532a]


@[simp]
theorem sign_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (successorAwayFromZero.exSucc x).sign = x.sign := by
  simp [successorAwayFromZero.exSucc]

@[simp]
theorem sig_sucessorAwayFromZero_exSucc (x : PackedFloat e s) :
    (successorAwayFromZero.exSucc x).sig = 0#s := by
  simp [successorAwayFromZero.exSucc]


@[simp]
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

TODO: Refactor this take x.ex ≠ Bv.allOnes, x.ex ≠ BV.allOnes - 1
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

@[grind .]
theorem lt_allOnes_sub_one_of_ne_of_ne (x : BitVec e) (he : 0 < e)
    (hx1 : x ≠ BitVec.allOnes e)
    (hx2 : x ≠ BitVec.allOnes e - 1#e) :
    x < BitVec.allOnes e - 1#e := by
  rw [BitVec.lt_def]
  rw [BitVec.toNat_sub_of_le]
  · simp
    rw [Nat.mod_eq_of_lt]
    · have : x.toNat ≠ 2^e - 1 := by grind
      have : x.toNat ≠ 2^e - 2 := by
        have := BitVec.toNat_ne |>.mp hx2
        rw [BitVec.toNat_sub_of_le] at this
        · simp at this
          grind
        · simp
      have : x.toNat < 2^e := by grind only [usr BitVec.isLt]
      grind only [!Nat.two_pow_pos, usr Nat.div_pow_of_pos, #1134]
    · grind only
  · simp

theorem toRatExp_successorAwayFromZero_exSucc
    (he : 1 < e)
    (x : PackedFloat e s)
    (hex1 : x.ex ≠ BitVec.allOnes e)
    (hex2 : x.ex ≠ BitVec.allOnes e - 1) :
    (successorAwayFromZero.exSucc x).toRatExp =
    if x.ex = 0#e then x.toRatExp else x.toRatExp + 1 := by
  simp [toRatExp]
  rw [isNorm_successorAwayFromZero_exSucc]
  · simp
    norm_cast
    rw [Nat.mod_eq_of_lt]
    · simp
      by_cases hxnorm : x.ex = 0#e
      · simp [hxnorm]
        have : x.isNorm = false := by grind
        simp [this]
        have : 0 < bias e := by
          refine bias_pos_of_one_lt e ?_
          simp [he]
        grind only
      · have : x.isNorm = true := by
          grind only [isNorm_iff_ex_ne_allOnes_and_ex_ne_zero, = BitVec.zero_eq]
        simp [this]
        grind only
    · grind only [!Nat.two_pow_pos, BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
  · grind only
  · grind only [= BitVec.ofNat_eq_ofNat, lt_allOnes_sub_one_of_ne_of_ne]


theorem Rat.mul_add_self (a b : Rat) : a * b + a = a * (b + 1) := by
  rw [Rat.mul_add]
  simp

/--
The successor is away by the right amount.
-/
theorem toRat_successorAwayFromZero_eq
    (x : PackedFloat e s)
    (hxNaN : ¬ x.isNaN)
    (hxInf : ¬ x.isInfinite)
    (hxMaxNormal : x ≠ maxNormalNumber e s x.sign) -- this is needed to avoid the case where successorAwayFromZero is ∞
    (he : 1 < e)
    (hs : 0 < s) :
    x.successorAwayFromZero.toRat =
      x.toRat + x.sign.toSign * ((2 : Rat) ^ (- (s : Int)) * 2 ^ (x.toRatExp)) := by
  simp [successorAwayFromZero, hxNaN, hxInf]
  split
  case isTrue hsig =>
    simp [toRat]
    rw [Rat.mul_assoc, Rat.mul_assoc]
    rw [← Rat.mul_add]
    apply Rat.mul_cancel_left .. |>.mpr
    have hex1 : x.ex ≠ BitVec.allOnes e := by grind only [=> not_isNaN_iff_ex_ne_or_sig_ne,
      = allOnes_eq_zero_eq_decide]
    have hex2 : x.ex ≠ BitVec.allOnes e - 1#e := by
      intros hcontra
      apply hxMaxNormal
      apply PackedFloat.ext
      · simp
      · simp [hcontra]
      · simp [hsig]
    rw [toRatSig_successorAwayFromZero_exSucc]
    · rw [toRatExp_successorAwayFromZero_exSucc]
      · by_cases hex0 : x.ex = 0#e
        · simp [hex0]
          rw [x.toRatSig_eq_of_not_isNorm]
          · simp [hsig]
            rw [← Rat.add_mul]
            rw [Rat.zpow_neg_natCast_eq_one_div_zpow]
            simp
            have : 2^s - 1 + 1 = 2^s := by grind
            norm_cast
            simp [this]
            have : (2 : Rat) ^s / (2 : Rat) ^s = 1 := by
              grind only [Rat.two_pow_nat_ne_zero]
            simp [this]
          · grind only [ex_ne_zero_if_isNorm, = BitVec.zero_eq]
        · simp [hex0]
          rw [x.toRatSig_eq_of_isNorm]
          · simp only [hsig, BitVec.toNat_allOnes]
            rw [Rat.zpow_add (by decide)]
            simp only [Rat.zpow_one]
            rw [Rat.add_mul]
            rw [Rat.zpow_neg_natCast_eq_one_div_zpow]
            simp
            rw [Rat.add_assoc]
            rw [← Rat.add_mul]
            simp
            norm_cast
            have : 2^s - 1 + 1 = 2^s := by grind
            simp [this]
            have : (2 : Rat) ^s / (2 : Rat) ^s = 1 := by
              grind only [Rat.two_pow_nat_ne_zero]
              -- apply?
            simp [this]
            grind
          · grind only [=> not_isNaN_iff_ex_ne_or_sig_ne, exp_eq_of_isNonzeroSubnorm,
            ex_eq_of_isZero,
            PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
      · grind only
      · grind only
      · grind only
    · grind only
    · grind only [lt_allOnes_sub_one_of_ne_of_ne]
    · simp
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

/--
info: 'PackedFloat.toRat_successorAwayFromZero_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms toRat_successorAwayFromZero_eq

/--
The successor is the next representable number
so either the exponent is less than the successor's exponent and the significant is all ones,
 or the exponents are equal and the significand is less than the successor's significand.
-/
theorem successor_exp_lt_or_sig_lt (x : PackedFloat e s)
    (he : 1 < e)
    (hxnan : ¬ x.isNaN)
    (hxinf : ¬ x.isInfinite) :
    (x.ex < (successorAwayFromZero x).ex ∧ x.sig = BitVec.allOnes s) ∨
      ((successorAwayFromZero x).ex = x.ex ∧ (x.sig < (successorAwayFromZero x).sig)) := by
  simp only [successorAwayFromZero, ne_eq, ite_not]
  simp only [hxnan, Bool.false_eq_true, ↓reduceIte, hxinf]
  have hpow : 1 < 2^e := by
    refine Nat.one_lt_two_pow (by grind only)
  by_cases hsig : x.sig = BitVec.allOnes s
  · simp only [hsig, ↓reduceIte, BitVec.not_allOnes_lt, and_false, or_false]
    by_cases hexp : BitVec.allOnes e - 1#e ≤ x.ex
    · simp
      rw [BitVec.lt_def]
      rw [BitVec.toNat_add_of_lt]
      · simp
        rw [Nat.mod_eq_of_lt]
        · grind only
        · grind only
      · simp;
        rw [Nat.mod_eq_of_lt]
        · have : x.ex ≠ BitVec.allOnes e := by grind only [→ not_isNorm_of_isNaN,
          exp_eq_of_isNonzeroSubnorm, ex_eq_of_isZero, = zero_ne_allOnes_eq_decide,
          PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm,
          isNorm_iff_ex_ne_allOnes_and_ex_ne_zero]
          grind only [BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
        · grind only
    · simp
      rw [BitVec.lt_def]
      rw [BitVec.toNat_add_of_lt]
      · simp
        rw [Nat.mod_eq_of_lt]
        · decide
        · grind only
      · simp
        rw [Nat.mod_eq_of_lt]
        · have : x.ex ≠ BitVec.allOnes e := by grind only [→ not_isNorm_of_isNaN,
          exp_eq_of_isNonzeroSubnorm, ex_eq_of_isZero, = zero_ne_allOnes_eq_decide,
          PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm,
          isNorm_iff_ex_ne_allOnes_and_ex_ne_zero]
          grind only [BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
        · grind
  · simp only [hsig, ↓reduceIte, ex_sucessorAwayFromZero_sigSucc, BitVec.lt_irrefl, true_and]
    rw [BitVec.lt_def]
    simp [hsig]


/--
relates the exponent and significand's value
to that of the significant.
-/
theorem toNat_successorAwayFromZero_exp_eq_lt_or_toNat_successorAwayFromZero_sig_lt (x : PackedFloat e s)
    (he : 1 < e)
    (hxnan : ¬ x.isNaN)
    (hxinf : ¬ x.isInfinite) :
    ((successorAwayFromZero x).ex.toNat = x.ex.toNat + 1 ∧ x.sig = BitVec.allOnes s ∧ (successorAwayFromZero x).sig.toNat = 0) ∨
      ((successorAwayFromZero x).ex.toNat = x.ex.toNat ∧ (x.sig.toNat + 1 = (successorAwayFromZero x).sig.toNat)) := by
  simp only [successorAwayFromZero, ne_eq, ite_not]
  simp only [hxnan, Bool.false_eq_true, ↓reduceIte, hxinf]
  have hpow : 1 < 2^e := by
    refine Nat.one_lt_two_pow (by grind only)
  by_cases hsig : x.sig = BitVec.allOnes s
  · simp only [hsig, ↓reduceIte]
    by_cases hexp : BitVec.allOnes e - 1#e ≤ x.ex
    · simp
      rw [Nat.mod_eq_of_lt]
      · have : x.ex ≠ BitVec.allOnes e := by grind only [→ not_isNorm_of_isNaN,
          exp_eq_of_isNonzeroSubnorm, ex_eq_of_isZero, = zero_ne_allOnes_eq_decide,
          PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm,
          isNorm_iff_ex_ne_allOnes_and_ex_ne_zero]
        grind only [BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
    · simp
      rw [Nat.mod_eq_of_lt]
      · have : x.ex ≠ BitVec.allOnes e := by
          grind only [→ not_isNorm_of_isNaN, exp_eq_of_isNonzeroSubnorm, ex_eq_of_isZero,
            = zero_ne_allOnes_eq_decide,
            PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm,
            isNorm_iff_ex_ne_allOnes_and_ex_ne_zero]
        grind only [BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
  · simp only [hsig, ↓reduceIte, ex_sucessorAwayFromZero_sigSucc, true_and]
    simp [sig_sucessorAwayFromZero_sigSucc]
    rw [Nat.mod_eq_of_lt]
    · grind only [!Nat.two_pow_pos, BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]


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
  intros hinf
  apply PackedFloat.ext
  · simp
  · simp
    grind
  · simp

@[simp]
theorem sign_successorAwayFromZero (x : PackedFloat e s) :
    (successorAwayFromZero x).sign = x.sign := by
  simp [successorAwayFromZero]
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
    · simp [hxInf]
      by_cases hxMaxNormal : x.sig = BitVec.allOnes s
      · simp [hxMaxNormal]
      · simp [hxMaxNormal]

@[simp]
theorem isNaN_successorAwayFromZero_exSucc
    (hs : 0 < s)
    (x : PackedFloat e s)
    (hx : ¬ x.isNaN) :
    (successorAwayFromZero.exSucc x).isNaN = x.isNaN := by
  simp [successorAwayFromZero.exSucc]
  simp [isNaN] at hx ⊢
  grind

@[grind ., simp ←]
theorem BitVec.eq_allOnes_iff_plus_one_eq_zero (x : BitVec s) :
    x = BitVec.allOnes s ↔ x + 1#s = 0#s := by
  constructor
  · intro h
    subst h
    apply BitVec.eq_of_toNat_eq
    simp
    have : 0 < 2^s := by grind only [!Nat.two_pow_pos]
    have : (2^s - 1) + 1 = 2^s := by grind
    rw [this]
    simp only [Nat.mod_self]
  · intro h
    have := BitVec.toNat_inj .. |>.mpr h
    simp at this
    have : x.toNat = 2^s - 1 := by grind
    apply BitVec.eq_of_toNat_eq
    simp
    rw [this]

@[simp]
theorem isNaN_successorAwayFromZero_sigSucc (hs : 0 < s)
    (x : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hxsig : x.sig ≠ BitVec.allOnes s) :
    (successorAwayFromZero.sigSucc x).isNaN = x.isNaN := by
  simp [successorAwayFromZero.sigSucc]
  simp [isNaN] at hxnan ⊢
  have : x.sig + 1#s ≠ 0#s := by
    simp
    intros hcontra
    apply hxsig
    grind only [BitVec.eq_allOnes_iff_plus_one_eq_zero]

  simp [show x.sig + 1#s != 0#s by grind]
  intros hex
  specialize hxnan hex
  obtain ⟨h1, h2⟩ := hxnan
  simp [h1, h2]
  have : x.ex ≠ BitVec.allOnes e := by grind only [=> isInfinite_iff_ex_eq_sig_eq]
  grind only [BitVec.eq_allOnes_iff_plus_one_eq_zero]


@[simp, grind .]
theorem isNaN_successorAwayFromZero (hs : 0 < s) (x : PackedFloat e s) :
    (successorAwayFromZero x).isNaN = x.isNaN := by
  simp [successorAwayFromZero]
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf, hs]
    · simp [hxInf, hs]
      by_cases hxMaxNormal : x.sig = BitVec.allOnes s
      · simp [hxMaxNormal, hs]
        rw [isNaN_successorAwayFromZero_exSucc]
        · grind only
        · grind only
        · grind only
      · simp [hxMaxNormal, hs, hxNaN, hxInf]


theorem ex_eq_allOnes_of_isNaN_or_isInfinite (he : 0 < e) (hs : 0 < s) (x : PackedFloat e s) :
    (x.ex = BitVec.allOnes e) ↔ x.isNaN ∨ x.isInfinite := by
  constructor
  · intros he
    simp [isNaN, isInfinite, he]
    grind
  · intros hx
    rcases hx with hx | hx
    · grind only [=> isNaN_iff_ex_eq_sig_eq]
    · grind only [=> isInfinite_iff_ex_eq_sig_eq]


/--
successor is always greater than the original number,
as long as the original number is a number.
-/
@[grind ., simp]
theorem self_lt_successorAwayFromZero (he : 1 < e) (hs : 0 < s)
  (y : PackedFloat e s) (hy : y.sign = false) (hynan : ¬ y.isNaN) (hyinf : ¬ y.isInfinite) :
    y < y.successorAwayFromZero := by
  have := successor_exp_lt_or_sig_lt y he hynan hyinf
  -- | TODO: rephrase this in terms of BitVec.lt instead of toNat lt toNat
  apply lt_of_ex_lt_ex_or_sig_lt_sig_of_nonneg_of_nonneg .. |>.mpr
  · obtain h | h := this
    · left
      bv_omega
    · right
      bv_omega
  · grind only
  · simp [hy]
  · grind only
  · simp; grind only [isNaN_successorAwayFromZero]

/--
successor is always larger than or equal to the original number,
-/
@[grind ., simp]
theorem self_le_successorAwayFromZero (he : 1 < e) (hs : 0 < s)
  (y : PackedFloat e s) (hy : y.sign = false) :
    y ≤ y.successorAwayFromZero := by
  by_cases hynan : y.isNaN
  · simp [hynan]
  · by_cases hyinf : y.isInfinite
    · simp [hyinf]
    · apply le_of_lt
      apply self_lt_successorAwayFromZero he hs y hy hynan hyinf

/--
The number 'y' is strictly larger than 'x' iff it is
larger than or equal to the successor of 'x'.
-/
@[simp ←, grind =, grind =_]
theorem lt_iff_le_successorAwayFromZero (he : 1 < e) (hs : 0 < s)
    (x : PackedFloat e s) (y : PackedFloat e s)
    (hxsign : x.sign = false) (hysign : y.sign = false)
    (hxnan : ¬ x.isNaN)
    (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite) :
    (x < y) ↔ x.successorAwayFromZero ≤ y := by
  constructor
  · intros hx
    have hxlt := lt_of_ex_lt_ex_or_sig_lt_sig_of_nonneg_of_nonneg
        (a := x)
        (b := y)
        (hbnan := by grind)
        (hanan := by grind)
        (hbsign := by grind)
        (hasign := by grind) |>.mp hx
    have succle := successor_exp_lt_or_sig_lt x he hxnan hxinf
    have hxsucc := toNat_successorAwayFromZero_exp_eq_lt_or_toNat_successorAwayFromZero_sig_lt
      (x := x) (he := he) (hxnan := hxnan) (hxinf := hxinf)
    apply le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg .. |>.mpr
    · rcases hxlt with hxlt | hxlt
      · rcases hxsucc with ⟨hxsuccex, hxsuccsig⟩ | ⟨hxsuccex, hxsuccsig⟩
        · grind only
        · grind only
      · rcases hxsucc with ⟨hxsuccex, hxsuccsig⟩ | ⟨hxsuccex, hxsuccsig⟩
        · -- contradiction, x.sig = allOnes, cannot be strictly less than another BV.
          have hysig : y.sig.toNat < 2^s := by grind only [usr BitVec.isLt]
          have hxsig : x.sig.toNat = 2^s - 1 := by grind only [BitVec.eq_allOnes_iff_toNat_eq, usr BitVec.isLt]
          have hxysig : x.sig.toNat < y.sig.toNat := by grind only
          grind only [!Nat.two_pow_pos]
        · grind only
    · simp [hxsign]
    · grind only [isNaN_successorAwayFromZero]
    · simp [hxnan, hs]
    · simp [hynan]

  · intros hx
    apply lt_of_lt_of_le_of_not_isNaN (y := x.successorAwayFromZero)
    · grind only
    · grind only [self_lt_successorAwayFromZero]
    · grind only

/--
info: 'PackedFloat.lt_iff_le_successorAwayFromZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms lt_iff_le_successorAwayFromZero

/--
Any number between 'x' and its successor (inclusive) must be 'x' or the successor.
-/
theorem eq_self_or_successor_of_le_of_le
    (he : 1 < e) (hs : 0 < s)
    (x : PackedFloat e s)
    (y : PackedFloat e s)
    (hxsign : x.sign = false) (hysign : y.sign = false)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite) (hyinf : ¬ y.isInfinite) :
    (x ≤ y ∧ y ≤ x.successorAwayFromZero) ↔ (y = x ∨ y = x.successorAwayFromZero) := by
  constructor
  · intros hlt
    obtain ⟨h1, h2⟩ := hlt
    by_cases hy_eq_x : y = x
    · simp [hy_eq_x]
    · have : x < y := by grind
      right
      have : x.successorAwayFromZero ≤ y := by
        apply lt_iff_le_successorAwayFromZero .. |>.mp <;> grind only
      grind only [le_iff_eq_of_isNaN, le_antisymm_of_ne_NaN]
  · intros hlt
    rcases hlt with rfl | hlt
    · simp
      apply self_le_successorAwayFromZero <;> grind only
    · subst hlt
      simp
      apply self_le_successorAwayFromZero <;> grind only

/--
info: 'PackedFloat.eq_self_or_successor_of_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_self_or_successor_of_le_of_le

/--
A number cannot be strictly between 'x' and its successor.
-/
theorem elim_self_lt_lt_successor (he : 1 < e) (hs : 0 < s)
    (x : PackedFloat e s) (y : PackedFloat e s)
    (hxsign : x.sign = false) (hysign : y.sign = false)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hlt : x < y)
    (hltsucc:  y < x.successorAwayFromZero) : False := by
  have : x.successorAwayFromZero ≤ y := by
    rw [← lt_iff_le_successorAwayFromZero] <;> grind only
  grind only [ne_of_lt, = lt_iff_ne_and_isNaN_of_isNaN', le_antisymm_of_ne_NaN, le_of_lt]

/--
info: 'PackedFloat.eq_self_or_successor_of_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_self_or_successor_of_le_of_le
