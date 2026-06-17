import Fp.Theorems.LowerUpperRound.Basic
import Fp.Theorems.LowerUpperRound.Functional

namespace Fp

#check PackedFloat.eq_getInfinity_of_lt_maxNormalNumber_of_isNaN_of_nonneg

/-- Negating `maxNormalNumber` flips the sign field and nothing else. -/
private theorem neg_maxNormalNumber_false {ep sp : Nat} :
    - PackedFloat.maxNormalNumber ep sp false = PackedFloat.maxNormalNumber ep sp true := rfl

/--
`maxNormalNumber` is a normal number or a nonzero subnormal whenever the widths
are positive. (For `ep = 1` its exponent field is zero, so it is the largest
subnormal; for `1 < ep` it is normal.)
-/
private theorem isNormOrNonzeroSubnorm_maxNormalNumber {ep sp : Nat}
    (hep : 0 < ep) (hsp : 0 < sp) (sign : Bool) :
    (PackedFloat.maxNormalNumber ep sp sign).isNormOrNonzeroSubnorm := by
  have h2ep : 2 ≤ 2 ^ ep := by
    have : 2 ^ 1 ≤ 2 ^ ep := Nat.pow_le_pow_right (by omega) hep
    omega
  have h2sp : 2 ≤ 2 ^ sp := by
    have : 2 ^ 1 ≤ 2 ^ sp := Nat.pow_le_pow_right (by omega) hsp
    omega
  have h1ep : (1#ep).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hexmax : (BitVec.allOnes ep - 1#ep).toNat = 2 ^ ep - 2 := by
    rw [BitVec.toNat_sub_of_le, BitVec.toNat_allOnes, h1ep]
    · omega
    · rw [BitVec.le_def, h1ep, BitVec.toNat_allOnes]
      omega
  have h1 : BitVec.allOnes ep - 1#ep ≠ BitVec.allOnes ep := by
    intro hcontra
    have h := congrArg BitVec.toNat hcontra
    rw [hexmax, BitVec.toNat_allOnes] at h
    omega
  simp [PackedFloat.isNormOrNonzeroSubnorm, h1]
  right
  omega

/-- The negative-signed `maxNormalNumber` has a negative rational value. -/
private theorem toRat_maxNormalNumber_true_neg {ep sp : Nat}
    (hep : 0 < ep) (hsp : 0 < sp) :
    (PackedFloat.maxNormalNumber ep sp true).toRat < 0 := by
  have h := PackedFloat.sign_iff_toRat_neg
    (isNormOrNonzeroSubnorm_maxNormalNumber hep hsp true)
  rw [PackedFloat.sign_maxNormalNumber] at h
  exact of_decide_eq_true h.symm

/--
Every finite (normal or nonzero subnormal) float is at least
`-(maxNormalNumber ep sp false).toRat = (maxNormalNumber ep sp true).toRat`.
-/
private theorem toRat_maxNormalNumber_true_le {ep sp : Nat}
    (hep : 0 < ep) (hsp : 0 < sp)
    (y : PackedFloat ep sp) (hy : y.isNormOrNonzeroSubnorm) :
    (PackedFloat.maxNormalNumber ep sp true).toRat ≤ y.toRat := by
  have hmaxneg := toRat_maxNormalNumber_true_neg hep hsp
  have h2ep : 2 ≤ 2 ^ ep := by
    have : 2 ^ 1 ≤ 2 ^ ep := Nat.pow_le_pow_right (by omega) hep
    omega
  have h1ep : (1#ep).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hsign : y.sign = true
  case neg =>
    -- `y` is nonnegative, while the negative max normal is negative.
    rw [Bool.not_eq_true] at hsign
    have h := PackedFloat.sign_iff_toRat_neg hy
    rw [hsign] at h
    have hpos : ¬ (y.toRat < 0) := by simpa using h.symm
    grind
  case pos =>
    -- `y` is negative: show `-y ≤ maxNormalNumber ep sp false` and negate back.
    have hmaxfin := isNormOrNonzeroSubnorm_maxNormalNumber hep hsp (sign := false)
    have hynegfin : (-y).isNormOrNonzeroSubnorm := by simpa using hy
    have hle : (-y) ≤ PackedFloat.maxNormalNumber ep sp false := by
      rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_nonneg_of_nonneg]
      · have hex := PackedFloat.toNat_ex_le_of_isNormOrNonzeroSubnorm (-y) hynegfin
        have hexmax : (PackedFloat.maxNormalNumber ep sp false).ex.toNat = 2 ^ ep - 2 := by
          rw [PackedFloat.ex_maxNormalNumber, BitVec.toNat_sub_of_le, BitVec.toNat_allOnes, h1ep]
          · omega
          · rw [BitVec.le_def, h1ep, BitVec.toNat_allOnes]
            omega
        have hsig : (-y).sig.toNat < 2 ^ sp := BitVec.isLt _
        have hsigmax : (PackedFloat.maxNormalNumber ep sp false).sig.toNat = 2 ^ sp - 1 := by
          rw [PackedFloat.sig_maxNormalNumber, BitVec.toNat_allOnes]
        omega
      · simp [hsign]
      · simp
      · simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hynegfin
      · simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hmaxfin
    have hrat : (-y).toRat ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
      apply PackedFloat.toRat_le_toRat_of_le hep hsp
      · simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hynegfin
      · simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hmaxfin
      · simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hynegfin
      · simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hmaxfin
      · exact hle
    rw [PackedFloat.toRat_neg] at hrat
    have hflip : (PackedFloat.maxNormalNumber ep sp true).toRat
        = - (PackedFloat.maxNormalNumber ep sp false).toRat := by
      rw [← neg_maxNormalNumber_false, PackedFloat.toRat_neg]
    grind

/--
NOTE: the conclusion of this theorem was originally stated with
`PackedFloat.getInfinity ep sp false` (i.e. `+∞`), which is **false**:
for `r` below `-maxNormal` the greatest float `≤ r` is `-∞`
(e.g. `lower 3 2 _ _ (.Number (-1000)) = getInfinity 3 2 true` by `decide`).
The sign has been corrected to `true` (`-∞`).
-/
theorem lower_Number_eq_getInfinity_of_maxNormalNumber_lt
  {ep sp : Nat}
  (hep : 0 < ep)
  (hsp : 0 < sp)
  (r : Rat)
  (hx :  r < (PackedFloat.maxNormalNumber ep sp true).toRat) :
  lower ep sp hep hsp (ExtRat.Number r) = PackedFloat.getInfinity ep sp true := by
  symm
  apply eq_lower_of_IsLawfulLower ep sp hep hsp _ _ (by simp)
  simp only [SmtLibSemantics.IsLawfulLower]
  constructor
  · -- `-∞` is below `r`.
    show (PackedFloat.getInfinity ep sp true).toExtRat ≤ ExtRat.Number r
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_getInfinity hsp]
    simp
  · -- Anything below `r` must be `-∞`, since `r` is below every finite float.
    intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number r := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']
      exact hy
    clear hy
    rw [PackedFloat.le_getInfinity_true_iff_eq hsp]
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hnan =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hnan] at hy'
      simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        exfalso
        rw [PackedFloat.toExtRat'_getInfinity hsp] at hy'
        simp at hy'
      case true => rfl
    | zeroCase sign =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [hep])] at hy'
      simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] at hy'
      have := toRat_maxNormalNumber_true_neg hep hsp
      grind
    | numCase n hn =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
      simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] at hy'
      have := toRat_maxNormalNumber_true_le hep hsp n hn
      grind


theorem upper_Number_eq_getInfinity_of_maxNormalNumber_lt
  {ep sp : Nat}
  (hep : 0 < ep)
  (hsp : 0 < sp)
  (r : Rat)
  (hx : (PackedFloat.maxNormalNumber ep sp false).toRat < r) :
  upper ep sp hep hsp (ExtRat.Number r) = PackedFloat.getInfinity ep sp false := by
  have hflip : (PackedFloat.maxNormalNumber ep sp true).toRat
      = - (PackedFloat.maxNormalNumber ep sp false).toRat := by
    rw [← neg_maxNormalNumber_false, PackedFloat.toRat_neg]
  rw [upper, ExtRat.ExtRat.neg_number]
  rw [lower_Number_eq_getInfinity_of_maxNormalNumber_lt hep hsp (-r) (by grind)]
  simp

end Fp
