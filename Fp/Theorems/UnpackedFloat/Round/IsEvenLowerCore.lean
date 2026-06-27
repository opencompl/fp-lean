import Fp.Theorems.UnpackedFloat.Round.LowerUpper
import Fp.Theorems.UnpackedFloat.Round.ExtractIsEven

namespace Fp

/-! # Parity of the rounding approximants

The SMT-LIB `isEven` of a packed float is the parity of its stored significand. This file relates
that parity, for the lower/upper approximants of `x.toRat'`, to the bitblasted even predicate
`blastExtractIsEven`. The key facts: consecutive floats have opposite parity (the successor adds one
ULP, flipping the significand LSB), and the lower approximant is the packed round-toward-zero. -/

/-- Consecutive floats have opposite parity: the `successorAwayFromZero` of a finite float adds one
to the stored significand (or wraps `allOnes → 0` on an exponent carry), so its LSB flips. -/
theorem isEven_successorAwayFromZero {e s : Nat} (hs : 0 < s) (pf : PackedFloat e s)
    (hNaN : pf.isNaN = false) (hInf : pf.isInfinite = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven pf.successorAwayFromZero
      = !SmtLibSemantics.roundableIsEven_of_packedFloat.isEven pf := by
  simp only [SmtLibSemantics.isEven_roundableIsEven_of_packedFloat]
  unfold PackedFloat.successorAwayFromZero
  simp only [hNaN, hInf, Bool.false_eq_true, if_false]
  by_cases hAll : pf.sig = BitVec.allOnes s
  · -- exponent carry: new significand is `0` (even), old is `allOnes` (odd).
    rw [if_neg (by simp [hAll])]
    rw [PackedFloat.sig_sucessorAwayFromZero_exSucc, hAll, BitVec.toNat_allOnes, BitVec.toNat_zero]
    have h2 : 2 ^ s = 2 ^ (s - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    have hpos := Nat.two_pow_pos s
    have : (2 ^ s - 1) % 2 = 1 := by omega
    simp [this]
  · -- significand increment: `toNat + 1`, so the LSB flips.
    rw [if_pos hAll, PackedFloat.toNat_sig_successorAwayFromZero_sigSucc_eq_toNat_add_one pf hAll]
    rcases Nat.mod_two_eq_zero_or_one pf.sig.toNat with h | h <;>
      simp [Nat.add_mod, h]

/-- CORE: for a nonnegative, in-range, normalized `x`, the SMT-LIB `isEven` of the lower
approximant of `x.toRat'` equals the bitblasted even predicate `blastExtractIsEven x`. The lower
approximant is the packed round-toward-zero (witness), whose stored significand's LSB is exactly
`x.sig` bit `L = off + (su-(sp+1))`, matching the index `blastExtractIsEven` inspects. -/
theorem isEven_smtLibLower_eq_blastExtractIsEven_of_sign_false
    {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = x.blastExtractIsEven ep sp := by
  -- side conditions for `blastExtractIsEven_eq_not_getLsbD`.
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide (by grind) hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide (by grind) hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdiffLower, hdiffUpper⟩ :=
    shift_range (by grind) hs heu (exInt := x.ex.toInt) (by grind) hoverE
  -- the witness: `lower = pf` (uniqueness) and its packed-significand parity.
  obtain ⟨pf, hpfNotNaN, hpfLower, _, _, _, _, _, hpfParity⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hs _)
  rw [← hpflow,
    blastExtractIsEven_eq_not_getLsbD (by grind) hs heu hsu x
      hdiffLower hdiffUpper hdiffNatLe]
  simp only [SmtLibSemantics.isEven_roundableIsEven_of_packedFloat]
  -- the inspected index `I = su-(sp+2)+off+1` equals the parity index `L = off+(su-(sp+1))`.
  have hIL : su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by grind
  rw [hIL, hpfParity, ← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one
    (x.sig.toNat / 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)))) with h | h <;>
    simp [h]

/-- `+∞` has significand `0`, so it is even. -/
theorem isEven_getInfinity {e s : Nat} :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven (PackedFloat.getInfinity e s false) = true := by
  simp [SmtLibSemantics.roundableIsEven_of_packedFloat, PackedFloat.getInfinity]

/-- `maxNormalNumber` has an all-ones significand (`2^s - 1`, odd), so it is *not* even. -/
theorem isEven_maxNormalNumber {e s : Nat} (hs : 0 < s) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven (PackedFloat.maxNormalNumber e s false) = false := by
  simp [SmtLibSemantics.roundableIsEven_of_packedFloat, PackedFloat.maxNormalNumber]; grind

/-- The SMT-LIB `isEven` of the *upper* approximant for a nonnegative, in-range, normalized `x`:
when `x` needs rounding the upper is `successorAwayFromZero(lower)` (parity flips), otherwise
`upper = lower`. Either way it matches the Option-B `blastIsEvenUpper` arm for nonnegatives,
`bif needsRounding then !blastExtractIsEven else blastExtractIsEven`. Takes the finiteness of `lower`
and its successor as hypotheses (discharged at the call site, as in `blastUpperNonneg_Rel_smtLibUpper`). -/
theorem isEven_smtLibUpper_eq_of_sign_false
    {eu su ep sp : Nat}
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxsign : x.sign = false) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
    SmtLibSemantics.roundableIsEven_of_packedFloat.isEven
        (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
      = (bif x.needsRounding ep sp then !x.blastExtractIsEven ep sp else x.blastExtractIsEven ep sp) := by
  have he' : 0 < ep := by grind
  have hCore := isEven_smtLibLower_eq_blastExtractIsEven_of_sign_false
    he hs heu hsu x hxsign hxnorm hnotunder hnotover
  -- `x > 0` and `lower` is finite (in range).
  have hmsb := UnpackedFloat.msb_eq_true_of_normalize_of_not_blastIsUnderflowNonneg
    (by grind) hs heu x hxnorm hnotunder
  have hxpos : 0 < x.toRat' := by
    have h1 := UnpackedFloat.two_pow_ex_le_toRat'_of_msb_of_sign_false x (by grind) hxsign hmsb
    have h2 : (0 : Rat) < 2 ^ (x.ex.toInt) := Rat.two_pow_pos _
    grind
  have hfinL := UnpackedFloat.isNormOrNonzeroSubnorm_lower_of_in_range
    (by grind) hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hLnan : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isNaN = false := by
    simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfinL
  have hLinf : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).isInfinite = false := by
    simpa using PackedFloat.not_isInfinite_of_isNormOrSubnorm hfinL
  -- pin `lower = pf` to read off its sign and the representability bridge.
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign, _⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      (by grind) hs heu hsu x hxsign hxnorm hnotunder hnotover
  have hpflow : pf = (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) :=
    eq_of_IsLawfulLower_of_IsLawfulLower ep sp (ExtRat.Number x.toRat') pf _ hpfNotNaN
      (by simpa using not_isNaN_lower_of_ne_NaN ep sp (by grind) hs _ (by simp))
      hpfLower (lsLawfulLower_smtLibLower ep sp (by grind) hs _)
  have hsignL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).sign
      = false := by rw [← hpflow, ← hSign, sign_blastRoundTowardZero, hxsign]
  by_cases hnr : x.needsRounding ep sp = true
  · -- needs rounding: `lower < x.toRat'`.
    have hne : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        ≠ x.toRat' := by
      rw [← hpflow, ← hToRat]
      intro hcontra
      have hnotneeds := (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
        (by grind) hs heu hsu x hxsign hnotunder hnotover).mp hcontra
      rw [hnotneeds] at hnr; simp at hnr
    have hltr : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        < x.toRat' := by
      have hle := lower_toRat_le he' hs x.toRat' hfinL; grind
    by_cases hmax : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false
    · -- `lower = maxNormal`: the successor overflows, so `upper = +∞` (even). Since `maxNormal` is
      -- odd, `isEven(+∞) = true = !isEven(maxNormal) = !blastExtractIsEven`, matching the `nR` arm.
      have hbe_false : x.blastExtractIsEven ep sp = false := by
        rw [← hCore, hmax]; exact isEven_maxNormalNumber hs
      have hupinf : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp)
          = PackedFloat.getInfinity ep sp false := by
        rw [smtLibUpper_eq_upper ep sp he' hs _ (by simp)]
        apply upper_Number_eq_getInfinity_of_maxNormalNumber_lt he' hs x.toRat'
        rw [← hmax]; exact hltr
      rw [hupinf, isEven_getInfinity, hnr, hbe_false]; simp
    · -- `lower ≠ maxNormal`: the successor is finite and `upper = successor(lower)`, parity flips.
      have hfinSucc := PackedFloat.isNormOrNonzeroSubnorm_successorAwayFromZero_of_ne_maxNormal
        (by grind) hs _ hsignL hfinL hmax
      rw [upper_eq_lower_successorAwayFromZero_of_ne (by grind) hs x.toRat' hxpos hfinL hfinSucc hsignL hne,
        isEven_successorAwayFromZero hs _ hLnan hLinf, hCore, hnr]
      simp
  · -- exactly representable: `upper = lower`.
    have hnr' : x.needsRounding ep sp = false := by grind
    have hrepr : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp).toRat
        = x.toRat' := by
      rw [← hpflow, ← hToRat]
      exact (UnpackedFloat.blastRoundTowardZero_toRat'_eq_toRat'_iff_not_needsRounding
        (by grind) hs heu hsu x hxsign hnotunder hnotover).mpr hnr'
    rw [upper_eq_lower_of_lower_isNormOrNonzeroSubnorm he' hs x.toRat' hfinL hrepr, hCore, hnr']
    simp

end Fp
