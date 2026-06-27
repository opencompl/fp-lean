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

end Fp
