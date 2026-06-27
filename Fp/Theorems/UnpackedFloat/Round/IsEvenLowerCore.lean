import Fp.Theorems.UnpackedFloat.Round.LowerUpper

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

end Fp
