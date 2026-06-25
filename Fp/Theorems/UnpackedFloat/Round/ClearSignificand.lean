import Fp.Theorems.UnpackedFloat.Round.Util

namespace Fp


@[simp]
theorem clearSignificand_sign (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).sign = uf.sign := by
  simp [UnpackedFloat.blastClearSignificand]

@[simp]
theorem clearSignificand_ex (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).ex = uf.ex := by
  simp [UnpackedFloat.blastClearSignificand]

/-- Clearing guard/sticky bits can only decrease the significand value. -/
theorem UnpackedFloat.blastClearSignificand_sig_toNat_le (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).sig.toNat ≤ uf.sig.toNat := by
  rw [UnpackedFloat.blastClearSignificand]
  simp only [BitVec.toNat_and]
  apply Nat.and_le_left


/-- For a nonnegative unpacked float, clearing guard/sticky bits yields a nonnegative result. -/
theorem UnpackedFloat.blastClearSignificand_toRat_nonneg_of_sign_eq_false (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : uf.sign = false) :
    0 ≤ (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).toRat := by
  simp [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat']
  generalize hcleared : uf.blastClearSignificand targetExponentWidth targetSignificandWidth = cleared
  have : 0 < (2 : Rat) ^ cleared.toExpInt := by grind only [Rat.two_pow_pos]
  have hsign : cleared.sign = false := by
    simp [← hcleared, UnpackedFloat.blastClearSignificand, h]
  simp [hsign]
  grind only [Rat.mul_nonneg]



/-- For a nonnegative unpacked float, clearing guard/sticky bits rounds toward zero:
    the cleared value is at most the original value. -/
theorem UnpackedFloat.blastClearSignificand_toRat_le_of_nonneg (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (hufsign : uf.sign = false) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).toRat ≤ uf.toRat := by
  simp only [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat' , UnpackedFloat.toRat']
  generalize hcleared : uf.blastClearSignificand targetExponentWidth targetSignificandWidth = cleared
  have hsign : cleared.sign = false := by
    simp only [← hcleared, UnpackedFloat.blastClearSignificand, hufsign,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp [hsign, hufsign]
  have hexp : cleared.toExpInt = uf.toExpInt := by
    simp only [UnpackedFloat.toExpInt, ← hcleared, UnpackedFloat.blastClearSignificand,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp only [hexp, ge_iff_le]
  have : cleared.sig.toNat ≤ uf.sig.toNat := by
    rw [← hcleared]
    apply UnpackedFloat.blastClearSignificand_sig_toNat_le
  suffices (cleared.sig.toNat : Rat) ≤ (uf.sig.toNat : Rat) by
    apply Rat.mul_le_mul_of_nonneg_right
    · simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]; grind only
    · grind only [Rat.le_of_lt, Rat.two_pow_pos]
  simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]
  grind only [UnpackedFloat.blastClearSignificand]

/-- `blastClearSignificand` zeroes the guard bit and every sticky bit below it, i.e.
rounds the significand down to a multiple of `2 ^ (guardBitIndex + 1)`. -/
theorem UnpackedFloat.blastClearSignificand_sig_toNat_eq (x : UnpackedFloat eu su)
    (ep sp : Nat) :
    (x.blastClearSignificand ep sp).sig.toNat
      = x.sig.toNat / 2 ^ ((x.guardBitIndex ep sp).toNat + 1)
          * 2 ^ ((x.guardBitIndex ep sp).toNat + 1) := by
  simp only [UnpackedFloat.blastClearSignificand]
  exact BitVec.toNat_and_not_oneHotBV_or_orderEncode x.sig (x.guardBitIndex ep sp)

end Fp
