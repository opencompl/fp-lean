import Fp.Theorems.Division
import Fp.Theorems.StickyEquivCore
namespace Fp

theorem UnpackedFloat.divSig_toNat_eq {e s : Nat} (x y : UnpackedFloat e s)
    (hs : 0 < s) (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (x.div y).sig.toNat
      = (x.sig.toNat * 2 ^ (s + 1) / y.sig.toNat
          * 2 ^ (if 2 ^ (s + 1) ≤ x.sig.toNat * 2 ^ (s + 1) / y.sig.toNat then 0 else 1))
        ||| (if x.sig.toNat * 2 ^ (s + 1) % y.sig.toNat = 0 then 0 else 1) := by
  -- Operand bounds (from msb).
  have hxlo : 2 ^ (s - 1) ≤ x.sig.toNat := by
    have h := hx; rw [BitVec.msb_eq_decide] at h; simpa using h
  have hylo : 2 ^ (s - 1) ≤ y.sig.toNat := by
    have h := hy; rw [BitVec.msb_eq_decide] at h; simpa using h
  have hxhi : x.sig.toNat < 2 ^ s := x.sig.isLt
  have hyhi : y.sig.toNat < 2 ^ s := y.sig.isLt
  have hypos : 0 < y.sig.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hylo
  have hs1 : s - 1 + 1 = s := by omega
  have e2s : 2 ^ (s - 1) * 2 ^ (s + 1) = 2 ^ (2 * s) := by rw [← Nat.pow_add]; congr 1; omega
  have hqlo : 2 ^ s ≤ x.sig.toNat * 2 ^ (s + 1) / y.sig.toNat := by
    rw [Nat.le_div_iff_mul_le hypos]
    have h1 : 2 ^ s * y.sig.toNat < 2 ^ (2 * s) := by
      have : 2 ^ s * y.sig.toNat < 2 ^ s * 2 ^ s :=
        (Nat.mul_lt_mul_left (Nat.two_pow_pos _)).mpr hyhi
      rw [← Nat.pow_add] at this; rwa [show s + s = 2 * s by omega] at this
    have h2 : 2 ^ (2 * s) ≤ x.sig.toNat * 2 ^ (s + 1) := by
      calc 2 ^ (2 * s) = 2 ^ (s - 1) * 2 ^ (s + 1) := e2s.symm
        _ ≤ x.sig.toNat * 2 ^ (s + 1) := Nat.mul_le_mul_right _ hxlo
    omega
  have hqhi : x.sig.toNat * 2 ^ (s + 1) / y.sig.toNat < 2 ^ (s + 2) := by
    rw [Nat.div_lt_iff_lt_mul hypos]
    have h1 : x.sig.toNat * 2 ^ (s + 1) < 2 ^ (2 * s + 1) := by
      have : x.sig.toNat * 2 ^ (s + 1) < 2 ^ s * 2 ^ (s + 1) :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hxhi
      rw [← Nat.pow_add] at this; rwa [show s + (s + 1) = 2 * s + 1 by omega] at this
    have h2 : 2 ^ (2 * s + 1) ≤ 2 ^ (s + 2) * y.sig.toNat := by
      calc 2 ^ (2 * s + 1) = 2 ^ (s + 2) * 2 ^ (s - 1) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ (s + 2) * y.sig.toNat := Nat.mul_le_mul_left _ hylo
    omega
  simp only [UnpackedFloat.div]
  have hdivisor : (y.sig.setWidth' (by omega : s ≤ s + 2 + (s + 1))).toNat = y.sig.toNat := by
    rw [BitVec.toNat_setWidth']
  have hdivident : ((x.sig.setWidth' (by omega : s ≤ s + 2) ++ 0#(s + 1))).toNat
      = x.sig.toNat * 2 ^ (s + 1) := by
    rw [BitVec.toNat_append, BitVec.toNat_setWidth', BitVec.toNat_ofNat]
    simp [Nat.shiftLeft_eq]
  sorry

end Fp
