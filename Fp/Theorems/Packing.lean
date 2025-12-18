import Fp.Basic
import Fp.Packing

def Bool.toSign (b : Bool) : Int :=
  if b then -1 else 1

-- TODO: upstream
theorem BitVec.toNat_clz_le (x : BitVec w) : x.clz.toNat ≤ w := by
  conv =>
    rhs
    rw [show w = (BitVec.ofNat w w).toNat by simp]
  simp only [← BitVec.ule_iff_toNat_le, BitVec.ule_iff_le]
  apply BitVec.clz_le

theorem BitVec.toNat_shiftLeft_clz (x : BitVec w)
  : (x <<< x.clz).toNat = x.toNat <<< x.clz.toNat := by
  simp
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := BitVec.toNat_lt_two_pow_sub_clz (x := x)
  have := BitVec.clz_le (x := x)
  have : x.clz.toNat ≤ w := BitVec.toNat_clz_le x
    -- simp [BitVec.clz_le (x := x)]
  conv =>
    rhs
    rw [show w = (w - x.clz.toNat) + x.clz.toNat by grind]
  simp [Nat.pow_add]
  apply Nat.mul_lt_mul_of_pos_right
  · grind
  · exact Nat.two_pow_pos x.clz.toNat


namespace UnpackedFloat

theorem toRat_eq {uf : UnpackedFloat e s}
  : uf.toRat = uf.sign.toSign * uf.sig.toNat * 2 ^ (uf.ex.toInt - (s - 1)) := by
  have hmsb : (uf.sig.setWidth' _).msb = false := BitVec.msb_setWidth'_of_lt (Nat.lt_succ_self s)
  simp only [toRat, toDyadic, BitVec.neg_eq, cond_eq_ite, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
    Int.neg_sub, Bool.toSign]
  congr
  split
  · simp only [Rat.intCast_neg, Rat.intCast_ofNat, ← Rat.intCast_natCast, Rat.neg_mul, Rat.one_mul]
    rewrite [← Rat.intCast_neg]
    congr
    rewrite [← Int.neg_inj, BitVec.neg_toInt_neg hmsb]
    simp
  · rewrite [BitVec.toInt_eq_toNat_of_msb hmsb]
    simp [Rat.intCast_natCast]

theorem toDyadic_eq {uf : UnpackedFloat e s}
  : uf.toDyadic = uf.sign.toSign * uf.sig.toNat * (.ofOdd 1 ((s - 1) - uf.ex.toInt) rfl) := by
  simpa [← Dyadic.toRat_inj, Dyadic.toRat_ofOdd_eq_mul_two_pow, Int.neg_sub] using toRat_eq

@[simp]
theorem toDyadic_mkZero_eq_zero {e s : Nat} {sign : Bool}
  : (@UnpackedFloat.mkZero e s sign).toDyadic = 0 := by
  simp [toDyadic, mkZero]

@[simp]
theorem toDyadic_sig_zero_eq_toDyadic_mkZero {uf : UnpackedFloat e s}
  : uf.sig = 0 → uf.toDyadic = 0 := by
  simp +contextual [toDyadic]

@[simp]
theorem toRat_mkZero_eq_zero {e s : Nat} {sign : Bool}
  : (@UnpackedFloat.mkZero e s sign).toRat = 0 := by
  simp [toRat, mkZero]

@[simp]
theorem toRat_sig_zero_eq_toRat_mkZero {uf : UnpackedFloat e s}
  : uf.sig = 0 → uf.toRat = 0 := by
  simp +contextual [toRat]

theorem two_mul_sigWidth_lt_exponentWidth :
  2 * s < 2 ^ (exponentWidth e s) := by
  simp only [exponentWidth]
  sorry

theorem toRat_normalize_eq_toRat {uf : UnpackedFloat e s}
  (hse : 2 * s < 2 ^ e)
  (hex : !uf.ex.ssubOverflow (BitVec.setWidth e uf.sig.clz))
  : uf.normalize.toRat = uf.toRat := by
  -- simp only []
  simp only [normalize, Bool.cond_eq_ite, beq_iff_eq, BitVec.clz_eq_iff_eq_zero]
  split
  · simp_all []
  · simp only [toRat_eq, Rat.mul_assoc]
    congr 1
    simp only [BitVec.toNat_shiftLeft_clz, Nat.shiftLeft_eq, Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_assoc]
    congr
    rewrite [← Rat.zpow_natCast, ← Rat.zpow_add, ← Int.add_sub_assoc]
    congr 2
    have hle : -↑(2 ^ e : Nat) ≤ ↑uf.sig.clz.toNat * (2 : Int) := by grind
    have hlt : ↑uf.sig.clz.toNat * (2 : Int) < ↑(2 ^ e : Nat) := by
      have : uf.sig.clz.toNat ≤ s := by
        suffices h : uf.sig.clz.toNat ≤ (↑s : BitVec s).toNat from by
          simpa using h
        simp only [← BitVec.ule_iff_toNat_le, BitVec.ule_iff_le, BitVec.clz_le]
      grind [BitVec.clz_le, ← BitVec.ule_iff_le, BitVec.ule_iff_toNat_le]
    rewrite [BitVec.toInt_sub_of_not_ssubOverflow, BitVec.toInt_setWidth, Int.bmod_eq_of_le_mul_two hle hlt]
    · grobner
    · simpa using hex
    · decide

end UnpackedFloat
