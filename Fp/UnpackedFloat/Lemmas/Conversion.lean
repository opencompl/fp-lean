import Fp.UnpackedFloat.Lemmas.Normalize

/-!
## UnpackedFloat rational/conversion lemmas

Lemmas about toDyadic/toRat/toRat'/toSigNat/toExpInt.
-/

namespace UnpackedFloat

@[simp]
theorem toRat_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).toRat = 0 := by
  simp [mkZero, toRat, toDyadic]


@[simp]
theorem toNat_toSigNat_eq (uf : UnpackedFloat e s) :
    toSigNat uf = uf.sig.toNat := rfl

@[simp]
theorem toSigNat_of_sig_eq_zero (uf : UnpackedFloat e s)  (h : uf.sig = 0#s) :
    uf.toSigNat = 0 := by
  simp [toSigNat, h]

@[simp]
theorem toExpInt_neg (uf : UnpackedFloat e s) :
  (- uf).toExpInt prec = uf.toExpInt prec := by
  simp [toExpInt]

@[simp]
theorem toRat'_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).toRat' prec = 0 := by
  simp [mkZero, toRat']

@[simp, grind =>]
theorem toRat'_eq_zero_iff_isZero (uf : UnpackedFloat e s) (prec : Nat) :
    uf.isZero ↔ uf.toRat' prec = 0 := by
  simp [toRat']
  simp [UnpackedFloat.isZero]
  grind only [= BitVec.toNat_zero, = BitVec.ofNat_toNat, = BitVec.getElem_zero,
    = BitVec.getElem_setWidth, = BitVec.getLsbD_eq_getElem, #b51e, #2e5b]

@[simp, grind =>]
theorem toRat'_ne_zero_iff_not_isZero (uf : UnpackedFloat e s) :
    ¬ uf.isZero ↔ ¬ uf.toRat' prec = 0 := by
  have := uf.toRat'_eq_zero_iff_isZero  prec
  grind

theorem toInt_setWidth_succ_eq_toNat (x : BitVec w) :
    (x.setWidth (w + 1)).toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp
  · grind only [= BitVec.msb_eq_getMsbD_zero, = BitVec.getMsbD_setWidth]

theorem toRat_eq_toRat' (uf : UnpackedFloat e s) : uf.toRat = uf.toRat' := by
  rw [toRat, toRat']
  rw [UnpackedFloat.toDyadic]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  simp only [BitVec.setWidth'_eq]
  rw [toInt_setWidth_succ_eq_toNat (x := uf.sig)]
  simp [toExpInt]
  norm_cast

@[grind =>, simp]
theorem toRat'_eq_zero_of_isZero (uf : UnpackedFloat e s) (hz : uf.isZero) :
    uf.toRat' prec = 0 := by
  simp [toRat']
  simp [UnpackedFloat.isZero] at hz
  simp [hz]

@[simp]
theorem toRat'_neg (uf : UnpackedFloat e s) :
    (- uf).toRat' prec = - uf.toRat' prec := by
  simp [toRat']
  grind only



theorem two_zpow_mul_two_zpow_neg_eq_one (z : Int) :
  (2 : Rat) ^ z * (2 : Rat) ^ (-z) = 1 := by
  rw [← Rat.zpow_add (by decide)]
  rw [show z + (-z) = 0 by grind]
  simp

/-
Use this to simplify exponentiation in Q,
since grind knows the field axioms,
and can correctly deduce from this
that these are multiplicative inverses.
-/
theorem two_pow_mul_two_pow_neg_intCast_eq_one (z : Nat) :
  (2 : Rat) ^ z * (2 : Rat) ^ (-( z : Int)) = 1 := by
  have := two_zpow_mul_two_zpow_neg_eq_one (z := z)
  simp at this ⊢
  grind only

-- TODO: find a more natural phrasing that
-- this does not overflow.
-- TODO: this is also in Fp/Theorems/Packing.lean, called 'toRat_normalize_eq_toRat'.
-- Find a way to remove this duplication.
theorem UnpackedFloat.toRat_normalize_eq {uf : UnpackedFloat e s}
  (hex : -(↑(2 ^ e) / 2) ≤ uf.ex.toInt - ↑uf.sig.clz.toNat) :
  uf.normalize.toRat = uf.toRat := by
  simp only [UnpackedFloat.toRat_eq_toRat']
  simp only [toRat', sign_normalize, beq_iff_eq, ite_self]
  rw [UnpackedFloat.normalize]
  by_cases hsig : uf.sig = 0#s
  · simp [hsig]
  · simp only [show ¬uf.sig == 0#s by grind, BitVec.shiftLeft_eq', cond_false]
    simp only [toNat_toSigNat_eq]
    rw [toNat_shiftLeft_clz_eq_toNat]
    simp only [toExpInt, BitVec.toInt_sub, BitVec.toInt_setWidth,
      Int.sub_bmod_bmod]

    have : uf.ex.toInt.bmod (2^e) = uf.ex.toInt := by
      rw [BitVec.toInt_eq_toNat_bmod]
      simp
    have hbmod : (uf.ex.toInt - uf.sig.clz.toNat).bmod (2^e) = uf.ex.toInt - uf.sig.clz.toNat := by
      rw [Int.bmod_eq_of_le]
      · grind
      · grind only [usr BitVec.two_mul_toInt_lt]
    rw [hbmod]
    have := BitVec.toNat_lt_two_pow_sub_clz (x := uf.sig) (w := s)
    rw [Nat.shiftLeft_eq]
    simp
    push_cast
    simp only [Int.neg_sub]
    simp only [Rat.zpow_sub_eq_zpow_mul_zpow (b := 2) (hb := by decide)]
    grind only [two_pow_mul_two_pow_neg_intCast_eq_one]
end UnpackedFloat
