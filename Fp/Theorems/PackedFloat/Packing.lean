import Fp.Basic
import Fp.Unpacking
import Fp.Theorems.PackedFloat.ToExtRat
import Fp.UnpackedFloat.packable
import Fp.EUnpackedFloat.packable

-- TODO: upstream
theorem BitVec.toNat_clz_le {x : BitVec w} : x.clz.toNat ≤ w := by
  suffices h : x.clz.toNat ≤ (BitVec.ofNat w w).toNat from by
    simpa using h
  simp only [← BitVec.ule_iff_toNat_le, BitVec.ule_iff_le]
  apply BitVec.clz_le

theorem BitVec.toNat_clz_lt_iff_ne_zero {x : BitVec w} : x.clz.toNat < w ↔ x.toNat ≠ 0 := by
  suffices h : x.clz.toNat < (BitVec.ofNat w w).toNat ↔ x.toNat ≠ (BitVec.ofNat w 0).toNat from by
    simpa using h
  simp only [← BitVec.ult_iff_toNat_lt, BitVec.ult_iff_lt, ne_eq, BitVec.toNat_inj]
  apply BitVec.clz_lt_iff_ne_zero

theorem BitVec.toNat_shiftLeft_clz (x : BitVec w)
  : (x <<< x.clz).toNat = x.toNat <<< x.clz.toNat := by
  simp
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := BitVec.toNat_lt_two_pow_sub_clz (x := x)
  have := BitVec.clz_le (x := x)
  have : x.clz.toNat ≤ w := BitVec.toNat_clz_le
  conv =>
    rhs
    rw [show w = (w - x.clz.toNat) + x.clz.toNat by grind]
  simp [Nat.pow_add]
  apply Nat.mul_lt_mul_of_pos_right
  · grind
  · exact Nat.two_pow_pos x.clz.toNat

-- TODO: @Sid, help!
axiom BitVec.toNat_clz_cons (b : Bool) (x : BitVec w)
  : (BitVec.cons b x).clz.toNat = if b then 0 else x.clz.toNat + 1 -- := by

namespace UnpackedFloat

@[simp]
theorem mkZero_isZero {sign : Bool} : (@mkZero e s sign).isZero := by
  simp [mkZero, isZero]

@[simp]
theorem toEUnpackedFloat_not_isNaN {uf : UnpackedFloat e s}
  : uf.toEUnpackedFloat.isNaN = false := by
  simp [toEUnpackedFloat, EUnpackedFloat.isNaN]

@[simp]
theorem toEUnpackedFloat_not_isInfinite {uf : UnpackedFloat e s}
  : uf.toEUnpackedFloat.isInfinite = false := by
  simp [toEUnpackedFloat, EUnpackedFloat.isInfinite]

theorem toRat_eq {uf : UnpackedFloat e s}
  : uf.toRat = uf.sign.toSign * uf.sig.toNat * 2 ^ (uf.ex.toInt - (s - 1 : Nat)) := by
  have hmsb : (uf.sig.setWidth' _).msb = false := BitVec.msb_setWidth'_of_lt (Nat.lt_succ_self s)
  simp only [toRat, toDyadic, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
    Int.neg_sub, Bool.toSign]
  congr
  split
  · simp only [Rat.intCast_neg, Rat.intCast_ofNat, ← Rat.intCast_natCast, Rat.neg_mul, Rat.one_mul]
    rewrite [← Rat.intCast_neg]
    congr
    simp only [Int.reduceNeg, BitVec.setWidth'_eq, Int.neg_one_mul,
      Int.neg_inj]
    rw [BitVec.toInt_eq_msb_cond]
    simp only [BitVec.toNat_setWidth, Nat.lt_add_one, BitVec.toNat_mod_cancel_of_lt,
      Int.natCast_pow, Int.cast_ofNat_Int, ite_eq_right_iff]
    intros hcontra
    simp [BitVec.msb_eq_getLsbD_last] at hcontra
  · rewrite [BitVec.toInt_eq_toNat_of_msb hmsb]
    simp [Rat.intCast_natCast]

theorem toRat_eq' {uf : UnpackedFloat e s}
  : uf.toRat = uf.sign.toSign * (uf.sig.toNat / 2 ^ (s - 1)) * 2 ^ uf.ex.toInt := by
  simp only [toRat_eq, Rat.div_def, ← Rat.zpow_natCast, ← Rat.zpow_neg, Rat.mul_assoc, ← @Rat.zpow_add 2 (by decide)]
  grind

theorem toDyadic_eq {uf : UnpackedFloat e s}
  : uf.toDyadic = uf.sign.toSign * uf.sig.toNat * (.ofOdd 1 ((s - 1 : Nat) - uf.ex.toInt) rfl) := by
  simpa only [← Dyadic.toRat_inj, Dyadic.toRat_mul, Dyadic.toRat_intCast, Dyadic.toRat_natCast,
    Dyadic.toRat_ofOdd_eq_mul_two_pow, Rat.intCast_ofNat, Int.neg_sub, Rat.one_mul] using toRat_eq

@[simp]
theorem toDyadic_mkZero_eq_zero {e s : Nat} {sign : Bool}
  : (@UnpackedFloat.mkZero e s sign).toDyadic = 0 := by
  simp only [toDyadic, mkZero, BitVec.setWidth'_eq, BitVec.setWidth_zero,
    BitVec.toInt_zero, Int.mul_zero, Dyadic.ofIntWithPrec_zero]

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

-- s ≤? 2 ^ ((2 ^ (e - 1) + s - 1).log2 + 2 - 1)
--


attribute [grind ← ] Nat.pow_le_pow_of_le

theorem sigWidth_le_exponentWidth_sub_one : s ≤ 2 ^ (exponentWidth e s - 1) := by
  unfold exponentWidth
  have : s ≤ (2 ^ (e - 1) + s - 1) := by grind only [Nat.pow_pos, #5690]
  have : 2 ^ (s.log2 + 2 - 1) ≤ 2 ^ ((2 ^ (e - 1) + s - 1).log2 + 2 - 1) := by
    apply Nat.pow_le_pow_of_le
    · decide
    · grind only [→ Nat.log2_le_log2_of_le]
  simp only [Nat.add_one_sub_one] at this
  have := Nat.lt_log2_self (n := s)
  grind only

theorem sigWidth_lt_exponentWidth_sub_one : s < 2 ^ (exponentWidth e s - 1) := by
  unfold exponentWidth
  have : s ≤ (2 ^ (e - 1) + s - 1) := by grind only [Nat.pow_pos, #5690]
  have : 2 ^ (s.log2 + 2 - 1) ≤ 2 ^ ((2 ^ (e - 1) + s - 1).log2 + 2 - 1) := by
    apply Nat.pow_le_pow_of_le
    · decide
    · grind only [→ Nat.log2_le_log2_of_le]
  have := Nat.lt_log2_self (n := s)
  grind

theorem expWidth_le_exponentWidth : e ≤ exponentWidth e s := by
  unfold exponentWidth
  match e with
  | 0 => simp
  | 1 => simp
  | e + 2 =>
    simp only [Nat.add_one_sub_one, Nat.add_le_add_iff_right]
    apply Nat.le_trans (m := (2 ^ e).log2)
    · simp
    · apply Nat.log2_le_log2_of_le
      grind

theorem sigWidth_add_bias_le_exponentWidth_sub_one : s + bias e ≤ 2 ^ (exponentWidth e s - 1) := by
  simp only [bias, exponentWidth]
  grind only [!Nat.two_pow_pos, !Nat.log2_eq_iff, #569066451790c837, #ccfcc644d1be4e5b]

-- theorem expWidth_lt_exponentWidth : e < exponentWidth e s := by
--   unfold exponentWidth
--   induction e with
--   | zero => simp
--   | succ e ih =>
--     simp only [Nat.add_one_sub_one, Nat.add_lt_add_iff_right]
--     apply Nat.lt_of_lt_of_le (m := (2 ^ e).log2 + 1)
--     · simp
--     · simp only [Nat.add_le_add_iff_right]
--       apply Nat.log2_le_log2_add

theorem bias_lt_exponentWidth : bias e < 2 ^ exponentWidth e s := by
  simp only [exponentWidth, bias]
  grind only [!Nat.two_pow_pos, !Nat.log2_eq_iff, #569066451790c837, #ccfcc644d1be4e5b]

theorem bias_lt_exponentWidth_sub_one : bias e < 2 ^ (exponentWidth e s - 1) := by
  simp only [exponentWidth, bias]
  grind only [!Nat.two_pow_pos, !Nat.log2_eq_iff, #569066451790c837, #ccfcc644d1be4e5b]


theorem sigWidth_add_one_lt_exponentWidth : s + 1 < 2 ^ exponentWidth e s := by
  unfold exponentWidth
  grind only [!Nat.two_pow_pos, !Nat.log2_eq_iff, #569066451790c837, #ccfcc644d1be4e5b]


theorem toRat'_normalize_eq_toRat' {uf : UnpackedFloat e s}
  (hse : s - 1 < 2 ^ (e - 1))
  (hex : !uf.ex.ssubOverflow (BitVec.setWidth e uf.sig.clz))
  (prec : Nat)
  : uf.normalize.toRat' prec = uf.toRat' prec := by
  simp only [toRat', sign_normalize, beq_iff_eq, ite_self]
  rw [UnpackedFloat.normalize]
  by_cases hsig : uf.sig = 0#s
  · simp [hsig]
  · simp only [show ¬uf.sig == 0#s by grind, BitVec.shiftLeft_eq', cond_false]
    simp only [toNat_toSigNat_eq]
    rw [toNat_shiftLeft_clz_eq_toNat]
    simp only [toExpInt]
    have hSigClzNeZero : uf.sig.clz < s := BitVec.clz_lt_iff_ne_zero.mpr hsig
    have hSigClzNeZero' : uf.sig.clz.toNat < s := by
      rw [BitVec.lt_def] at hSigClzNeZero
      simp at hSigClzNeZero
      apply (toNat_clz_lt_iff_ne_zero ..) |>.mpr hsig
    have hsub : (uf.ex - BitVec.setWidth e uf.sig.clz).toInt
        = uf.ex.toInt - uf.sig.clz.toNat := by
      rewrite [BitVec.toInt_sub_of_not_ssubOverflow (by grind)]
      have hle : -((2 ^ e : Nat) / 2 : Int) ≤ ↑uf.sig.clz.toNat := by grind
      rw [BitVec.toInt_setWidth]
      have : (uf.sig.clz.toNat : Int).bmod (2 ^ e) = uf.sig.clz.toNat := by
        refine Int.bmod_eq_of_le hle ?_
        have : (2 ^ e + 1) / 2 = 2 ^ (e - 1) := by cases e <;> grind
        grind
      simp [this]
    rw [hsub]
    have := BitVec.toNat_lt_two_pow_sub_clz (x := uf.sig) (w := s)
    rw [Nat.shiftLeft_eq]
    simp
    push_cast
    simp only [Int.neg_sub]
    simp only [Rat.zpow_sub_eq_zpow_mul_zpow (b := 2) (hb := by decide)]
    grind only [two_pow_mul_two_pow_neg_intCast_eq_one]

theorem toRat_normalize_eq_toRat {uf : UnpackedFloat e s}
  (hse : s - 1 < 2 ^ (e - 1))
  (hex : !uf.ex.ssubOverflow (BitVec.setWidth e uf.sig.clz))
  : uf.normalize.toRat = uf.toRat := by
  simp only [normalize, Bool.cond_eq_ite, beq_iff_eq]
  split
  · simp_all
  case isFalse h =>
    simp only [toRat_eq, Rat.mul_assoc]
    congr 1
    simp only [BitVec.toNat_shiftLeft_clz, Nat.shiftLeft_eq, Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_assoc]
    congr
    rewrite [← Rat.zpow_natCast, ← Rat.zpow_add, ← Int.add_sub_assoc]
    congr 2
    have hle : -((2 ^ e : Nat) / 2 : Int) ≤ ↑uf.sig.clz.toNat := by grind
    rewrite [BitVec.toInt_sub_of_not_ssubOverflow]
    · have hSigClzNeZero : uf.sig.clz < s := by
        exact BitVec.clz_lt_iff_ne_zero.mpr h
      have hSigClzNeZero' : uf.sig.clz.toNat < s := by
        rw [BitVec.lt_def] at hSigClzNeZero
        simp at hSigClzNeZero
        apply (toNat_clz_lt_iff_ne_zero ..) |>.mpr h
      rw [BitVec.toInt_setWidth]
      have : (uf.sig.clz.toNat : Int).bmod (2 ^ e) = uf.sig.clz.toNat := by
        refine Int.bmod_eq_of_le hle ?_
        have : (2 ^ e + 1) / 2 = 2 ^ (e - 1) := by cases e <;> grind
        grind
      simp [this]
      grind
    · grobner
    · simp

end UnpackedFloat

namespace EUnpackedFloat

@[simp]
theorem mkNaN_isNaN : (@mkNaN e s).isNaN := by
  simp [mkNaN, isNaN]

@[simp]
theorem mkNaN_not_isInfinite : (@mkNaN e s).isInfinite = false := by
  simp [mkNaN, isInfinite]

@[simp]
theorem mkInfinity_isInfinite {sign : Bool} : (@mkInfinity e s sign).isInfinite := by
  simp [mkInfinity, isInfinite]

@[simp]
theorem mkInfinity_not_isNaN {sign : Bool} : (@mkInfinity e s sign).isNaN = false := by
  simp [mkInfinity, isNaN]

@[simp]
theorem mkZero_isZero {sign : Bool} : (@mkZero e s sign).isZero := by
  simp [mkZero, isZero, isNumber]

@[simp]
theorem mkZero_not_isNaN {sign : Bool} : (@mkZero e s sign).isNaN = false := by
  simp [mkZero, isNaN]

@[simp]
theorem mkZero_not_isInfinite {sign : Bool} : (@mkZero e s sign).isInfinite = false := by
  simp [mkZero, isInfinite]

end EUnpackedFloat

namespace PackedFloat

example {x y : α} [Decidable c] (f : α → β) : f (if c then x else y) = if c then f x else f y := by
  exact apply_ite f c x y

@[simp]
theorem sig_ne_zero_of_isNonzeroSubnorm {pf : PackedFloat e s}
  : pf.isNonzeroSubnorm → pf.sig.toNat ≠ 0 := by
  grind [isNonzeroSubnorm]

theorem exp_lt_max_of_isNorm {pf : PackedFloat e s}
  : pf.isNorm → pf.ex.toNat < 2 ^ e - 1 := by
  grind [isNorm, BitVec.allOnes, BitVec.ofNatLT_toNat]

theorem bias_fits₁ : -2 ^ (exponentWidth e s - 1) ≤ (bias e : Int) := by
  apply Int.le_trans (b := 0)
  · simp only [Int.neg_le_zero_iff]
    norm_cast
    simp
  · norm_cast
    simp [bias]

theorem minNormalExp_fits₁ : -2 ^ (exponentWidth e s - 1) ≤ minNormalExp e := by
  unfold minNormalExp
  simp only [Int.neg_le_neg_iff]
  norm_cast
  simp only [bias, exponentWidth]
  grind only [!Nat.two_pow_pos, !Nat.log2_eq_iff, #569066451790c837, #542258ac646a68ca,
    #ccfcc644d1be4e5b]

theorem minNormalExp_fits₂ : minNormalExp e < 2 ^ (exponentWidth e s - 1) := by
  apply Int.lt_of_le_of_lt (b := 0)
  · grind [minNormalExp]
  · norm_cast
    apply Nat.two_pow_pos

theorem exponentWidth_gt_zero : exponentWidth e s > 0 := by
  simp [exponentWidth]

-- | TODO: refactor by pulling out lemmas that talk about the 'toNat' of the various
-- significand, and so on.
theorem toExtRat_unpack_eq_toExtRat {pf : PackedFloat e s}
  : pf.unpack.toExtRat = pf.toExtRat := by
  simp only [unpack, unpackNum, BitVec.truncate_eq_setWidth, toExtRat_eq_toExtRat']
  cases hNaN : pf.isNaN
  · cases hInf : pf.isInfinite
    · cases hZero : pf.isZero
      · cases hNorm : pf.isNorm
        · simp only [EUnpackedFloat.toExtRat, Bool.false_eq_true, ↓reduceIte, cond_false,
          EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
          EUnpackedFloat.num_mkNumber, toExtRat', hNaN, hInf, ExtRat.Number.injEq]
          simp only [toRat, PackedFloat.toRatSig, PackedFloat.toRatExp]
          simp only [hNorm, Bool.false_eq_true, ↓reduceIte,
            Rat.zero_add]
          rewrite [UnpackedFloat.toRat_normalize_eq_toRat UnpackedFloat.sigWidth_lt_exponentWidth_sub_one]
          · simp only [UnpackedFloat.toRat_eq, Rat.mul_assoc]
            congr 1
            simp only [BitVec.toNat_cons, Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_or, Rat.div_def, Rat.mul_assoc]
            congr
            simp only [← Rat.zpow_natCast, ← Rat.zpow_neg, ← @Rat.zpow_add 2 (by decide)]
            simp only [BitVec.toInt_ofInt_eq_self exponentWidth_gt_zero minNormalExp_fits₁ minNormalExp_fits₂]
            simp only [minNormalExp]
            grind
          · simp only [Nat.add_one_sub_one, Bool.not_eq_eq_eq_not, Bool.not_true]
            simp only [BitVec.ssubOverflow_eq]
            simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not,
              Bool.not_false]
            have hSubnorm : pf.isNonzeroSubnorm = true := by
              grind [PackedFloat.classification_exhaustive]
            have hClz : pf.sig.clz.toNat < s := BitVec.toNat_clz_lt_iff_ne_zero.mpr (sig_ne_zero_of_isNonzeroSubnorm hSubnorm)
            have he0 : e > 0 := PackedFloat.expWidth_ge_one_of_isNonzeroSubnorm hSubnorm
            constructor
            · left; right
              simp only [BitVec.msb_eq_toNat, BitVec.toNat_setWidth, ge_iff_le,
                decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_clz_cons]
              rewrite [Nat.mod_eq_of_lt]
              · grind [UnpackedFloat.sigWidth_lt_exponentWidth_sub_one]
              · grind [UnpackedFloat.sigWidth_add_one_lt_exponentWidth]
            · right
              simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.toInt_ofInt,
                BitVec.toInt_setWidth, Int.sub_bmod_bmod, Int.bmod_sub_bmod, decide_eq_true_eq]
              rewrite [Int.bmod_eq_of_le]
              · simp [minNormalExp]
                have : (BitVec.cons false pf.sig).clz.toNat ≥ 1 := by
                  simp [BitVec.toNat_clz_cons]
                omega
              · apply Int.le_of_neg_le_neg
                have hexpWidth : 2 ^ 1 ∣ 2 ^ exponentWidth e s := Nat.pow_dvd_pow 2 (by grind [UnpackedFloat.expWidth_le_exponentWidth])
                simp only [minNormalExp, BitVec.toNat_clz_cons, Int.neg_sub, Int.sub_neg,
                  Int.natCast_pow, Int.cast_ofNat_Int, Int.neg_neg]
                norm_cast
                simp only [bias, exponentWidth]
                grind only [usr Nat.pow_pos, !Nat.log2_eq_iff, #569066451790c837, #542258ac646a68ca,
                  #ccfcc644d1be4e5b]
              · simp only [minNormalExp, Int.natCast_pow, Int.cast_ofNat_Int]
                have : (2 ^ exponentWidth e s + 1) / (2 : Int) = 2 ^ (exponentWidth e s - 1) := by
                  cases exponentWidth e s <;> grind
                rewrite [this]
                simp only [exponentWidth, Nat.add_one_sub_one, gt_iff_lt, Int.sub_eq_add_neg, ← Int.neg_add, ← Int.natCast_add]
                apply Int.lt_of_le_of_lt (b := 0)
                · simp [Int.neg_le_zero_iff]
                  norm_cast
                  simp
                · simp [Int.pow_pos]
        ·
          simp only [EUnpackedFloat.toExtRat, ↓reduceIte, cond_false,
          EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
          EUnpackedFloat.num_mkNumber, toExtRat', hNaN, hInf,
          ExtRat.Number.injEq]
          simp only [toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, hNorm, if_true]
          simp only [UnpackedFloat.toRat_eq, Rat.mul_assoc]
          congr 1
          simp only [BitVec.toNat_cons', Nat.shiftLeft_eq, Bool.toNat, cond_true]
          have he0 : e > 0 := Nat.lt_trans Nat.zero_lt_one (PackedFloat.expWidth_ge_two_of_isNorm hNorm)
          have he1 : e > 1 := PackedFloat.expWidth_ge_two_of_isNorm hNorm
          have : (BitVec.zeroExtend (exponentWidth e s) pf.ex - BitVec.ofNat (exponentWidth e s) (bias e)).toInt =
              pf.ex.toNat - bias e := by
            simp only [BitVec.truncate_eq_setWidth, bias, BitVec.toInt_sub, BitVec.toInt_setWidth,
              BitVec.toInt_ofNat', Int.natCast_sub (Nat.two_pow_pos _), Int.natCast_pow,
              Int.cast_ofNat_Int, Nat.succ_eq_add_one, Nat.zero_add, Int.sub_bmod_bmod,
              Int.bmod_sub_bmod]
            rewrite [Int.bmod_eq_of_le]
            · rfl
            · apply Int.le_of_neg_le_neg
              simp only [Int.neg_sub, Int.natCast_pow, Int.cast_ofNat_Int, Int.neg_neg]
              apply Int.le_trans (b := 2 ^ (e - 1))
              · omega
              · norm_cast
                apply Nat.le_of_mul_le_mul_right (c := 2) _ (by decide)
                have he : 2 ^ 1 ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
                have hexpWidth : 2 ^ 1 ∣ 2 ^ exponentWidth e s := Nat.pow_dvd_pow 2 (by grind [UnpackedFloat.expWidth_le_exponentWidth])
                simp only [Nat.pow_pred_div he0, Nat.div_mul_cancel he, Nat.div_mul_cancel hexpWidth]
                apply Nat.pow_le_pow_of_le (by decide)
                apply UnpackedFloat.expWidth_le_exponentWidth
            · simp [Int.two_pow_succ_div_two]
              apply Int.lt_of_lt_of_le (b := 2 ^ (e - 1))
              · simp only [Int.sub_eq_add_neg, Int.reduceNeg, Int.neg_add, Int.neg_neg]
                norm_cast
                have : pf.ex.toNat < 2 ^ e - 1 := exp_lt_max_of_isNorm hNorm
                have : 2 ^ 1 ∣ 2 ^ e := Nat.pow_dvd_pow 2 he0
                simp only [Nat.pow_pred_div he0, Int.natCast_ediv]
                simp
                grind
              · norm_cast
                apply Nat.pow_le_pow_of_le (by decide)
                grind [UnpackedFloat.expWidth_le_exponentWidth]
          rewrite [this]
          simp only [Nat.one_mul, Rat.natCast_add, Rat.natCast_pow, Rat.natCast_ofNat,
            Nat.add_one_sub_one, @Int.sub_eq_add_neg _ s, @Rat.zpow_add 2 (by decide)]
          rw [Rat.mul_comm _ (2 ^ (-s : Int)), ← Rat.mul_assoc, Rat.add_mul, ← Rat.zpow_natCast, ← Rat.zpow_add (by decide) s (-s), Int.add_neg_eq_sub, Int.sub_self, Rat.zpow_zero, Rat.zpow_neg, ← Rat.div_def]
      · simp only [EUnpackedFloat.toExtRat, cond_true, cond_false, EUnpackedFloat.mkZero_not_isNaN,
        EUnpackedFloat.mkZero_not_isInfinite, toExtRat', hNaN, hInf]
        simp [EUnpackedFloat.mkZero]
        simp [hZero]
    · simp only [EUnpackedFloat.toExtRat, cond_true, cond_false,
      EUnpackedFloat.mkInfinity_not_isNaN, EUnpackedFloat.mkInfinity_isInfinite, toExtRat', hNaN,
      hInf]
      simp [EUnpackedFloat.mkInfinity]
  · simp only [EUnpackedFloat.toExtRat, cond_true, EUnpackedFloat.mkNaN_isNaN, toExtRat', hNaN]



/--
info: 'PackedFloat.toExtRat_unpack_eq_toExtRat' depends on axioms: [propext,
 BitVec.toNat_clz_cons,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms toExtRat_unpack_eq_toExtRat

@[simp]
theorem toExtRat_unpack_eq_toExtRat' (pf : PackedFloat e s) :
    pf.unpack.toExtRat = pf.toExtRat' := by
  rw [← PackedFloat.toExtRat_eq_toExtRat']
  exact toExtRat_unpack_eq_toExtRat

/--
This shows that calling 'toRat' agrees with 'toExtRat'.
-/
theorem toRat_eq_of_toExtRat_eq_Number {pf : PackedFloat e s}
    (hpf : pf.isNormOrNonzeroSubnorm)
    {r : Rat}
    (hr : pf.toExtRat = .Number r)
    : pf.toRat = r := by
  have := pf.toExtRat_unpack_eq_toExtRat
  rw [PackedFloat.unpack] at this
  simp at this
  simp [show ¬ pf.isNaN by grind, show ¬ pf.isInfinite by grind] at this
  by_cases hz : pf.isZero
  · simp [hz] at this
    rw [PackedFloat.toExtRat_eq_toExtRat'] at hr
    simp [PackedFloat.toExtRat'] at hr
    simp [show ¬ pf.isNaN by grind, show ¬ pf.isInfinite by grind] at hr
    exact hr
  · simp [hz] at this
    simp [PackedFloat.toExtRat'] at hr
    simp [show ¬ pf.isNaN by grind, show ¬ pf.isInfinite by grind] at hr
    exact hr


/-- the unpacked value as a rational number equals the packed float as a rational number. -/
@[simp, grind =]
theorem unpackNum_toRat_eq_toRat {pf : PackedFloat e s}
    (hpf : pf.isNormOrNonzeroSubnorm)
    : pf.unpackNum.toRat = pf.toRat := by
  have hunpack := pf.toExtRat_unpack_eq_toExtRat'
  rw [pf.unpack_eq_unpackNum_of hpf] at hunpack
  rw [pf.toExtRat'_eq_toRat_of hpf] at hunpack
  simp at hunpack
  exact hunpack

end PackedFloat


namespace EUnpackedFloat

/-- Packing a NaN gives a NaN PackedFloat. -/
@[simp]
theorem isNaN_pack'_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isNaN) :
    uf.pack'.isNaN = true := by
  simp only [isNaN_eq_decide, decide_eq_true_eq] at huf ⊢
  simp only [PackedFloat.isNaN, pack', isNaN_eq_decide, huf, decide_true, ↓reduceIte,
    PackedFloat.ex_getNaN, BEq.rfl, PackedFloat.sig_getNaN, BitVec.zero_eq, Bool.true_and,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, BitVec.intMin_eq_zero_iff]
  grind only


/-
@[simp]
theorem isNaN_of_isNaN_pack (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.normalize = uf)
    (hexp1 : uf.exp.toInt ≤ maxNormalExp e)
    (hexp2 : minSubnormalExp e s ≤ uf.exp.toInt) -- recall that we want normalzed ufs.
    (huf : uf.pack.isNaN) :
    uf.isNaN = true := by
  simp [pack, PackedFloat.isNaN] at huf ⊢
  by_cases hnan : uf.isNaN
  · simp [hnan]
  · simp [hnan] at huf
    by_cases hinf : uf.isInfinite
    · simp [hinf] at huf
      grind only
    · simp [hinf] at huf
      by_cases hzero : uf.isZero
      · simp [hzero] at huf
        grind only
      · simp [hzero] at huf
        split at huf
        case neg.isTrue hle =>
          simp [hle] at huf
          grind
        case neg.isFalse hle =>
          -- simp at hle
          simp [hle] at huf
          simp at hle
          obtain ⟨huf1, huf2⟩ := huf
          rcases huf2 with huf2 | huf2
          · grind only
          · rw [BitVec.sle_eq_decide] at hle
            rw [toInt_ofInt_minNormalExp_eq_minNormalExp he hs] at hle
            simp at hle
            obtain huf1 := BitVec.toInt_inj .. |>.mpr huf1
            simp only [BitVec.toInt_setWidth] at huf1
            rw [BitVec.toNat_add] at huf1
            rw [toNat_ofNat_bias_eq_bias he hs] at huf1
            rw [BitVec.toInt_allOnes] at huf1
            simp [show 0 < e by grind only] at huf1


@[simp, grind .]
theorem pack_isNaN_eq_isNaN (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack'.isNaN = uf.isNaN := by
  have h1 := isNaN_pack'_of_isNaN uf
  have h2 := isNaN_of_isNaN_pack he hs uf
  grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN, #9c18]
-/


/--
Packing an infinity gives an infinite PackedFloat. Requires `0 < s` because with no sig bits,
the PackedFloat infinity encoding aliases NaN.
-/
@[simp, grind .]
theorem isInfinite_pack'_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack'.isInfinite = true := by
  have hnan : uf.isNaN = false := by
    simp [isNaN, isInfinite] at huf ⊢
    grind
  simp [pack', PackedFloat.isInfinite, huf, hnan]
  grind

/-- Packing preseves the sign of non-NaN variables. -/
@[simp, grind .]
theorem sign_pack
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack.sign = if uf.isNaN then false else uf.sign := by
  simp [pack, EUnpackedFloat.sign]
/--
Packing then unpacking an infinity recovers `mkInfinity` with the same sign.
-/
@[simp, grind .]
theorem unpack_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack.unpack = EUnpackedFloat.mkInfinity uf.sign := by
  rw [pack_eq_pack', pack'_eq_getInfinity_of_isInfinite uf huf,
    PackedFloat.unpack_getInfinity]
  simp [hs]

/--
Packing then unpacking a NaN yields `mkNaN`.
The PackedFloat's NaN status is preserved by `isNaN_pack_of_isNaN`, so unpack takes the NaN branch.
-/
@[simp, grind .]
theorem unpack_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isNaN) :
    uf.pack.unpack = EUnpackedFloat.mkNaN := by
  rw [pack_eq_pack', pack'_eq_getNaN_of_isNaN uf huf]
  exact PackedFloat.unpack_eq_NaN_of_isNaN _ PackedFloat.isNaN_getNaN

/-! ### Helper lemmas for the Number round-trip

The main `unpack_pack_of_isNumber` proof below is a 3-way case split (zero / normal / subnormal).
Each branch is pushed into its own `sorry` lemma below; those are the "real" content left to prove.
-/

/--
For a bitvec with its top bit set, re-inserting that top bit via `cons` after dropping it with
`setWidth` is the identity.
-/
@[simp]
theorem BitVec.cons_true_setWidth_of_msb {n : Nat}
    (x : BitVec (n + 1)) (hmsb : x.msb = true) :
    BitVec.cons true (x.setWidth n) = x := by
  ext i hi
  by_cases hi : i = n
  · grind only [= BitVec.msb_eq_getMsbD_zero, = BitVec.getElem_cons, = BitVec.getMsbD_eq_getLsbD,
    = BitVec.getLsbD_eq_getElem]
  · grind only [= BitVec.getElem_cons, = BitVec.getElem_setWidth, = BitVec.getLsbD_eq_getElem]


/--
For a normalized Number-state `uf`, `¬ uf.isZero` implies the significand is nonzero.
-/
theorem sig_ne_zero_of_isNumber_of_not_isZero_of_normalize
    (uf : EUnpackedFloat e s)
    (hNum : uf.isNumber)
    (hZ : ¬ uf.isZero)
    -- | TODO: why do I need hnorm?
    (hnorm : uf.num.normalize = uf.num) :
    uf.num.sig ≠ 0#s := by
  intro hsig
  apply hZ
  have hnormZ : uf.num.normalize = UnpackedFloat.mkZero uf.num.sign := by
    simp [UnpackedFloat.normalize, hsig]
  have heq : uf.num = UnpackedFloat.mkZero uf.num.sign := hnorm.symm.trans hnormZ
  simp only [EUnpackedFloat.isZero, hNum, Bool.true_and]
  rw [heq]
  simp [UnpackedFloat.isZero]

/-! #### BitVec sub-lemmas for the normal round-trip -/

@[simp, grind =>]
theorem EUnpackedFloat.isNaN_iff_state_eq
  (uf : EUnpackedFloat e s) :
  uf.isNaN ↔ (uf.state = .NaN) := by simp [isNaN]

@[simp, grind =>]
theorem EUnpackedFloat.isInfinite_iff_state_eq
  (uf : EUnpackedFloat e s) :
  uf.isInfinite ↔ (uf.state = .Infinity) := by simp [isInfinite]

@[simp, grind =>]
theorem EUnpackedFloat.isNumber_iff_state_eq
  (uf : EUnpackedFloat e s) :
  uf.isNumber ↔ (uf.state = .Number) := by simp [isNumber]

/-! ### Corollary: `toExtRat` preservation -/

@[simp]
theorem pack_mkNaN_eq_isNaN :
    (EUnpackedFloat.mkNaN).pack = PackedFloat.getNaN e s := by
  simp [pack, PackedFloat.getNaN, mkNaN,
  EUnpackedFloat.sign, EUnpackedFloat.isNaN]

@[simp]
theorem pack_mkInfinity_eq_isInfinite {sign : Bool} :
    (EUnpackedFloat.mkInfinity sign).pack = PackedFloat.getInfinity e s sign := by
  simp [pack, PackedFloat.getInfinity, mkInfinity, EUnpackedFloat.sign,
    EUnpackedFloat.isInfinite, isNaN]
  grind only

@[simp]
theorem State.beq_eq_decide_eq {x y : State} :
    (x == y) = decide (x = y) := by
  grind [State]

set_option maxHeartbeats 1000000 in
/--
Packing a Number-state unpacked float preserves its rational value.

NOTE: hypotheses `hnorm`, `hexp1`, `hexp2` were ADDED (statement strengthened) because the
bare statement is FALSE; `grep` shows no other use site. Exhaustive enumeration at
`(e, s) ∈ {(2,1), (2,2), (3,1), (3,2), (4,2)}` confirms the statement below has no
counterexamples, and that each hypothesis is necessary:
* without `hnorm` (normalization): `uf = { sign := false, ex := 0#3, sig := 1#2 }` at
  `e = 2, s = 1` has `uf.toRat = 1/2` but packs (gaining the implicit leading 1 bit)
  to a float with value `3/2`;
* without `hexp1` (exponent upper bound): `uf = { sign := false, ex := 2#3, sig := 2#2 }`
  wraps the packed exponent past `allOnes` (cf. `pack_isInfinite_eq_isInfinite` above);
* without `hexp2` (subnormal exactness): `uf = { sign := false, ex := 7#3, sig := 3#2 }`
  (value `3/4 = 1.1₂ × 2⁻¹`) loses its low bit in the subnormal right-shift and packs to
  a float with value `1/2`; the divisibility condition states precisely that the bits
  shifted out are zero, i.e. `uf` is exactly representable. Note that it holds trivially
  (with `2^0 ∣ _`) whenever `uf` is in the normal range `minNormalExp e ≤ uf.ex.toInt`,
  and for `uf.sig = 0`, so the disjunction covers the zero / normal / subnormal trichotomy.

The proof is the corresponding 3-way case split.
-/
theorem toRat_pack_mkNumber_eq_toRat
    (he : 1 < e) (hs : 0 < s)
    (uf : UnpackedFloat (exponentWidth e s) (s + 1))
    (hpack : uf.Packable) :
    (EUnpackedFloat.mkNumber uf).pack.toRat = uf.toRat := by
  obtain ⟨hnorm, hexp1, hexp2⟩ := hpack
  rw [EUnpackedFloat.pack_eq_pack']
  by_cases hzero : uf.sig = 0#(s + 1)
  case pos =>
    rw [pack'_eq_getZero_of_isZero _ (by simp [UnpackedFloat.isZero, hzero])]
    rw [PackedFloat.toRat_getZero (by omega)]
    exact (UnpackedFloat.toRat_sig_zero_eq_toRat_mkZero hzero).symm
  case neg =>
    -- basic facts
    have hmin_eq : minNormalExp e = -((bias e - 1 : Nat) : Int) := rfl
    have hmax_eq : maxNormalExp e = (bias e : Int) := rfl
    have hbias_pos : 0 < bias e := bias_pos_of_one_lt e he
    have hmsb : uf.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff uf hzero).mp hnorm
    have hsig_lt : uf.sig.toNat < 2 ^ (s + 1) := uf.sig.isLt
    have hsig_ge : 2 ^ s ≤ uf.sig.toNat := by
      have h := hmsb
      rw [BitVec.msb_eq_decide] at h
      simpa using h
    have hpow_s : (2:Nat) ^ (s + 1) = 2 ^ s * 2 := by rw [Nat.pow_succ]
    have hpowW : (2:Nat) ^ exponentWidth e s = 2 ^ (exponentWidth e s - 1) * 2 :=
      (Nat.two_pow_pred_mul_two (zero_lt_exponentWidth (e := e) (s := s))).symm
    -- reduce `pack'` to `packNumber'`
    have hZ : (EUnpackedFloat.mkNumber uf).isZero = false := by
      simp [UnpackedFloat.isZero, hzero]
    simp only [EUnpackedFloat.pack', EUnpackedFloat.isNaN_mkNumber,
      EUnpackedFloat.isInfinite_mkNumber, hZ, Bool.false_eq_true, ↓reduceIte,
      EUnpackedFloat.sign, EUnpackedFloat.sig, EUnpackedFloat.exp, EUnpackedFloat.num_mkNumber]
    rw [UnpackedFloat.toRat_eq]
    simp only [Nat.add_sub_cancel]
    by_cases hrange : minNormalExp e ≤ uf.ex.toInt
    case pos =>
      -- normal case
      have hinr : EUnpackedFloat.packNumber'.inNormalRange (s := s) (e := e) uf.ex = true :=
        (EUnpackedFloat.packNumber'.inNormalRange_iff he hs uf.ex).mpr hrange
      have hexW : e < exponentWidth e s := self_lt_exponentWidth e s he hs
      have h2bias : bias e + bias e = 2 ^ e - 2 := bias_plus_bias_eq_twoPow_minus_two e he
      have h2e4 : 4 ≤ 2 ^ e := by
        calc (4:Nat) = 2 ^ 2 := rfl
        _ ≤ 2 ^ e := Nat.pow_le_pow_of_le (by decide) he
      have hpow3 : (2:Nat) ^ e ≤ 2 ^ (exponentWidth e s - 1) :=
        Nat.pow_le_pow_of_le (by decide) (by omega)
      have hlo : 1 ≤ uf.ex.toInt + bias e := by omega
      have hhi : uf.ex.toInt + bias e ≤ 2 * bias e := by omega
      have hA : (uf.ex + BitVec.ofNat (exponentWidth e s) (bias e)).toInt
          = uf.ex.toInt + bias e := by
        rw [BitVec.toInt_add, toInt_ofNat_bias_eq_bias he hs]
        apply Int.bmod_eq_of_le <;> omega
      have hAmsb : (uf.ex + BitVec.ofNat (exponentWidth e s) (bias e)).msb = false := by
        rw [BitVec.msb_eq_toInt, hA]
        simp only [decide_eq_false_iff_not, Int.not_lt]
        omega
      have hAnat : ((uf.ex + BitVec.ofNat (exponentWidth e s) (bias e)).toNat : Int)
          = uf.ex.toInt + bias e := by
        rw [← BitVec.toInt_eq_toNat_of_msb hAmsb, hA]
      have hexPacked : EUnpackedFloat.packNumber'.exPacked (s := s) uf.ex =
          BitVec.setWidth e (uf.ex + BitVec.ofNat (exponentWidth e s) (bias e)) := by
        simp only [EUnpackedFloat.packNumber'.exPacked, hinr, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hexW)]
      have hexN : ((EUnpackedFloat.packNumber'.exPacked (s := s) uf.ex).toNat : Int)
          = uf.ex.toInt + bias e := by
        rw [hexPacked, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        exact hAnat
      have hnormPf : (EUnpackedFloat.packNumber' uf.sign uf.sig uf.ex).isNorm = true := by
        simp only [PackedFloat.isNorm, EUnpackedFloat.packNumber', BitVec.zero_eq,
          Bool.and_eq_true, bne_iff_ne, ne_eq]
        constructor
        · intro hc
          have h := congrArg BitVec.toNat hc
          simp only [BitVec.toNat_allOnes] at h
          omega
        · intro hc
          have h := congrArg BitVec.toNat hc
          simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h
          omega
      have hsigPacked : (EUnpackedFloat.packNumber'.sigPacked uf.sig uf.ex).toNat
          = uf.sig.toNat - 2 ^ s := by
        simp only [EUnpackedFloat.packNumber'.sigPacked, hinr, ↓reduceIte,
          BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
        rw [Nat.mod_eq_sub_mod hsig_ge, Nat.mod_eq_of_lt (by omega)]
      simp only [PackedFloat.toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, hnormPf,
        ↓reduceIte]
      simp only [EUnpackedFloat.packNumber', hsigPacked]
      rw [hexN]
      rw [show uf.ex.toInt + (bias e : Int) - (bias e : Int) = uf.ex.toInt from by omega]
      rw [Rat.natCast_sub_of_le hsig_ge, Rat.natCast_pow, Rat.natCast_ofNat]
      simp only [Rat.mul_assoc]
      congr 1
      -- ⊢ (1 + (↑sig - 2^s)/2^s) * 2^ex = ↑sig * 2^(ex - ↑s)
      have key : (1 : Rat) + ((uf.sig.toNat : Rat) - 2 ^ s) / 2 ^ s
          = (uf.sig.toNat : Rat) / 2 ^ s := by
        simp only [Rat.div_def, Rat.inv_zpow_natCast_eq_zpow_neg, Rat.sub_mul,
          UnpackedFloat.two_pow_mul_two_pow_neg_intCast_eq_one]
        grind
      rw [key]
      rw [show uf.ex.toInt - (s : Int) = -(s : Int) + uf.ex.toInt from by omega]
      rw [← Rat.zpow_mul_zpow (by decide : (2:Rat) ≠ 0) (-(s : Int)) uf.ex.toInt]
      rw [Rat.div_def, Rat.inv_zpow_natCast_eq_zpow_neg, Rat.mul_assoc]
    case neg =>
      -- subnormal case
      have hinr : EUnpackedFloat.packNumber'.inNormalRange (s := s) (e := e) uf.ex = false :=
        Bool.eq_false_iff.mpr
          (fun hc => hrange ((EUnpackedFloat.packNumber'.inNormalRange_iff he hs uf.ex).mp hc))
      have hdvd : 2 ^ (minNormalExp e - uf.ex.toInt).toNat ∣ uf.sig.toNat := by
        rcases hexp2 with h | h
        · exact absurd h hrange
        · exact h
      have hd_int : ((minNormalExp e - uf.ex.toInt).toNat : Int)
          = minNormalExp e - uf.ex.toInt :=
        Int.toNat_of_nonneg (by omega)
      obtain ⟨d, hd_def⟩ : ∃ d, (minNormalExp e - uf.ex.toInt).toNat = d := ⟨_, rfl⟩
      rw [hd_def] at hdvd hd_int
      have hd_pos : 0 < d := by omega
      obtain ⟨q, hq⟩ := hdvd
      have hsig_pos : 0 < uf.sig.toNat := by
        have := Nat.two_pow_pos s
        omega
      have hq_pos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h, Nat.mul_zero] at hq
          omega
        · exact h
      have h2d_le : 2 ^ d ≤ uf.sig.toNat := Nat.le_of_dvd hsig_pos ⟨q, hq⟩
      have hd_le : d ≤ s := by
        rcases Nat.lt_or_ge s d with h | h
        · exfalso
          have h1 : (2:Nat) ^ (s + 1) ≤ 2 ^ d := Nat.pow_le_pow_of_le (by decide) (by omega)
          omega
        · exact h
      have h2d_two : 2 ≤ 2 ^ d := by
        calc (2:Nat) = 2 ^ 1 := rfl
        _ ≤ 2 ^ d := Nat.pow_le_pow_of_le (by decide) hd_pos
      have hq_lt : q < 2 ^ s := by
        have h1 : 2 ^ d * q < 2 ^ s * 2 := by
          rw [← hq, ← hpow_s]
          exact hsig_lt
        have h2 : 2 ^ s * 2 ≤ 2 ^ d * 2 ^ s := by
          calc (2:Nat) ^ s * 2 = 2 * 2 ^ s := Nat.mul_comm _ _
          _ ≤ 2 ^ d * 2 ^ s := Nat.mul_le_mul_right _ h2d_two
        exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_lt_of_le h1 h2)
      have hs_lt : s < 2 ^ (exponentWidth e s - 1) :=
        UnpackedFloat.sigWidth_lt_exponentWidth_sub_one
      -- the shift amount
      have hshift_int : (EUnpackedFloat.packNumber'.shift (s := s) uf.ex).toInt = (d : Int) := by
        simp only [EUnpackedFloat.packNumber'.shift]
        rw [BitVec.toInt_sub, toInt_ofInt_minNormalExp_eq_minNormalExp he hs, ← hd_int]
        apply Int.bmod_eq_of_le <;> omega
      have hshift_msb : (EUnpackedFloat.packNumber'.shift (s := s) uf.ex).msb = false := by
        rw [BitVec.msb_eq_toInt, hshift_int]
        simp only [decide_eq_false_iff_not, Int.not_lt]
        omega
      have hshift_nat : (EUnpackedFloat.packNumber'.shift (s := s) uf.ex).toNat = d := by
        have h := BitVec.toInt_eq_toNat_of_msb hshift_msb
        rw [hshift_int] at h
        exact_mod_cast h.symm
      have hexPacked : EUnpackedFloat.packNumber'.exPacked (s := s) uf.ex = 0#e := by
        simp only [EUnpackedFloat.packNumber'.exPacked, hinr, Bool.not_false, ↓reduceIte]
      have hsigPacked : (EUnpackedFloat.packNumber'.sigPacked uf.sig uf.ex).toNat = q := by
        simp only [EUnpackedFloat.packNumber'.sigPacked, hinr, Bool.false_eq_true, ↓reduceIte,
          BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
        rw [BitVec.ushiftRight_eq', hshift_nat, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow, hq, Nat.mul_div_cancel_left q (Nat.two_pow_pos d)]
        exact Nat.mod_eq_of_lt hq_lt
      have hnormPf : (EUnpackedFloat.packNumber' uf.sign uf.sig uf.ex).isNorm = false := by
        simp only [PackedFloat.isNorm, EUnpackedFloat.packNumber', hexPacked, BitVec.zero_eq,
          bne_self_eq_false, Bool.and_false]
      simp only [PackedFloat.toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, hnormPf,
        Bool.false_eq_true, ↓reduceIte]
      simp only [EUnpackedFloat.packNumber', hsigPacked]
      rw [hq]
      have hex_eq : uf.ex.toInt = minNormalExp e - (d : Int) := by omega
      rw [hex_eq]
      rw [show -((bias e - 1 : Nat) : Int) = minNormalExp e from rfl]
      simp only [Rat.zero_add, Rat.mul_assoc]
      congr 1
      -- ⊢ ↑q / 2^s * 2^M = ↑(2^d * q) * 2^(M - ↑d - ↑s)
      rw [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat]
      rw [show minNormalExp e - (d : Int) - (s : Int)
          = -(d : Int) + (-(s : Int) + minNormalExp e) from by omega]
      rw [← Rat.zpow_mul_zpow (by decide : (2:Rat) ≠ 0) (-(d : Int)) (-(s : Int) + minNormalExp e)]
      rw [← Rat.zpow_mul_zpow (by decide : (2:Rat) ≠ 0) (-(s : Int)) (minNormalExp e)]
      rw [Rat.div_def, Rat.inv_zpow_natCast_eq_zpow_neg, Rat.mul_assoc]
      have hone_d : (2:Rat) ^ d * 2 ^ (-(d : Int)) = 1 :=
        UnpackedFloat.two_pow_mul_two_pow_neg_intCast_eq_one d
      grind


end EUnpackedFloat

/--
`pf.unpackNum` is exactly packable: it is normalized, its exponent does not exceed
`maxNormalExp`, and (for subnormals) the significand is divisible by the shift amount
needed to express it at `minNormalExp`. These are precisely the hypotheses of
`toRat_pack_mkNumber_eq_toRat`, so this lemma lets call sites that pack `pf.unpackNum`
discharge that theorem's structural side conditions.
-/
theorem PackedFloat.unpackNum_packable {e s : Nat} (he : 1 < e) (hs : 0 < s)
    (pf : PackedFloat e s) (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.unpackNum.Packable := by
  have hbias_pos : 0 < bias e := bias_pos_of_one_lt e he
  have hmin_eq : minNormalExp e = -((bias e - 1 : Nat) : Int) := rfl
  have hmax_eq : maxNormalExp e = (bias e : Int) := rfl
  have hbias_def : bias e = 2 ^ (e - 1) - 1 := rfl
  have h2e : 2 ^ e = 2 ^ (e - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have key : pf.unpackNum.ex.toInt ≤ maxNormalExp e ∧
      (minNormalExp e ≤ pf.unpackNum.ex.toInt ∨
        2 ^ (minNormalExp e - pf.unpackNum.ex.toInt).toNat ∣ pf.unpackNum.sig.toNat) := by
    by_cases hnorm : pf.isNorm
    · -- normal case: `ex = pf.ex.toNat - bias`, which lands in `[minNormalExp, maxNormalExp]`.
      have hexeq : pf.unpackNum.ex.toInt = (pf.ex.toNat : Int) - bias e := by
        unfold PackedFloat.unpackNum
        simp only [hnorm, if_true]
        simp only [BitVec.truncate_eq_setWidth, bias, BitVec.toInt_sub, BitVec.toInt_setWidth,
          BitVec.toInt_ofNat', Int.natCast_sub (Nat.two_pow_pos _), Int.natCast_pow,
          Int.cast_ofNat_Int, Nat.succ_eq_add_one, Nat.zero_add, Int.sub_bmod_bmod,
          Int.bmod_sub_bmod]
        rewrite [Int.bmod_eq_of_le]
        · rfl
        · apply Int.le_of_neg_le_neg
          simp only [Int.neg_sub, Int.natCast_pow, Int.cast_ofNat_Int, Int.neg_neg]
          apply Int.le_trans (b := 2 ^ (e - 1))
          · omega
          · norm_cast
            apply Nat.le_of_mul_le_mul_right (c := 2) _ (by decide)
            have he' : 2 ^ 1 ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
            have hexpWidth : 2 ^ 1 ∣ 2 ^ exponentWidth e s :=
              Nat.pow_dvd_pow 2 (by grind [UnpackedFloat.expWidth_le_exponentWidth])
            simp only [Nat.pow_pred_div (by omega : 0 < e), Nat.div_mul_cancel he',
              Nat.div_mul_cancel hexpWidth]
            apply Nat.pow_le_pow_of_le (by decide)
            apply UnpackedFloat.expWidth_le_exponentWidth
        · simp [Int.two_pow_succ_div_two]
          apply Int.lt_of_lt_of_le (b := 2 ^ (e - 1))
          · simp only [Int.sub_eq_add_neg, Int.reduceNeg, Int.neg_add, Int.neg_neg]
            norm_cast
            have : pf.ex.toNat < 2 ^ e - 1 := PackedFloat.exp_lt_max_of_isNorm hnorm
            have : 2 ^ 1 ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
            simp only [Nat.pow_pred_div (by omega : 0 < e), Int.natCast_ediv]
            simp
            grind
          · norm_cast
            apply Nat.pow_le_pow_of_le (by decide)
            grind [UnpackedFloat.expWidth_le_exponentWidth]
      have hexlo : 1 ≤ pf.ex.toNat := by
        have := PackedFloat.ex_ne_zero_if_isNorm hnorm
        simp only [bne_iff_ne, ne_eq] at this
        have h0 : pf.ex.toNat ≠ 0 := by
          intro hc; apply this; apply BitVec.eq_of_toNat_eq; simpa using hc
        omega
      have hexhi : pf.ex.toNat < 2 ^ e - 1 := PackedFloat.exp_lt_max_of_isNorm hnorm
      refine ⟨?_, ?_⟩
      · rw [hexeq, hmax_eq]; omega
      · left; rw [hexeq, hmin_eq]; omega
    · -- subnormal case: `unpackNum = (… cons false …).normalize`, shifted left by `clz`.
      have hsigne : pf.sig ≠ 0#s := by
        simp only [PackedFloat.isNorm, PackedFloat.isNormOrNonzeroSubnorm, Bool.and_eq_true,
          bne_iff_ne, ne_eq, Bool.not_eq_true, Bool.or_eq_true, BitVec.zero_eq] at hnorm hpf
        grind
      obtain ⟨sig0, hsig0⟩ : ∃ x : BitVec (s + 1), x = pf.sig.cons false := ⟨_, rfl⟩
      have hsig0ne : sig0 ≠ 0#(s + 1) := by
        intro hc
        apply hsigne
        have := congrArg BitVec.toNat hc
        simp only [hsig0, BitVec.toNat_cons, Bool.toNat, cond_false, Nat.zero_shiftLeft,
          Nat.zero_add, BitVec.toNat_zero] at this
        apply BitVec.eq_of_toNat_eq; simpa using this
      have hclz_lt : pf.sig.clz.toNat < s := BitVec.toNat_clz_lt_iff_ne_zero.mpr (by
        intro hc; apply hsigne; apply BitVec.eq_of_toNat_eq; simpa using hc)
      have hclz0 : sig0.clz.toNat = pf.sig.clz.toNat + 1 := by
        rw [hsig0, BitVec.toNat_clz_cons]; simp
      -- the normalized record
      have hnormrec : pf.unpackNum =
          { sign := pf.sign, ex := BitVec.ofInt _ (minNormalExp e) - sig0.clz.setWidth _,
            sig := sig0 <<< sig0.clz : UnpackedFloat (exponentWidth e s) (s + 1) } := by
        have hbeq : (sig0 == 0#(s + 1)) = false := by simpa using hsig0ne
        unfold PackedFloat.unpackNum
        rw [if_neg hnorm]
        unfold UnpackedFloat.normalize
        dsimp only
        rw [← hsig0, hbeq]
        rfl
      have hclz_setWidth : (sig0.clz.setWidth (exponentWidth e s)).toInt = (sig0.clz.toNat : Int) := by
        rw [BitVec.toInt_eq_toNat_of_msb]
        · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
          have := UnpackedFloat.sigWidth_lt_exponentWidth_sub_one (e := e) (s := s)
          have hpow : 2 ^ (exponentWidth e s - 1) ≤ 2 ^ exponentWidth e s :=
            Nat.pow_le_pow_of_le (by decide) (by omega)
          omega
        · rw [BitVec.msb_eq_decide, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
          · have := UnpackedFloat.sigWidth_lt_exponentWidth_sub_one (e := e) (s := s)
            have hpowsucc : 2 ^ (exponentWidth e s - 1) * 2 = 2 ^ exponentWidth e s :=
              Nat.two_pow_pred_mul_two (zero_lt_exponentWidth (e := e) (s := s))
            simp only [decide_eq_false_iff_not, Nat.not_le]
            omega
          · have := UnpackedFloat.sigWidth_lt_exponentWidth_sub_one (e := e) (s := s)
            have hpow : 2 ^ (exponentWidth e s - 1) ≤ 2 ^ exponentWidth e s :=
              Nat.pow_le_pow_of_le (by decide) (by omega)
            omega
      have hexeq : pf.unpackNum.ex.toInt = minNormalExp e - (sig0.clz.toNat : Int) := by
        rw [hnormrec]
        dsimp only
        rw [BitVec.toInt_sub, toInt_ofInt_minNormalExp_eq_minNormalExp he hs, hclz_setWidth]
        rw [Int.bmod_eq_of_le]
        · have := UnpackedFloat.sigWidth_add_bias_le_exponentWidth_sub_one (e := e) (s := s)
          have hpowsucc : 2 ^ (exponentWidth e s - 1) * 2 = 2 ^ exponentWidth e s :=
            Nat.two_pow_pred_mul_two (zero_lt_exponentWidth (e := e) (s := s))
          rw [hmin_eq]; simp only [bias]; omega
        · have := UnpackedFloat.sigWidth_add_bias_le_exponentWidth_sub_one (e := e) (s := s)
          have hpowsucc : 2 ^ (exponentWidth e s - 1) * 2 = 2 ^ exponentWidth e s :=
            Nat.two_pow_pred_mul_two (zero_lt_exponentWidth (e := e) (s := s))
          rw [hmin_eq]; simp only [bias]; omega
      refine ⟨?_, ?_⟩
      · rw [hexeq, hmax_eq, hmin_eq]; omega
      · right
        have hsigeq : pf.unpackNum.sig.toNat = sig0.toNat * 2 ^ sig0.clz.toNat := by
          rw [hnormrec]; dsimp only
          rw [BitVec.toNat_shiftLeft_clz, Nat.shiftLeft_eq]
        have hd : (minNormalExp e - pf.unpackNum.ex.toInt).toNat = sig0.clz.toNat := by
          rw [hexeq]; omega
        rw [hd, hsigeq]
        exact ⟨sig0.toNat, Nat.mul_comm _ _⟩
  exact ⟨UnpackedFloat.normalize_eq_self_of_msb_eq_true _
    (PackedFloat.msb_unpackNum_eq_true hpf), key.1, key.2⟩
