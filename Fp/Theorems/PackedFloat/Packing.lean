import Fp.Basic
import Fp.Unpacking
import Fp.Theorems.PackedFloat.ToExtRat

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
  simp at this
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
  simp [pack', PackedFloat.isNaN, huf]
  grind

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

theorem isInfinite_of_isInfinite_pack' (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.pack'.isInfinite) :
    uf.isInfinite = true := by
  sorry


@[simp, grind .]
theorem pack_isInfinite_eq_isInfinite (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack.isInfinite = uf.isInfinite := by
  sorry

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
  sorry

/--
Packing then unpacking a NaN yields `mkNaN`.
The PackedFloat's NaN status is preserved by `isNaN_pack_of_isNaN`, so unpack takes the NaN branch.
-/
@[simp, grind .]
theorem unpack_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isNaN) :
    uf.pack.unpack = EUnpackedFloat.mkNaN := by
  sorry

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
Zero case: a Number-state `uf` which is a zero
must be exactly `mkZero uf.sign`.
-/
theorem eq_mkZero_of_isNumber_of_isZero
    (uf : EUnpackedFloat e s)
    (hNum : uf.isNumber) (hZ : uf.isZero) :
    uf = EUnpackedFloat.mkZero uf.sign := by
  rcases uf with ⟨state, sign, ex, sig⟩
  simp [isNumber] at hNum
  simp [isZero, isNumber, UnpackedFloat.isZero] at hZ
  simp [EUnpackedFloat.mkZero, UnpackedFloat.mkZero, EUnpackedFloat.sign]
  grind

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

theorem toRat_pack_mkNumber_eq_toRat
    (he : 1 < e) (hs : 0 < s)
    (uf : UnpackedFloat (exponentWidth e s) (s + 1)) :
    (EUnpackedFloat.mkNumber uf).pack.toRat = uf.toRat := by
  sorry


end EUnpackedFloat
