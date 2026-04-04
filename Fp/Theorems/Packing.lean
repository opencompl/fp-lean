import Fp.Basic
import Fp.Packing

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

theorem Nat.pow_pred_div (h : 0 < n) :
  2 ^ (n - 1) = (2 ^ n) / 2 := by
  grind [Nat.pow_pred_mul]

theorem Nat.two_pow_succ_div_two {n : Nat} :
  (2 ^ n + 1) / 2 = 2 ^ (n - 1) := by
  cases n <;> grind

theorem Int.two_pow_succ_div_two {n : Nat} :
  (2 ^ n + 1) / 2 = (2 ^ (n - 1) : Int) := by
  cases n <;> grind

-- TODO: @Sid, help!
axiom BitVec.toNat_clz_cons (b : Bool) (x : BitVec w)
  : (BitVec.cons b x).clz.toNat = if b then 0 else x.clz.toNat + 1 -- := by

theorem Nat.log2_eq_exists (n : Nat) (hn : n ≠ 0) :
  ∃ k, n.log2 = k ∧ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  let k := n.log2
  exists k
  simp [k]
  apply Nat.log2_eq_iff .. |>.mp <;> grind


-- @[grind →]
theorem Nat.log2_le_log2_of_le {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  induction a using Nat.div2Induction generalizing b with
  | ind a ih =>
    match ha : a with
    | 0 => simp
    | 1 => simp
    | a' + 2 =>
      match hb : b with
      | 0 => simp_all
      | 1 => simp_all
      | b' + 2 =>
        simp only [succ_eq_add_one] at ha hb
        simp only [← ha, ← hb] at ⊢ h ih
        replace ih := ih (ha ▸ Nat.zero_lt_succ _) (Nat.div_le_div_right h)
        rewrite [Nat.log2_def a, Nat.log2_def b]
        simp only [ha, le_add_left, ↓reduceIte, hb, Nat.add_le_add_iff_right, ge_iff_le]
        simp [← ha, ← hb, ih]

grind_pattern Nat.log2_le_log2_of_le => 2^a ≤ 2^b


theorem Nat.log2_le_log2_add {a b : Nat} : a.log2 ≤ (a + b).log2 := by
  apply Nat.log2_le_log2_of_le
  apply Nat.le_add_right

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

theorem Rat.zpow_sub {q : Rat} (hq : q ≠ 0) {a b : Int} : q ^ (a - b) = q ^ a * q ^ (-b) := by
  rw [Int.sub_eq_add_neg]
  rw [Rat.zpow_add hq]

@[simp]
theorem toExtRat_eq_toExtRat' {pf : PackedFloat e s}
  : pf.toExtRat = pf.toExtRat' := by
  cases hNaN : pf.isNaN <;>
  cases hInf : pf.isInfinite <;>
  cases hZero : pf.isZero <;>
  cases hNorm : pf.isNorm <;>
  all_goals simp only [toExtRat, toExtDyadic, ExtDyadic.toExtRat, toExtRat', hNaN, hInf, hZero, hNorm, cond_true,
    cond_false, Dyadic.toRat_zero, toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, Bool.false_eq_true, if_false, if_true]
  all_goals simp only [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, ExtRat.Number.injEq,
    Int.neg_add, Int.neg_sub, Bool.apply_cond]
  -- all_goals (simp only [PackedFloat.toRat, PackedFloat.toRatSig, PackedFloat.toRatExp, if_true, if_false, hNorm, Bool.false_eq_true])
  all_goals (try simp only [BitVec.toInt_setWidth'_of_lt (Nat.lt_succ_self (s + 1)), Rat.intCast_natCast, BitVec.toInt_neg_eq_of_msb (BitVec.msb_setWidth'_of_lt (Nat.lt_succ_self (s + 1))), BitVec.toNat_cons', Bool.toNat, cond_false, cond_true, Nat.zero_shiftLeft, Nat.one_shiftLeft, Nat.zero_add, Int.natCast_add, Rat.intCast_neg, Rat.intCast_add, Rat.natCast_pow, Rat.natCast_ofNat])
  all_goals (cases pf.sign <;> simp only [cond_false, cond_true, Bool.toSign, if_true, Bool.false_eq_true, if_false, Rat.intCast_ofNat, Rat.intCast_neg, Rat.zero_add, Rat.one_mul, Rat.neg_mul])
  all_goals (rewrite [Rat.div_def])
  all_goals (try rewrite [← Rat.zpow_natCast, ← Rat.zpow_neg])
  all_goals (push_cast)
  · simp only [Int.neg_add]
    simp only [Rat.zpow_add (q := 2) (hq := by decide)]
    grind
  · simp only [Int.neg_add]
    simp only [Rat.zpow_add (q := 2) (hq := by decide)]
    grind
  · simp only [Rat.add_mul]
    ac_nf
    norm_cast
    congr 1
    · simp only [← Rat.zpow_add (q := 2) (hq := by decide)]
      congr 1
      grind only
    · rw [Rat.zpow_add (q := 2) (hq := by decide)]
      grind only
  · -- TODO: disgusting, write a solver for this that does power-of-2 simplification.
    simp only [Rat.add_mul]
    simp only [Rat.zpow_add (q := 2) (hq := by decide)]
    simp only [Rat.zpow_sub (q := 2) (hq := by decide)]
    simp only [Rat.one_mul]
    simp only [← Rat.zpow_add (q := 2) (hq := by decide)]
    norm_cast
    congr 2
    · congr 1
      grind only
    · rw [Rat.zpow_add (q := 2) (hq := by decide)]
      grind only
  · grind only [→ eq_mkZero_of_isZero, Rat.natCast_eq_zero_iff, = sig_getZero,
    = BitVec.ofNat_eq_ofNat, = BitVec.toNat_zero, #a5422ce67b0854c8]
  · grind only [→ eq_mkZero_of_isZero, Rat.natCast_eq_zero_iff, = sig_getZero,
    = BitVec.ofNat_eq_ofNat, = BitVec.toNat_zero, #a5422ce67b0854c8]
  · grind only [→ not_isNorm_of_isZero]
  · grind only [→ not_isNorm_of_isZero]

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
          simp [hNorm]
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
        EUnpackedFloat.mkZero_not_isInfinite, toExtRat', hNaN, hInf, hZero]
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


@[simp]
private theorem Rat.neg_one_mul_le_neg_one_mul_iff {a b : Rat} : -1 * a ≤ -1 * b ↔ b ≤ a := by
  grind

/--
if `a.ex ≤ b.ex`,
then `a.toRatExp ≤ b.toRatExp`..
-/
theorem PackedFloat.toRatExp_le_toRatExp_of_le (a b : PackedFloat e s)
    (hbnan : ¬ b.isNaN)
    (hbinf : ¬ b.isInfinite)
    (hbzero : ¬ b.isZero)
    (hle : a.ex ≤ b.ex)
    : a.toRatExp ≤ b.toRatExp := by
  simp [PackedFloat.toRatExp]
  by_cases ha : a.isNorm
  · simp [ha]
    by_cases hb : b.isNorm
    · simp [hb]
      rw [← BitVec.le_def]
      apply hle
    · simp [hb]
      have haexp := a.ex_ne_zero_if_isNorm
      simp at haexp
      have : b.isNonzeroSubnorm = true := by grind only [=
          isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
        = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
        isNormOrSubnorm_eq_isNorm_or_isSubnorm]
      have := b.exp_eq_of_isNonzeroSubnorm
      rw [this] at hle
      simp at hle
      grind only
  · by_cases hb : b.isNorm
    · simp [ha]
      simp [hb]
      grind
    · simp [hb, ha]

/-
theorem PackedFloat.toRatExp_lt_toRatExp_of_lt (a b : PackedFloat e s)
    (he : 0 < e)
    (hanan : ¬ a.isNaN)
    (hainf : ¬ a.isInfinite)
    (hazero : ¬ a.isZero)
    (hbnan : ¬ b.isNaN)
    (hbinf : ¬ b.isInfinite)
    (hbzero : ¬ b.isZero)
    (hle : a.ex < b.ex)
    : a.toRatExp < b.toRatExp := by
  simp [PackedFloat.toRatExp]
  by_cases ha : a.isNorm
  · simp [ha]
    by_cases hb : b.isNorm
    · simp [hb]
      rw [← BitVec.lt_def]
      apply hle
    · simp [hb]
      have haexp := a.ex_ne_zero_if_isNorm
      simp at haexp
      have : b.isNonzeroSubnorm = true := by grind only [=
          isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
        = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
        isNormOrSubnorm_eq_isNorm_or_isSubnorm]
      have := b.exp_eq_of_isNonzeroSubnorm
      rw [this] at hle
      simp at hle
  · by_cases hb : b.isNorm
    · simp [ha]
      simp [hb]
      have haexp := a.exp_eq_of_isNonzeroSubnorm
      have hbexp := b.ex_ne_zero_if_isNorm
      simp at haexp hbexp
      have : 0 < b.ex.toNat := by exact BitVec.toNat_pos_of_ne_zero hbexp
      have hbias : bias e = 0 ∨ 0 < bias e  := by grind
      rcases hbias with (hbias | hbias)
      · simp [hbias]
        grind
      · rw [show (((bias e - 1) : Nat) : Int) = bias e - 1 by grind]
        rw [Int.neg_sub]
        simp
        sorry
    · simp [hb, ha]
      have := b.exp_eq_of_isNonzeroSubnorm
      have := a.exp_eq_of_isNonzeroSubnorm
      grind only
-/

@[simp]
theorem PackedFloat.toRatExp_eq_toRatExp_of_ex_eq_ex (a b : PackedFloat e s)
    (ha : a.isNormOrNonzeroSubnorm)
    (hb : b.isNormOrNonzeroSubnorm)
    (heq : a.ex = b.ex)
    : a.toRatExp = b.toRatExp := by
  simp [PackedFloat.toRatExp]
  by_cases ha : a.isNorm
  · simp [ha]
    by_cases hb : b.isNorm
    · simp [hb]
      grind only
    · simp [hb]
      have haexp := a.ex_ne_zero_if_isNorm
      have hbexp := b.exp_eq_of_isNonzeroSubnorm
      simp at haexp
      grind only
  · simp [ha]
    intros hb
    have haexp := a.exp_eq_of_isNonzeroSubnorm
    have hbexp := b.exp_eq_of_isNonzeroSubnorm
    rw [hbexp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Int.cast_ofNat_Int, Int.zero_sub, Int.neg_inj]
    grind only [ex_ne_zero_if_isNorm, = BitVec.zero_eq]


/--
Amongst normal numbers, the ordering by `toRatExp` agrees with the ordering by exponent.
-/
theorem PackedFloat.toRatExp_lt_toRatExp_of_lt_of_isNorm (a b : PackedFloat e s)
    (hanorm : a.isNorm)
    (hbnorm : b.isNorm)
    (hle : a.ex < b.ex)
    : a.toRatExp < b.toRatExp := by
  simp [PackedFloat.toRatExp]
  simp [hanorm]
  simp [hbnorm]
  rw [← BitVec.lt_def]
  apply hle

/--
the 'toRatSig' is in the same order as that of the 'sig'
interpreted as a 2s complement unsigned number.
-/
@[simp]
theorem PackedFloat.toRatSig_le_toRatSig_of_le_of_isNorm_eq_isNorm
  (x y : PackedFloat e s)
  (hxy : x.isNorm = y.isNorm)
  (hle : x.sig ≤ y.sig) : x.toRatSig ≤ y.toRatSig := by
  simp [PackedFloat.toRatSig]
  rw [hxy]
  by_cases hynorm : y.isNorm
  · simp [hynorm]
    rw [Rat.div_le_div_self]
    · exact Rat.natCast_le_natCast.mpr hle
    · grind only [Rat.pow_pos]
  · simp [hynorm]
    have : x.sig.toNat ≤ y.sig.toNat :=  BitVec.le_def.mp hle
    apply Rat.div_le_div_self .. |>.mpr
    · norm_cast
    · grind only [Rat.pow_pos]

/--
The exponent of a subnormal number is always less than or equal to the exponent of a normal number.
-/
@[simp, grind .]
theorem PackedFloat.ex_le_ex_of_isNonzeroSubnorm_of_not_isNorm (x y : PackedFloat e s)
    (hxnorm : x.isNonzeroSubnorm)
    (hynorm : y.isNorm) : x.ex ≤ y.ex := by
  have hxexp := x.exp_eq_of_isNonzeroSubnorm
  have := y.ex_ne_zero_if_isNorm
  simp at this
  have : x.ex.toNat = 0 := by grind only [= BitVec.toNat_zero]
  have : y.ex.toNat ≠ 0 := by grind only [BitVec.toNat_inj]
  rw [BitVec.le_def]
  grind

@[grind .]
theorem PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm (x : PackedFloat e s)
    (hxnan : ¬ x.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hxero : ¬ x.isZero)
    (hxsubnorm : ¬ x.isNonzeroSubnorm) : x.isNorm := by
  grind only [= isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
    = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
    isNormOrSubnorm_eq_isNorm_or_isSubnorm]

/--
The interpretation of the exponent of a subnormal number is always less than or equal to the exponent of a normal number.
-/
@[simp, grind .]
theorem PackedFloat.toRatExp_le_toRatExp_of_isNonzeroSubnorm_of_not_isNorm (x y : PackedFloat e s)
    (hxnorm : ¬ x.isNorm)
    (hynorm : y.isNorm) : x.toRatExp ≤ y.toRatExp := by
  simp [PackedFloat.toRatExp]
  have hxexp := x.toRatExp_eq_of_not_isNorm (by grind only)
  simp [show ¬ x.isNorm by grind]
  simp [show y.isNorm by grind]
  have hyexp := y.toRatExp_eq_of_isNorm (by grind only)
  by_cases hbias : bias e = 0
  · simp [hbias]
  · rw [Int.natCast_sub (by grind only)]
    norm_cast
    rw [Int.neg_sub]
    simp only [Int.sub_le_sub_right_iff, ge_iff_le]
    have := y.ex_ne_zero_if_isNorm -- TODO: rephrase to be in terms of simp-nf
    simp at this
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    have yzero : y.ex.toNat = 0 := by grind only
    have yzero' : y.ex = 0 := by
      rw [← BitVec.toNat_inj]
      simp [yzero]
    grind only



theorem Rat.zpow_succ {q : Rat} (hq : q ≠ 0) {a : Int} : q ^ (a + 1) = q ^ a * q := by
  exact Rat.zpow_add_one hq a

/--
The heart of showing that the ordering by `toRat'`
agrees with packed float ordering, where we show that
if the packed floats are ordered by `(exponent, significand)` (in lex ordering),
then their `toRat'` are ordered by the usual ordering on rationals.
See that this reduction only talks about the nonnegative cases.
Case splitting on signs will handle the general case.

TODO: can we drop `isZero`?
-/
theorem toExtRat'_le_toExtRat'_of_le_of_number
    {e s : Nat}
    (x y : PackedFloat e s)
    (hxzero : ¬x.isZero = true)
    (hyzero : ¬y.isZero = true)
    (hxnan : ¬x.isNaN = true)
    (hynan : ¬y.isNaN = true)
    (hxinf : ¬x.isInfinite = true)
    (hyinf : ¬y.isInfinite = true)
    (hxy' : x.ex.toNat < y.ex.toNat ∨ x.ex = y.ex ∧ x.sig.toNat ≤ y.sig.toNat)
    : x.toRatSig * 2 ^ x.toRatExp ≤ y.toRatSig * 2 ^ y.toRatExp := by
  by_cases hxsubnorm : x.isNonzeroSubnorm
  · -- x subnorm
    have hxexp := x.toRatExp_eq_of_not_isNorm (by grind)
    have hxex := x.exp_eq_of_isNonzeroSubnorm
    by_cases hysubnorm : y.isNonzeroSubnorm
    · -- x subnorm, y subnorm.
      have hyexp := y.toRatExp_eq_of_not_isNorm (by grind)
      have hyex := y.exp_eq_of_isNonzeroSubnorm
      rw [hxexp, hyexp]
      rw [Rat.mul_le_mul_cancel_right_of_lt]
      simp [hxex, hyex] at hxy'
      · apply PackedFloat.toRatSig_le_toRatSig_of_le_of_isNorm_eq_isNorm
        · grind
        · exact BitVec.le_def.mpr hxy'
      · grind only [Fp.Rat.two_pow_pos]
    · -- x subnorm, y norm.
      -- compare exponents and show that one is dominated by the other.
      have hexpLe : x.toRatExp ≤ y.toRatExp := by
        apply PackedFloat.toRatExp_le_toRatExp_of_isNonzeroSubnorm_of_not_isNorm
        · grind only [→ not_isNorm_of_isSubnorm]
        · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
      have : (2 : Rat) ^ x.toRatExp ≤ 2 ^ y.toRatExp := by
        grind only [Rat.two_pow_le_two_pow_of_le]
      apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
      · apply Rat.le_trans (b := 1)
        · grind only [Rat.le_of_lt, → not_isNorm_of_isSubnorm, toRatSig_lt_one_of_not_isNorm]
        · grind only [= isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm,
          one_le_toRatSig_of_isNorm, = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero,
          isNormOrSubnorm_eq_isNorm_or_isSubnorm]
      · grind only
      · grind only [zero_le_twoNumberRatSig]
      · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · -- x norml.
    by_cases hysubnorm : y.isNonzeroSubnorm
    · -- x normal, y subnormale, x ≤ y. impossible, since x is normal and x ≤ y.
      have := y.exp_eq_of_isNonzeroSubnorm
      rw [this] at hxy'
      simp at hxy'
      have : x.ex ≠ 0#e := by
        have := x.ex_ne_zero_if_isNorm
        simp at this
        grind only
      grind only
    · -- x normal, y normal, x ≤ y
      rcases hxy' with (hlexp | hleSig)
      · -- x.exp < y.exp,
        have := x.toRatSig_lt_two
        have := x.one_le_toRatSig_of_isNorm (by grind)
        have := y.toRatSig_lt_two
        have := y.one_le_toRatSig_of_isNorm (by grind)
        apply Rat.le_trans (b := 2 * ((2 : Rat) ^ x.toRatExp))
        · apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
          · grind only
          · grind only
          · grind only
          · grind only [Fp.Rat.two_pow_pos]
        · rw [show y.toRatExp = (y.toRatExp - 1) + 1 by grind only]
          rw [Rat.zpow_succ (by grind only)]
          apply Rat.le_trans (b := (y.toRatSig * 2)* 2 ^ (y.toRatExp - 1))
          · apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
            · grind only
            · apply Rat.two_pow_le_two_pow_of_le
              suffices x.toRatExp < y.toRatExp from by grind only
              apply PackedFloat.toRatExp_lt_toRatExp_of_lt_of_isNorm
              · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
              · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
              · grind only [BitVec.lt_def]
              -- apply PackedFloat.toRatExp_le_toRatExp_of_le
            · grind only [zero_le_twoNumberRatSig]
            · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
          · grind only
      · -- x.exp = y.exp
        obtain ⟨hexpEq, hsigLe⟩ := hleSig
        rw [x.toRatExp_eq_of_ex_eq (h := hexpEq)]
        apply Rat.mul_le_mul_cancel_right_of_lt .. |>.mpr
        · apply PackedFloat.toRatSig_le_toRatSig_of_le_of_isNorm_eq_isNorm
          · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          · rw [BitVec.le_def]; grind only
        · grind only [Fp.Rat.two_pow_pos]

/--
info: 'PackedFloat.toExtRat'_le_toExtRat'_of_le_of_number' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms toExtRat'_le_toExtRat'_of_le_of_number

/--
The packed float '≤' relationship captures ordering by `toRat'`.
-/
@[simp]
theorem toExtRat'_le_toExtRat'_of_le (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hxy : x ≤ y) : x.toExtRat' ≤ y.toExtRat' := by
  rw [PackedFloat.toExtRat']
  have hxy' := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hxy'
  simp [hxnan, hynan] at hxy'
  simp [hxnan] at ⊢
  by_cases hxinf : x.isInfinite
  · simp [hxinf]
    by_cases hxsign : x.sign
    · simp [hxsign, hynan]
    · simp at hxsign
      simp [hxsign]
      have := PackedFloat.eq_getInfinity_iff_isInfinity hs |>.mp hxinf
      simp [hxsign] at this
      subst this
      simp [hs] at hxy
      subst hxy
      simp [hs]
  · simp [hxinf]
    rw [PackedFloat.toExtRat']
    by_cases hyinf : y.isInfinite
    · simp [hyinf, hynan]
      by_cases hysign : y.sign
      · simp [hysign]
        have := PackedFloat.eq_getInfinity_iff_isInfinity hs |>.mp hyinf
        simp [hysign] at this
        subst this
        simp [hs] at hxy
        grind only
      · simp [hysign]
    · simp [hyinf, hynan]
      rw [PackedFloat.toRat, PackedFloat.toRat]
      by_cases hxsign : x.sign
      · simp [hxsign]
        -- x -ve
        by_cases hysign : y.sign
        · -- x -ve, y -ve
          simp [hysign]
          simp [hxsign, hysign] at hxy'
          rw [Rat.mul_assoc, Rat.mul_assoc]
          simp only [Rat.neg_one_mul_le_neg_one_mul_iff]
          apply toExtRat'_le_toExtRat'_of_le_of_number <;> grind only
        · -- x -ve, y +ve
          simp [hysign]
          simp [hxsign, hysign] at hxy'
          have := x.zero_le_twoNumberRatSig
          have := y.zero_le_twoNumberRatSig
          have := Rat.zpow_nonneg (a := 2) (h := by decide) (n := y.toRatExp)
          have := Rat.zpow_nonneg (a := 2) (h := by decide) (n := x.toRatExp)
          simp only [ge_iff_le]
          apply Rat.le_trans (b := 0)
          · grind =>
            instantiate only [Rat.le_of_lt, toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
            instantiate only [Fp.Rat.two_pow_pos, → Rat.mul_pos,
              = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero]
          · grind => instantiate only [Rat.mul_nonneg]
          -- grind?
      · -- x +ve
        simp at hxsign
        simp [hxsign]
        by_cases hysign : y.sign
        · -- x+ve, y -ve
          simp [hxsign, hysign] at hxy'
        · -- x+ve, y +ve
          simp at hysign
          simp [hysign]
          simp [hxsign, hysign] at hxy'
          apply toExtRat'_le_toExtRat'_of_le_of_number <;> grind only

/--
Two packed floats that are ordered by `≤` are ordered by `toRat`, if they are numbers.
TODO: can we drop `isZero`?
-/
@[simp]
theorem toRat_le_toRat_of_le (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero)
    (hyzero : ¬ y.isZero)
    (hxnan : ¬ x.isNaN)
    (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hyinf : ¬ y.isInfinite)
    (hxy : x ≤ y) : x.toRat ≤ y.toRat := by
  have := toExtRat'_le_toExtRat'_of_le he hs x y hxzero hyzero hxnan hynan hxy
  simp [PackedFloat.toExtRat', hxnan, hxinf, hynan, hyinf] at this
  exact this


theorem Rat.inv_eq_div (a : Rat)  : a⁻¹ = 1 / a := by
  grind only

-- TODO: write a simp lemma
@[simp]
theorem Rat.zpow_neg_natCast_eq_one_div_zpow (a : Rat) (n : Nat)
    : a ^ (-n : Int) = 1 / a ^ n := by
  rw [Rat.zpow_neg]
  rw [Rat.inv_eq_div]
  simp



@[simp]
theorem PackedFloat.one_le_ex_of_isNorm (x : PackedFloat e s) (hxnorm : x.isNorm) (he : 0 < e) :
   1#e ≤ x.ex := by
  have hxexp := x.ex_ne_zero_if_isNorm
  simp at hxexp
  have : x.ex.toNat ≠ 0 := by grind only [BitVec.toNat_pos_of_ne_zero hxexp]
  rw [BitVec.le_def]
  simp [he]
  grind only

/--
exponents of normal numbers are ordered by the packed float ordering, amongst
nonnegative numbers.
-/
theorem Packedfloat.ex_le_ex_of_le_of_nonneg (x y : PackedFloat e s)
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (hxsign : x.sign = false) (hysign : y.sign = false)
  (hle : x ≤ y) : x.ex ≤ y.ex := by
  rw [← PackedFloat.le_def, PackedFloat.le] at hle
  simp at hle
  simp [show ¬ x.isNaN by grind,
        show ¬ y.isNaN by grind, hxsign, hysign] at hle
  have : x.ex.toNat ≤ y.ex.toNat := by grind only [BitVec.le_def]
  rw [BitVec.le_def]
  exact this


/--
amongst nonnegative numbers,
normal numbers are always greater than subnormal numbers,
-/
theorem not_le_of_isNorm_of_isNonzeroSubnorm_of_nonneg
    (x y : PackedFloat e s)
    (hxsign : x.sign = false)
    (hysign : y.sign = false)
    (hxnorm : x.isNorm)
    (hynonzerosubnorm : y.isNonzeroSubnorm) : ¬ x ≤ y := by
  intros hcontra
  have hxexp := x.ex_ne_zero_if_isNorm
  have hyexp := y.exp_eq_of_isNonzeroSubnorm
  simp only [BitVec.zero_eq, bne_iff_ne, ne_eq] at hxexp hyexp
  have hxnonzero : x.ex.toNat ≠ 0 := by grind only [BitVec.toNat_pos_of_ne_zero hxexp]
  have hyzero : y.ex.toNat = 0 := by grind only [BitVec.toNat_zero]
  have : x.ex ≥ y.ex := by
    simp
    rw [BitVec.le_def]
    grind only
  have : x.ex ≤ y.ex := by
    apply Packedfloat.ex_le_ex_of_le_of_nonneg
    · grind only [→ isNormOrSubnorm_of_isNorm]
    · grind only [→ isNormOrSubnorm_of_isSubnorm]
    · grind only
    · grind only
    · grind only
  have : x.ex = y.ex := by grind only
  grind only


/--
We can show that the significands of two packed floats are ordered by the packed float ordering,
amongst those with the same sign and exponent, and that are not NaN, and not infinite.
-/
theorem PackedFloat.sig_lt_sig_of_lt_of_of_exp_eq_exp_of_sign_eq_false
  (x y : PackedFloat e s)
  (hxy : x < y)
  (hxnan : ¬ x.isNaN)
  (hynan : ¬ y.isNaN)
  (hexpEq : x.ex = y.ex)
  (hxsign : x.sign = false)
  (hysign : y.sign = false) : x.sig < y.sig := by
  rw [← PackedFloat.lt_def, PackedFloat.lt] at hxy
  obtain ⟨hle, hne⟩ := hxy
  rw [← PackedFloat.le_def, PackedFloat.le] at hle
  simp at hle
  simp [hxnan, hynan, hxsign, hysign] at hle
  rcases hle with (hleExp | hleSig)
  · have : x.ex = y.ex := by grind only [← BitVec.le_def]
    rw [this] at hexpEq
    grind only
  · have : x.sig.toNat ≤ y.sig.toNat := by grind only
    have : x.sig.toNat ≠ y.sig.toNat := by
      intros hcontra
      apply hne
      ext
      · grind only
      · grind only
      · grind only [BitVec.toNat_inj]
    apply BitVec.lt_of_le_ne
    · grind only [BitVec.le_def]
    · grind only

/-
This shows that the packed floats packed floats are always at least a distance
of 2^-e. This gives us the discreteness of the ordering
that lets us define 'lower' and 'upper',
and show that 'lower' and 'upper' are always some distance apart.

-- x < y => x + 1 ≤ y
-/
theorem toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxsign : x.sign = false)
    (hysign : y.sign = false)
    (hxzero : ¬ x.isZero)
    (hyzero : ¬ y.isZero)
    (hxnan : ¬ x.isNaN)
    (hynan : ¬ y.isNaN)
    (hxinf : ¬ x.isInfinite)
    (hyinf : ¬ y.isInfinite)
    (hlt : x < y) :
    x.toRat + (2 : Rat)^(-(s : Int)) * 2 ^ x.toRatExp ≤ y.toRat := by
  have hxle := PackedFloat.le_of_lt hlt
  by_cases hx : x.isNorm
  · -- x norm
    by_cases hy : y.isNorm
    · -- xnorm, y norm, x ≤ y
      simp [PackedFloat.toRat, PackedFloat.toRat, hxsign, hysign]
      have hxyrat := PackedFloat.toRat_le_toRat_of_le he hs x y hxzero hyzero hxnan hynan hxinf hyinf (by grind?)
      rw [← PackedFloat.lt_def, PackedFloat.lt] at hlt
      obtain ⟨hle, hne⟩ := hlt
      rw [← PackedFloat.le_def, PackedFloat.le] at hle
      simp [hxsign, hysign, hxzero, hyzero, hxnan, hynan, hxinf, hyinf] at hle
      rcases hle with (hleExp | hleSig)
      · rw [← Rat.add_mul]
        rw [show y.toRatExp = (y.toRatExp - 1) + 1 by grind only]
        rw [Rat.zpow_succ (by grind only)]
        suffices (x.toRatSig + 1 / 2 ^ s) * 2 ^ x.toRatExp ≤ (2 * y.toRatSig) * (2 ^ (y.toRatExp - 1)) by grind only
        apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
        · have := x.one_le_toRatSig_of_isNorm (by grind)
          have := x.toRatSig_lt_two
          have := y.toRatSig_lt_two
          have := y.one_le_toRatSig_of_isNorm (by grind)
          apply Rat.le_trans (b := 2)
          · have := x.toRatSig_le_two_sub_of_isNorm (by grind)
            grind only
          · suffices 2 * 1 ≤ 2 * y.toRatSig by
              simp
              grind only
            apply Rat.mul_le_mul_of_nonneg_left
            · grind only
            · grind only
        · apply Rat.two_pow_le_two_pow_of_le
          suffices x.toRatExp < y.toRatExp from by grind only
          apply PackedFloat.toRatExp_lt_toRatExp_of_lt_of_isNorm
          · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
          · grind only [BitVec.lt_def]
          -- apply PackedFloat.toRatExp_le_toRatExp_of_le
        · have := x.nonneg_toRatSig
          have : 0 ≤ (1 : Rat) / 2 ^ s := by
            grind only [Fp.Rat.inv_nonneg, Rat.pow_nonneg]
          grind only
        · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
      · -- exp equal
        obtain ⟨hexpEq, hleSig'⟩ := hleSig
        have : x.toRatExp = y.toRatExp := by
          grind only [x.toRatExp_eq_of_ex_eq]
        rw [this]
        have hleSig'' : x.sig ≤ y.sig := by
            grind only [BitVec.le_def]
        have hsigNe : x.sig ≠ y.sig := by grind only [=> not_isNaN_iff_ex_ne_or_sig_ne,
          le_antisymm_of_ne_NaN, le_eq_of_sign_eq_false_of_sign_eq_false]
        have hsigLt : x.sig < y.sig := by grind only
        suffices (x.toRatSig + 1 / 2 ^ s) * 2 ^  y.toRatExp ≤ y.toRatSig * 2 ^ y.toRatExp by
          grind only
        apply Rat.mul_le_mul_cancel_right_of_lt .. |>.mpr
        · -- ⊢  x.toRatSig + 2 ^ -s ≤ y.toRatSig
          apply PackedFloat.toRatSig_add_le_toRatSig_of_lt_of_isNorm_eq_isNorm
          · grind only
          · grind only
        · grind only [Fp.Rat.two_pow_pos]
    · -- x norm, y subnorm, x ≤ y:  This is impossible when restricted to nonnegative numbers.
      have : ¬ (x ≤ y) := by
        apply not_le_of_isNorm_of_isNonzeroSubnorm_of_nonneg
        · grind only
        · grind only
        · grind only
        · grind only [PackedFloat.isNorm_of_not_isNaN_of_not_isInfinity_of_not_isZero_isNonzeroSubnorm]
      grind only
  · -- x subnormal
    have : x.isNonzeroSubnorm := by grind
    by_cases hy : y.isNorm
    · -- x subnorm, y norm, x ≤ y: This is trivial when restricted to nonnegative numbers.
      simp only [toRat, hxsign, toSign_false, Rat.intCast_ofNat, Rat.one_mul,
        Rat.zpow_neg_natCast_eq_one_div_zpow, hysign, ge_iff_le]
      rw [← Rat.add_mul]
      have : x.toRatExp ≤ y.toRatExp := by
        exact PackedFloat.toRatExp_le_toRatExp_of_isNonzeroSubnorm_of_not_isNorm x y hx hy
      have : x.toRatSig + 1 / 2 ^ s ≤  1 := by
        apply toRatSig_plus_le_one_of_isNonzeroSubnorm x (by grind only)
      have : 0 ≤ x.toRatSig := by
        exact zero_le_twoNumberRatSig x
      have : 0 ≤ (1 : Rat) / 2 ^ s := by
        grind only [Fp.Rat.inv_nonneg, Rat.pow_nonneg]
      have : 1 ≤ y.toRatSig := by
        apply y.one_le_toRatSig_of_isNorm (by grind only)
      have : x.toRatSig + 1 / 2 ^ s ≤ y.toRatSig := by
        grind only
      apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
      · grind only
      · apply Rat.two_pow_le_two_pow_of_le
        · grind only
      · grind only
      · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]

    · -- x subnorm, y subnorm, x ≤ y: This will be possible by the analysis.
      simp only [toRat, hxsign, toSign_false, Rat.intCast_ofNat, Rat.one_mul,
        Rat.zpow_neg_natCast_eq_one_div_zpow, hysign, ge_iff_le]
      rw [← Rat.add_mul]
      have hxex := x.exp_eq_of_isNonzeroSubnorm
      have hyex := y.exp_eq_of_isNonzeroSubnorm
      have hxexp := x.toRatExp_eq_of_not_isNorm (by grind)
      have hyexp := y.toRatExp_eq_of_not_isNorm (by grind)
      have hxyexp : x.toRatExp = y.toRatExp := by
        simp [hxexp, hyexp]
      simp [hxyexp]
      suffices (x.toRatSig + 1 / 2 ^ s)  ≤ y.toRatSig by
        apply Rat.mul_le_mul_cancel_right_of_lt .. |>.mpr
        · exact this
        · grind only [Fp.Rat.two_pow_pos]
      apply toRatSig_add_le_toRatSig_of_lt_of_isNorm_eq_isNorm
      · grind only
      · apply PackedFloat.sig_lt_sig_of_lt_of_of_exp_eq_exp_of_sign_eq_false
        · grind only
        · grind only
        · grind only
        · grind only
        · grind only
        · grind only

/--
info: 'PackedFloat.toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false

end PackedFloat
