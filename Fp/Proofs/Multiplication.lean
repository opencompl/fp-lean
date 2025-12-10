import Fp.Basic
import Fp.Rounding
import Fp.Multiplication
import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat

@[grind =]
theorem Int.toNat_neg_eq_zero_of_nonpos {z : Int} (h : z ≤ 0) : z.toNat = 0 := by
  grind 

@[grind .] -- What is a grind '.' pattern?
theorem mkRat_eq_mkRat_of_eq_of_eq
  {n1 n2 : Int}
  {d1 d2 : Nat}
  (hn : n1 = n2)
  (hd : d1 = d2)
  :
  mkRat n1 d1 = mkRat n2 d2 := by grind

@[simp]
theorem Bool.xor_eq_true_of_ne {b1 b2 : Bool} (h : b1 ≠ b2) :
  b1.xor b2 = true := by
  grind

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_sign_eq_one_of_eq 
  {b1 b2 : Bool} (h : b1 = b2) :
  (-1) ^ b1.toNat * (-1) ^ b2.toNat = 1 := by
  grind [Bool.toNat]

@[grind =, grind .]
theorem neg_one_pow_toNat_eq_ite
  { b : Bool } :
  (-1) ^ b.toNat = if b then -1 else 1 := by
  grind [Bool.toNat]

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_sign_eq_neg_one_of_ne 
  {b1 b2 : Bool} (h : b1 ≠ b2) :
  (-1) ^ b1.toNat * (-1) ^ b2.toNat = -1 := by
  grind [Bool.toNat]

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_toNat_eq_one_of_self
  {b : Bool} : (-1) ^ b.toNat * (-1) ^ b.toNat = 1 := by
  grind [Bool.toNat]

attribute [grind] Bool.toNat
attribute [grind funCC] mkRat

/-
@[grind .]
theorem Int.mul_congr (a a' b b' : Int)
  (ha : a = a') (hb : b = b') :
  a * b = a' * b' := by grind
-/

@[grind .]
theorem Int.mul_congr_right (a b b' : Int) (hb : b = b') :
  a * b = a * b' := by
  grind
  

theorem f_mul_DyadicEqualsFixedPoint_mul
    [HExOffset e m] (da db : Dyadic) (fa fb : FixedPoint m e)
   (ha : fa ∼d da) (hb : fb ∼d db) 
  : (f_mul fa fb) ∼d  (da * db) := by
  apply DyadicEqualsFixedPoint_of_eq
  rw [f_mul]
  by_cases hsign : fa.sign = fb.sign
  case pos =>
    simp [hsign]
    rw [FixedPoint.toDyadic]
    simp
    obtain ⟨ha⟩ := ha
    obtain ⟨hb⟩ := hb
    subst ha
    subst hb
    rw [FixedPoint.toDyadic]
    rw [FixedPoint.toDyadic]
    rw [Dyadic.eq_iff_toRat_eq]
    simp
    -- extract out into a single theorem.
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    simp
    norm_cast
    rw [Nat.mod_eq_of_lt]
    · rw [hsign]
      norm_cast
      -- TODO: should be simp lemma.
      simp [Nat.shiftLeft_eq, Int.toNat_add, Nat.pow_add, Int.neg_add]
      -- TODO: should not need ac_nf.
      ac_nf
      grind (splits := 40)
    · rw [Nat.pow_add]
      apply Nat.mul_lt_mul'' 
      · omega
      · omega
  case neg =>
    simp [hsign]
    rw [FixedPoint.toDyadic]
    simp
    obtain ⟨ha⟩ := ha
    obtain ⟨hb⟩ := hb
    subst ha
    subst hb
    rw [FixedPoint.toDyadic]
    rw [FixedPoint.toDyadic]
    rw [Dyadic.eq_iff_toRat_eq]
    simp
    -- extract out into a single theorem.
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    simp
    norm_cast
    rw [Nat.mod_eq_of_lt]
    · norm_cast
      -- TOO: should be simp lemma.
      simp only [Int.natCast_mul, Int.natCast_add, Int.neg_add, Int.natCast_nonneg, Int.toNat_add,
        Int.toNat_natCast, Nat.shiftLeft_eq, Nat.pow_add, Nat.one_mul, Int.reduceNeg]
      grind
    · rw [Nat.pow_add]
      -- TODO: create grind lemmas.
      apply Nat.mul_lt_mul'' 
      · omega
      · omega

/--
info: 'f_mul_DyadicEqualsFixedPoint_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms f_mul_DyadicEqualsFixedPoint_mul

