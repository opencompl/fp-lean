import Fp.Basic
import Fp.Rounding
import Fp.Division
import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat
import Fp.Proofs.Grind


theorem f_mul_DyadicEqualsFixedPoint_mul
    [HExOffset e m] (da db : Dyadic) (fa fb : FixedPoint m e)
   (ha : fa ∼d da) (hb : fb ∼d db) 
  : (f_div fa fb) ∼d  (da / db) := by
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


