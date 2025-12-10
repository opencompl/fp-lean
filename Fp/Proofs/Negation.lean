import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.Negation
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat


theorem f_neg_DyadicEqualsFixedPoint_neg
    [HExOffset e m]
    (da : Dyadic) (fa : FixedPoint m e)
 (ha : fa ∼d da) 
  : (f_neg fa) ∼d  (- da) := by
  apply DyadicEqualsFixedPoint_of_eq
  rw [f_neg]
  obtain ⟨ha⟩ := ha
  subst ha
  rw [FixedPoint.toDyadic, FixedPoint.toDyadic]
  simp
  rw [Dyadic.eq_iff_toRat_eq]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  simp 
  push_cast
  by_cases hsign : fa.sign <;> simp [hsign]

/--
info: 'f_neg_DyadicEqualsFixedPoint_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms f_neg_DyadicEqualsFixedPoint_neg

