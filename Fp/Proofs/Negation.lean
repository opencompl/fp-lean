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
  rw [FixedPoint.toDyadic]
  rw [Dyadic.eq_iff_toRat_eq]
  simp
    -- extract out into a single theorem.
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  simp

/-- info: 'fp_add_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fp_add_neg

