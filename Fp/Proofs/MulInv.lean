import Fp.Basic
import Fp.Rounding
import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.MulInv
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat

theorem fp_mulinv (da : Dyadic) (fa : FixedPoint m e)
 (ha : fa ∼d da)
  : FixedPointApproximatesRatUpto (f_mulinv fa) m da.toRat.inv   := by
  constructor
  simp only [FixedPointEqualsDyadic_iff] at ha
  rw[← ha]
  simp [f_mulinv]
  rw [FixedPoint.toRat, FixedPoint.toDyadic, FixedPoint.toDyadic]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat, Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  simp
  sorry

/-- info: 'fp_add_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fp_mulinv
