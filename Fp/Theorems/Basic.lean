import Init.Data.Dyadic
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat

/-- Show that a dyadic number corresponds to a fixed-point number. -/
structure FixedPointEqualsDyadic (f : FixedPoint m e) (d : Dyadic) where
    h : FixedPoint.toDyadic f = d

@[simp]
theorem FixedPointEqualsDyadic_iff
  {d : Dyadic} {f : FixedPoint m e} :
  (FixedPointEqualsDyadic f d) ↔ (FixedPoint.toDyadic f = d) := by
  constructor
  · intros h
    exact h.h
  · intros h
    constructor
    exact h


theorem DyadicEqualsFixedPoint_of_eq
  {d : Dyadic} {f : FixedPoint m e}
  (h : FixedPoint.toDyadic f = d) :
    FixedPointEqualsDyadic f d:=
  ⟨h⟩

/-- The fixed point number approximates the rational number up to a certain precision.
That is, `|f - r| < 1/2^n`. -/
structure FixedPointApproximatesRatUpto
    (f : FixedPoint m e) (n : Nat) (r : Rat)  where
  h : (f.toRat - r).abs < Rat.twoPowInv n

/-- The dyadic number equals the fixed point number. -/
notation (name := fixedEqDyadic) f "∼d " d =>
    (FixedPointEqualsDyadic f d)

/-- The dyadic number equals the fixed point number. -/
notation (name := fixedApproxRat) f "∼r[" n "] " d =>
    (FixedPointApproximatesRatUpto f n d)

theorem Dyadic.eq_iff_toRat_eq (d₁ d₂ : Dyadic) :
    d₁ = d₂ ↔ d₁.toRat = d₂.toRat := by
  constructor
  · intros h
    subst d₁
    simp
  · intros h
    rw [← Dyadic.toRat_inj, h]
