import Init.Data.Dyadic
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat

/-- Show that a dyadic number corresponds to a fixed-point number. -/
structure DyadicEqualsFixedPoint
    [HExOffset e m] (d : Dyadic) (f : FixedPoint m e) where
    h : FixedPoint.toDyadic f = d

theorem DyadicEqualsFixedPoint_of_eq
  [HExOffset e m]
  {d : Dyadic} {f : FixedPoint m e}
  (h : FixedPoint.toDyadic f = d) :
    DyadicEqualsFixedPoint d f :=
  ⟨h⟩

/-- The dyadic number equals the fixed point number. -/
notation (name := dyadicSim) f "∼d " d =>
    (DyadicEqualsFixedPoint d f)

theorem Dyadic.eq_iff_toRat_eq (d₁ d₂ : Dyadic) :
    d₁ = d₂ ↔ d₁.toRat = d₂.toRat := by
  constructor
  · intros h
    subst d₁
    simp
  · intros h
    rw [← Dyadic.toRat_inj, h]


