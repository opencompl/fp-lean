import Init.Data.Dyadic
import Fp.Addition


open Lean

class HExOffset (e : Nat) (m : Nat) where
  h : e < m


instance HExOffsetSucc [hex : HExOffset e m] : HExOffset e (m + 1) where
  h := by
    have := hex.h
    omega


def FixedPoint.ofInt (i : Int) [HExOffset e m] : FixedPoint m e :=
  {
    sign := i ≥ 0
    val := BitVec.ofNat m (i.natAbs)
    hExOffset := HExOffset.h
  }

def FixedPoint.ofDyadic (d : Dyadic) [HExOffset e m]  : FixedPoint m e :=
  FixedPoint.ofInt (d.toRat.ceil)


/-- Show that a dyadic number corresponds to a fixed-point number. -/
structure DyadicRefinesFixedPoint [HExOffset e m] (d : Dyadic) (f : FixedPoint m e) where
   h : FixedPoint.ofDyadic d = f

notation (name := dyadicSim) f "⊆d " d => (DyadicRefinesFixedPoint d f)

theorem fp_add_dyadic [HExOffset e m] (da db : Dyadic) (fa fb : FixedPoint m e)
 (ha : fa ⊆d da) (hb : fb ⊆d db) (mode : RoundingMode)
  : (f_add mode fa fb) ⊆d  (Dyadic.add da db) := by
  sorry
