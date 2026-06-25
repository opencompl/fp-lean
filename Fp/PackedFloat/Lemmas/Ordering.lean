import Fp.PackedFloat.Lemmas.Conversion

/-!
## Basic ordering lemmas about `PackedFloat`

Properties of `≤`/`<` on `PackedFloat` (reflexivity, antisymmetry, transitivity,
NaN/zero/sign-based facts).
-/

namespace PackedFloat

@[simp, grind =>]
theorem le_getInfinity_true_iff_eq (hs : 0 < s)
    (y : PackedFloat e s) :
    y ≤ PackedFloat.getInfinity e s true ↔ y = .getInfinity e s true := by
  constructor
  · intros h
    grind only [PackedFloat.le_iff_eq_of_isNaN, PackedFloat.le_iff_eq_of_isNaN', le_antisymm_of_ne_NaN,
      => PackedFloat.getInfinity_true_le_of_not_isNaN]
  · intros h
    subst h
    grind only [PackedFloat.le_refl]

end PackedFloat
