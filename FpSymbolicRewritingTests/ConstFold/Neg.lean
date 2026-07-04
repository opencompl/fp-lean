import Fp
/-! `fp_normalize_consts` symbolically evaluates `PackedFloat.neg` on a literal: -(1.0) = -1.0. -/
example :
    PackedFloat.neg (⟨false, 3#3, 0#4⟩ : PackedFloat 3 4)
      = (⟨true, 3#3, 0#4⟩ : PackedFloat 3 4) := by
  simp only [fp_normalize_consts]
