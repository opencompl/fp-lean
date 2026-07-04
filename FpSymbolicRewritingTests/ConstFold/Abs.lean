import Fp
/-! `fp_normalize_consts` symbolically evaluates `PackedFloat.abs` on a literal: |-1.0| = 1.0. -/
example :
    PackedFloat.abs (⟨true, 3#3, 0#4⟩ : PackedFloat 3 4)
      = (⟨false, 3#3, 0#4⟩ : PackedFloat 3 4) := by
  simp only [fp_normalize_consts]
