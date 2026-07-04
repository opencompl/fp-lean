import Fp
/-! `fp_normalize_consts` symbolically evaluates `PackedFloat.fma` on literals: 1.0 * 0.5 + 0.5 = 1.0. -/
example :
    PackedFloat.fma .RNE (⟨false, 3#3, 0#4⟩ : PackedFloat 3 4) (⟨false, 2#3, 0#4⟩ : PackedFloat 3 4)
      (⟨false, 2#3, 0#4⟩ : PackedFloat 3 4)
      = (⟨false, 3#3, 0#4⟩ : PackedFloat 3 4) := by
  simp only [fp_normalize_consts]
