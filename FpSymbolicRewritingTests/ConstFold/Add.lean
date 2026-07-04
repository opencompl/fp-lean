import Fp
/-! `fp_normalize_consts` symbolically evaluates `PackedFloat.add` on literals: 1.0 + 0.5 = 1.5. -/
example :
    PackedFloat.add .RNE (⟨false, 3#3, 0#4⟩ : PackedFloat 3 4) (⟨false, 2#3, 0#4⟩ : PackedFloat 3 4)
      = (⟨false, 3#3, 8#4⟩ : PackedFloat 3 4) := by
  simp only [fp_normalize_consts]
