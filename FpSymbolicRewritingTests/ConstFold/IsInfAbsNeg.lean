import Fp
/-! Bitwuzla `FP_IS_INF_ABS_NEG`: `isInfinite (abs/neg a) = isInfinite a`,
at both the `PackedFloat` and `EUnpackedFloat` levels. -/
example (a : PackedFloat 3 4) :
    PackedFloat.isInfinite (PackedFloat.abs a) = PackedFloat.isInfinite a := by
  simp only [fp_normalize_consts]

example (a : PackedFloat 3 4) :
    PackedFloat.isInfinite (PackedFloat.neg a) = PackedFloat.isInfinite a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.isInfinite (EUnpackedFloat.abs a) = EUnpackedFloat.isInfinite a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.isInfinite (EUnpackedFloat.neg a) = EUnpackedFloat.isInfinite a := by
  simp only [fp_normalize_consts]
