import Fp
/-! Bitwuzla `FP_IS_ZERO_ABS_NEG`: `isZero (abs/neg a) = isZero a`,
at both the `PackedFloat` and `EUnpackedFloat` levels. -/
example (a : PackedFloat 3 4) :
    PackedFloat.isZero (PackedFloat.abs a) = PackedFloat.isZero a := by
  simp only [fp_normalize_consts]

example (a : PackedFloat 3 4) :
    PackedFloat.isZero (PackedFloat.neg a) = PackedFloat.isZero a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.isZero (EUnpackedFloat.abs a) = EUnpackedFloat.isZero a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.isZero (EUnpackedFloat.neg a) = EUnpackedFloat.isZero a := by
  simp only [fp_normalize_consts]
