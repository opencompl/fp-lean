import Fp
/-! Bitwuzla `FP_IS_NAN_ABS_NEG`: `isNaN (abs/neg a) = isNaN a`,
at both the `PackedFloat` and `EUnpackedFloat` levels. -/
example (a : PackedFloat 3 4) :
    PackedFloat.isNaN (PackedFloat.abs a) = PackedFloat.isNaN a := by
  simp only [fp_normalize_consts]

example (a : PackedFloat 3 4) :
    PackedFloat.isNaN (PackedFloat.neg a) = PackedFloat.isNaN a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.isNaN (EUnpackedFloat.abs a) = EUnpackedFloat.isNaN a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.isNaN (EUnpackedFloat.neg a) = EUnpackedFloat.isNaN a := by
  simp only [fp_normalize_consts]
