import Fp
/-! Bitwuzla `FP_IS_NORM_ABS_NEG`: `isNorm (abs/neg a) = isNorm a`
(`isNorm` = `fp.isNormal`). Available only at the `PackedFloat` level. -/
example (a : PackedFloat 3 4) :
    PackedFloat.isNorm (PackedFloat.abs a) = PackedFloat.isNorm a := by
  simp only [fp_normalize_consts]

example (a : PackedFloat 3 4) :
    PackedFloat.isNorm (PackedFloat.neg a) = PackedFloat.isNorm a := by
  simp only [fp_normalize_consts]
