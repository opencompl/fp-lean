import Fp
/-! Bitwuzla `FP_IS_SUBNORM_ABS_NEG`: `isNonzeroSubnorm (abs/neg a) =
isNonzeroSubnorm a` (`isNonzeroSubnorm` = `fp.isSubnormal`). Available only at
the `PackedFloat` level. -/
example (a : PackedFloat 3 4) :
    PackedFloat.isNonzeroSubnorm (PackedFloat.abs a)
      = PackedFloat.isNonzeroSubnorm a := by
  simp only [fp_normalize_consts]

example (a : PackedFloat 3 4) :
    PackedFloat.isNonzeroSubnorm (PackedFloat.neg a)
      = PackedFloat.isNonzeroSubnorm a := by
  simp only [fp_normalize_consts]
