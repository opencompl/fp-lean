import Fp
/-! `fp_normalize_consts` collapses the bitwuzla `FP_ABS_ABS_NEG` rewrite
`abs (abs a) = abs a` symbolically, at both the `PackedFloat` and
`EUnpackedFloat` levels. -/
example (a : PackedFloat 3 4) :
    PackedFloat.abs (PackedFloat.abs a) = PackedFloat.abs a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.abs (EUnpackedFloat.abs a) = EUnpackedFloat.abs a := by
  simp only [fp_normalize_consts]
