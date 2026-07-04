import Fp
/-! Bitwuzla `FP_NEG_NEG`: `neg (neg a) = a` (double-negation elimination),
at both the `PackedFloat` and `EUnpackedFloat` levels. -/
example (a : PackedFloat 3 4) :
    PackedFloat.neg (PackedFloat.neg a) = a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.neg (EUnpackedFloat.neg a) = a := by
  simp only [fp_normalize_consts]
