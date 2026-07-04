import Fp
/-! Bitwuzla `FP_LT_EQ` / `FP_LEQ_EQ`: `lt a a = false`, `leq a a = ¬isNaN a`
(with the SMT-LIB `whenBothNaN` flag fixed to `false`), at both the
`PackedFloat` and `EUnpackedFloat` levels. -/
example (a : PackedFloat 3 4) :
    PackedFloat.smtBlt false a a = false := by
  simp only [fp_normalize_consts]

example (a : PackedFloat 3 4) :
    PackedFloat.smtBle false a a = !PackedFloat.isNaN a := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.smtBlt false a a = false := by
  simp only [fp_normalize_consts]

example (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.smtBle false a a = !EUnpackedFloat.isNaN a := by
  simp only [fp_normalize_consts]
