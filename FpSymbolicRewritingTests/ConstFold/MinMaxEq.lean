import Fp
/-! Bitwuzla `FP_MIN_EQ` / `FP_MAX_EQ`: `min a a = a`, `max a a = a`.

Stated at the `EUnpackedFloat` level, where `minAux`/`maxAux` collapse via
`cond_self`. The `PackedFloat` versions are intentionally absent: they route
through `(a.unpack).pack`, which canonicalizes non-canonical NaN payloads and so
is not a bit-identity. -/
example (b : Bool) (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.minAux b a a = a := by
  simp only [fp_normalize_consts]

example (b : Bool) (a : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    EUnpackedFloat.maxAux b a a = a := by
  simp only [fp_normalize_consts]
