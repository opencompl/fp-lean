import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on `EUnpackedFloat.mul`. -/
example (m : RoundingMode) (a b : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    ((EUnpackedFloat.mul m a b).pack).unpack = EUnpackedFloat.mul m a b := by
  simp only [fp_normalize_pack_unpack_eunpacked]
