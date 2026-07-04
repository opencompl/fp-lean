import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on `EUnpackedFloat.mod`. -/
example (m : RoundingMode) (a b : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    ((EUnpackedFloat.mod m a b).pack).unpack = EUnpackedFloat.mod m a b := by
  simp only [fp_normalize_pack_unpack_eunpacked]
