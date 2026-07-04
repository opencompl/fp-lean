import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on `EUnpackedFloat.fma`. -/
example (m : RoundingMode) (a b c : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    ((EUnpackedFloat.fma m a b c).pack).unpack = EUnpackedFloat.fma m a b c := by
  simp only [fp_normalize_pack_unpack_eunpacked, Nat.reduceLT]
