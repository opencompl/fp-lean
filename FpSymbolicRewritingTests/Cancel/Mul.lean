import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on
`EUnpackedFloat.mul` (RNE). The single generic rewrite fires without a `Canonical`
hypothesis on the operands: the assumption `EUnpackedFloat.Canonical_all` supplies it. -/
example (a b : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) :
    ((EUnpackedFloat.mul .RNE a b).pack).unpack = EUnpackedFloat.mul .RNE a b := by
  simp only [fp_normalize_pack_unpack_eunpacked, Nat.reduceLT]
