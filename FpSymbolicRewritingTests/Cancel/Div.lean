import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on
`EUnpackedFloat.div` (RNE), given the operands are `Canonical`. -/
example (a b : EUnpackedFloat (exponentWidth 3 4) (4 + 1)) (ha : a.Canonical) (hb : b.Canonical) :
    ((EUnpackedFloat.div .RNE a b).pack).unpack = EUnpackedFloat.div .RNE a b := by
  simp only [fp_normalize_pack_unpack_eunpacked, Nat.reduceLT, ha, hb]
