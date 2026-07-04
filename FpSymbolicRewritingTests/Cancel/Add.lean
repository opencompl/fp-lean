import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on
`EUnpackedFloat.add` (RNE), given the operands are `Canonical`. -/
example (a b : EUnpackedFloat (exponentWidth 3 4) (4 + 1))
    (ha : EUnpackedFloat.Canonical a) (hb : EUnpackedFloat.Canonical b) :
    ((EUnpackedFloat.add .RNE a b).pack).unpack = EUnpackedFloat.add .RNE a b := by
  simp only [fp_normalize_pack_unpack_eunpacked, Nat.reduceLT, ha, hb]
