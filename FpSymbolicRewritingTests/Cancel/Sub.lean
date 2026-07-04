import Fp
/-! `fp_normalize_pack_unpack_eunpacked` cancels the `.pack.unpack` round-trip on
`EUnpackedFloat.sub` (RNE), given the operands are `CanonState` (canonical). -/
example (a b : EUnpackedFloat (exponentWidth 3 4) (4 + 1))
    (ha : EUnpackedFloat.CanonState a) (hb : EUnpackedFloat.CanonState b) :
    ((EUnpackedFloat.sub .RNE a b).pack).unpack = EUnpackedFloat.sub .RNE a b := by
  simp only [fp_normalize_pack_unpack_eunpacked, Nat.reduceLT, ha, hb]
