import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.mod` into its unpack/EUnpacked/pack form. -/
example (m : RoundingMode) (x y : PackedFloat 3 4) :
    PackedFloat.mod m x y = (EUnpackedFloat.mod m x.unpack y.unpack).pack := by
  simp only [fp_expand_pack_unpack]
