import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.div` into its unpack/EUnpacked/pack form. -/
example (m : RoundingMode) (x y : PackedFloat 3 4) :
    PackedFloat.div m x y = (EUnpackedFloat.div m x.unpack y.unpack).pack := by
  simp only [fp_expand_pack_unpack]
