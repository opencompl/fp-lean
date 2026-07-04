import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.sub` into its unpack/EUnpacked/pack form. -/
example (m : RoundingMode) (x y : PackedFloat 3 4) :
    PackedFloat.sub m x y = (EUnpackedFloat.sub m x.unpack y.unpack).pack := by
  simp only [fp_expand_pack_unpack]
