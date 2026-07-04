import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.fma` into its unpack/EUnpacked/pack form. -/
example (m : RoundingMode) (x y z : PackedFloat 3 4) :
    PackedFloat.fma m x y z = (EUnpackedFloat.fma m x.unpack y.unpack z.unpack).pack := by
  simp only [fp_expand_pack_unpack]
