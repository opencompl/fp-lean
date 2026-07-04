import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.mul` into its unpack/EUnpacked/pack form. -/
example (m : RoundingMode) (x y : PackedFloat 3 4) :
    PackedFloat.mul m x y = (EUnpackedFloat.mul m x.unpack y.unpack).pack := by
  simp only [fp_expand_pack_unpack]
