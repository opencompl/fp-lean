import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.add` into its unpack/EUnpacked/pack form. -/
example (m : RoundingMode) (x y : PackedFloat 3 4) :
    PackedFloat.add m x y = (EUnpackedFloat.add m x.unpack y.unpack).pack := by
  simp only [fp_expand_pack_unpack]
