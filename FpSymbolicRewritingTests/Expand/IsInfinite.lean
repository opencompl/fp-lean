import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.isInfinite` onto the unpacked form. -/
example (x : PackedFloat 3 4) :
    PackedFloat.isInfinite x = EUnpackedFloat.isInfinite x.unpack := by
  simp only [fp_expand_pack_unpack]
