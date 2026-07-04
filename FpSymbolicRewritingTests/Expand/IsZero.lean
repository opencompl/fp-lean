import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.isZero` onto the unpacked form. -/
example (x : PackedFloat 3 4) :
    PackedFloat.isZero x = EUnpackedFloat.isZero x.unpack := by
  simp only [fp_expand_pack_unpack]
