import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.isNaN` onto the unpacked form. -/
example (x : PackedFloat 3 4) :
    PackedFloat.isNaN x = EUnpackedFloat.isNaN x.unpack := by
  simp only [fp_expand_pack_unpack]
