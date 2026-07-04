import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.ieeeBeq` onto the unpacked form. -/
example (x y : PackedFloat 3 4) :
    PackedFloat.ieeeBeq x y = EUnpackedFloat.ieeeBeq x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
