import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.smtBne` onto the unpacked form. -/
example (x y : PackedFloat 3 4) :
    PackedFloat.smtBne x y = EUnpackedFloat.smtBne x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
