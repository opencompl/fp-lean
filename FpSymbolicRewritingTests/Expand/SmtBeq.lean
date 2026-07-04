import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.smtBeq` onto the unpacked form. -/
example (x y : PackedFloat 3 4) :
    PackedFloat.smtBeq x y = EUnpackedFloat.smtBeq x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
