import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.smtBle` onto the unpacked form. -/
example (wbn : Bool) (x y : PackedFloat 3 4) :
    PackedFloat.smtBle wbn x y = EUnpackedFloat.smtBle wbn x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
