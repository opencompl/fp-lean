import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.smtBge` onto the unpacked form. -/
example (wbn : Bool) (x y : PackedFloat 3 4) :
    PackedFloat.smtBge wbn x y = EUnpackedFloat.smtBge wbn x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
