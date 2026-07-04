import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.smtBgt` onto the unpacked form. -/
example (wbn : Bool) (x y : PackedFloat 3 4) :
    PackedFloat.smtBgt wbn x y = EUnpackedFloat.smtBgt wbn x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
