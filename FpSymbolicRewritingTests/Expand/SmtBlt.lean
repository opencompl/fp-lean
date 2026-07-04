import Fp
/-! `fp_expand_pack_unpack` expands `PackedFloat.smtBlt` onto the unpacked form. -/
example (wbn : Bool) (x y : PackedFloat 3 4) :
    PackedFloat.smtBlt wbn x y = EUnpackedFloat.smtBlt wbn x.unpack y.unpack := by
  simp only [fp_expand_pack_unpack]
