import Fp.UnpackedFloat.Basic
import Fp.Basic

@[simp]
theorem UnpackedFloat.isZero_iff (x : UnpackedFloat e s) :
  x.isZero = true ↔ x.toRat = 0 := by
  simp [UnpackedFloat.isZero]
  constructor
  · intros h
    simp at h
    simp [UnpackedFloat.toRat_eq_toRat']
    rw [← h]
    simp [UnpackedFloat.toRat]
  · intros h
    simp at h
    rw [h]
    simp [UnpackedFloat.toRat]
