import Fp.PackedFloat.Basic
import Fp.UnpackedFloat.Basic
import Fp.Theorems.UnpackedFloat.ToRat
import Fp.EUnpackedFloat.Basic
import Fp.Basic


/--
An unpacked float is related to a packed float
iff they have the same rational value and the same sign.
-/
def UnpackedFloat.Rel (uf : UnpackedFloat e s) (pf : PackedFloat ep sp) :=
  uf.toRat' = pf.toRat ∧ uf.sign = pf.sign -- ∧ ¬ pf.isInfinite ∧ ¬ pf.isNaN


@[simp, grind .]
theorem sign_eq_sign_of_Rel (uf : UnpackedFloat e s) (pf : PackedFloat ep sp) (hRel : uf.Rel pf) :
  uf.sign = pf.sign := by
  simp only [UnpackedFloat.Rel] at hRel
  exact hRel.2

theorem toRat'_eq_toRat_of_Rel (uf : UnpackedFloat e s) (pf : PackedFloat ep sp) (hRel : uf.Rel pf) :
  uf.toRat' = pf.toRat := by
  simp only [UnpackedFloat.Rel] at hRel
  exact hRel.1

@[grind =>]
theorem UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign (uf : UnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (hToRat : uf.toRat' = pf.toRat) (hSign : uf.sign = pf.sign) :
  UnpackedFloat.Rel uf pf := by
  simp only [UnpackedFloat.Rel]
  simp [hToRat, hSign]

theorem UnpackedFloat.Rel_of_isZero_of_isZero
  (uf : UnpackedFloat ef uf)
  (pf : PackedFloat ep sp)
  (huf : uf.isZero) (hpf : pf.isZero) (hsign : uf.sign = pf.sign) :
  UnpackedFloat.Rel uf pf := by
  simp only [UnpackedFloat.Rel]
  simp [hpf, hsign, huf]

theorem UnpackedFloat.neg_Rel_neg (he : 1 < e) (hs : 0 < s)
  (uf : UnpackedFloat e s) (pf : PackedFloat ep sp)
  (h : uf.Rel pf) :
  (- uf).Rel (-pf) := by
  constructor
  · sorry
  · simp; grind only [sign_eq_sign_of_Rel]


/--
An extended unpacked float is related to a packed float
iff they are both NaN, or they are both infinite with the same sign,
or they are either NaN and infinite, and have the same rational value and the same sign.
-/
def EUnpackedFloat.Rel (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp) :=
  (euf.isNaN ∧ pf.isNaN) ∨
  (euf.isInfinite ∧ pf.isInfinite ∧ euf.sign = pf.sign) ∨
  (¬ euf.isNaN ∧ ¬ euf.isInfinite ∧ euf.num.Rel pf)

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_isNaN_of_isNaN (euf : EUnpackedFloat ef uf)
  (pf : PackedFloat ep sp)
  (heuf : euf.isNaN) (hpf : pf.isNaN) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, hpf]

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_isInfinite_of_isInfinite_and_sign (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : euf.isInfinite) (hpf : pf.isInfinite) (hsign : euf.sign = pf.sign) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, hpf, hsign]

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_Rel_of_not_isNaN_of_not_isInfinite (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : ¬ euf.isNaN) (heuf' : ¬ euf.isInfinite) (hRel : euf.num.Rel pf) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, heuf', hRel]

theorem EUnpackedFloat.neg_Rel_neg (he : 1 < e) (hs : 0 < s)
  (euf : EUnpackedFloat e s) (pf : PackedFloat ep sp)
  (h : euf.Rel pf) :
euf.neg.Rel (-pf) := by
  simp [EUnpackedFloat.Rel]
  rcases h with h | h | h
  · have heuf : euf.neg.isNaN = true := by
      simp [h]
    have hpf : (-pf).isNaN = true := by
      simp [h]
    grind only
  · simp [h]
  · obtain ⟨hnan, hinf, hnum⟩ := h
    simp at hnan
    simp at hinf
    simp [hnan, hinf]
    apply UnpackedFloat.
    sorry
