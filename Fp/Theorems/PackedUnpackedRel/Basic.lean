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
