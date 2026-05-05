import Fp.PackedFloat.Basic
import Fp.Theorems.PackedFloat.Negation
import Fp.Theorems.PackedFloat.Packing
import Fp.UnpackedFloat.Basic
import Fp.Theorems.UnpackedFloat.ToRat
import Fp.EUnpackedFloat.Basic
import Fp.Basic
import Fp.Comparison
import Fp.Utils


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

@[simp]
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

@[simp]
theorem UnpackedFloat.neg_Rel_neg
  (uf : UnpackedFloat e s) (pf : PackedFloat ep sp)
  (h : uf.Rel pf) :
  (- uf).Rel (-pf) := by
  constructor
  · simp
    apply toRat'_eq_toRat_of_Rel uf pf h
  · simp; grind only [sign_eq_sign_of_Rel]

/-- info: 'UnpackedFloat.neg_Rel_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UnpackedFloat.neg_Rel_neg

/--
An extended unpacked float is related to a packed float
iff they are both NaN, or they are both infinite with the same sign,
or they are either NaN and infinite, and have the same rational value and the same sign.
-/
def EUnpackedFloat.Rel (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp) :=
  (euf.state = .NaN ∧ pf.isNaN) ∨
  (euf.state = .Infinity ∧ pf.isInfinite ∧ euf.sign = pf.sign) ∨
  (euf.state = .Number ∧ euf.num.Rel pf)

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_state_eq_NaN_of_isNaN (euf : EUnpackedFloat ef uf)
  (pf : PackedFloat ep sp)
  (heuf : euf.state = .NaN)
  (hpf : pf.isNaN) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, hpf]

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : euf.state = .Infinity)
  (hpf : pf.isInfinite)
  (hsign : euf.sign = pf.sign) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, hpf, hsign]

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_Rel_of_state_eq_Number (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : euf.state = .Number) (hRel : euf.num.Rel pf) :
  EUnpackedFloat.Rel euf pf := by
  simp [EUnpackedFloat.Rel]
  simp [heuf, hRel]


@[simp, grind .]
theorem EUnpackedFloat.neg_Rel_neg {e s ep sp}
  (euf : EUnpackedFloat e s) (pf : PackedFloat ep sp)
  (h : euf.Rel pf) :
euf.neg.Rel (-pf) := by
  simp [EUnpackedFloat.Rel]
  rcases h with h | h | h
  · have heuf : euf.state = .NaN := by
      simp [h]
    have hpf : (pf).isNaN = true := by
      simp [h]
    grind only [=> EUnpackedFloat.isNaN_iff_state_eq]
  · simp [h]
  · obtain ⟨hnan, hinf, hnum⟩ := h
    simp [hnan]
    apply UnpackedFloat.neg_Rel_neg _ _
    grind only [=> UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign]

@[grind .]
theorem EUnpackeDFloat.num_Rel_of_Rel_of_eq_Number {e s ep sp}
  (euf : EUnpackedFloat e s) (pf : PackedFloat ep sp)
  (hRel : euf.Rel pf) (heuf : euf.state = .Number) :
  euf.num.Rel pf := by
  simp [EUnpackedFloat.Rel] at hRel
  grind only

/-- info: 'EUnpackedFloat.neg_Rel_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EUnpackedFloat.neg_Rel_neg

/--
If an extended unpacked float is related to a packed float,
then packing the extended unpacked gives a packed float that is equal
to the related one according to SMT-LIB equality.
This allows the 'NaN' bit pattern to change, but requires all else to remain equal.
Thus, all our theorems will be stated in terms of SMT-LIB equality.
-/
theorem EUnpackedFloat.pack'_EquivUptoNaN_of_Rel
    (hsp : 0 < sp)
    (euf : EUnpackedFloat (exponentWidth ep sp) (sp + 1))
    (pf : PackedFloat ep sp)
    (hRel : euf.Rel pf) :
    euf.pack'.EquivUptoNaN pf := by
  simp [EUnpackedFloat.Rel] at hRel
  simp [PackedFloat.EquivUptoNaN]
  rcases heuf : euf.state
  case NaN =>
    simp [heuf] at hRel ⊢
    simp [hRel]
  case Infinity =>
    simp [heuf] at hRel ⊢
    left
    simp [hRel, hsp]
    have := pf.eq_getInfinity_iff_isInfinity hsp |>.mp (by simp [hRel])
    rw [this]
    simp [hsp]
  case Number =>
    simp [heuf] at hRel ⊢
    left
    -- this needs an actual proof, that packing and unpacking a number returns the number.
    sorry

-- theorem unpack_eq_of_Rel (euf : EUnpackedFloat ef uf) (pf : PackedFloat (exponentWidth ef uf) (uf + 1)) (hRel : euf.Rel pf) :
--   pf.unpack = euf := sorry
