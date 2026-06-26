import Fp.EUnpackedFloat.Basic

/-!
## EUnpackedFloat classification/constructor lemmas

Lemmas about isNaN/isInfinite/isNumber/isZero, sign, mkNaN/mkInfinity/mkNumber/mkZero, normalize.
-/

namespace EUnpackedFloat


@[bv_normalize]
theorem eq_state_ex {e s b} {x y : EUnpackedFloat e s} :
  (bif b then x else y).state = bif b then x.state else y.state := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_num_ex {x y : EUnpackedFloat e s} :
  (bif b then x else y).num = bif b then x.num else y.num := by
  cases b <;> rfl



@[simp, grind =]
theorem isNaN_eq_decide (x : EUnpackedFloat e s) : isNaN x = decide (x.state = .NaN) := by
  simp [isNaN]
  grind only

@[simp]
theorem isNaN_neg_eq_isNaN (x : EUnpackedFloat e s) : isNaN (- x) = isNaN x := by
  rw [← EUnpackedFloat.neg_def]
  simp [isNaN, neg]

@[simp, grind =]
theorem isInfinite_eq_decide (x : EUnpackedFloat e s) : isInfinite x = decide (x.state = .Infinity) := by
  simp [isInfinite]
  grind only

@[simp, grind =]
theorem isInfinite_neg_eq_isInfinite (x : EUnpackedFloat e s) : isInfinite (- x) = isInfinite x := by
  rw [← EUnpackedFloat.neg_def]
  simp [isInfinite, neg]

@[simp, grind =]
theorem isNumber_eq_decide (x : EUnpackedFloat e s) : isNumber x = decide (x.state = .Number) := by
  simp [isNumber]
  grind only

@[simp, grind .]
theorem state_eq_number_of_isZero (x : EUnpackedFloat e s) (h : x.isZero) : x.state = .Number := by
  simp [isZero] at h ⊢
  grind only

@[simp]
theorem neg_sign (x : EUnpackedFloat e s) : (-x).sign = !x.sign := by
  rw [← EUnpackedFloat.neg_def]
  simp [sign, neg]

@[simp]
theorem neg_state (uf : EUnpackedFloat e s) : (-uf).state = uf.state := by
  rw [← EUnpackedFloat.neg_def]
  simp [neg]

@[simp]
theorem state_mkNaN : (mkNaN : EUnpackedFloat e s).state = .NaN := rfl

@[simp]
theorem state_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).state = .Infinity := rfl

@[simp]
theorem sign_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).sign = sign := rfl

@[simp]
theorem sign_num_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).num.sign = sign := rfl

@[simp, grind =]
theorem eq_of_mkInfinity_eq_mkInfinity {e s} (sign1 sign2 : Bool) :
    (mkInfinity sign1 : EUnpackedFloat e s) = mkInfinity sign2 ↔ sign1 = sign2 := by
  simp [mkInfinity]

@[simp]
theorem state_mkNumber (num : UnpackedFloat e s) : (mkNumber num : EUnpackedFloat e s).state = .Number := rfl

@[simp]
theorem num_mkNumber (num : UnpackedFloat e s) : (mkNumber num : EUnpackedFloat e s).num = num := rfl

@[simp]
theorem isNaN_mkNaN {e s} : isNaN (EUnpackedFloat.mkNaN : EUnpackedFloat e s)  = true := rfl

@[simp]
theorem isNaN_mkInfinity {e s} {sign : Bool} : isNaN (mkInfinity sign : EUnpackedFloat e s) = false := by
  simp [isNaN, mkInfinity]

@[simp]
theorem isNaN_mkNumber {e s} (num : UnpackedFloat e s) : isNaN (mkNumber num : EUnpackedFloat e s) = false := by
  simp [isNaN, mkNumber]

@[simp]
theorem isInfinite_mkNaN {e s} : isInfinite (EUnpackedFloat.mkNaN : EUnpackedFloat e s) = false := by
  simp [isInfinite, mkNaN]

@[simp]
theorem isInfinite_mkInfinity {e s} (sign : Bool) : isInfinite (mkInfinity sign : EUnpackedFloat e s) = true := rfl

@[simp]
theorem isInfinite_mkNumber {e s} (num : UnpackedFloat e s) : isInfinite (mkNumber num : EUnpackedFloat e s) = false := by
  simp [isInfinite, mkNumber]

@[simp]
theorem isNumber_mkNaN {e s} : isNumber (EUnpackedFloat.mkNaN : EUnpackedFloat e s) = false := by
  simp [isNumber, mkNaN]

@[simp]
theorem isNumber_mkInfinity {e s} (sign : Bool) : isNumber (mkInfinity sign : EUnpackedFloat e s) = false := by
  simp [isNumber, mkInfinity]

@[simp]
theorem isNumber_mkNumber {e s} (num : UnpackedFloat e s) : isNumber (mkNumber num : EUnpackedFloat e s) = true := rfl

@[simp, grind =]
theorem mkZero_sign {e s} (sign : Bool) : (mkZero sign : EUnpackedFloat e s).sign = sign := by
  simp [mkZero, EUnpackedFloat.sign, UnpackedFloat.mkZero]

@[simp, grind =]
theorem num_mkZero {e s} (sign : Bool) :
    (mkZero sign : EUnpackedFloat e s).num = UnpackedFloat.mkZero sign := rfl

@[simp, grind =]
theorem mkZero_num_sign {e s} (sign : Bool) : (mkZero sign : EUnpackedFloat e s).num.sign = sign := by
  simp [mkZero, UnpackedFloat.mkZero]

@[simp, grind! .]
theorem isZero_mkZero {e s} (sign : Bool) : isZero (mkZero sign : EUnpackedFloat e s) = true := by
  simp [isZero, mkZero, UnpackedFloat.mkZero, isNumber, UnpackedFloat.isZero]

@[simp, grind! . ]
theorem isZero_mkInfinity {e s} (sign : Bool) : isZero (mkInfinity sign : EUnpackedFloat e s) = false := by
  simp [isZero, mkInfinity, isNumber, mkInfinity]

@[simp, grind! .]
theorem isZero_mkNaN {e s} : isZero (EUnpackedFloat.mkNaN : EUnpackedFloat e s) = false := by
  simp [isZero, mkNaN, isNumber, mkNaN]

@[simp, grind! .]
theorem isZero_mkNumber {e s} (num : UnpackedFloat e s) : isZero (mkNumber num : EUnpackedFloat e s) = num.isZero := by
  simp [isZero, mkNumber, isNumber, UnpackedFloat.isZero]

@[simp, grind! .]
theorem isNaN_mkZero {e s} (sign : Bool) : isNaN (EUnpackedFloat.mkZero sign : EUnpackedFloat e s) = false := by
  simp [isNaN, mkZero]

@[simp, grind! .]
theorem isInfinite_mkZero {e s} (sign : Bool) : isInfinite (EUnpackedFloat.mkZero sign : EUnpackedFloat e s) = false := by
  simp [isInfinite, mkZero]

@[simp, grind! .]
theorem isNumber_mkZero {e s} (sign : Bool) : isNumber (mkZero sign : EUnpackedFloat e s) = true := by
  simp [mkZero, UnpackedFloat.mkZero, isNumber]

@[simp]
theorem state_normalize (euf : EUnpackedFloat e s) : (normalize euf).state = euf.state := by
  simp [normalize]
  by_cases hs : euf.state = .Number
  · simp [hs]
  · simp [hs]
end EUnpackedFloat
