import Fp.EUnpackedFloat.Lemmas.Constructors

/-!
## EUnpackedFloat conversion lemmas

Lemmas about toExtDyadic/toExtRat.
-/

namespace EUnpackedFloat

@[simp]
theorem toExtRat_mkNan : toExtRat (mkNaN : EUnpackedFloat e s) = .NaN := by
  simp [toExtRat]

@[simp]
theorem toExtRat_mkInfinity (sign : Bool) : toExtRat (mkInfinity sign : EUnpackedFloat e s) = .Infinity sign := by
  simp [toExtRat]


@[simp]
theorem toExtRat_mkZero (sign : Bool) : toExtRat (mkZero sign : EUnpackedFloat e s) = .Number 0 := by
  simp [mkZero, toExtRat,
    isNaN, isInfinite,
    show (State.Number == State.NaN) = false by rfl,
    show (State.Number == State.Infinity) = false by rfl]

@[simp]
theorem toExtRat_mkNumber (num : UnpackedFloat e s) : toExtRat (mkNumber num : EUnpackedFloat e s) = .Number num.toRat := by
  simp [toExtRat]
end EUnpackedFloat
