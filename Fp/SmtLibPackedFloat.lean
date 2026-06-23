import Fp.Basic
import Fp.Unpacking
import Fp.Addition
import Fp.Multiplication
import Fp.Division
import Fp.Negation

/-!
# `SmtLibPackedFloat`: `PackedFloat` quotiented by NaN-equivalence

SMT-LIB treats all NaN bit-patterns as a single floating-point value. The
`PackedFloat` representation, by contrast, has many distinct NaN bit-patterns.
`SmtLibPackedFloat e s` is the quotient of `PackedFloat e s` by
`PackedFloat.EquivUptoNaN`, which identifies all NaNs (and is otherwise
equality). This lets us state the SMT-LIB semantics up to *equality* on
`SmtLibPackedFloat`.

The `Setoid (PackedFloat e s)` instance (`PackedFloat.instSetoidEquivUptoNaN`)
lives in `Fp/Basic.lean`, next to `EquivUptoNaN`.
-/

/--
`SmtLibPackedFloat e s` is the quotient of `PackedFloat e s` by `EquivUptoNaN`,
which identifies all NaN representations (and is otherwise equality). This lets
us state the SMT-LIB semantics up to equality, since SMT-LIB treats all NaNs as
a single value.
-/
def SmtLibPackedFloat (e s : Nat) : Type :=
  Quotient (PackedFloat.instSetoidEquivUptoNaN e s)

namespace PackedFloat

/-- The canonical map sending a `PackedFloat` to its `SmtLibPackedFloat` class. -/
def toSmtLib (x : PackedFloat e s) : SmtLibPackedFloat e s :=
  Quotient.mk (PackedFloat.instSetoidEquivUptoNaN e s) x

@[simp]
theorem toSmtLib_eq_toSmtLib {x y : PackedFloat e s} :
    x.toSmtLib = y.toSmtLib ↔ EquivUptoNaN x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ## NaN propagation for the packed operations

Each arithmetic operation collapses to the canonical NaN whenever one of its
arguments is a NaN. These facts are exactly what is needed to show the
operations respect `EquivUptoNaN`, so they descend to the quotient.
-/

theorem add_eq_getNaN_of_left_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hx : x.isNaN) : PackedFloat.add m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.add, PackedFloat.unpack_eq_NaN_of_isNaN x hx, EUnpackedFloat.add]

theorem add_eq_getNaN_of_right_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hy : y.isNaN) : PackedFloat.add m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.add, PackedFloat.unpack_eq_NaN_of_isNaN y hy, EUnpackedFloat.add]

theorem mul_eq_getNaN_of_left_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hx : x.isNaN) : PackedFloat.mul m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.mul, PackedFloat.unpack_eq_NaN_of_isNaN x hx, EUnpackedFloat.mul]

theorem mul_eq_getNaN_of_right_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hy : y.isNaN) : PackedFloat.mul m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.mul, PackedFloat.unpack_eq_NaN_of_isNaN y hy, EUnpackedFloat.mul]

theorem div_eq_getNaN_of_left_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hx : x.isNaN) : PackedFloat.div m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.div, PackedFloat.unpack_eq_NaN_of_isNaN x hx, EUnpackedFloat.div]

theorem div_eq_getNaN_of_right_isNaN (m : RoundingMode) (x y : PackedFloat e s)
    (hy : y.isNaN) : PackedFloat.div m x y = PackedFloat.getNaN e s := by
  simp [PackedFloat.div, PackedFloat.unpack_eq_NaN_of_isNaN y hy, EUnpackedFloat.div]

/-! ## The operations respect `EquivUptoNaN` -/

theorem add_EquivUptoNaN (m : RoundingMode) {x x' y y' : PackedFloat e s}
    (hx : EquivUptoNaN x x') (hy : EquivUptoNaN y y') :
    EquivUptoNaN (PackedFloat.add m x y) (PackedFloat.add m x' y') := by
  rcases hx with rfl | ⟨hxn, hx'n⟩
  · rcases hy with rfl | ⟨hyn, hy'n⟩
    · exact EquivUptoNaN.refl _
    · apply EquivUptoNaN.of_eq
      rw [add_eq_getNaN_of_right_isNaN m x y hyn, add_eq_getNaN_of_right_isNaN m x y' hy'n]
  · apply EquivUptoNaN.of_eq
    rw [add_eq_getNaN_of_left_isNaN m x y hxn, add_eq_getNaN_of_left_isNaN m x' y' hx'n]

theorem mul_EquivUptoNaN (m : RoundingMode) {x x' y y' : PackedFloat e s}
    (hx : EquivUptoNaN x x') (hy : EquivUptoNaN y y') :
    EquivUptoNaN (PackedFloat.mul m x y) (PackedFloat.mul m x' y') := by
  rcases hx with rfl | ⟨hxn, hx'n⟩
  · rcases hy with rfl | ⟨hyn, hy'n⟩
    · exact EquivUptoNaN.refl _
    · apply EquivUptoNaN.of_eq
      rw [mul_eq_getNaN_of_right_isNaN m x y hyn, mul_eq_getNaN_of_right_isNaN m x y' hy'n]
  · apply EquivUptoNaN.of_eq
    rw [mul_eq_getNaN_of_left_isNaN m x y hxn, mul_eq_getNaN_of_left_isNaN m x' y' hx'n]

theorem div_EquivUptoNaN (m : RoundingMode) {x x' y y' : PackedFloat e s}
    (hx : EquivUptoNaN x x') (hy : EquivUptoNaN y y') :
    EquivUptoNaN (PackedFloat.div m x y) (PackedFloat.div m x' y') := by
  rcases hx with rfl | ⟨hxn, hx'n⟩
  · rcases hy with rfl | ⟨hyn, hy'n⟩
    · exact EquivUptoNaN.refl _
    · apply EquivUptoNaN.of_eq
      rw [div_eq_getNaN_of_right_isNaN m x y hyn, div_eq_getNaN_of_right_isNaN m x y' hy'n]
  · apply EquivUptoNaN.of_eq
    rw [div_eq_getNaN_of_left_isNaN m x y hxn, div_eq_getNaN_of_left_isNaN m x' y' hx'n]

theorem neg_EquivUptoNaN {x y : PackedFloat e s} (h : EquivUptoNaN x y) :
    EquivUptoNaN (-x) (-y) := by
  rcases h with rfl | ⟨hxn, hyn⟩
  · exact EquivUptoNaN.refl _
  · exact EquivUptoNaN.of_isNaN_isNaN _ _ (by simpa using hxn) (by simpa using hyn)

end PackedFloat

namespace SmtLibPackedFloat

/-- Addition on `SmtLibPackedFloat`, lifted from `PackedFloat.add`. -/
def add (m : RoundingMode) : SmtLibPackedFloat e s → SmtLibPackedFloat e s → SmtLibPackedFloat e s :=
  Quotient.lift₂ (fun x y => (PackedFloat.add m x y).toSmtLib)
    (fun _ _ _ _ hx hy =>
      PackedFloat.toSmtLib_eq_toSmtLib.mpr (PackedFloat.add_EquivUptoNaN m hx hy))

/-- Multiplication on `SmtLibPackedFloat`, lifted from `PackedFloat.mul`. -/
def mul (m : RoundingMode) : SmtLibPackedFloat e s → SmtLibPackedFloat e s → SmtLibPackedFloat e s :=
  Quotient.lift₂ (fun x y => (PackedFloat.mul m x y).toSmtLib)
    (fun _ _ _ _ hx hy =>
      PackedFloat.toSmtLib_eq_toSmtLib.mpr (PackedFloat.mul_EquivUptoNaN m hx hy))

/-- Division on `SmtLibPackedFloat`, lifted from `PackedFloat.div`. -/
def div (m : RoundingMode) : SmtLibPackedFloat e s → SmtLibPackedFloat e s → SmtLibPackedFloat e s :=
  Quotient.lift₂ (fun x y => (PackedFloat.div m x y).toSmtLib)
    (fun _ _ _ _ hx hy =>
      PackedFloat.toSmtLib_eq_toSmtLib.mpr (PackedFloat.div_EquivUptoNaN m hx hy))

/-- Negation on `SmtLibPackedFloat`, lifted from `PackedFloat.neg`. -/
def neg : SmtLibPackedFloat e s → SmtLibPackedFloat e s :=
  Quotient.lift (fun x => (-x).toSmtLib)
    (fun _ _ h => PackedFloat.toSmtLib_eq_toSmtLib.mpr (PackedFloat.neg_EquivUptoNaN h))

instance : Neg (SmtLibPackedFloat e s) where
  neg := SmtLibPackedFloat.neg

/-! ## Computation rules: the lifts agree with the packed operations -/

@[simp]
theorem add_toSmtLib (m : RoundingMode) (x y : PackedFloat e s) :
    SmtLibPackedFloat.add m x.toSmtLib y.toSmtLib = (PackedFloat.add m x y).toSmtLib := rfl

@[simp]
theorem mul_toSmtLib (m : RoundingMode) (x y : PackedFloat e s) :
    SmtLibPackedFloat.mul m x.toSmtLib y.toSmtLib = (PackedFloat.mul m x y).toSmtLib := rfl

@[simp]
theorem div_toSmtLib (m : RoundingMode) (x y : PackedFloat e s) :
    SmtLibPackedFloat.div m x.toSmtLib y.toSmtLib = (PackedFloat.div m x y).toSmtLib := rfl

@[simp]
theorem neg_toSmtLib (x : PackedFloat e s) :
    -x.toSmtLib = (-x).toSmtLib := rfl

end SmtLibPackedFloat
