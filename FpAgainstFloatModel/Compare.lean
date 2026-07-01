import FpAgainstFloatModel.Basic

/-! # Comparisons agree with `Float.Model.{le,lt,beq,compare}`.

The model's `le`/`lt`/`beq` are the IEEE partial order (`NaN` incomparable, `±0` equal),
matching the project's SMT-LIB comparators with the `whenBothNaN := false` flag. All proofs
relate the two comparison circuits on the unpacked forms — no rational comparison. -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

theorem le_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    PackedFloat.smtBle false a b = fa.le fb := by
  sorry

theorem lt_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    PackedFloat.smtBlt false a b = fa.lt fb := by
  sorry

theorem beq_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    PackedFloat.ieeeBeq a b = fa.beq fb := by
  sorry

/-- An `Option Ordering` comparison on `PackedFloat`, matching `Float.Model.compare`
(`none` on NaN, `some .eq` on `±0`). -/
def compareOpt (x y : PackedFloat 11 52) : Option Ordering :=
  if x.isNaN || y.isNaN then none
  else if PackedFloat.ieeeBeq x y then some .eq
  else if PackedFloat.smtBlt false x y then some .lt
  else some .gt

theorem compare_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    compareOpt a b = fa.compare fb := by
  sorry

end FpAgainstFloatModel
