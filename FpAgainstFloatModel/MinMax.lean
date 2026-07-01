import FpAgainstFloatModel.Basic

/-! # `min`/`max` agree with `Float.Model.{min,max}`.

The model's `Min`/`Max` are left-leaning (`Min.leftLeaningOfLE`); we match them to the
project's `smtMin`/`smtMax`. NOTE: IEEE min/max on differing-signed zeros is under-specified;
the `xOnDiffZeros` flag is fixed to `false` here and this is the point most likely to need a
convention tweak. -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

theorem min_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (PackedFloat.smtMin false a b).ModelEquiv (Min.min fa fb) := by
  sorry

theorem max_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (PackedFloat.smtMax false a b).ModelEquiv (Max.max fa fb) := by
  sorry

end FpAgainstFloatModel
