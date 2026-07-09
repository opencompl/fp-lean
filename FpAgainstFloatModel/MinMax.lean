import FpAgainstFloatModel.Basic

/-! # `min`/`max` agree with `Float.Model.{min,max}`.

The model's `Min`/`Max` are left-leaning (`Min.leftLeaningOfLE`); we match them to the
project's `smtMin`/`smtMax`. NOTE: IEEE min/max on differing-signed zeros is under-specified;
the two tie-break flags `zpm`/`zmp` are both fixed to `false` here and this is the point most
likely to need a convention tweak (whichever `(zpm, zmp)` pair reproduces the model's
left-leaning choice on each ordering). -/

namespace FpAgainstFloatModel

variable {a b : PackedFloat 11 52} {fa fb : Float.Model}

theorem min_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (PackedFloat.smtMin false false a b).ModelEquiv (Min.min fa fb) := by
  sorry

theorem max_agree (ha : a.ModelEquiv fa) (hb : b.ModelEquiv fb) :
    (PackedFloat.smtMax false false a b).ModelEquiv (Max.max fa fb) := by
  sorry

end FpAgainstFloatModel
