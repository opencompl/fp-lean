import Fp.SmtLibSemantics

/-!
# `abs` circuit vs. SMT-LIB spec

The bit-blasted `PackedFloat.abs` (clear the sign bit unconditionally) agrees with the
SMT-LIB spec `SmtLibSemantics.SmtLibFunctions.abs` (clear the sign bit, but return NaN
inputs unchanged) up to the NaN bit pattern.

There is no rounding involved, so unlike `add`/`mul`/… this holds for every width and
every rounding mode.
-/

namespace Fp

theorem abs_eq_abs {e s : Nat} (a : PackedFloat e s) :
    (Fp.SmtLibSemantics.SmtLibFunctions.abs a).EquivUptoNaN (PackedFloat.abs a) := by
  unfold Fp.SmtLibSemantics.SmtLibFunctions.abs
  split
  case isTrue ha =>
    -- spec returns `a` (a NaN), circuit returns `abs a` (also a NaN since `isNaN`
    -- ignores the sign bit, so `(abs a).isNaN` is defeq to `a.isNaN`).
    apply PackedFloat.EquivUptoNaN.of_isNaN_isNaN
    · exact ha
    · exact ha
  case isFalse ha =>
    -- Neither side is NaN, and both reduce to `{ a with sign := false } = abs a`.
    exact PackedFloat.EquivUptoNaN.of_eq _ _ rfl

/--
info: 'Fp.abs_eq_abs' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in #print axioms abs_eq_abs

end Fp
