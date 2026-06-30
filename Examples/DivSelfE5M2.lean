import Fp

namespace Example

theorem div_self_is_one_e5m2 (a : PackedFloat 5 2)
    (h1 : a.isNaN = false) (h2 : a.isInfinite = false) (h3 : a.isZero = false) :
    a / a = oneE5M2 := by
  bv_decide

/-- info: 'Example.div_self_is_one_e5m2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms div_self_is_one_e5m2

end Example
