import Fp

namespace Example

theorem div_self_is_one_e3m4 (a : PackedFloat 3 4)
    (h1 : a.isNaN = false) (h2 : a.isInfinite = false) (h3 : a.isZero = false) :
    a / a = oneE3M4 := by
  bv_decide

/-- info: 'Example.div_self_is_one_e3m4' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms div_self_is_one_e3m4

end Example
