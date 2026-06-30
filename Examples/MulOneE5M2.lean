import Fp

namespace Example

theorem mul_one_is_id_e5m2 (a : PackedFloat 5 2) (h : a.isNaN = false) :
    a * oneE5M2 = a := by
  bv_decide

/-- info: 'Example.mul_one_is_id_e5m2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mul_one_is_id_e5m2

end Example
