import Fp

namespace Example

theorem add_eq_mul_two_e5m2 (x : PackedFloat 5 2) : x + x = x * twoE5M2 := by
  bv_decide

/-- info: 'Example.add_eq_mul_two_e5m2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms add_eq_mul_two_e5m2

end Example
