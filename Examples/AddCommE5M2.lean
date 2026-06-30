import Fp

namespace Example

theorem add_comm_e5m2 (x y : PackedFloat 5 2) : x + y = y + x := by
  bv_decide

/-- info: 'Example.add_comm_e5m2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms add_comm_e5m2

end Example
