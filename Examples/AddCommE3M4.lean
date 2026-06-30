import Fp

namespace Example

theorem add_comm_e3m4 (x y : PackedFloat 3 4) : x + y = y + x := by
  bv_decide

/-- info: 'Example.add_comm_e3m4' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms add_comm_e3m4

end Example
