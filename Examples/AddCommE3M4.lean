import Fp

namespace Example

theorem add_comm_e3m4 (x y : PackedFloat 3 4) : x + y = y + x := by
  bv_decide

/-- info: 'Example.add_comm_e3m4' depends on axioms: [propext, Classical.choice, Quot.sound, add_comm_e3m4._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in #print axioms add_comm_e3m4

end Example
