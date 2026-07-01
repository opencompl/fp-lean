import Fp

namespace Example

theorem add_eq_mul_two_e3m4 (x : PackedFloat 3 4) : x + x = x * twoE3M4 := by
  bv_decide

/-- info: 'Example.add_eq_mul_two_e3m4' depends on axioms: [propext, Classical.choice, Quot.sound, add_eq_mul_two_e3m4._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in #print axioms add_eq_mul_two_e3m4

end Example
