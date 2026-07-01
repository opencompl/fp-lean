import Fp

namespace Example

theorem mul_one_is_id_e3m4 (a : PackedFloat 3 4) (h : a.isNaN = false) :
    a * oneE3M4 = a := by
  bv_decide

/-- info: 'Example.mul_one_is_id_e3m4' depends on axioms: [propext, Classical.choice, Quot.sound, mul_one_is_id_e3m4._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in #print axioms mul_one_is_id_e3m4

end Example
