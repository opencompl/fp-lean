import Fp

namespace Example

theorem mul_one_is_id_e5m2 (a : PackedFloat 5 2) (h : a.isNaN = false) :
    a * oneE5M2 = a := by
  bv_decide

/-- info: 'Example.mul_one_is_id_e5m2' depends on axioms: [propext, Classical.choice, Quot.sound, mul_one_is_id_e5m2._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in #print axioms mul_one_is_id_e5m2

end Example
