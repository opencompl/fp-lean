import Fp

namespace Example

theorem div_one_is_id_e5m2 (a : PackedFloat 5 2) (h : a.isNaN = false) :
    a / oneE5M2 = a := by
  bv_decide

/-- info: 'Example.div_one_is_id_e5m2' depends on axioms: [propext, Classical.choice, Quot.sound, div_one_is_id_e5m2._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in #print axioms div_one_is_id_e5m2

end Example
