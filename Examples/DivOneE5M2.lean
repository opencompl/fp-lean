import Fp

namespace Example

theorem div_one_is_id_e5m2 (a : PackedFloat 5 2) (h : a.isNaN = false) :
    a / oneE5M2 = a := by
  bv_decide

/-- info: 'Example.div_one_is_id_e5m2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms div_one_is_id_e5m2

end Example
