import Fp

namespace Example

theorem div_one_is_id_e3m4 (a : PackedFloat 3 4) (h : a.isNaN = false) :
    a / oneE3M4 = a := by
  bv_decide

/-- info: 'Example.div_one_is_id_e3m4' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms div_one_is_id_e3m4

end Example
