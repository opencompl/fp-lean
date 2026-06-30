import Fp

namespace Example

theorem add_monotone_e3m4 (a b c : PackedFloat 3 4)
    (hle : PackedFloat.smtBle false a b = true)
    (hcinf : c.isInfinite = false) (hcnan : c.isNaN = false) :
    PackedFloat.smtBle false (a + c) (b + c) = true := by
  bv_decide

/-- info: 'Example.add_monotone_e3m4' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms add_monotone_e3m4

end Example
