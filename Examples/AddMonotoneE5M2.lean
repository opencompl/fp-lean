import Fp

namespace Example

theorem add_monotone_e5m2 (a b c : PackedFloat 5 2)
    (hle : PackedFloat.smtBle false a b = true)
    (hcinf : c.isInfinite = false) (hcnan : c.isNaN = false) :
    PackedFloat.smtBle false (a + c) (b + c) = true := by
  bv_decide

/-- info: 'Example.add_monotone_e5m2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms add_monotone_e5m2

end Example
