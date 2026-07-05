import Fp.PackedFloat.Lemmas

/-!
# Classification predicates as bit patterns (BTRW15)

The `PackedFloat` kind-classification predicates coincide with the bit-pattern sets of
Brain–Tinelli–Rümmer–Wahl (BTRW15). Writing `0` for the all-zeros exponent `0_ε` and
`allOnes` for the all-ones exponent `1_ε`, and `m` for the significand:

| predicate      | BTRW15 set | bit pattern                    |
|----------------|------------|--------------------------------|
| `fp.isZero`      | `FZ`     | `e = 0`,      `m = 0`          |
| `fp.isSubnormal` | `FS`     | `e = 0`,      `m ≠ 0`          |
| `fp.isNormal`    | `FN`     | `e ≠ allOnes`, `e ≠ 0`        |
| `fp.isInfinite`  | `FI`     | `e = allOnes`, `m = 0`        |
| `fp.isNaN`       | `{NaN}`  | `e = allOnes`, `m ≠ 0`        |

The `hs : 0 < s` / `he : 0 < e` hypotheses rule out the degenerate zero-width formats
(BTRW15 assumes `ε, σ ≥ 1`), where the circuit collapses some cases (e.g. with no
significand bits every all-ones exponent is taken to be NaN).
-/

namespace PackedFloat

/-- `fp.isNaN`: exponent all-ones, significand nonzero. -/
theorem isNaN_iff (pf : PackedFloat e s) (hs : 0 < s) :
    pf.isNaN ↔ (pf.ex = .allOnes e ∧ pf.sig ≠ 0#s) :=
  isNaN_iff_ex_eq_sig_eq pf hs

/-- `fp.isInfinite`: exponent all-ones, significand zero. -/
theorem isInfinite_iff (pf : PackedFloat e s) (hs : 0 < s) :
    pf.isInfinite ↔ (pf.ex = .allOnes e ∧ pf.sig = 0#s) :=
  isInfinite_iff_ex_eq_sig_eq pf hs

/-- `fp.isZero`: exponent zero, significand zero. -/
theorem isZero_iff (pf : PackedFloat e s) (he : 0 < e) :
    pf.isZero ↔ (pf.ex = 0#e ∧ pf.sig = 0#s) :=
  isZero_iff_ex_eq_zero_and_sig_eq_zero he

/-- `fp.isNormal`: exponent neither all-ones nor zero. -/
theorem isNormal_iff (pf : PackedFloat e s) :
    pf.isNorm ↔ (pf.ex ≠ .allOnes e ∧ pf.ex ≠ 0#e) := by
  rw [isNorm_iff_ex_ne_allOnes_and_ex_ne_zero, BitVec.zero_eq]

/-- `fp.isSubnormal`: exponent zero, significand nonzero. -/
theorem isSubnormal_iff (pf : PackedFloat e s) (he : 0 < e) :
    pf.isNonzeroSubnorm ↔ (pf.ex = 0#e ∧ pf.sig ≠ 0#s) := by
  simp only [isNonzeroSubnorm, BitVec.zero_eq, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, decide_eq_true_eq]
  grind

end PackedFloat
