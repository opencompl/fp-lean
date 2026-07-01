import FpAgainstFloatModel.Theory
import FpAgainstFloatModel.Basic
import FpAgainstFloatModel.ExtRat
import FpAgainstFloatModel.Add
import FpAgainstFloatModel.Sub
import FpAgainstFloatModel.Mul
import FpAgainstFloatModel.Div
import FpAgainstFloatModel.Neg
import FpAgainstFloatModel.Abs
import FpAgainstFloatModel.Sqrt
import FpAgainstFloatModel.Compare
import FpAgainstFloatModel.MinMax

/-!
# `PackedFloat` agrees with Lean's `Float.Model` (IEEE `binary64`)

Umbrella module. `PackedFloat 11 52` with its round-to-nearest-even arithmetic (`+`,`-`,`*`,
`/`, `neg`, `abs`, `sqrt`) and SMT-LIB comparators (`smtBle`/`smtBlt`/`ieeeBeq`/`smtMin`/
`smtMax`) computes bit-identical (up to NaN) results to `Float.Model`, via the single
relation `PackedFloat.ModelEquiv`.

- Foundation + `ModelEquiv` / `UnpackedRel`: `FpAgainstFloatModel/Basic.lean`.
- One agreement theorem per file: `Add`, `Sub`, `Mul`, `Div`, `Neg`, `Abs`, `Sqrt`,
  `Compare` (`le`/`lt`/`beq`/`compare`), `MinMax`.

**Status:** all statements typed; proofs are `sorry`. `toModelUnpacked` is `sorry`-free and
validated empirically against `Float.Model.unpack`. **Scope:** round-to-nearest-even only;
the model has no `rem`/`fma`/`roundToInt` counterpart. See the ordering plan in
`FpAgainstFloatModel/ORDER.md`.
-/
