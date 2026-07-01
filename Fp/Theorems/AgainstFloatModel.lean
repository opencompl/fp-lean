import Fp.Theorems.AgainstFloatModel.Basic
import Fp.Theorems.AgainstFloatModel.Add
import Fp.Theorems.AgainstFloatModel.Sub
import Fp.Theorems.AgainstFloatModel.Mul
import Fp.Theorems.AgainstFloatModel.Div
import Fp.Theorems.AgainstFloatModel.Neg
import Fp.Theorems.AgainstFloatModel.Abs
import Fp.Theorems.AgainstFloatModel.Sqrt
import Fp.Theorems.AgainstFloatModel.Compare
import Fp.Theorems.AgainstFloatModel.MinMax

/-!
# `PackedFloat` agrees with Lean's `Float.Model` (IEEE `binary64`)

Umbrella module. `PackedFloat 11 52` with its round-to-nearest-even arithmetic (`+`,`-`,`*`,
`/`, `neg`, `abs`, `sqrt`) and SMT-LIB comparators (`smtBle`/`smtBlt`/`ieeeBeq`/`smtMin`/
`smtMax`) computes bit-identical (up to NaN) results to `Float.Model`, via the single
relation `PackedFloat.ModelEquiv`.

- Foundation + `ModelEquiv` / `UnpackedRel`: `AgainstFloatModel/Basic.lean`.
- One agreement theorem per file: `Add`, `Sub`, `Mul`, `Div`, `Neg`, `Abs`, `Sqrt`,
  `Compare` (`le`/`lt`/`beq`/`compare`), `MinMax`.

**Status:** all statements typed; proofs are `sorry`. `toModelUnpacked` is `sorry`-free and
validated empirically against `Float.Model.unpack`. **Scope:** round-to-nearest-even only;
the model has no `rem`/`fma`/`roundToInt` counterpart. See the ordering plan in
`AgainstFloatModel/ORDER.md`.
-/
