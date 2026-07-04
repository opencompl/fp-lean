import FpSymbolicRewritingTests.ConstFold.Abs
import FpSymbolicRewritingTests.ConstFold.Add
import FpSymbolicRewritingTests.ConstFold.Div
import FpSymbolicRewritingTests.ConstFold.Fma
import FpSymbolicRewritingTests.ConstFold.Mod
import FpSymbolicRewritingTests.ConstFold.Mul
import FpSymbolicRewritingTests.ConstFold.Neg
import FpSymbolicRewritingTests.ConstFold.Sub
import FpSymbolicRewritingTests.Expand.Add
import FpSymbolicRewritingTests.Expand.Div
import FpSymbolicRewritingTests.Expand.Fma
import FpSymbolicRewritingTests.Expand.IeeeBeq
import FpSymbolicRewritingTests.Expand.IsInfinite
import FpSymbolicRewritingTests.Expand.IsNaN
import FpSymbolicRewritingTests.Expand.IsZero
import FpSymbolicRewritingTests.Expand.Mod
import FpSymbolicRewritingTests.Expand.Mul
import FpSymbolicRewritingTests.Expand.SmtBeq
import FpSymbolicRewritingTests.Expand.SmtBge
import FpSymbolicRewritingTests.Expand.SmtBgt
import FpSymbolicRewritingTests.Expand.SmtBle
import FpSymbolicRewritingTests.Expand.SmtBlt
import FpSymbolicRewritingTests.Expand.SmtBne
import FpSymbolicRewritingTests.Expand.Sub
import FpSymbolicRewritingTests.Cancel.Add
import FpSymbolicRewritingTests.Cancel.Div
import FpSymbolicRewritingTests.Cancel.Fma
import FpSymbolicRewritingTests.Cancel.Mod
import FpSymbolicRewritingTests.Cancel.Mul
import FpSymbolicRewritingTests.Cancel.Sub

/-!
# FpSymbolicRewritingTests

Regression tests for the staged FP pack/unpack-cancellation simp sets. Each module
under this directory checks, via `simp only [<set>]`, that a single rewrite fires:
- `ConstFold/*` — the `fp_normalize_consts` symbolic-evaluation dsimprocs;
- `Expand/*`    — the `fp_expand_pack_unpack` op/comparison/predicate expansions;
- `Cancel/*`    — the `fp_normalize_pack_unpack_eunpacked` round-trip cancellations.
-/
