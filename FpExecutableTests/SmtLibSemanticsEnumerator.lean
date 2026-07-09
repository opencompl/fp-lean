import Fp.Rounding
import Fp.SmtLibSemantics
import Fp.Comparison
import Fp.Theorems.LowerUpperRound.Functional
import FpExecutableTests.PackedFloatEnumeration

namespace Fp
open SmtLibSemantics

namespace SmtLibSemanticsEnumerator

/-
This file defines a computable version of the SMT-LIB semantics,
which is used for comparing results from SMT solvers with those from Lean's floating-point library.

The computable lower/upper bounds are routed through the *proven* enumeration
`Fp.lower` / `Fp.upper` (`Fp.Theorems.LowerUpperRound.Functional`), which are
proven equal to the noncomputable SMT-LIB spec `smtLibLower` / `smtLibUpper`
(see `Fp.smtLibLower_eq_lower` / `Fp.smtLibUpper_eq_upper`, both axiom-clean).
So the runtime rounder here inherits that correctness guarantee.
-/

/--
Computable SMT-LIB greatest lower bound, via the proven `Fp.lower`.

`Fp.lower` requires `0 < e` and `0 < s`; every floating-point format we test
satisfies this, so the `getNaN` fallback for the degenerate `e = 0` / `s = 0`
widths is unreachable in practice.
-/
def lowerProven (e s : Nat) (r : ExtRat) : PackedFloat e s :=
  if he : 0 < e then
    if hs : 0 < s then Fp.lower e s he hs r
    else PackedFloat.getNaN e s
  else PackedFloat.getNaN e s

/-- Computable SMT-LIB least upper bound, via the proven `Fp.upper`. See `lowerProven`. -/
def upperProven (e s : Nat) (r : ExtRat) : PackedFloat e s :=
  if he : 0 < e then
    if hs : 0 < s then Fp.upper e s he hs r
    else PackedFloat.getNaN e s
  else PackedFloat.getNaN e s

def computableV : RoundableAdjunction (PackedFloat e s) ExtRat where
  lower := lowerProven e s
  upper := upperProven e s
  embed := PackedFloat.toExtRat

abbrev computableSmtLibRoundMethod (e s : Nat) :
    RoundMethod (PackedFloat e s) ExtRat := smtLibRoundMethod e s
    (computableV)
    (computableV)

instance : DecidablePred ((computableSmtLibRoundMethod e s).lowerHalf) := by
  simp [computableSmtLibRoundMethod]
  infer_instance

instance : DecidablePred ((computableSmtLibRoundMethod e s).tieBreak) := by
  simp [computableSmtLibRoundMethod]
  infer_instance


/-- A computable version of the SMT-LIB rounder functions. -/
def computableSmtLibRound {e s : Nat}
  (rm : RoundingMode) (sign : Bool)
  (r : ExtRat) : PackedFloat e s :=
  (computableSmtLibRoundMethod e s).round rm sign r

/-!
## Min/Max Relation Tests

We test that the concrete implementations `PackedFloat.smtMax` and `PackedFloat.smtMin`
satisfy the abstract SMT-LIB relations `FpMaxRel` and `FpMinRel`.
-/

/-- The embedding of PackedFloat into ExtRat, used for testing relations. -/
def computableVEmbed {e s : Nat} : RoundableEmbed (PackedFloat e s) ExtRat where
  embed := PackedFloat.toExtRat

/-- Test result for min/max relation tests. -/
structure MinMaxTestResult (e s : Nat) where
  f : PackedFloat e s
  g : PackedFloat e s
  h : PackedFloat e s
  zpm : Bool
  zmp : Bool
  relationHolds : Bool

/-- Summary of min/max test results. -/
structure MinMaxTestSummary (e s : Nat) where
  op : String
  failures : Nat := 0
  successes : Nat := 0
  failedRecords : Array (MinMaxTestResult e s) := #[]

def MinMaxTestSummary.toFormat (summary : MinMaxTestSummary e s)
    (nFailedRecordsToPrint : Nat := 5) : Std.Format := Id.run do
  let percentSuccess : Float :=
    if summary.failures + summary.successes == 0 then 100
    else (summary.successes).toFloat / ((summary.failures + summary.successes).toFloat) * 100
  let mut out :=
    "===" ++ "\n" ++
    f!"🧪 Testing {summary.op} Relation exp({e}) significand({s}) | #success ({summary.successes}) #failures ({summary.failures}) %success({percentSuccess})\n"
  if summary.failures == 0 then
    out := out ++ "  ✅  (no failed records)\n"
    return out
  else
    out := out ++ "  ❌  Failed Records:\n"
  let mut nPrinted := 0
  for record in summary.failedRecords do
    if nPrinted >= nFailedRecordsToPrint then
      out := out ++ f!"    ... (truncated, {summary.failedRecords.size - nPrinted} more failed records)\n"
      break
    out := out ++
      f!"    f: {reprStr record.f.toExtRat}, g: {reprStr record.g.toExtRat}, h: {reprStr record.h.toExtRat}, zpm: {record.zpm}, zmp: {record.zmp}\n"
    nPrinted := nPrinted + 1
  return out

/-- Generate all PackedFloats including NaN and infinities for testing. -/
def allPackedFloats (e s : Nat) : Array (PackedFloat e s) := Id.run do
  let mut arr : Array (PackedFloat e s) := #[]
  for sign in [true, false] do
    for exp in [:2^e] do
      for sig in [:2^s] do
        let pf : PackedFloat e s := PackedFloat.mk sign exp sig
        arr := arr.push pf
  return arr

/-- Test that `PackedFloat.smtMax` satisfies `FpMaxRel`. -/
def testFpMaxRel (e s : Nat) : IO (MinMaxTestSummary e s) := do
  let mut summary : MinMaxTestSummary e s := { op := "FpMaxRel" }
  let allFloats := allPackedFloats e s
  for f in allFloats do
    for g in allFloats do
      for zpm in [true, false] do
        for zmp in [true, false] do
          let h := PackedFloat.smtMax zpm zmp f g
          let v := computableVEmbed (e := e) (s := s)
          let relationHolds := FpMaxRel v f g h
          if relationHolds then
            summary := { summary with successes := summary.successes + 1 }
          else
            let record : MinMaxTestResult e s := {
              f := f, g := g, h := h,
              zpm := zpm, zmp := zmp,
              relationHolds := relationHolds
            }
            summary := { summary with
              failures := summary.failures + 1,
              failedRecords := summary.failedRecords.push record
            }
  return summary

/-- Test that `PackedFloat.smtMin` satisfies `FpMinRel`. -/
def testFpMinRel (e s : Nat) : IO (MinMaxTestSummary e s) := do
  let mut summary : MinMaxTestSummary e s := { op := "FpMinRel" }
  let allFloats := allPackedFloats e s
  for f in allFloats do
    for g in allFloats do
      for zpm in [true, false] do
        for zmp in [true, false] do
          let h := PackedFloat.smtMin zpm zmp f g
          let v := computableVEmbed (e := e) (s := s)
          let relationHolds := FpMinRel v f g h
          if relationHolds then
            summary := { summary with successes := summary.successes + 1 }
          else
            let record : MinMaxTestResult e s := {
              f := f, g := g, h := h,
              zpm := zpm, zmp := zmp,
              relationHolds := relationHolds
            }
            summary := { summary with
              failures := summary.failures + 1,
              failedRecords := summary.failedRecords.push record
            }
  return summary

/-!
## Binary Relation Tests

We test that the concrete comparison implementations satisfy the abstract SMT-LIB relations.
For each relation, we verify bi-implication: `boolFn f g = true ↔ Rel v f g`.
-/

/-- Test result for binary relation tests. -/
structure BinaryRelTestResult (e s : Nat) where
  f : PackedFloat e s
  g : PackedFloat e s
  boolResult : Bool
  relationHolds : Bool

/-- Summary of binary relation test results. -/
structure BinaryRelTestSummary (e s : Nat) where
  op : String
  failures : Nat := 0
  successes : Nat := 0
  failedRecords : Array (BinaryRelTestResult e s) := #[]

def BinaryRelTestSummary.toFormat (summary : BinaryRelTestSummary e s)
    (nFailedRecordsToPrint : Nat := 5) : Std.Format := Id.run do
  let percentSuccess : Float :=
    if summary.failures + summary.successes == 0 then 100
    else (summary.successes).toFloat / ((summary.failures + summary.successes).toFloat) * 100
  let mut out :=
    "===" ++ "\n" ++
    f!"🧪 Testing {summary.op} Relation exp({e}) significand({s}) | #success ({summary.successes}) #failures ({summary.failures}) %success({percentSuccess})\n"
  if summary.failures == 0 then
    out := out ++ "  ✅  (no failed records)\n"
    return out
  else
    out := out ++ "  ❌  Failed Records:\n"
  let mut nPrinted := 0
  for record in summary.failedRecords do
    if nPrinted >= nFailedRecordsToPrint then
      out := out ++ f!"    ... (truncated, {summary.failedRecords.size - nPrinted} more failed records)\n"
      break
    out := out ++
      f!"    f: {reprStr record.f.toExtRat}, g: {reprStr record.g.toExtRat}, bool: {record.boolResult}, rel: {record.relationHolds}\n"
    nPrinted := nPrinted + 1
  return out

/-- Generic test for binary relations: verifies `boolFn f g = true ↔ Rel v f g`. -/
def testBinaryRel (e s : Nat) (opName : String)
    (boolFn : PackedFloat e s → PackedFloat e s → Bool)
    (relFn : RoundableEmbed (PackedFloat e s) ExtRat → PackedFloat e s → PackedFloat e s → Prop)
    [∀ v f g, Decidable (relFn v f g)] : IO (BinaryRelTestSummary e s) := do
  let mut summary : BinaryRelTestSummary e s := { op := opName }
  let allFloats := allPackedFloats e s
  let v := computableVEmbed (e := e) (s := s)
  for f in allFloats do
    for g in allFloats do
      let boolResult := boolFn f g
      let relationHolds := relFn v f g
      -- Test bi-implication: boolResult = true ↔ relationHolds
      if boolResult == relationHolds then
        summary := { summary with successes := summary.successes + 1 }
      else
        let record : BinaryRelTestResult e s := {
          f := f, g := g,
          boolResult := boolResult,
          relationHolds := relationHolds
        }
        summary := { summary with
          failures := summary.failures + 1,
          failedRecords := summary.failedRecords.push record
        }
  return summary

-- The `smtB*` order comparisons take a `whenBothNaN` boolean resolving the only
-- ambiguous case `(NaN,NaN)`; differing-signed zeros are determined. Here we
-- bake in the `(NaN,NaN)` value that reproduces each total `FpXRel` so the
-- exhaustive test exercises the full domain (including NaN and ±0 pairs).

/-- Test that `PackedFloat.smtBlt` satisfies `FpLtRel`. -/
def testFpLtRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpLtRel (smtBlt)" (PackedFloat.smtBlt false) FpLtRel

/-- Test that `PackedFloat.smtBle` satisfies `FpLeqRel`. -/
def testFpLeqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpLeqRel (smtBle)" (PackedFloat.smtBle true) FpLeqRel

/-- Test that `PackedFloat.smtBgt` satisfies `FpGtRel`. -/
def testFpGtRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpGtRel (smtBgt)" (PackedFloat.smtBgt false) FpGtRel

/-- Test that `PackedFloat.smtBge` satisfies `FpGeqRel`. -/
def testFpGeqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpGeqRel (smtBge)" (PackedFloat.smtBge true) FpGeqRel

/-- Test that `PackedFloat.smtBeq` satisfies `FpSmtLibEqRel`. -/
def testFpSmtLibEqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpSmtLibEqRel (smtBeq)" PackedFloat.smtBeq FpSmtLibEqRel

/-- Test that `PackedFloat.ieeeBeq` satisfies `FpIeeeEqRel`. -/
def testFpIeeeEqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpIeeeEqRel (ieeeBeq)" PackedFloat.ieeeBeq FpIeeeEqRel

end SmtLibSemanticsEnumerator

end Fp
