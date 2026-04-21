import Fp.Rounding
import Fp.SmtLibSemantics
import Fp.Comparison
import Fp.Tests.PackedFloatEnumeration

namespace Fp
open SmtLibSemantics

namespace SmtLibSemanticsEnumerator

def mkZero (sign : Bool) (e s : Nat) : PackedFloat e s :=
  EUnpackedFloat.mkNumber (UnpackedFloat.mkZero sign) |>.pack
/-
This file defines a computable version of the SMT-LIB semantics,
which is used for comparing results from SMT solvers with those from Lean's floating-point library.
-/

def lowerFromEmbedByEnumeration {e s}
    (enum : PackedFloatEnumeration e s) :
    RoundableLower (PackedFloat e s) ExtRat where
  lower := fun (r : ExtRat) =>
    match r with
    | .NaN => PackedFloat.getNaN e s -- NaN is representable.
    | .Infinity x => PackedFloat.getInfinity e s x -- infinity is representable.
    | .Number r =>
      -- for a number, if it is below the min number, return -inf
      match enum.greatestLowerBound r with
      | some (pf, rpf) =>
        if rpf = 0
        then mkZero false e s -- lower bound is +0 (footnote 5)
        else pf
      | none => PackedFloat.getInfinity _ _ true


def upperFromEmbedByEnumeration {e s}
    (enum : PackedFloatEnumeration e s) :
    RoundableUpper (PackedFloat e s) ExtRat where
  upper := fun (r : ExtRat) =>
    match r with
    | .NaN => PackedFloat.getNaN e s -- NaN is representable.
    | .Infinity x => .getInfinity e s x -- infinity is representable.
    | .Number r =>
      -- for a number, if it is above the max number, return +inf
      match enum.leastUpperBound r with
      | some (pf, rpf) =>
          if rpf = 0
          then mkZero true e s -- upper bound is -0 (footnote 5)
          else pf
      | none => PackedFloat.getInfinity _ _ false

def computableV : RoundableAdjunction (PackedFloat e s) ExtRat where
  lower := lowerFromEmbedByEnumeration (PackedFloatEnumeration.mk e s) |>.lower
  upper := upperFromEmbedByEnumeration (PackedFloatEnumeration.mk e s) |>.upper
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
  xOnDiffZeros : Bool
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
      f!"    f: {reprStr record.f.toExtRat}, g: {reprStr record.g.toExtRat}, h: {reprStr record.h.toExtRat}, xOnDiffZeros: {record.xOnDiffZeros}\n"
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
      for xOnDiffZeros in [true, false] do
        let h := PackedFloat.smtMax xOnDiffZeros f g
        let v := computableVEmbed (e := e) (s := s)
        let relationHolds := FpMaxRel v f g h
        if relationHolds then
          summary := { summary with successes := summary.successes + 1 }
        else
          let record : MinMaxTestResult e s := {
            f := f, g := g, h := h,
            xOnDiffZeros := xOnDiffZeros,
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
      for xOnDiffZeros in [true, false] do
        let h := PackedFloat.smtMin xOnDiffZeros f g
        let v := computableVEmbed (e := e) (s := s)
        let relationHolds := FpMinRel v f g h
        if relationHolds then
          summary := { summary with successes := summary.successes + 1 }
        else
          let record : MinMaxTestResult e s := {
            f := f, g := g, h := h,
            xOnDiffZeros := xOnDiffZeros,
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

/-- Test that `PackedFloat.smtBlt` satisfies `FpLtRel`. -/
def testFpLtRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpLtRel (smtBlt)" PackedFloat.smtBlt FpLtRel

/-- Test that `PackedFloat.smtBle` satisfies `FpLeqRel`. -/
def testFpLeqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpLeqRel (smtBle)" PackedFloat.smtBle FpLeqRel

/-- Test that `PackedFloat.smtBgt` satisfies `FpGtRel`. -/
def testFpGtRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpGtRel (smtBgt)" PackedFloat.smtBgt FpGtRel

/-- Test that `PackedFloat.smtBge` satisfies `FpGeqRel`. -/
def testFpGeqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpGeqRel (smtBge)" PackedFloat.smtBge FpGeqRel

/-- Test that `PackedFloat.smtBeq` satisfies `FpSmtLibEqRel`. -/
def testFpSmtLibEqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpSmtLibEqRel (smtBeq)" PackedFloat.smtBeq FpSmtLibEqRel

/-- Test that `PackedFloat.ieeeBeq` satisfies `FpIeeeEqRel`. -/
def testFpIeeeEqRel (e s : Nat) : IO (BinaryRelTestSummary e s) :=
  testBinaryRel e s "FpIeeeEqRel (ieeeBeq)" PackedFloat.ieeeBeq FpIeeeEqRel

end SmtLibSemanticsEnumerator

end Fp
