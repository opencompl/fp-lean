/-
Exhuaustively enumerate semantics by rational number comparisons.
-/
import Fp.Basic
import Fp.Addition
import Fp.Multiplication
import Fp.Tests.PackedFloatEnumeration

namespace Fp
namespace ExhaustiveEnumerationRat

/--
Result of running an unpacked float operation test.
-/
structure UnpackedRatTestResult (ein sin : Nat) : Type where
  args : Array (PackedFloat ein sin × Rat)
  {eout : Nat}
  {sout : Nat}
  producedUnpacked : UnpackedFloat eout sout
  expectedResult : Rat

def UnpackedRatTestResult.producedRat (res : UnpackedRatTestResult ein sin) : Rat :=
  res.producedUnpacked.toRat

/-- Check if the extended rationals 'e1, 'e2' are equal within the given precision. -/
def ratWithinPrecision (r1 r2 : Rat) (prec : Nat) : Bool :=
    let diff := (r1 - r2).abs
    diff <= (2 : Rat) ^ (-(prec : Int))

/--
Return the precision difference magnitude between the produced and expected result.
-/
def UnpackedRatTestResult.precisionDifferenceMagnitude {ein sin : Nat}
    (res : UnpackedRatTestResult ein sin) : Int :=
  let diff := (res.producedRat - res.expectedResult).abs
  let dyadic := diff.toDyadic (sin + 10)
  dyadic.precision.getD 0

def UnpackedRatTestResult.isSuccess {ein sin : Nat}
    (res : UnpackedRatTestResult ein sin) (expectedPrecision : Nat := sin + 2) : Bool :=
  ratWithinPrecision res.producedRat res.expectedResult expectedPrecision

/--
A summary of the results of applying an operation,
which counts the number of successes and failures.
-/
structure UnpackedRatTestSummary (ein sin : Nat) where
  op : String
  failures : Nat := 0
  successes : Nat := 0
  records : Array (UnpackedRatTestResult ein sin) := #[]

/--
Make an empty summary for the given operation.
-/
def UnpackedRatTestSummary.empty (op : String) : UnpackedRatTestSummary ein sin :=
  { op := op }

def UnpackedRatTestSummary.toFormat (summary : UnpackedRatTestSummary ein sin)
    (nFailedRecordsToPrint? : Option Nat := some 2) : Std.Format := Id.run do
  let percentSuccess : Float :=
    if summary.failures + summary.successes == 0 then 100
    else (summary.successes).toFloat / ((summary.failures + summary.successes).toFloat) * 100
  let mut out :=
    "===" ++ "\n" ++
    f!"🧪 Testing Unpacked Rational Computations OP({summary.op}) exp({ein}) significand({sin}) | #success ({summary.successes}) #failures ({summary.failures}) %success({percentSuccess})\n"
  let nFailedRecordsToPrint := nFailedRecordsToPrint?.getD summary.records.size
  if summary.failures == 0 then
    out := out ++ "  ✅  (no failed records)\n"
    return out
  else
    out := out ++ "  ❌  Failed Records:\n"
  let mut nPrinted := 0
  for record in summary.records do
    if record.isSuccess then continue
    if nPrinted >= nFailedRecordsToPrint then
      out := out ++ f!"    ... (truncated, {summary.records.size - nPrinted} more failed records)\n"
      break
    out := out ++
      f!"    args: {formatArgs record.args}, produced: {record.producedRat}, expected: {record.expectedResult}, precision: {record.precisionDifferenceMagnitude}, expected precision {sin + 2} \n"
    nPrinted := nPrinted + 1
  return out
where
  formatArgs (arr : Array (PackedFloat ein sin × Rat)) : Std.Format :=
    Std.Format.joinSep
      (arr.map (fun (_pf, r) => f!"Q({r})")).toList
      ", "

def summarizeUnpackedRatTestResults {ein sin : Nat} (op : String)
  (results : Array (UnpackedRatTestResult ein sin)) : (UnpackedRatTestSummary ein sin) := Id.run do
  let mut summary : (UnpackedRatTestSummary ein sin) := .empty op
  for res in results do
    let isSuccess := res.isSuccess
    let updatedSummary :=
      if isSuccess then
        { op := summary.op , failures := summary.failures + 0, successes := summary.successes + 1, records := summary.records.push res }
      else
        { op := summary.op, failures := summary.failures + 1, successes := summary.successes + 0, records := summary.records.push res }
    summary := updatedSummary
  return summary

/--
Produce the results from adding all pairs of packed floats for the given exponent and significand sizes.
-/
def testAdd (ein sin : Nat) : IO (UnpackedRatTestSummary ein sin) := do
  let mut results : Array (UnpackedRatTestResult ein sin) := #[]
  let enum : PackedFloatEnumeration ein sin := PackedFloatEnumeration.mk ein sin
  for (pf1, r1) in enum.enumeration do
    for (pf2, r2) in enum.enumeration do
      let uf1 := pf1.unpack.num
      let uf2 := pf2.unpack.num
      let produced := UnpackedFloat.add uf1 uf2
      let expected := r1 + r2
      let result := UnpackedRatTestResult.mk (Array.mk [(pf1, r1), (pf2, r2)]) produced expected
      results := results.push result
  return summarizeUnpackedRatTestResults "add" results

def testMul (ein sin : Nat) : IO (UnpackedRatTestSummary ein sin) := do
  let mut results : Array (UnpackedRatTestResult ein sin) := #[]
  let enum : PackedFloatEnumeration ein sin := PackedFloatEnumeration.mk ein sin
  for (pf1, r1) in enum.enumeration do
    for (pf2, r2) in enum.enumeration do
      let uf1 := pf1.unpack.num
      let uf2 := pf2.unpack.num
      let produced := UnpackedFloat.mul uf1 uf2
      let expected := r1 * r2
      let result := UnpackedRatTestResult.mk (Array.mk [(pf1, r1), (pf2, r2)]) produced expected
      results := results.push result
  return summarizeUnpackedRatTestResults "mul" results

end ExhaustiveEnumerationRat
end Fp
