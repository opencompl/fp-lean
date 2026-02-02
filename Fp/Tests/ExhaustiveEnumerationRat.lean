/-
Exhuaustively enumerate semantics by rational number comparisons.
-/
import Fp.Basic
import Fp.Addition
import Fp.Multiplication
import Fp.Division
import Fp.Sqrt
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
  expectedRat : Rat

def UnpackedRatTestResult.producedRat (res : UnpackedRatTestResult ein sin) : Rat :=
  res.producedUnpacked.toRat


/--
Return the numerical precision of the rational number.
If the rational is less than `2^-i`, then it has precision at least i.
returns None if the rational is zero.
-/
def getRatPrecision (r : Rat) (maxPrec : Nat) : Option Nat :=
  if r = 0 then none
  else Id.run do
    let mut prec : Nat := 0
    for _ in [:maxPrec] do
      if r.abs ≥ (1 : Rat) / (2 : Rat) ^ (prec : Nat) then
        break
      else
        prec := prec + 1
    return prec

/--
Return the precision of the produced result compared to the expected result.
-/
def UnpackedRatTestResult.precision {ein sin : Nat}
      (res : UnpackedRatTestResult ein sin) (maxPrec : Nat) : Option Nat :=
    let diff := (res.producedRat - res.expectedRat).abs
    getRatPrecision diff maxPrec

/--
Check if the test result is a success, i.e., if the precision is at least `expectedPrecision`.
-/
def UnpackedRatTestResult.isSuccess {ein sin : Nat}
    (res : UnpackedRatTestResult ein sin) (expectedPrecision : Nat := sin + 2) : Bool :=
  match res.precision (maxPrec := expectedPrecision * 2) with
  | none => true
  | some p => p >= expectedPrecision

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

instance : Std.ToFormat Dyadic where
  format d :=
    match d.precision with
    | none => "0"
    | some prec =>
      if prec < 0 then
        f!"{d.numerator}/2^{prec.natAbs}"
      else
        f!"{d.numerator}*2^{prec.natAbs}"

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
    let maxPrec : Nat := sin * 5
    let delta := (record.producedRat - record.expectedRat).abs
    let _deltaDyadic := delta.toDyadic maxPrec
    out := out ++
      f!"    args: {formatArgs record.args}, produced: {record.producedRat}, expected: {record.expectedRat}, δ: {delta}={(Float.ofInt delta.num) / (Float.ofNat delta.den)}: {record.precision (maxPrec := maxPrec)}, expected precision {sin + 2} \n"
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

def testDiv (ein sin : Nat) : IO (UnpackedRatTestSummary ein sin) := do
  let mut results : Array (UnpackedRatTestResult ein sin) := #[]
  let enum : PackedFloatEnumeration ein sin := PackedFloatEnumeration.mk ein sin
  for (pf1, r1) in enum.enumeration do
    for (pf2, r2) in enum.enumeration do
      if r2 == 0 then continue
      let uf1 := pf1.unpack.num
      let uf2 := pf2.unpack.num
      let produced := UnpackedFloat.div uf1 uf2
      let expected := r1 / r2
      let result := UnpackedRatTestResult.mk (Array.mk [(pf1, r1), (pf2, r2)]) produced expected
      results := results.push result
  return summarizeUnpackedRatTestResults "div" results

/--
Compute a rational approximation of sqrt(r) using Newton's method.
-/
def ratSqrt (r : Rat) (iters : Nat := 20) : Rat :=
  if r ≤ 0 then 0
  else Id.run do
    let mut x : Rat := r
    for _ in [:iters] do
      x := (x + r / x) / 2
    return x

/--
Produce the results from taking the square root of all packed floats
for the given exponent and significand sizes.
-/
def testSqrt (ein sin : Nat) : IO (UnpackedRatTestSummary ein sin) := do
  let mut results : Array (UnpackedRatTestResult ein sin) := #[]
  let enum : PackedFloatEnumeration ein sin := PackedFloatEnumeration.mk ein sin
  for (pf, r) in enum.enumeration do
    if r ≤ 0 then continue
    let uf := pf.unpack.num
    let produced := UnpackedFloat.sqrt uf
    let expected := ratSqrt r
    let result := UnpackedRatTestResult.mk (Array.mk [(pf, r)]) produced expected
    results := results.push result
  return summarizeUnpackedRatTestResults "sqrt" results

end ExhaustiveEnumerationRat
end Fp
