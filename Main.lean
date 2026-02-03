import Fp
import Fp.Tests

structure OpResult where
  oper : String
  mode : RoundingMode
  result : List String

structure FPFormat where
  e : Nat
  m : Nat

def FPFormat.nbits (f : FPFormat) : Nat :=
  1 + f.e + f.m

def FPFormat.packedFloatOfNat (f : FPFormat) (n : Nat) : PackedFloat f.e f.m :=
  PackedFloat.ofBits f.e f.m (BitVec.ofNat (f.nbits) n)

structure FP8Format extends FPFormat where
  h8 : 1 + e + m = 8

namespace FP8Format
theorem h (f : FP8Format)
  : BitVec (1 + f.e + f.m) = BitVec 8 := by simp only [f.h8]
end FP8Format

def PackedFloat.toBits' (pf : PackedFloat e s) (normNaN : Bool := true) :=
  let pf := if pf.isNaN && normNaN then .mkNaN else pf
  pf.toBits

def toDigits (b : BitVec n) : String :=
  let b' := b.reverse
  String.join ((List.finRange n).map (fun i => b'[i].toNat.digitChar.toString))

instance : Repr OpResult where
  reprPrec res _ :=
    let joinedResults := String.intercalate "," (res.result)
    f!"{res.oper},{repr res.mode},{joinedResults}"

def allRoundingModes : List RoundingMode :=
  [.RNA, .RNE, .RTN, .RTP, .RTZ]

def test_add (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "add"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.add m a' b').toBits'].map toDigits
  }

def test_sub (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "sub"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.sub m a' b').toBits'].map toDigits
  }

def test_div (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "div"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.div m a' b' ).toBits'].map toDigits
  }

def test_mul (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "mul"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.mul m a' b').toBits'].map toDigits
  }

def test_lt (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "lt"
    mode := m
    result := [a, b].map toDigits ++ [(PackedFloat.bltAux false a' b').toNat.digitChar.toString]
  }

def test_min (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "min"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.minAux a'.sign a' b').toBits'].map toDigits
  }

def test_max (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "max"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.maxAux a'.sign a' b').toBits'].map toDigits
  }

def test_neg (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "neg"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits' a'.neg)].map toDigits
  }

def test_abs (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "abs"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits' a'.abs)].map toDigits
  }

def test_roundToInt (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "roundToInt"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits' (roundToInt m a'))].map toDigits
  }

def test_sqrt (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "sqrt"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits' (sqrt a' m))].map toDigits
  }

def test_rem (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "rem"
    mode := m
    result := [a, b, f.h.mp (remainder a' b').toBits'].map toDigits
  }

def test_binop (f : RoundingMode → BitVec 8 → BitVec 8 → OpResult) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).map (fun b =>
        f m (BitVec.ofNat 8 a) (BitVec.ofNat 8 b)
      )
    )
  )

def test_unop (f : RoundingMode → BitVec 8 → OpResult) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).map (fun a => f m (BitVec.ofNat 8 a))
  )

def test_unop_multi (f : RoundingMode → BitVec 8 → OpResult) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).map (fun _b =>
        f m (BitVec.ofNat 8 a)
      )
    )
  )

def test_all (f : FP8Format) : Thunk (List OpResult) :=
  List.flatten [
    Thunk.get $ test_unop  $ test_abs f,
    Thunk.get $ test_binop $ test_add f,
    Thunk.get $ test_binop $ test_div f,
    Thunk.get $ test_binop $ test_lt f,
    Thunk.get $ test_binop $ test_max f,
    Thunk.get $ test_binop $ test_min f,
    Thunk.get $ test_binop $ test_mul f,
    Thunk.get $ test_unop  $ test_neg f,
    Thunk.get $ test_binop $ test_rem f,
    Thunk.get $ test_unop  $ test_roundToInt f,
    Thunk.get $ test_unop  $ test_sqrt f,
    Thunk.get $ test_binop $ test_sub f
  ]

def test_fma (f : FP8Format) (m : RoundingMode) (a b c : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  let c' := PackedFloat.ofBits f.e f.m (f.h.mpr c)
  {
    oper := "fma"
    mode := m
    result := [a, b, c, f.h.mp (PackedFloat.fma m a' b' c').toBits'].map toDigits
  }

def test_ternop (f : RoundingMode → BitVec 8 → BitVec 8 → BitVec 8 → OpResult) (_ : Unit) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).flatMap (fun b =>
        (List.range (2 ^ 8)).map (fun c =>
          f m (BitVec.ofNat 8 a) (BitVec.ofNat 8 b) (BitVec.ofNat 8 c)
        )
      )
    )
  )

def e5m2 : FP8Format where
  e := 5
  m := 2
  h8 := by omega

def e3m4 : FP8Format where
  e := 3
  m := 4
  h8 := by omega


 def printResults (results : Thunk (List OpResult)) : IO Unit := do
  for res in results.get do
    IO.println (repr res)



def test_roundCircuitAgainstSmtlib (ein sin eout sout : Nat) : IO Unit := do
  -- round from e2m4 to e2m2
  let e2m4 : FPFormat := { e := ein, m := sin }
  let e2m2 : FPFormat := { e := eout, m := sout }
  for rm in allRoundingModes do
    IO.println "==="
    IO.println s!"🧪 ROUNDING MODE {repr rm}"
    let mut nsuccess := 0
    let mut nfailure := 0
    for x in [0:2^e2m4.nbits] do
      let pf := e2m4.packedFloatOfNat x
      if pf.isNaN then continue
      let roundSmt : PackedFloat e2m2.e e2m2.m := Fp.SmtLibSemanticsComputable.computableSmtLibRound rm pf.sign pf.unpack.toExtRat
      let roundCircuit : PackedFloat e2m2.e e2m2.m := (pf.unpack |>.round rm (targetExponentWidth := e2m2.e) (targetSignificandWidth := e2m2.m)).pack

      if roundSmt.equal_denotation roundCircuit then
        nsuccess := nsuccess + 1
        if nsuccess < 1 then
          IO.println s!""
          IO.println s!"  ✅({repr rm}) (Q: {repr pf.unpack.toExtRat}); {repr pf.unpack}"
          IO.println s!"    - (Q: {repr roundSmt.unpack.toExtRat}); {repr roundSmt.unpack}"
      else
        nfailure := nfailure + 1
        if nfailure < 10 then
         IO.println s!""
         IO.println s!"  ❌({repr rm} (Q: {repr pf.unpack.toExtRat}); {repr pf.unpack}"
         IO.println s!"    - SMT-LIB  (Q: {repr roundSmt.unpack.toExtRat}); {repr roundSmt.unpack}"
         IO.println s!"    - Circuit  (Q: {repr roundCircuit.unpack.toExtRat}); {repr roundCircuit.unpack}"
    let percentSuccess : Float :=
      if nsuccess + nfailure == 0 then 100.0
      else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
    IO.println s!"  📜 Final({repr rm}): {nsuccess} successes, {nfailure} failures, {percentSuccess}% success rate"

/-- Test expectation mode -/
inductive TestMode
  | pass  -- expect test to pass (exit 0 on success, exit 1 on failure)
  | xfail -- expect test to fail (exit 0 on failure, exit 1 on success)
  deriving Repr

/-- Parse command line arguments to extract test mode and test name -/
def parseArgs (args : List String) : Option (TestMode × String) :=
  match args with
  | ["--fail", testName] => some (.pass, testName)
  | ["--xfail", testName] => some (.xfail, testName)
  | [testName] => some (.pass, testName)  -- default to --fail behavior
  | _ => none

/-- Compute exit code based on test mode and whether test passed -/
def exitCode (mode : TestMode) (passed : Bool) : UInt32 :=
  match mode, passed with
  | .pass, true => 0   -- expected pass, got pass
  | .pass, false => 1  -- expected pass, got fail
  | .xfail, true => 1  -- expected fail, got pass (unexpected)
  | .xfail, false => 0 -- expected fail, got fail (expected)

/-- Run a test that returns a summary with a `passed` method -/
def runTestWithSummary (mode : TestMode) (testName : String)
    (runTest : IO (Std.Format × Bool)) : IO UInt32 := do
  let (fmt, passed) ← runTest
  IO.println fmt
  let code := exitCode mode passed
  if code != 0 then
    match mode with
    | .pass => IO.println s!"❌ Test {testName} failed (expected pass)"
    | .xfail => IO.println s!"❌ Test {testName} passed unexpectedly (expected fail)"
  return code

/-- Run legacy tests that don't return pass/fail status -/
def runLegacyTest (action : IO Unit) : IO UInt32 := do
  action
  return 0

def runTest (mode : TestMode) (testName : String) : IO UInt32 := do
  match testName with
  -- Legacy tests (no pass/fail tracking)
  | "e5m2" => runLegacyTest (printResults <| test_all e5m2)
  | "e3m4" => runLegacyTest (printResults <| test_all e3m4)
  | "fma_e5m2" => runLegacyTest (printResults <| test_ternop (test_fma e5m2) ())
  | "fma_e3m4" => runLegacyTest (printResults <| test_ternop (test_fma e3m4) ())
  | "abs" => runLegacyTest (printResults <| test_unop_multi $ (test_abs e3m4))
  | "add" => runLegacyTest (printResults <| test_binop $ (test_add e3m4))
  | "div" => runLegacyTest (printResults <| test_binop $ (test_div e3m4))
  | "lt" => runLegacyTest (printResults <| test_binop $ (test_lt e3m4))
  | "max" => runLegacyTest (printResults <| test_binop $ (test_max e3m4))
  | "min" => runLegacyTest (printResults <| test_binop $ (test_min e3m4))
  | "mul" => runLegacyTest (printResults <| test_binop $ (test_mul e3m4))
  | "neg" => runLegacyTest (printResults <| test_unop_multi $ (test_neg e3m4))
  | "rem" => runLegacyTest (printResults <| test_binop $ (test_rem e3m4))
  | "sqrt" => runLegacyTest (printResults <| test_unop_multi $ (test_sqrt e3m4))
  | "sub" => runLegacyTest (printResults <| test_binop $ (test_sub e3m4))
  | "roundToInt" => runLegacyTest (printResults <| test_unop_multi $ (test_roundToInt e3m4))
  | "roundCircuitAgainstSmtLib" => runLegacyTest do
      test_roundCircuitAgainstSmtlib (ein := 3) (sin := 6) (eout := 3) (sout := 4)
      test_roundCircuitAgainstSmtlib (ein := 3) (sin := 6) (eout := 3) (sout := 4)
  | ["fpMaxRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpMaxRel 3 4).toFormat
  | ["fpMinRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpMinRel 3 4).toFormat
  | ["fpLtRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpLtRel 3 4).toFormat
  | ["fpLeqRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpLeqRel 3 4).toFormat
  | ["fpGtRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpGtRel 3 4).toFormat
  | ["fpGeqRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpGeqRel 3 4).toFormat
  | ["fpSmtLibEqRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpSmtLibEqRel 3 4).toFormat
  | ["fpIeeeEqRel"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpIeeeEqRel 3 4).toFormat
  | ["fpAllRels"] =>
      IO.println (← Fp.SmtLibSemanticsComputable.testFpLtRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpLeqRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpGtRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpGeqRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpSmtLibEqRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpIeeeEqRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpMaxRel 3 4).toFormat
      IO.println (← Fp.SmtLibSemanticsComputable.testFpMinRel 3 4).toFormat

  -- Rational tests with pass/fail tracking
  | "addRat" => runTestWithSummary mode testName do
      let s ← Fp.ExhaustiveEnumerationRat.testAdd 3 4
      return (s.toFormat, s.passed)
  | "mulRat" => runTestWithSummary mode testName do
      let s ← Fp.ExhaustiveEnumerationRat.testMul 3 4
      return (s.toFormat, s.passed)
  | "divRat" => runTestWithSummary mode testName do
      let s ← Fp.ExhaustiveEnumerationRat.testDiv 3 4
      return (s.toFormat, s.passed)

  -- SMT-LIB relation tests with pass/fail tracking
  | "fpMaxRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpMaxRel 3 4
      return (s.toFormat, s.passed)
  | "fpMinRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpMinRel 3 4
      return (s.toFormat, s.passed)
  | "fpLtRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpLtRel 3 4
      return (s.toFormat, s.passed)
  | "fpLeqRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpLeqRel 3 4
      return (s.toFormat, s.passed)
  | "fpGtRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpGtRel 3 4
      return (s.toFormat, s.passed)
  | "fpGeqRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpGeqRel 3 4
      return (s.toFormat, s.passed)
  | "fpSmtLibEqRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpSmtLibEqRel 3 4
      return (s.toFormat, s.passed)
  | "fpIeeeEqRel" => runTestWithSummary mode testName do
      let s ← Fp.SmtLibSemanticsComputable.testFpIeeeEqRel 3 4
      return (s.toFormat, s.passed)

  -- Aggregate test (always runs all, reports combined status)
  | "fpAllRels" => do
      let mut allPassed := true
      -- Binary relation tests
      for test in [
        Fp.SmtLibSemanticsComputable.testFpLtRel 3 4,
        Fp.SmtLibSemanticsComputable.testFpLeqRel 3 4,
        Fp.SmtLibSemanticsComputable.testFpGtRel 3 4,
        Fp.SmtLibSemanticsComputable.testFpGeqRel 3 4,
        Fp.SmtLibSemanticsComputable.testFpSmtLibEqRel 3 4,
        Fp.SmtLibSemanticsComputable.testFpIeeeEqRel 3 4
      ] do
        let s ← test
        IO.println s.toFormat
        if !s.passed then allPassed := false
      -- Min/Max relation tests (different type)
      for test in [
        Fp.SmtLibSemanticsComputable.testFpMaxRel 3 4,
        Fp.SmtLibSemanticsComputable.testFpMinRel 3 4
      ] do
        let s ← test
        IO.println s.toFormat
        if !s.passed then allPassed := false
      return exitCode mode allPassed

  | _ =>
      IO.println s!"Unknown test: {testName}"
      IO.println "Usage: fp-lean [--fail|--xfail] <test-name>"
      IO.println ""
      IO.println "Options:"
      IO.println "  --fail   Expect test to pass (default). Exit 0 on success, 1 on failure."
      IO.println "  --xfail  Expect test to fail. Exit 0 on failure, 1 on success."
      IO.println ""
      IO.println "Available tests:"
      IO.println "  Relation tests: fpMaxRel, fpMinRel, fpLtRel, fpLeqRel, fpGtRel, fpGeqRel,"
      IO.println "                  fpSmtLibEqRel, fpIeeeEqRel, fpAllRels"
      IO.println "  Rational tests: addRat, mulRat, divRat"
      IO.println "  Golden tests:   e5m2, e3m4, fma_e5m2, fma_e3m4"
      IO.println "  Op tests:       add, sub, mul, div, min, max, lt, neg, abs, sqrt, rem, roundToInt"
      return 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | some (mode, testName) => runTest mode testName
  | none =>
      IO.println "Usage: fp-lean [--fail|--xfail] <test-name>"
      IO.println "Run with no arguments to see available tests."
      return 1


/-- info: { sign := -, ex := 0x04#5, sig := 0x1#2 } -/
#guard_msgs in #eval PackedFloat.add .RNE (PackedFloat.ofBits 5 2 0b00000011#8) (PackedFloat.ofBits 5 2 0b10010001#8)
/-- info: { sign := +, ex := 0x01#5, sig := 0x2#2 } -/
#guard_msgs in #eval EFixedPoint.round 5 2 .RNE (PackedFloat.toEFixed {sign := false, ex := 1#5, sig := 2#2})
/-- info: { sign := +, ex := 0x1f#5, sig := 0x2#2 } -/
#guard_msgs in #eval PackedFloat.mul .RTZ (PackedFloat.getZero 5 2 false) (PackedFloat.getInfinity 5 2 true)
/-- info: { sign := +, ex := 0x1f#5, sig := 0x0#2 } -/
#guard_msgs in #eval PackedFloat.div .RTZ oneE5M2 (PackedFloat.getZero 5 2 false)
/-- info: { sign := +, ex := 0x00#5, sig := 0x1#2 } -/
#guard_msgs in #eval PackedFloat.mul .RNE (PackedFloat.ofBits 5 2 0b00000001#8) (PackedFloat.ofBits 5 2 0b00111001#8)
