import FpExecutableTests

/-!
# `fp-executable-test-runner` executable entry point

Thin CLI dispatcher over the executable-testing infrastructure in `FpExecutableTests`.
All harness/enumeration/reporting code lives in the sibling modules; this file only
parses arguments and selects which test suite to run.
-/

/-- Run test and return ExitCode. -/
def get_long_operation (args : List String) : IO ExitCode := do
  match args with
  | ["e5m2"] => printResults <| test_all e5m2; return .Success
  | ["e3m4"] => printResults <| test_all e3m4; return .Success
  | ["fma_e5m2"]  => printResults <| test_ternop (test_fma e5m2) (); return .Success
  | ["fma_e3m4"]  => printResults <| test_ternop (test_fma e3m4) (); return .Success
  | ["abs"] => printResults <| test_unop_multi $ (test_abs e3m4); return .Success
  | ["add"] => printResults <| test_binop $ (test_add e3m4); return .Success
  | ["div"] => printResults <| test_binop $ (test_div e3m4); return .Success
  | ["lt"] => printResults <| test_binop $ (test_lt e3m4); return .Success
  | ["max"] => printResults <| test_binop $ (test_max e3m4); return .Success
  | ["min"] => printResults <| test_binop $ (test_min e3m4); return .Success
  | ["mul"] => printResults <| test_binop $ (test_mul e3m4); return .Success
  | ["neg"] => printResults <| test_unop_multi $ (test_neg e3m4); return .Success
  | ["rem"] => printResults <| test_binop $ (test_rem e3m4); return .Success
  | ["sqrt"] => printResults <| test_unop_multi $ (test_sqrt e3m4); return .Success
  | ["sub"] => printResults <| test_binop $ (test_sub e3m4); return .Success
  | ["roundToInt"] => printResults <| test_unop_multi $ (test_roundToInt e3m4); return .Success
  | ["addRat"] =>
      let result ← Fp.ExhaustiveEnumerationRat.testAdd 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["mulRat"] =>
      let result ← Fp.ExhaustiveEnumerationRat.testMul 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["divRat"] =>
      let result ← Fp.ExhaustiveEnumerationRat.testDiv 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["sqrtRat"] =>
      let result ← Fp.ExhaustiveEnumerationRat.testSqrt 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["roundCircuitAgainstSmtLib"] =>
      -- eout > sout
      let exit1 ← test_roundCircuitAgainstSmtlib (ein := 5) (sin := 7) (eout := 4) (sout := 3)
      -- eoout = soug
      let exit2 ← test_roundCircuitAgainstSmtlib (ein := 4) (sin := 6) (eout := 4) (sout := 4)
      -- eoout < soug
      let exit3 ← test_roundCircuitAgainstSmtlib (ein := 3) (sin := 6) (eout := 3) (sout := 4)
      return exit1 &&& exit2 &&& exit3
  | ["fpMaxRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpMaxRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpMinRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpMinRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpLtRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpLtRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpLeqRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpLeqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpGtRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpGtRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpGeqRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpGeqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpSmtLibEqRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpSmtLibEqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpIeeeEqRel"] =>
      let result ← Fp.SmtLibSemanticsEnumerator.testFpIeeeEqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpAllRels"] =>
      let r1 ← Fp.SmtLibSemanticsEnumerator.testFpLtRel 3 4
      IO.println r1.toFormat
      let r2 ← Fp.SmtLibSemanticsEnumerator.testFpLeqRel 3 4
      IO.println r2.toFormat
      let r3 ← Fp.SmtLibSemanticsEnumerator.testFpGtRel 3 4
      IO.println r3.toFormat
      let r4 ← Fp.SmtLibSemanticsEnumerator.testFpGeqRel 3 4
      IO.println r4.toFormat
      let r5 ← Fp.SmtLibSemanticsEnumerator.testFpSmtLibEqRel 3 4
      IO.println r5.toFormat
      let r6 ← Fp.SmtLibSemanticsEnumerator.testFpIeeeEqRel 3 4
      IO.println r6.toFormat
      let r7 ← Fp.SmtLibSemanticsEnumerator.testFpMaxRel 3 4
      IO.println r7.toFormat
      let r8 ← Fp.SmtLibSemanticsEnumerator.testFpMinRel 3 4
      IO.println r8.toFormat
      return .ofFailures (r1.failures + r2.failures + r3.failures + r4.failures + r5.failures + r6.failures + r7.failures + r8.failures)
  | _ => FpExecutableTests.AgainstFloatModel.dispatch args

def main (args : List String) : IO UInt32 := do
  let xfail := args.contains "--xfail"
  let args := args.filter (· != "--xfail")
  if args != [] then do
    let exitCode ← get_long_operation args
    let exitCode := if xfail then exitCode.invert else exitCode
    return exitCode.toUInt32
  else do
      IO.println "Please run with command line arg e5m2 or e3m4"
      return ExitCode.Failure.toUInt32


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
