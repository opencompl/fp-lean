import Fp
import Fp.Remainder
import Fp.Tests

inductive ExitCode where
  | Success
  | Failure
deriving Repr

def ExitCode.and (a b : ExitCode) : ExitCode :=
  match a, b with
  | .Success, .Success => .Success
  | _, _ => .Failure

instance : AndOp ExitCode where
  and := ExitCode.and

def ExitCode.toUInt32 : ExitCode → UInt32
  | .Success => 0
  | .Failure => 1

/-- Invert exit code for xfail (expected failure) tests. -/
def ExitCode.invert : ExitCode → ExitCode
  | .Success => .Failure
  | .Failure => .Success

structure OpResult where
  oper : String
  mode : RoundingMode
  result : List String

structure FPFormat where
  e : Nat
  m : Nat

def FPFormat.nbits (f : FPFormat) : Nat :=
  1 + f.e + f.m

def FPFormat.unpackedExponentWidth (f : FPFormat) : Nat :=
  exponentWidth f.e f.m

def FPFormat.unpackedSignificandWidth (f : FPFormat) : Nat :=
  f.m + 1

def FPFormat.packedFloatOfNat (f : FPFormat) (n : Nat) : PackedFloat f.e f.m :=
  PackedFloat.ofBits f.e f.m (BitVec.ofNat (f.nbits) n)

structure FP8Format extends FPFormat where
  h8 : 1 + e + m = 8

namespace FP8Format
theorem h (f : FP8Format)
  : BitVec (1 + f.e + f.m) = BitVec 8 := by simp only [f.h8]
end FP8Format

def PackedFloat.toBits' (pf : PackedFloat e s) (normNaN : Bool := true) :=
  let pf := if pf.isNaN && normNaN then PackedFloat.getNaN e s else pf
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
    result := [a, b, f.h.mp (a' % b').toBits'].map toDigits
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



def test_roundCircuitAgainstSmtlib (ein sin eout sout : Nat) : IO ExitCode := do
  -- round from e2m4 to e2m2
  let e2m4 : FPFormat := { e := ein, m := sin }
  let e2m2 : FPFormat := { e := eout, m := sout }
  let mut totalFailures := 0
  for rm in allRoundingModes do
    IO.println "==="
    IO.println s!"🧪 ROUNDING MODE {repr rm}"
    let mut nsuccess := 0
    let mut nfailure := 0
    for x in [0:2^e2m4.nbits] do
      let pf := e2m4.packedFloatOfNat x
      if pf.isNaN then continue
      let roundSmt : PackedFloat e2m2.e e2m2.m := Fp.SmtLibSemanticsComputable.computableSmtLibRound rm pf.sign pf.unpack.toExtRat
      let roundCircuit : PackedFloat e2m2.e e2m2.m := (pf.unpack |>.round rm (tep := e2m2.e) (tsp := e2m2.m)).pack

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
    totalFailures := totalFailures + nfailure
  return if totalFailures == 0 then .Success else .Failure

def ExitCode.ofFailures (n : Nat) : ExitCode :=
  if n == 0 then .Success else .Failure

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
      let result ← Fp.SmtLibSemanticsComputable.testFpMaxRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpMinRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpMinRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpLtRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpLtRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpLeqRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpLeqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpGtRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpGtRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpGeqRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpGeqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpSmtLibEqRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpSmtLibEqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpIeeeEqRel"] =>
      let result ← Fp.SmtLibSemanticsComputable.testFpIeeeEqRel 3 4
      IO.println result.toFormat
      return .ofFailures result.failures
  | ["fpAllRels"] =>
      let r1 ← Fp.SmtLibSemanticsComputable.testFpLtRel 3 4
      IO.println r1.toFormat
      let r2 ← Fp.SmtLibSemanticsComputable.testFpLeqRel 3 4
      IO.println r2.toFormat
      let r3 ← Fp.SmtLibSemanticsComputable.testFpGtRel 3 4
      IO.println r3.toFormat
      let r4 ← Fp.SmtLibSemanticsComputable.testFpGeqRel 3 4
      IO.println r4.toFormat
      let r5 ← Fp.SmtLibSemanticsComputable.testFpSmtLibEqRel 3 4
      IO.println r5.toFormat
      let r6 ← Fp.SmtLibSemanticsComputable.testFpIeeeEqRel 3 4
      IO.println r6.toFormat
      let r7 ← Fp.SmtLibSemanticsComputable.testFpMaxRel 3 4
      IO.println r7.toFormat
      let r8 ← Fp.SmtLibSemanticsComputable.testFpMinRel 3 4
      IO.println r8.toFormat
      return .ofFailures (r1.failures + r2.failures + r3.failures + r4.failures + r5.failures + r6.failures + r7.failures + r8.failures)
  | _ => return .Success

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
