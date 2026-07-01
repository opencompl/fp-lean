import Fp
import Fp.Remainder
import FpExecutableTests.SmtLibSemanticsEnumerator

/-!
# Executable test harness (shared infrastructure)

Reusable, model-independent scaffolding for the `fp-executable-test-runner` executable:
exit codes, the CSV `OpResult` format used by the FloatX/symfpu golden-diff path,
bit-string formatting, format descriptors, and the exhaustive `BitVec 8` enumeration
drivers. This code was previously inlined in the top-level `Main.lean`.
-/

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

def ExitCode.ofFailures (n : Nat) : ExitCode :=
  if n == 0 then .Success else .Failure

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
      let roundSmt : PackedFloat e2m2.e e2m2.m := Fp.SmtLibSemanticsEnumerator.computableSmtLibRound rm pf.sign pf.unpack.toExtRat
      let roundCircuit : PackedFloat e2m2.e e2m2.m := (pf.unpack |>.blastSmtLibRound e2m2.e e2m2.m rm ).pack

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
