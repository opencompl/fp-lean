import Fp
import FpExecutableTests.Harness
import FpExecutableTests.Sampling
import Init.Data.Float.Model.Float

/-!
# Format-generic differential testing against `Float.Model`

Verifies this project's `PackedFloat` operations against Lean's toolchain floating-point
model, `Float.Model` — which is format-parametric via `Float.Model.Format`. For a given
format `(e, s)` we build `spec := { exponentBits := e, mantissaBitsWithoutImplicit := s }`
(so `spec.numBits = 1 + e + s`, matching `PackedFloat`'s bit width), enumerate/sample
`PackedFloat` bit patterns (see `FpExecutableTests.Sampling`), run each operation on both
sides, and compare the resulting packed bits (treating two NaNs as equal).

**Scope.** `Float.Model` implements only round-to-nearest-ties-to-even (RNE), so the
project side is exercised with `.RNE`. The model provides no `rem`/`fma`/`roundToInt`, nor a
format-generic `min`/`max`, so those remain covered by the FloatX/symfpu CSV path. The ops
tested here — all with genuine model counterparts — are:
`add sub mul div` (rounded), `sqrt` (rounded), `neg abs` (exact), and `le lt beq`.
-/

open Float.Model (Format)

namespace FpExecutableTests.AgainstFloatModel

/-- Alias for the model's meaning-level float, to avoid clashing with this project's own
`UnpackedFloat`. -/
abbrev MUF := Float.Model.UnpackedFloat

/-- Build a model `Format` from an exponent/significand width. `spec.numBits` is then
definitionally `1 + e + s`. -/
def mkSpec (e s : Nat) (he : 0 < e := by decide) (hs : 0 < s := by decide) : Format :=
  { mantissaBitsWithoutImplicit := s, hm := hs, exponentBits := e, he := he }

/-- The model has a single canonical NaN; detect it structurally. -/
def isModelNaN : MUF → Bool
  | .notANumber => true
  | _ => false

/-- A boolean rendered as the digit strings used elsewhere in the harness. -/
def boolDigit (b : Bool) : String := if b then "1" else "0"

/-- One differential comparison outcome. -/
structure DiffRecord where
  op : String
  args : Array String
  ours : String
  oracle : String
  ok : Bool
deriving Repr

/-- Aggregated result of running one operation over a sample. -/
structure DiffSummary where
  op : String
  e : Nat
  s : Nat
  strategy : String
  failures : Nat := 0
  successes : Nat := 0
  records : Array DiffRecord := #[]
deriving Repr

def DiffSummary.push (x : DiffSummary) (r : DiffRecord) : DiffSummary :=
  if r.ok then { x with successes := x.successes + 1 }
  else { x with failures := x.failures + 1, records := x.records.push r }

/-- Emoji-formatted, single-line-per-record report (mirrors the other test summaries). -/
def DiffSummary.report (x : DiffSummary) (maxFailShown : Nat := 10) : String :=
  let total := x.successes + x.failures
  let pct := if total == 0 then 100.0 else (x.successes.toFloat / total.toFloat) * 100.0
  let emoji := if x.failures == 0 then "✅" else "❌"
  let header :=
    s!"🧪 {emoji} [e{x.e}m{x.s} | {x.strategy}] op={x.op}: {x.successes}/{total} ok ({pct}%), {x.failures} failures"
  let shown := x.records.toList.take maxFailShown
  let lines := shown.map fun r =>
    s!"    ❌ {r.op}({String.intercalate ", " r.args.toList}) ours={r.ours} oracle={r.oracle}"
  String.intercalate "\n" (header :: lines)

/-- Cast a project-width bit pattern into the model's `spec.numBits` width. -/
def toSpecBits {e s : Nat} (spec : Format) (hw : spec.numBits = 1 + e + s)
    (b : BitVec (1 + e + s)) : BitVec spec.numBits :=
  b.cast hw.symm

/-- Differential check for a rounded binary op (RNE on our side). -/
def checkBin (e s : Nat) (spec : Format) (hw : spec.numBits = 1 + e + s) (opName : String)
    (ourOp : PackedFloat e s → PackedFloat e s → PackedFloat e s)
    (modelOp : MUF → MUF → MUF)
    (ba bb : BitVec (1 + e + s)) : DiffRecord :=
  let ourR := ourOp (PackedFloat.ofBits e s ba) (PackedFloat.ofBits e s bb)
  let ourBits := ourR.toBits'
  let mR := modelOp (Float.Model.UnpackedFloat.unpack spec (toSpecBits spec hw ba)) (Float.Model.UnpackedFloat.unpack spec (toSpecBits spec hw bb))
  let oracleBits := Float.Model.UnpackedFloat.pack spec mR
  let bothNaN := ourR.isNaN && isModelNaN mR
  { op := opName, args := #[toDigits ba, toDigits bb],
    ours := toDigits ourBits, oracle := toDigits oracleBits,
    ok := bothNaN || ourBits.toNat == oracleBits.toNat }

/-- Differential check for a unary op (rounded for `sqrt`, exact for `neg`/`abs`). -/
def checkUnary (e s : Nat) (spec : Format) (hw : spec.numBits = 1 + e + s) (opName : String)
    (ourOp : PackedFloat e s → PackedFloat e s)
    (modelOp : MUF → MUF)
    (ba : BitVec (1 + e + s)) : DiffRecord :=
  let ourR := ourOp (PackedFloat.ofBits e s ba)
  let ourBits := ourR.toBits'
  let mR := modelOp (Float.Model.UnpackedFloat.unpack spec (toSpecBits spec hw ba))
  let oracleBits := Float.Model.UnpackedFloat.pack spec mR
  let bothNaN := ourR.isNaN && isModelNaN mR
  { op := opName, args := #[toDigits ba],
    ours := toDigits ourBits, oracle := toDigits oracleBits,
    ok := bothNaN || ourBits.toNat == oracleBits.toNat }

/-- Differential check for a boolean comparison op. -/
def checkCmp (e s : Nat) (spec : Format) (hw : spec.numBits = 1 + e + s) (opName : String)
    (ourOp : PackedFloat e s → PackedFloat e s → Bool)
    (modelOp : MUF → MUF → Bool)
    (ba bb : BitVec (1 + e + s)) : DiffRecord :=
  let ourV := ourOp (PackedFloat.ofBits e s ba) (PackedFloat.ofBits e s bb)
  let mV := modelOp (Float.Model.UnpackedFloat.unpack spec (toSpecBits spec hw ba)) (Float.Model.UnpackedFloat.unpack spec (toSpecBits spec hw bb))
  { op := opName, args := #[toDigits ba, toDigits bb],
    ours := boolDigit ourV, oracle := boolDigit mV, ok := ourV == mV }

/-- Run one op's `check` over every sample (pair, or single value when `unary`). -/
def verifyOp (e s : Nat) (strat : SampleStrategy) (opName : String)
    (check : BitVec (1 + e + s) → BitVec (1 + e + s) → DiffRecord) (unary : Bool := false)
    : DiffSummary := Id.run do
  let samples := samplePackedFloats e s strat
  let mut sum : DiffSummary := { op := opName, e := e, s := s, strategy := strat.describe }
  for ba in samples do
    if unary then
      sum := sum.push (check ba ba)
    else
      for bb in samples do
        sum := sum.push (check ba bb)
  return sum

/-- Verify all supported operations for format `(e, s)` under the given sample strategy. -/
def verifyAllOps (e s : Nat) (he : 0 < e) (hs : 0 < s) (strat : SampleStrategy)
    : Array DiffSummary :=
  let spec := mkSpec e s he hs
  let hw : spec.numBits = 1 + e + s := rfl
  let bin (name : String) (our : PackedFloat e s → PackedFloat e s → PackedFloat e s)
      (mdl : MUF → MUF → MUF) : DiffSummary :=
    verifyOp e s strat name (checkBin e s spec hw name our mdl)
  let un (name : String) (our : PackedFloat e s → PackedFloat e s) (mdl : MUF → MUF)
      : DiffSummary :=
    verifyOp e s strat name (fun ba _ => checkUnary e s spec hw name our mdl ba) (unary := true)
  let cmp (name : String) (our : PackedFloat e s → PackedFloat e s → Bool)
      (mdl : MUF → MUF → Bool) : DiffSummary :=
    verifyOp e s strat name (checkCmp e s spec hw name our mdl)
  #[
    bin "add" (PackedFloat.add .RNE) (Float.Model.UnpackedFloat.add spec),
    bin "sub" (PackedFloat.sub .RNE) (Float.Model.UnpackedFloat.sub spec),
    bin "mul" (PackedFloat.mul .RNE) (Float.Model.UnpackedFloat.mul spec),
    bin "div" (PackedFloat.div .RNE) (Float.Model.UnpackedFloat.div spec),
    un  "sqrt" (fun a => sqrt a .RNE) (Float.Model.UnpackedFloat.sqrt spec),
    un  "neg" PackedFloat.neg Float.Model.UnpackedFloat.neg,
    un  "abs" PackedFloat.abs Float.Model.UnpackedFloat.abs,
    cmp "le" (PackedFloat.bleAux true) Float.Model.UnpackedFloat.le,
    cmp "lt" (PackedFloat.bltAux false) Float.Model.UnpackedFloat.lt,
    cmp "beq" PackedFloat.ieeeBeq Float.Model.UnpackedFloat.beq
  ]

/-- Run `verifyAllOps`, print each op's report, and return an aggregate exit code. -/
def runFormat (e s : Nat) (he : 0 < e) (hs : 0 < s) (strat : SampleStrategy) : IO ExitCode := do
  IO.println s!"=== FloatModel differential test: e{e}m{s}, {strat.describe} ==="
  let sums := verifyAllOps e s he hs strat
  let mut fails := 0
  for x in sums do
    IO.println x.report
    fails := fails + x.failures
  return ExitCode.ofFailures fails

/-- Parse the optional sample-strategy flags (`--random N SEED` / `--subdivided K`). -/
def parseStrategy? : List String → Option SampleStrategy
  | "--random" :: n :: seed :: _ => some (.random n.toNat! seed.toNat!)
  | "--subdivided" :: k :: _ => some (.subdivided k.toNat!)
  | _ => none

private def usage : String :=
  "usage: floatModel_<fmt> [--random N SEED | --subdivided K]\n" ++
  "  fmt ∈ {e5m2, e3m4, e5m10, e8m23, e11m52}; e5m2/e3m4 default to exhaustive,\n" ++
  "  larger formats require --random or --subdivided (exhaustive is infeasible)."

/-- CLI entry point for the `floatModel_*` test names. Returns `.Success` for
unrecognized arguments so it composes as a fall-through in the main dispatcher. -/
def dispatch (args : List String) : IO ExitCode := do
  match args with
  | "floatModel_e5m2" :: rest =>
      runFormat 5 2 (by decide) (by decide) ((parseStrategy? rest).getD .exhaustive)
  | "floatModel_e3m4" :: rest =>
      runFormat 3 4 (by decide) (by decide) ((parseStrategy? rest).getD .exhaustive)
  | "floatModel_e5m10" :: rest => largeFormat 5 10 (by decide) (by decide) rest
  | "floatModel_e8m23" :: rest => largeFormat 8 23 (by decide) (by decide) rest
  | "floatModel_e11m52" :: rest => largeFormat 11 52 (by decide) (by decide) rest
  | _ => return .Success
where
  largeFormat (e s : Nat) (he : 0 < e) (hs : 0 < s) (rest : List String) : IO ExitCode := do
    match parseStrategy? rest with
    | some strat => runFormat e s he hs strat
    | none =>
        IO.eprintln s!"exhaustive enumeration of e{e}m{s} is infeasible; pick a sampling strategy."
        IO.eprintln usage
        return .Failure

end FpExecutableTests.AgainstFloatModel
