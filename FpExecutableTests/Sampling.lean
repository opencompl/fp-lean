import Init.Data.Random

/-!
# Sampling strategies for packed-float differential testing

Format-generic generators of `PackedFloat`-shaped bit patterns (`BitVec (1+e+s)`,
laid out MSB-first as `sign ++ exponent ++ significand`, matching
`PackedFloat.toBits` and `Float.Model.UnpackedFloat.packComponents`).

Three strategies, all pure:

* `exhaustive`     — every one of the `2^(1+e+s)` bit patterns.
* `random c seed`  — `c` patterns from a seeded, reproducible PRNG.
* `subdivided k`   — for every exponent (both signs), `2^k` evenly-spaced mantissa
  values between `0` and the all-ones significand, plus a fixed set of named
  critical points (zeros, infinities, NaN, subnormal/normal extremes). When
  `k = s` this reproduces *all* packed floats.
-/

namespace FpExecutableTests

/-- Assemble a packed bit pattern from a sign, exponent, and significand, MSB-first.
Matches `PackedFloat.toBits = ofBool sign ++ ex ++ sig`. -/
def mkBits (e s : Nat) (sign : Bool) (ex sig : Nat) : BitVec (1 + e + s) :=
  BitVec.ofBool sign ++ BitVec.ofNat e ex ++ BitVec.ofNat s sig

/-- How to pick which packed floats to test. Format-generic. -/
inductive SampleStrategy where
  /-- Every bit pattern of width `1+e+s`. Feasible only for small formats. -/
  | exhaustive
  /-- `count` bit patterns drawn from a PRNG seeded by `seed` (reproducible). -/
  | random (count : Nat) (seed : Nat)
  /-- All exponents × `2^k` evenly-spaced mantissas + named critical points. -/
  | subdivided (k : Nat)
deriving Repr, Inhabited, DecidableEq

/-- Human-readable description for report headers. -/
def SampleStrategy.describe : SampleStrategy → String
  | .exhaustive => "exhaustive"
  | .random count seed => s!"random(count={count}, seed={seed})"
  | .subdivided k => s!"subdivided(k={k})"

/-- Sort-and-deduplicate a `Nat` array (core-only, no `HashSet` dependency). -/
private def dedupNat (xs : Array Nat) : Array Nat := Id.run do
  let sorted := xs.qsort (· < ·)
  let mut out : Array Nat := #[]
  let mut prev : Option Nat := none
  for x in sorted do
    if prev != some x then
      out := out.push x
      prev := some x
  return out

/-- Deduplicate an array of bit patterns (via their `Nat` value). -/
private def dedupBits {n : Nat} (xs : Array (BitVec n)) : Array (BitVec n) :=
  (dedupNat (xs.map (·.toNat))).map (BitVec.ofNat n)

/-- Exhaustive enumeration of every bit pattern of width `1+e+s`. -/
def sampleExhaustive (e s : Nat) : Array (BitVec (1 + e + s)) := Id.run do
  let mut a := #[]
  for sign in [false, true] do
    for ex in [0:2^e] do
      for sig in [0:2^s] do
        a := a.push (mkBits e s sign ex sig)
  return a

/-- `count` bit patterns from a `StdGen` seeded by `seed`. Pure and reproducible. -/
def sampleRandom (e s : Nat) (count seed : Nat) : Array (BitVec (1 + e + s)) := Id.run do
  let n := 1 + e + s
  let mut g := mkStdGen seed
  let mut a := #[]
  for _ in [0:count] do
    let (v, g') := randNat g 0 (2^n - 1)
    g := g'
    a := a.push (BitVec.ofNat n v)
  return a

/-- `2^k` evenly-spaced mantissa values in `[0, 2^s - 1]` inclusive.

`mant_i = i * (2^s - 1) / (2^k - 1)` for `i ∈ [0, 2^k)`, with `k = 0 ↦ {0}`.
Endpoints are hit exactly (`i = 0 ↦ 0`, `i = 2^k - 1 ↦ 2^s - 1`), and when `k = s`
this is the identity on `[0, 2^s)`, i.e. every mantissa. Duplicates (possible when
`k > s`) are removed. -/
def subdividedMantissas (s k : Nat) : Array Nat := Id.run do
  let hi := 2^s - 1
  if k == 0 then
    return #[0]
  let steps := 2^k - 1
  let mut a := #[]
  for i in [0:2^k] do
    a := a.push (i * hi / steps)
  return dedupNat a

/-- Named critical points for format `(e, s)`: ±0, ±∞, NaN, and the
subnormal/normal extremes and midpoints. Returned as bit patterns. -/
def namedCriticalPoints (e s : Nat) : Array (BitVec (1 + e + s)) := Id.run do
  let allOnesExp := 2^e - 1        -- exponent field all ones (∞ / NaN)
  let maxNormExp := 2^e - 2        -- largest finite exponent field
  let allOnesSig := 2^s - 1
  let bias := 2^(e - 1) - 1        -- exponent bias (0 for e = 0, harmless)
  let midSig := 2^s / 2            -- significand msb set (0 when s = 0)
  let quietNaNSig := if s == 0 then 0 else 2^(s - 1)  -- quiet NaN payload
  let pts : List (Bool × Nat × Nat) :=
    [ (false, 0, 0),                       -- +0
      (true,  0, 0),                        -- -0
      (false, allOnesExp, 0),               -- +∞
      (true,  allOnesExp, 0),               -- -∞
      (false, allOnesExp, quietNaNSig),     -- NaN (quiet)
      (false, 0, 1),                        -- +min subnormal
      (true,  0, 1),                        -- -min subnormal
      (false, 0, midSig),                   -- +mid subnormal
      (false, 0, allOnesSig),               -- +max subnormal
      (true,  0, allOnesSig),               -- -max subnormal
      (false, 1, 0),                        -- +min normal
      (true,  1, 0),                        -- -min normal
      (false, bias, midSig),                -- +mid normal (≈ 1.5)
      (false, maxNormExp, allOnesSig),      -- +max normal
      (true,  maxNormExp, allOnesSig) ]     -- -max normal
  return (pts.map (fun (sgn, ex, sig) => mkBits e s sgn ex sig)).toArray

/-- Structured critical-point sampling: every exponent (both signs) crossed with
`2^k` evenly-spaced mantissas, unioned with the named critical points. Deduplicated. -/
def sampleSubdivided (e s k : Nat) : Array (BitVec (1 + e + s)) := Id.run do
  let mants := subdividedMantissas s k
  let mut a := #[]
  for sign in [false, true] do
    for ex in [0:2^e] do
      for m in mants do
        a := a.push (mkBits e s sign ex m)
  return dedupBits (a ++ namedCriticalPoints e s)

/-- Generate the sample of packed-float bit patterns for the given strategy. -/
def samplePackedFloats (e s : Nat) : SampleStrategy → Array (BitVec (1 + e + s))
  | .exhaustive => sampleExhaustive e s
  | .random count seed => sampleRandom e s count seed
  | .subdivided k => sampleSubdivided e s k

end FpExecutableTests
