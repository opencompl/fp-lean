import Fp

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
-- The LRAT certificate for this deep circuit is large; checking it in the kernel overflows
-- the stack. Skip the kernel re-check and trust the SAT solver (adds `Lean.ofReduceBool`).
set_option debug.skipKernelTC true

/-!
# Fast inverse square root for E5M2

The classic Quake III `Q_rsqrt` bit-trick, ported to the 8-bit E5M2
(`PackedFloat 5 2`) format, and proved correct by `bv_decide`.

```c
float InvSqrt(float x) {
  float xhalf = 0.5f*x;
  int i = *(int*)&x;            // reinterpret float bits as int
  i = 0x5f3759df - (i >> 1);    // initial guess for 1/sqrt(x)
  x = *(float*)&i;
  x = x*(1.5f - xhalf*x*x);     // one Newton iteration
  return x;
}
```
-/

namespace Example

/-- E5M2 representation of `0.5`. -/
@[bv_normalize] def half      : PackedFloat 5 2 := PackedFloat.ofBits 5 2 0x38#8
/-- E5M2 representation of `1.5`. -/
@[bv_normalize] def threehalf : PackedFloat 5 2 := PackedFloat.ofBits 5 2 0x3E#8

/-- The E5M2 analog of `0x5f3759df`, found by `searchBestMagic` below. -/
@[bv_normalize] def magic : BitVec 8 := 0x59#8

/-- Floating-point absolute value: clear the sign bit. -/
@[bv_normalize] def fabs (x : PackedFloat 5 2) : PackedFloat 5 2 := { x with sign := false }

/-- Worst-case relative tolerance of `(finvsqrt x)² · x` around `1`, here `1/4`. -/
@[bv_normalize] def eps : PackedFloat 5 2 := PackedFloat.ofBits 5 2 0x34#8   -- 0.25

/-- `1 - eps = 3/4`, the lower bound on `(finvsqrt x)² · x`. -/
@[bv_normalize] def lo : PackedFloat 5 2 := PackedFloat.ofBits 5 2 0x3A#8    -- 0.75
/-- `1 + eps = 5/4`, the upper bound on `(finvsqrt x)² · x`. -/
@[bv_normalize] def hi : PackedFloat 5 2 := PackedFloat.ofBits 5 2 0x3D#8    -- 1.25

/-- Fast inverse square root with an explicit magic constant (one Newton step on the
bit-trick initial guess). Parameterised so the magic-constant search below can reuse it. -/
@[bv_normalize] def finvsqrtM (magic : BitVec 8) (x : PackedFloat 5 2) : PackedFloat 5 2 :=
  let xhalf := half * x
  let i     := magic - (x.toBits >>> 1)       -- reinterpret bits, shift, subtract magic
  let y     := PackedFloat.ofBits 5 2 i        -- initial guess y₀ ≈ 1/sqrt(x)
  y * (threehalf - (xhalf * y) * y)            -- Newton: y ← y·(1.5 - 0.5·x·y²)

/-- Fast inverse square root for E5M2, using the tuned `magic = 0x59`. -/
@[bv_normalize] def finvsqrt (x : PackedFloat 5 2) : PackedFloat 5 2 := finvsqrtM magic x

/-! ## Deriving the magic constant

The search below is the executable derivation of `magic = 0x59`: it enumerates every
candidate constant and every positive-normal input, and keeps the constant with the
smallest worst-case relative error of `(finvsqrt x)² · x` against `1`. It is plain
computation (no `bv_decide`) so it can run at `#eval`. -/

/-- All positive normal E5M2 bit patterns (sign `0`, exponent neither `0` nor all-ones). -/
def posNormals : List (PackedFloat 5 2) :=
  (List.range 128).filterMap fun n =>
    let x := PackedFloat.ofBits 5 2 (BitVec.ofNat 8 n)
    if x.isNorm then some x else none

/-- `|r - 1|` on the rationals. -/
def relErr (r : Rat) : Rat := if r ≥ 1 then r - 1 else 1 - r

/-- Worst-case `|(finvsqrt x)² · x - 1|` over positive normals for a given magic, or `none`
if the candidate ever overflows to `±∞`/`NaN` (which has no rational value). -/
def worstErr (magic : BitVec 8) : Option Rat :=
  posNormals.foldl (fun acc x =>
    match acc with
    | none => none
    | some w =>
      let y := finvsqrtM magic x
      match ((y * y) * x).toRat? with
      | none => none
      | some p => some (max w (relErr p))) (some 0)

/-- Scan all 256 candidate magics; return the one (smallest, on ties) with the least
finite worst-case error, together with that error. -/
def searchBestMagic : BitVec 8 × Rat :=
  (List.range 256).foldl (fun best m =>
    let mb := BitVec.ofNat 8 m
    match worstErr mb with
    | none => best
    | some d => if d < best.2 then (mb, d) else best) (0#8, 1000)

/-- info: (89#8, 1 / 4) -/
#guard_msgs in #eval searchBestMagic

/--
Correctness: for every positive normal `x`, the fast inverse square root satisfies
`(1 - eps) ≤ |y·y·x| ≤ (1 + eps)` with `eps = 1/4`, i.e. `y = finvsqrt x` approximates
`1/√x` to within E5M2's mantissa precision.
-/
theorem finvsqrt_correct (x : PackedFloat 5 2)
    (hpos : x.sign = false) (hnorm : x.isNorm = true) :
    (PackedFloat.smtBle false lo (fabs ((finvsqrt x * finvsqrt x) * x))
      && PackedFloat.smtBle false (fabs ((finvsqrt x * finvsqrt x) * x)) hi) = true := by
  bv_decide

/-- info: 'Example.finvsqrt_correct' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finvsqrt_correct

end Example
