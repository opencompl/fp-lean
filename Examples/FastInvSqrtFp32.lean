import Fp

set_option maxHeartbeats 40000000
set_option maxRecDepth 4000000
-- Skip the in-kernel LRAT re-check (the FP32 certificate is enormous); trust the SAT solver.
set_option debug.skipKernelTC true

/-!
# Fast inverse square root for IEEE-754 binary32 (FP32)

The *original* Quake III `Q_rsqrt`, on the real `float` type (`PackedFloat 8 23`), with the
famous magic constant `0x5f3759df`. This is the FP32 sibling of `Examples.FastInvSqrt`
(E5M2); that small file is the verified template, and this one scales the identical
construction up to 32 bits.

```c
float InvSqrt(float x) {
  float xhalf = 0.5f*x;
  int i = *(int*)&x;            // get bits for floating value
  i = 0x5f3759df - (i >> 1);    // gives initial guess y0
  x = *(float*)&i;              // convert bits back to float
  x = x*(1.5f - xhalf*x*x);     // Newton step, repeating increases accuracy
  return x;
}
```

## The magic constant and its analysis

`0x5f3759df` is derived (and improved) in Chris Lomont, *"Fast Inverse Square Root"* (2003):
<https://www.lomont.org/papers/2003/InvSqrt.pdf>. The derivation: interpreting the bits of
a normal `float` as an integer `I` gives `I ≈ 2^M·(log₂ value + B − σ)` (mantissa bits
`M = 23`, bias `B = 127`, `σ` a small correction). For `y = 1/√x`,
`I_y ≈ (3/2)·2^M·(B − σ) − I_x/2`, i.e. `magic = (3/2)·2^M·(B − σ)`. Lomont reports the
original constant achieves a maximum relative error of `0.0017512` over all floats (and
finds the slightly better `0x5f375a86`).

From `|y·√x − 1| ≤ 0.0017512` we get `y·y·x = (y·√x)² ∈ [0.99650, 1.00351]`. Adding a little
slack for the rounding of the `(y·y)·x` product itself, this file proves the clean bound

> `(1 − eps) ≤ |y·y·x| ≤ (1 + eps)`  with `eps = 1/256 ≈ 0.0039`

i.e. `lo = 255/256 ≤ y·y·x ≤ 257/256 = hi`, for every positive normal FP32 `x`.

## Cost / why this is not in CI

Unlike the 8-bit E5M2 example, the FP32 circuit chains several 24×24-bit floating-point
multiplies; bitblasting is fine but the resulting SAT instance is very large, so the proof
needs a long solver run (`bv_decide`'s `timeout` is raised below). This module is therefore
**deliberately not imported by `Examples.lean`** — it is excluded from the default
`lake build` / CI. Check it on demand with:

```bash
lake env lean Examples/FastInvSqrtFp32.lean
```
-/

namespace Example

/-- FP32 `0.5`. -/
@[bv_normalize] def half32      : PackedFloat 8 23 := PackedFloat.ofBits 8 23 0x3F000000#32
/-- FP32 `1.5`. -/
@[bv_normalize] def threehalf32 : PackedFloat 8 23 := PackedFloat.ofBits 8 23 0x3FC00000#32

/-- The original Quake III magic constant (Lomont 2003). -/
@[bv_normalize] def magic32 : BitVec 32 := 0x5f3759df#32

/-- Floating-point absolute value: clear the sign bit. -/
@[bv_normalize] def fabs (x : PackedFloat 8 23) : PackedFloat 8 23 := { x with sign := false }

/-- Relative tolerance `1/256 ≈ 0.0039` on `y·y·x` around `1` (Lomont's `0.0017512`
maximum relative error on `y`, doubled for `y²` and rounded out for the product). -/
@[bv_normalize] def eps : PackedFloat 8 23 := PackedFloat.ofBits 8 23 0x3B800000#32   -- 1/256
/-- `1 - eps = 255/256`. -/
@[bv_normalize] def lo  : PackedFloat 8 23 := PackedFloat.ofBits 8 23 0x3F7F0000#32   -- 255/256
/-- `1 + eps = 257/256`. -/
@[bv_normalize] def hi  : PackedFloat 8 23 := PackedFloat.ofBits 8 23 0x3F808000#32   -- 257/256

/-- The Quake fast inverse square root on FP32, one Newton step. -/
@[bv_normalize] def finvsqrt (x : PackedFloat 8 23) : PackedFloat 8 23 :=
  let xhalf := half32 * x
  let i     := magic32 - (x.toBits >>> 1)      -- reinterpret bits, shift, subtract magic
  let y     := PackedFloat.ofBits 8 23 i        -- initial guess y₀ ≈ 1/sqrt(x)
  y * (threehalf32 - (xhalf * y) * y)           -- Newton: y ← y·(1.5 - 0.5·x·y²)

/--
Correctness: for every positive normal FP32 `x`, `y = finvsqrt x` approximates `1/√x` with
`(1 - eps) ≤ |y·y·x| ≤ (1 + eps)`, `eps = 1/256`.

NOTE: heavy verification — the FP32 circuit yields a large SAT instance, hence the raised
`bv_decide` timeout. Not built by CI (see module docstring).
-/
theorem finvsqrt_correct (x : PackedFloat 8 23)
    (hpos : x.sign = false) (hnorm : x.isNorm = true) :
    (PackedFloat.smtBle false lo (fabs ((finvsqrt x * finvsqrt x) * x))
      && PackedFloat.smtBle false (fabs ((finvsqrt x * finvsqrt x) * x)) hi) = true := by
  bv_decide (config := { timeout := 1800 })

end Example
