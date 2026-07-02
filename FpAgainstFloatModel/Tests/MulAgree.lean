import FpAgainstFloatModel.Mul

/-!
# Empirical validation: `PackedFloat.mul` computes the same bits as `Float.Model.mul`

Both multiplications are computable, so we can *validate* `mul_agree` on concrete `binary64`
patterns before/while proving it. Each `#guard` fails the build if the project and the model
disagree on the 64-bit product. Cases cover: exact products, round-up / round-down /
ties-to-even, subnormal (underflow) results, overflow → ∞, ±0 sign, ∞ × finite, ∞ × 0 → NaN,
and NaN propagation. (All pass bit-for-bit — the model and project even canonicalize NaN
identically, so agreement here is exact, not just up-to-NaN.)
-/

namespace FpAgainstFloatModel.Tests

/-- The project's `binary64` product, as 64 bits. -/
def projMul (b₁ b₂ : BitVec 64) : BitVec 64 :=
  (PackedFloat.ofBits 11 52 (b₁.cast (by decide))
    * PackedFloat.ofBits 11 52 (b₂.cast (by decide))).toBits.cast (by decide)

/-- Lean's `Float.Model` product, as 64 bits. -/
def modelMul (b₁ b₂ : BitVec 64) : BitVec 64 :=
  (Float.Model.ofBits (UInt64.ofBitVec b₁) * Float.Model.ofBits (UInt64.ofBitVec b₂)).toBits.toBitVec

/-- `true` iff the project and the model agree bit-for-bit on `b₁ * b₂`. -/
def agree (b₁ b₂ : BitVec 64) : Bool := projMul b₁ b₂ == modelMul b₁ b₂

-- normal × normal, exact:  3.0 * 2.5 = 7.5
#guard agree 0x4008000000000000 0x4004000000000000
-- identity:  1.0 * x = x
#guard agree 0x3FF0000000000000 0x3FF0000000000001
-- rounding (round to nearest):  (1 + 2^-52)^2
#guard agree 0x3FF0000000000001 0x3FF0000000000001
-- rounding, larger operands:  π-ish * e-ish
#guard agree 0x400921FB54442D18 0x4005BF0A8B145769
-- tie-to-even territory:  1.5 * 1.5 = 2.25 (exact) and neighbours
#guard agree 0x3FF8000000000000 0x3FF8000000000000
#guard agree 0x3FF8000000000001 0x3FF8000000000001
-- overflow to +∞:  maxNormal * 2.0
#guard agree 0x7FEFFFFFFFFFFFFF 0x4000000000000000
-- overflow to −∞:  maxNormal * −2.0
#guard agree 0x7FEFFFFFFFFFFFFF 0xC000000000000000
-- large * large overflow:  1e200 * 1e200
#guard agree 0x6974E718D7D7625A 0x6974E718D7D7625A
-- underflow to a subnormal:  minNormal * 0.5
#guard agree 0x0010000000000000 0x3FE0000000000000
-- subnormal * normal staying subnormal
#guard agree 0x0008000000000000 0x3FE0000000000000
-- underflow all the way to 0:  minSubnormal * minSubnormal
#guard agree 0x0000000000000001 0x0000000000000001
-- ±0 signs:  +0*+3=+0, −0*+3=−0, −0*−3=+0, +3*−0=−0
#guard agree 0x0000000000000000 0x4008000000000000
#guard agree 0x8000000000000000 0x4008000000000000
#guard agree 0x8000000000000000 0xC008000000000000
#guard agree 0x4008000000000000 0x8000000000000000
-- ∞ handling:  +∞*3=+∞, −∞*3=−∞, +∞*−3=−∞
#guard agree 0x7FF0000000000000 0x4008000000000000
#guard agree 0xFFF0000000000000 0x4008000000000000
#guard agree 0x7FF0000000000000 0xC008000000000000
-- ∞ * 0 = NaN
#guard agree 0x7FF0000000000000 0x0000000000000000
#guard agree 0x7FF0000000000000 0x8000000000000000
-- NaN propagation
#guard agree 0x7FF8000000000000 0x4008000000000000
#guard agree 0x4008000000000000 0x7FF8000000000000
#guard agree 0x7FF8000000000000 0x7FF0000000000000

end FpAgainstFloatModel.Tests
