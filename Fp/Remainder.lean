/-
  IEEE 754 remainder (fp.rem).

  ## Specification (SMT-LIB / BTRW15)
    rem(rm, f, g) = v(f) - (v(g) * y)
      where y = rnd(in, rm, ⊥, v(f)/v(g))
  The integer quotient x/y is rounded using `roundingDecision` with `qMod2`
  for the tie-breaking even/odd check. The final result is always exactly
  representable, so no float rounding is needed.

  ## Algorithm
  Uses modular arithmetic to avoid exponential-width bitvectors.
  The key insight: we only need q mod 2, guard, sticky, and tie to decide
  the rounding of the integer quotient. All of these can be recovered
  from N mod (2*D) where D is the effective divisor, using O(s)-bit
  arithmetic and O(e) iterations of modular squaring.
-/
import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound

-- Modular multiplication: (a * b) % m in double width to avoid overflow.
@[bv_normalize]
def BitVec.umulMod (a b m : BitVec w) : BitVec w :=
  ((a.zeroExtend (2 * w) * b.zeroExtend (2 * w)) % m.zeroExtend (2 * w)).truncate w

-- Modular doubling: (a * 2) % m using shift and conditional subtract.
-- Requires a < m (invariant maintained by modular arithmetic).
-- Since a < m ≤ 2^(w-1), a <<< 1 fits in w bits without overflow.
@[bv_normalize]
def BitVec.umul2Mod (a m : BitVec w) : BitVec w :=
  let doubled := a <<< 1
  bif doubled >= m then doubled - m else doubled

-- Modular exponentiation: base^exp % m via repeated squaring.
-- Processes bits of exp from MSB to LSB. O(n) iterations where n = exp bit-width.
@[bv_normalize]
def BitVec.upowMod (base : BitVec w) (exp : BitVec n) (m : BitVec w)
    (acc : BitVec w := 1#w) : (remaining : Nat := n) → BitVec w
  | 0 => acc
  | remaining + 1 =>
    let sq := acc.umulMod acc m
    let acc' := bif exp.getMsbD (n - 1 - remaining) then sq.umulMod base m else sq
    upowMod base exp m acc' remaining

-- Specialized 2^exp % m: uses umul2Mod for the multiply-by-2 step.
@[bv_normalize]
def BitVec.upow2Mod (exp : BitVec n) (m : BitVec w)
    (acc : BitVec w := 1#w) : (remaining : Nat := n) → BitVec w
  | 0 => acc
  | remaining + 1 =>
    let sq := acc.umulMod acc m
    let acc' := bif exp.getMsbD (n - 1 - remaining) then sq.umul2Mod m else sq
    upow2Mod exp m acc' remaining

-- Core IEEE 754 remainder: computes rem(rm, x, y) = x - y * n
-- where n = rti(rm, x/y) (integer quotient rounded with rounding mode m).
-- The result is always exactly representable, so no float rounding is needed.
@[bv_normalize]
def UnpackedFloat.mod (m : RoundingMode) (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  -- Signed exponent difference
  let k : BitVec (e + 1) := x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1)
  let kIsNeg1 := k == BitVec.ofInt (e + 1) (-1)
  let kLeNeg2 := k.slt (BitVec.ofInt (e + 1) (-1))

  -- Effective divisor: y.sig when k >= 0, 2*y.sig when k = -1
  -- (aligns x and y to common exponent for the k = -1 case)
  let D : BitVec (s + 2) := y.sig.zeroExtend (s + 2)
  let D_eff : BitVec (s + 2) := bif kIsNeg1 then D <<< 1 else D
  let M : BitVec (s + 2) := D_eff <<< 1

  -- 2^max(k,0) mod M via repeated squaring (O(e) iterations).
  -- When kIsNeg1, k < 0 so kPos = 0, giving pow2k = 1; this is correct since
  -- the k = -1 scaling is already absorbed into D_eff above.
  let kPos : BitVec (e + 1) := bif kIsNeg1 then 0 else k
  let pow2k := BitVec.upow2Mod kPos M

  -- (x.sig * 2^max(k,0)) mod M
  let sx : BitVec (s + 2) := x.sig.zeroExtend (s + 2)
  let NmodM := BitVec.umulMod sx pow2k M

  -- Integer quotient parity and remainder
  let qMod2 := (NmodM / D_eff).getLsbD 0
  let r := NmodM % D_eff

  -- Guard and sticky bits for the integer quotient rounding (rnd(in, ...)).
  -- guard: fractional part of quotient >= 0.5, i.e., 2*r >= D_eff.
  -- sticky: fractional part != exact 0.5, i.e., (2*r) mod D_eff != 0.
  let r2 := r <<< 1
  let guard := r2 >= D_eff
  let sticky := r2 % D_eff != 0#(s + 2)

  -- rnd(in, rm, ...): round quotient to integer
  let roundUp := roundingDecision m x.sign (!qMod2) guard sticky false

  -- Reconstruct remainder = x - y * n (at common exponent)
  let remMag : BitVec (s + 2) := bif roundUp then D_eff - r else r
  let remSig : BitVec s := remMag.truncate s
  let commonExp : BitVec e := bif kIsNeg1 then x.ex else y.ex
  let remSign : Bool := bif remSig == 0#s then x.sign else (x.sign ^^ roundUp)

  -- For k <= -2: |x/y| < 0.5, n = 0, remainder = x.
  -- This passthrough is essential: for k <= -2 the effective divisor would be
  -- D * 2^|k| which requires exponential-width bitvectors to represent.
  let rem : UnpackedFloat e s := { sign := remSign, ex := commonExp, sig := remSig }
  -- Guard and sticky are 0 since the remainder is always exactly representable:
  --   Let x = sx · 2^(ex-(s-1)), y = sy · 2^(ey-(s-1)) with sx, sy < 2^s.
  --   For any integer n, rem = x - y·n = (sx · 2^(ex-ey) - sy·n) · 2^(ey-(s-1)).
  --   Since |rem| < |y|, we have |sx · 2^(ex-ey) - sy·n| < sy < 2^s,
  --   so the remainder fits in s significand bits at exponent ≤ ey.
  --   This holds for all rounding modes (RNE, RNA, RTP, RTN, RTZ) since
  --   n is always an integer and |rem| < |y| regardless of how n was chosen.
  bif kLeNeg2 then x else rem.normalize

-- IEEE 754 remainder with special cases (NaN, ∞, zero).
@[bv_normalize]
def EUnpackedFloat.mod (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isNaN || y.isNaN || x.isInfinite || y.isZero then
    mkNaN
  else bif y.isInfinite || x.isZero then
    x
  else
    (UnpackedFloat.mod m x.num y.num).toEUnpackedFloat

namespace PackedFloat

@[bv_normalize]
def mod (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.mod m x.unpack y.unpack).pack

instance : Mod (PackedFloat e s) where
  mod := .mod .RNE

@[bv_normalize]
theorem PackedFloat.mod_def {x y : PackedFloat e s} : x % y = PackedFloat.mod .RNE x y := rfl

end PackedFloat
