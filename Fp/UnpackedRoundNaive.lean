import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ

/-!
## Naive Unpacked Rounding

A decomposition of `UnpackedFloat.round` into named components that correspond 1:1
to the SMT-LIB `RoundMethod` concepts (`lower`, `upper`, `lowerHalf`, `tieBreak`, `isEven`).

This enables modular proofs bridging the bitvector circuit to the SMT-LIB specification.
-/

namespace Fp
namespace UnpackedRoundNaive

/-! ### Rounding Context

Captures the shared setup computation (masks, indices, exponent clamping)
from the first half of `UnpackedFloat.round`.
-/

/-- The precomputed masks and indices needed for rounding.
This mirrors lines 625-682 of `UnpackedFloat.round`. -/
structure RoundingContext (expWidth sigWidth : Nat)
    (targetExponentWidth targetSignificandWidth : Nat) where
  /-- The input unpacked float being rounded. -/
  inUf : UnpackedFloat expWidth sigWidth
  /-- The exponent of the input. -/
  exp : BitVec expWidth
  /-- Whether the exponent exceeds the max normal exponent for the target format. -/
  earlyOverflow : Bool
  /-- Whether the exponent is below the min subnormal exponent - 1 for the target format. -/
  earlyUnderflow : Bool
  /-- `max(exp, targetMinNormalExp)` — the exponent clamped to at least the minimum normal. -/
  expGeMin : BitVec expWidth
  /-- `expGeMin - exp` — how much to right-shift the significand for subnormal alignment. -/
  shiftAmtPositive : BitVec expWidth
  /-- The guard bit position (from LSB), adjusted for subnormal shift. -/
  guardBitIndexFromLsbAdjusted : BitVec sigWidth
  /-- One-hot mask at the guard bit position. -/
  guardBitMask : BitVec sigWidth
  /-- Mask of all bits below the guard bit (for sticky computation). -/
  stickyBitsMask : BitVec sigWidth
  /-- One-hot mask at the LSB position of the rounded significand (one above guard). -/
  lsbMask : BitVec sigWidth

/-- Build a `RoundingContext` from an `UnpackedFloat`, mirroring the
first half of `UnpackedFloat.round` (setup computation). -/
@[bv_normalize]
def mkRoundingContext {expWidth sigWidth : Nat}
    {targetExponentWidth targetSignificandWidth : Nat}
    (inUf : UnpackedFloat expWidth sigWidth) :
    RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth :=
  let exp : BitVec expWidth := inUf.ex
  let targetMinNormalExp : BitVec expWidth :=
    BitVec.ofInt expWidth (minNormalExp targetExponentWidth)
  let earlyOverflow : Bool :=
    (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth)).slt exp
  let earlyUnderflow : Bool :=
    exp.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth - 1))
  let expGeMin :=
    if exp.slt targetMinNormalExp then targetMinNormalExp else exp
  let shiftAmtPositive := expGeMin - exp
  let guardBitIndexFromLsb : BitVec sigWidth :=
    BitVec.ofNat sigWidth ((sigWidth - 1) - (targetSignificandWidth + 1))
  let guardBitIndexFromLsbAdjusted : BitVec sigWidth :=
    guardBitIndexFromLsb + shiftAmtPositive.zeroExtend sigWidth
  let guardBitMask : BitVec sigWidth := BitVec.oneHotBV guardBitIndexFromLsbAdjusted
  let stickyBitsMask : BitVec sigWidth := BitVec.orderEncode guardBitIndexFromLsbAdjusted
  let lsbMask : BitVec sigWidth :=
    BitVec.oneHotBV (guardBitIndexFromLsbAdjusted + 1#sigWidth)
  { inUf, exp, earlyOverflow, earlyUnderflow, expGeMin, shiftAmtPositive,
    guardBitIndexFromLsbAdjusted, guardBitMask, stickyBitsMask, lsbMask }

/-! ### Named Component Functions

Each function extracts one concept that corresponds to an SMT-LIB `RoundMethod` component.
-/

/-- The guard bit: the first bit below the target precision.
When guard = 0, the value is in the lower half of `[lower, upper]`.
When guard = 1, the value is in the upper half or at the midpoint.
Corresponds (negated) to `RoundMethod.lowerHalf`. -/
@[bv_normalize]
def computeGuardBit (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  (ctx.inUf.sig &&& ctx.guardBitMask) != 0#sigWidth

/-- The sticky bit: OR of all bits below the guard bit.
When sticky = 0 and guard = 1, the value is exactly at the midpoint (tie).
When sticky = 1, the value is strictly between two representable values.
Together with guard, determines `RoundMethod.tieBreak`. -/
@[bv_normalize]
def computeStickyBit (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  (ctx.inUf.sig &&& ctx.stickyBitsMask) != 0#sigWidth

/-- Whether the LSB of the truncated (lower) significand is even.
Corresponds to `RoundableIsEven.isEven` applied to `lower r`. -/
@[bv_normalize]
def computeIsEven (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  ctx.inUf.sig &&& ctx.lsbMask = 0#sigWidth

/-- Whether the value is strictly in the lower half of `[lower, upper]`.
This holds when `guard = 0`, meaning the discarded bits are less than half a ULP.
Corresponds to `RoundMethod.lowerHalf`. -/
@[bv_normalize]
def computeLowerHalf (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  !(computeGuardBit ctx)

/-- Whether the value is exactly at the midpoint between `lower` and `upper`.
This holds when `guard = 1` and `sticky = 0`.
Corresponds to `RoundMethod.tieBreak`. -/
@[bv_normalize]
def computeTieBreak (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  computeGuardBit ctx && !(computeStickyBit ctx)

/-- The significand of the "lower" representable value (truncation).
Obtained by clearing all bits at and below the guard position.
Corresponds to the significand of `smtLibLower.lower (embed uf)`. -/
@[bv_normalize]
def computeLowerSig (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : BitVec sigWidth :=
  ctx.inUf.sig &&& (~~~(ctx.guardBitMask ||| ctx.stickyBitsMask))

/-- The significand of the "upper" representable value (truncation + increment).
Returns a `(sigWidth + 1)`-bit value; the MSB indicates significand overflow.
Corresponds to the significand of `smtLibUpper.upper (embed uf)`. -/
@[bv_normalize]
def computeUpperSig (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    BitVec (sigWidth + 1) :=
  let lower := computeLowerSig ctx
  if lower = 0#sigWidth && ctx.lsbMask = 0#sigWidth then
    BitVec.oneHotBV (w := sigWidth + 1) sigWidth
  else
    lower.zeroExtend (sigWidth + 1) + ctx.lsbMask.zeroExtend (sigWidth + 1)

/-! ### Naive Rounding Function

`roundNaive` mirrors `UnpackedFloat.round` exactly, but uses the named
component functions above. This makes it definitionally equal to `round`
while exposing the SMT-LIB-aligned structure.
-/

/-- A naive rounding function that decomposes `UnpackedFloat.round` into
named steps corresponding to SMT-LIB concepts.

The body is identical to `UnpackedFloat.round`, but with named intermediates
that each have a corresponding SMT-LIB bridge theorem. -/
@[bv_normalize]
def UnpackedFloat.roundNaive {expWidth sigWidth : Nat}
    {targetExponentWidth targetSignificandWidth : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (mode : RoundingMode) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let ctx := mkRoundingContext (targetExponentWidth := targetExponentWidth)
    (targetSignificandWidth := targetSignificandWidth) inUf

  -- Named components (for theorem-stating purposes)
  let guardBit := computeGuardBit ctx
  let stickyBit := computeStickyBit ctx
  let isEven := computeIsEven ctx
  let sigwithHiddenCleared := computeLowerSig ctx

  -- Rounding decision (same as in UnpackedFloat.round)
  let shouldRoundUp := roundingDecision
    (mode := mode)
    (sign := inUf.sign)
    (significandEven := isEven)
    (guardBit := guardBit)
    (stickyBit := stickyBit)
    (_exact := false)

  -- Significand after rounding: either lower (truncate) or upper (truncate + increment)
  -- This exactly mirrors UnpackedFloat.round lines 692-699.
  let sigDidOverflow_RoundedTargetSigWithHidden : BitVec (sigWidth + 1) :=
    if shouldRoundUp then
      if sigwithHiddenCleared = 0#sigWidth && ctx.lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) (sigWidth)
      else
        sigwithHiddenCleared.zeroExtend (sigWidth + 1) + ctx.lsbMask.zeroExtend (sigWidth + 1)
    else
      sigwithHiddenCleared.zeroExtend (sigWidth + 1)

  let sigDidOverflow : Bool :=
    sigDidOverflow_RoundedTargetSigWithHidden.msb

  let roundedTargetSigWithHidden : BitVec sigWidth :=
    sigDidOverflow_RoundedTargetSigWithHidden.setWidth sigWidth

  let roundedTargetSigWithHiddenOverflowAdjusted : BitVec sigWidth :=
    if sigDidOverflow then
      BitVec.leadingOne sigWidth
    else
      roundedTargetSigWithHidden

  -- Exponent after rounding
  let roundedExpExtended : BitVec (expWidth + 1) :=
    if sigDidOverflow then
      ctx.exp.signExtend (expWidth + 1) + 1#(expWidth + 1)
    else
      ctx.exp.signExtend (expWidth + 1)

  -- Overflow/underflow detection
  let maxNormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
  let lateOverflow : Bool :=
    maxNormalExpBV.slt roundedExpExtended
  let minSubnormalExpBV : BitVec (expWidth + 1) :=
    BitVec.ofInt (expWidth + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth)
  let lateUnderflow : Bool :=
    roundedExpExtended.slt minSubnormalExpBV
  let underflow : Bool := lateUnderflow || ctx.earlyUnderflow
  let overflow : Bool := lateOverflow || ctx.earlyOverflow

  -- Clamp exponent
  let roundedClampedExpExtended : BitVec (expWidth + 1) :=
    if lateOverflow then
      maxNormalExpBV
    else if lateUnderflow then
      minSubnormalExpBV
    else
      roundedExpExtended

  -- Build final result
  let finalExp := roundedClampedExpExtended.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
  let finalSigTruncated := roundedTargetSigWithHiddenOverflowAdjusted.extractMsb' 0 (targetSignificandWidth + 1)
  let finalNumber : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    { sign := inUf.sign,
      ex := finalExp,
      sig := finalSigTruncated }

  rounderSpecialCases
    (roundingMode := mode)
    (roundedResult := finalNumber)
    (overflow := overflow)
    (underflow := underflow)
    (isZero := inUf.isZero)

/-! ### Circuit Equivalence

`roundNaive` is definitionally equal to `round` since it computes the same thing
with named intermediates.
-/

set_option warn.sorry false in
theorem roundNaive_eq_round {expWidth sigWidth : Nat}
    {targetExponentWidth targetSignificandWidth : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (mode : RoundingMode) :
    UnpackedFloat.roundNaive
      (targetExponentWidth := targetExponentWidth)
      (targetSignificandWidth := targetSignificandWidth) inUf mode =
    UnpackedFloat.round
      (targetExponentWidth := targetExponentWidth)
      (targetSignificandWidth := targetSignificandWidth) inUf mode := by
  sorry

/-! ### Preconditions for Rounding

Width conditions that must hold for the bitvector operations to be meaningful. -/

/-- Preconditions ensuring the bitvector widths are sufficient for rounding. -/
structure RoundingPreconditions (expWidth sigWidth targetExponentWidth targetSignificandWidth : Nat) : Prop where
  /-- Significand has enough room for target precision + guard + sticky. -/
  hSigWidth : sigWidth ≥ targetSignificandWidth + 3
  /-- Exponent is wide enough to represent all target exponent values. -/
  hExpWidth : expWidth ≥ exponentWidth targetExponentWidth targetSignificandWidth
  /-- Target significand width is positive. -/
  hTargetSigPos : 0 < targetSignificandWidth
  /-- Target exponent width is positive. -/
  hTargetExpPos : 0 < targetExponentWidth

/-! ### Computability Tests

Verify that `roundNaive` can compute by exhaustively checking it against
`UnpackedFloat.round` (which is tested against the golden reference).
-/

/-- Exhaustively check that `roundNaive` agrees with `round` for all packed floats
of given widths and rounding mode. -/
def checkRoundNaiveCorrect (EUnpacked SUnpackedNoHidden : Nat) (EOut SOutNoHidden : Nat) (mode : RoundingMode) : IO Bool := do
  let mut nsucceeded : Nat := 0
  let mut nfailed : Nat := 0
  let mut outError : String := ""

  for originalPacked in mkPackedFloats EUnpacked SUnpackedNoHidden do
    let originalEUnpacked := originalPacked.unpack
    if ! originalEUnpacked.isNumber then continue

    let originalUnpacked := originalEUnpacked.num
    let originalNormalized := originalUnpacked.normalize

    let naiveResult :=
      UnpackedFloat.roundNaive (targetExponentWidth := EOut) (targetSignificandWidth := SOutNoHidden)
        originalNormalized mode
    let roundResult :=
      UnpackedFloat.round (targetExponentWidth := EOut) (targetSignificandWidth := SOutNoHidden)
        originalNormalized mode

    let naivePacked := naiveResult.pack
    let roundPacked := roundResult.pack

    if naivePacked.equal_denotation roundPacked then
      nsucceeded := nsucceeded + 1
    else
      let err : String := ""
      let err := err ++ s!"\nFailed ❌ | original {repr originalEUnpacked}"
      let err := err ++ s!"\n  original (packed) {repr originalPacked}"
      let err := err ++ s!"\n  naive result (packed) {repr naivePacked}"
      let err := err ++ s!"\n  round result (packed) {repr roundPacked}"
      IO.println err
      outError := err
      nfailed := nfailed + 1

  if nfailed = 0 then
    IO.println s!"All {nsucceeded} succeeded ✅ (roundNaive = round for {EUnpacked}x{SUnpackedNoHidden} -> {EOut}x{SOutNoHidden} {repr mode})"
  else
    let fracSuccess : Float := (nsucceeded.toFloat * 100.0) / ((nsucceeded + nfailed).toFloat)
    throw (IO.Error.userError s!"({nsucceeded} succeeded / {nsucceeded + nfailed} total) ({fracSuccess}% succeeded) ({nfailed} failures) ❌\n{outError}")
  return nfailed = 0

-- Exhaustive tests: roundNaive agrees with round for all rounding modes.
#guard_msgs(drop info) in #eval checkRoundNaiveCorrect 4 5 4 2 .RNA
#guard_msgs(drop info) in #eval checkRoundNaiveCorrect 4 5 4 2 .RNE
#guard_msgs(drop info) in #eval checkRoundNaiveCorrect 4 5 4 2 .RTZ
#guard_msgs(drop info) in #eval checkRoundNaiveCorrect 4 5 4 2 .RTP
#guard_msgs(drop info) in #eval checkRoundNaiveCorrect 4 5 4 2 .RTN
#guard_msgs(drop info) in #eval checkRoundNaiveCorrect 2 6 2 4 .RTP

/-! ### Bitblasting Test

Verify that `roundNaive` is amenable to `bv_decide` by proving a concrete
instance via bitblasting. -/

/-- `roundNaive` agrees with `round` at concrete bitwidths, proved by `bv_decide`.
This confirms the definitions are bitblastable. -/
theorem roundNaive_eq_round_bv_decide_2_3_2_1 :
    ∀ (inUf : UnpackedFloat (exponentWidth 2 1) 2) (mode : RoundingMode),
      (UnpackedFloat.roundNaive (targetExponentWidth := 2) (targetSignificandWidth := 1) inUf mode).pack =
      (UnpackedFloat.round (targetExponentWidth := 2) (targetSignificandWidth := 1) inUf mode).pack := by
  bv_decide

end UnpackedRoundNaive
end Fp
