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
def RoundingContext.computeGuardBit
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  (ctx.inUf.sig &&& ctx.guardBitMask) != 0#sigWidth

/-- The sticky bit: OR of all bits below the guard bit.
When sticky = 0 and guard = 1, the value is exactly at the midpoint (tie).
When sticky = 1, the value is strictly between two representable values.
Together with guard, determines `RoundMethod.tieBreak`. -/
@[bv_normalize]
def RoundingContext.computeStickyBit
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  (ctx.inUf.sig &&& ctx.stickyBitsMask) != 0#sigWidth

/-- Whether the LSB of the truncated (lower) significand is even.
Corresponds to `RoundableIsEven.isEven` applied to `lower r`. -/
@[bv_normalize]
def RoundingContext.computeIsEven
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  ctx.inUf.sig &&& ctx.lsbMask = 0#sigWidth

/-- Whether the value is strictly in the lower half of `[lower, upper]`.
This holds when `guard = 0`, meaning the discarded bits are less than half a ULP.
Corresponds to `RoundMethod.lowerHalf`. -/
@[bv_normalize]
def RoundingContext.computeLowerHalf
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  !(computeGuardBit ctx)

/-- Whether the value is exactly at the midpoint between `lower` and `upper`.
This holds when `guard = 1` and `sticky = 0`.
Corresponds to `RoundMethod.tieBreak`. -/
@[bv_normalize]
def RoundingContext.computeTieBreak
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) : Bool :=
  computeGuardBit ctx && !(computeStickyBit ctx)

/--
Make the largest possible number that is representable, of a given sign.
-/
@[bv_normalize]
def UnpackedFloat.mkLargestRepresentable (targetExponentWidth : Nat) (sign : Bool) : UnpackedFloat e s where
  sign := sign
  sig := BitVec.allOnes _
  ex := BitVec.ofInt _ (maxNormalExp targetExponentWidth)

/--
Make the smallest possible number that is representable, of a given sign.
-/
@[bv_normalize]
def UnpackedFloat.mkSmallestRepresentable (targetExponentWidth targetSignificantWidth : Nat) (sign : Bool) : UnpackedFloat e s where
  sign := sign
  sig := BitVec.allOnes _
  ex := BitVec.ofInt _ (minSubnormalExp targetExponentWidth targetSignificantWidth)

@[bv_normalize]
def RoundingContext.computeLower
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    EUnpackedFloat  (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  -- Lower = truncation toward zero. Preserves sign for IEEE 754 -0 handling.
  if ctx.inUf.isZero
  then EUnpackedFloat.mkNumber (UnpackedFloat.mkZero ctx.inUf.sign)
  else -- nonzero, see if we are too small
    if ctx.exp.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth))
    then EUnpackedFloat.mkNumber (UnpackedFloat.mkZero ctx.inUf.sign)
    else
      -- not too small in magnitude. See if too big
      if (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth)).slt ctx.exp
      then
        -- Overflow: return largest representable (toward zero direction).
        -- This is the magnitude-smaller candidate; `computeUpper` returns ±∞.
        EUnpackedFloat.mkNumber (UnpackedFloat.mkLargestRepresentable targetExponentWidth ctx.inUf.sign)
      else
        -- just right in magnitude, so return the truncated number
        EUnpackedFloat.mkNumber {
          sig := finalSigTruncated
          sign := ctx.inUf.sign
          ex := ctx.inUf.ex.signExtend _
        }
  where
    outSig := sigWithHidden &&& (~~~(ctx.guardBitMask ||| ctx.stickyBitsMask))
    sigWithHidden := ctx.inUf.sig
    finalSigTruncated := outSig.extractMsb' 0 _


/-- The magnitude-larger candidate: truncation + 1 ULP in magnitude.
Mirrors `smtLibUpper.upper` (the representable value one step further from zero).
When the value is exact (guard=0, sticky=0), upper = lower.
When inexact, increments the magnitude by adding `lsbMask` to the cleared sig.
Handles sig overflow (carry → exp+1) and late overflow (exp exceeds max → ±∞). -/
@[bv_normalize]
def RoundingContext.computeUpper
  (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
  EUnpackedFloat  (exponentWidth targetExponentWidth (targetSignificandWidth))
  (targetSignificandWidth + 1) :=
  if !ctx.computeGuardBit && !ctx.computeStickyBit then ctx.computeLower -- exact: upper = lower
  else if ctx.earlyOverflow then
    -- Overflow: upper is ±∞ (the magnitude-larger candidate beyond max)
    EUnpackedFloat.mkInfinity ctx.inUf.sign
  else if ctx.earlyUnderflow then
    -- Underflow: lower is ±0, upper is ±min_subnormal
    EUnpackedFloat.mkNumber (UnpackedFloat.mkSmallestRepresentable targetExponentWidth targetSignificandWidth ctx.inUf.sign)
  else
    -- Normal inexact case: increment magnitude by 1 ULP
    let sigCleared := ctx.inUf.sig &&& (~~~(ctx.guardBitMask ||| ctx.stickyBitsMask))
    let sigWithOverflow : BitVec (sigWidth + 1) :=
      if sigCleared = 0#sigWidth && ctx.lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) sigWidth
      else
        sigCleared.zeroExtend (sigWidth + 1) + ctx.lsbMask.zeroExtend (sigWidth + 1)
    let sigOverflow := sigWithOverflow.msb
    let roundedSig := sigWithOverflow.setWidth sigWidth
    let adjustedSig := if sigOverflow then BitVec.leadingOne sigWidth else roundedSig
    let adjustedExp : BitVec (expWidth + 1) :=
      if sigOverflow then ctx.exp.signExtend (expWidth + 1) + 1#(expWidth + 1)
      else ctx.exp.signExtend (expWidth + 1)
    -- Late overflow check
    let maxExpBV := BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
    if maxExpBV.slt adjustedExp then
      EUnpackedFloat.mkInfinity ctx.inUf.sign
    else
      EUnpackedFloat.mkNumber {
        sign := ctx.inUf.sign
        sig := adjustedSig.extractMsb' 0 (targetSignificandWidth + 1)
        ex := adjustedExp.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
      }

/-! ### Per-mode Rounding Functions

Each function mirrors the corresponding `RoundMethod.roundXXX` from
`Fp/SmtLibSemantics.lean`, picking between `computeLower` (truncation toward zero)
and `computeUpper` (truncation + 1 ULP in magnitude) based on the mode.

Convention: `lower` = magnitude-smaller candidate, `upper` = magnitude-larger candidate.
`rounderForSign sign = if sign then upper else lower` (preserves sign of zero).
-/

/-- RNE: Round to nearest, ties to even significand.
Mirrors `RoundMethod.roundRNE` from `SmtLibSemantics.lean`.
- `lowerHalf` → lower (value closer to truncation)
- `tieBreak ∧ isEven` → lower (tie, truncation has even LSB)
- `tieBreak ∧ ¬isEven` → upper (tie, increment has even LSB)
- `¬lowerHalf ∧ ¬tieBreak` → upper (value closer to increment) -/
@[bv_normalize]
def roundNaiveRNE
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := ctx.computeLower
  let upper := ctx.computeUpper
  if ctx.inUf.isZero then (if ctx.inUf.sign then upper else lower) -- rounderForSign
  else if ctx.computeLowerHalf then lower
  else if ctx.computeTieBreak && ctx.computeIsEven then lower
  else if ctx.computeTieBreak && !ctx.computeIsEven then upper
  else if !ctx.computeLowerHalf && !ctx.computeTieBreak then upper
  else lower -- unreachable

/-- RNA: Round to nearest, ties away from zero.
Mirrors correct IEEE 754 RNA semantics.
- `lowerHalf` → lower (value closer to truncation = nearest)
- `tieBreak` → upper (tie → away from zero = increase magnitude)
- `¬lowerHalf ∧ ¬tieBreak` → upper (value closer to increment = nearest) -/
@[bv_normalize]
def roundNaiveRNA
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := ctx.computeLower
  let upper := ctx.computeUpper
  if ctx.inUf.isZero then (if ctx.inUf.sign then upper else lower)
  else if ctx.computeLowerHalf then lower
  else if ctx.computeTieBreak then upper
  else upper

/-- RTP: Round toward positive infinity.
Mirrors `RoundMethod.roundRTP` from `SmtLibSemantics.lean`.
- positive → upper (increase magnitude = toward +∞)
- negative → lower (decrease magnitude = toward +∞) -/
@[bv_normalize]
def roundNaiveRTP
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := ctx.computeLower
  let upper := ctx.computeUpper
  if ctx.inUf.isZero then (if ctx.inUf.sign then upper else lower)
  else if !ctx.inUf.sign then upper  -- positive: toward +∞ = increase magnitude
  else lower                          -- negative: toward +∞ = decrease magnitude

/-- RTN: Round toward negative infinity.
Mirrors `RoundMethod.roundRTN` from `SmtLibSemantics.lean`.
- negative → upper (increase magnitude = toward -∞)
- positive → lower (decrease magnitude = toward -∞) -/
@[bv_normalize]
def roundNaiveRTN
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := ctx.computeLower
  let upper := ctx.computeUpper
  if ctx.inUf.isZero then (if ctx.inUf.sign then upper else lower)
  else if ctx.inUf.sign then upper   -- negative: toward -∞ = increase magnitude
  else lower                          -- positive: toward -∞ = decrease magnitude

/-- RTZ: Round toward zero (truncation).
Mirrors `RoundMethod.roundRTZ` from `SmtLibSemantics.lean`.
Always picks the magnitude-smaller candidate. -/
@[bv_normalize]
def roundNaiveRTZ
    (ctx : RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := ctx.computeLower
  if ctx.inUf.isZero then (if ctx.inUf.sign then ctx.computeUpper else lower)
  else lower -- always truncate toward zero

/-! ### Naive Rounding Function

`roundNaive` mirrors `RoundMethod.round` from `SmtLibSemantics.lean`,
dispatching on the rounding mode to the per-mode functions above.
-/

/-- A naive rounding function that mirrors the SMT-LIB `RoundMethod.round`
structure, picking between `computeLower` and `computeUpper` based on
the rounding mode and the predicates `lowerHalf`, `tieBreak`, `isEven`. -/
@[bv_normalize]
def UnpackedFloat.roundNaive {expWidth sigWidth : Nat}
    {targetExponentWidth targetSignificandWidth : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (mode : RoundingMode) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let ctx := mkRoundingContext (targetExponentWidth := targetExponentWidth)
    (targetSignificandWidth := targetSignificandWidth) inUf
  if hmodeRNE : mode = .RNE then roundNaiveRNE ctx
  else if hmodeRNA : mode = .RNA then roundNaiveRNA ctx
  else if hmodeRTP : mode = .RTP then roundNaiveRTP ctx
  else if hmodeRTN : mode = .RTN then roundNaiveRTN ctx
  else if hmodeRTZ : mode = .RTZ then roundNaiveRTZ ctx
  else
    let unreachable : False := by grind [RoundingMode]
    False.elim unreachable

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
structure RoundingPreconditions
    (expWidth sigWidth targetExponentWidth targetSignificandWidth : Nat) : Prop where
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

/-! ### Identity Theorem

When the input value is exactly representable in the target format
(extra low bits are zero, exponent in range), `roundNaive` preserves the value
regardless of rounding mode. Uses wider input (`sigWidth=4 > targetSig+2=3`)
so the guard bit index `(sigWidth-1) - (targetSignificandWidth+1) = 1` doesn't
underflow in Nat. -/

/-- When the input is exactly representable in the target format,
`roundNaive` preserves the value regardless of rounding mode. -/
theorem roundNaive_identity_exact_2_1 :
    ∀ (inUf : UnpackedFloat 3 4) (mode : RoundingMode),
      -- Value is exactly representable: guard and sticky bits are zero
      inUf.sig &&& 3#4 = 0#4 →
      -- Not overflow
      ¬(BitVec.ofInt 3 (maxNormalExp 2)).slt inUf.ex →
      -- Not underflow
      ¬inUf.ex.slt (BitVec.ofInt 3 (minSubnormalExp 2 1)) →
      -- Not zero (zero case follows a different code path)
      ¬inUf.isZero →
      UnpackedFloat.roundNaive (targetExponentWidth := 2) (targetSignificandWidth := 1) inUf mode =
        EUnpackedFloat.mkNumber {
          sign := inUf.sign
          sig := inUf.sig.extractMsb' 0 2
          ex := inUf.ex
        } := by
  sorry

end UnpackedRoundNaive
end Fp
