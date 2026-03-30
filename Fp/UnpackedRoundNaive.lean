import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Negation

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
  isEven : Bool
  lowerHalf : Bool
  tieBreak : Bool

/-- Build a `RoundingContext` from an `UnpackedFloat`, mirroring the
first half of `UnpackedFloat.round` (setup computation). -/
@[bv_normalize]
def mkRoundingContext {expWidth sigWidth : Nat}
    (targetExponentWidth targetSignificandWidth : Nat)
    (inUf : UnpackedFloat expWidth sigWidth) :
    RoundingContext expWidth sigWidth targetExponentWidth targetSignificandWidth :=
  let targetMinNormalExp : BitVec expWidth :=
    BitVec.ofInt expWidth (minNormalExp targetExponentWidth)
  let expGeMin :=
    if inUf.ex.slt targetMinNormalExp then targetMinNormalExp else inUf.ex
  let shiftAmtPositive := expGeMin - inUf.ex
  let guardBitIndexFromLsb : BitVec sigWidth :=
    BitVec.ofNat sigWidth ((sigWidth - 1) - (targetSignificandWidth + 1))
  let guardBitIndexFromLsbAdjusted : BitVec sigWidth :=
    guardBitIndexFromLsb + shiftAmtPositive.zeroExtend sigWidth
  let guardBitMask : BitVec sigWidth := BitVec.oneHotBV guardBitIndexFromLsbAdjusted
  let stickyBitsMask : BitVec sigWidth := BitVec.orderEncode guardBitIndexFromLsbAdjusted
  let guardBit : Bool := (inUf.sig &&& guardBitMask) != 0#sigWidth
  let stickyBit : Bool := (inUf.sig &&& stickyBitsMask) != 0#sigWidth
  let lsbMask : BitVec sigWidth :=
    BitVec.oneHotBV (guardBitIndexFromLsbAdjusted + 1#sigWidth)
  let isEven := (inUf.sig &&& lsbMask) = 0#sigWidth
  let lowerHalf := !guardBit
  let tieBreak := guardBit && !stickyBit

  { shiftAmtPositive, guardBitIndexFromLsbAdjusted, guardBitMask, stickyBitsMask, lsbMask,
    isEven, lowerHalf, tieBreak }

/-! ### Named Component Functions

Each function extracts one concept that corresponds to an SMT-LIB `RoundMethod` component.
-/

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
def UnpackedFloat.mkSmallestRepresentable (targetExponentWidth targetSignificandWidth : Nat) (sign : Bool) : UnpackedFloat e s where
  sign := sign
  sig := BitVec.allOnes _
  ex := BitVec.ofInt _ (minSubnormalExp targetExponentWidth targetSignificandWidth)

@[bv_normalize]
def UnpackedFloat.incrementMagnitude (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth) :
        EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let ctx := mkRoundingContext targetExponentWidth targetSignificandWidth uf
  if uf.isZero then
    -- incrementing zero gives the smallest representable subnormal
    EUnpackedFloat.mkNumber (UnpackedFloat.mkSmallestRepresentable targetExponentWidth targetSignificandWidth uf.sign)
  else
    -- Normal inexact case: increment magnitude by 1 ULP
    let sigCleared := uf.sig &&& (~~~(ctx.guardBitMask ||| ctx.stickyBitsMask))
    let sigWithOverflow : BitVec (sigWidth + 1) :=
      if sigCleared = 0#sigWidth && ctx.lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) sigWidth
      else
        sigCleared.zeroExtend (sigWidth + 1) + ctx.lsbMask.zeroExtend (sigWidth + 1)
    let sigOverflow := sigWithOverflow.msb
    let roundedSig := sigWithOverflow.setWidth sigWidth
    let adjustedSig := if sigOverflow then BitVec.leadingOne sigWidth else roundedSig
    let adjustedExp : BitVec (expWidth + 1) :=
      if sigOverflow then uf.ex.signExtend (expWidth + 1) + 1#(expWidth + 1)
      else uf.ex.signExtend (expWidth + 1)
    -- Late overflow check
    let maxExpBV := BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
    if maxExpBV.slt adjustedExp then
      EUnpackedFloat.mkInfinity uf.sign
    else
      EUnpackedFloat.mkNumber {
        sign := uf.sign
        sig := adjustedSig.extractMsb' 0 (targetSignificandWidth + 1)
        ex := adjustedExp.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
      }

-- upper x = - lower(-x)
@[bv_normalize]
def computeLowerNonneg (targetExponentWidth targetSignificandWidth : Nat)
    (inUf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat  (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  if inUf.isZero
  then EUnpackedFloat.mkNumber (UnpackedFloat.mkZero false)
  else -- nonzero, see if we are too small
    if inUf.ex.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth))
    then
      if inUf.sign
      then
        -- -ve: make smallest subnormal
        EUnpackedFloat.mkNumber (UnpackedFloat.mkSmallestRepresentable targetExponentWidth targetSignificandWidth true)
      else
        -- +ve: make +0, since it is the greatest lower bound.
        EUnpackedFloat.mkNumber (UnpackedFloat.mkZero false)
    else
      -- not too small in magnitude. See if too big
      if (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth)).slt inUf.ex
      then
        -- Overflow: return largest representable (toward zero direction).
        -- This is the magnitude-smaller candidate; `computeUpper` returns ±∞.
        EUnpackedFloat.mkNumber (UnpackedFloat.mkLargestRepresentable targetExponentWidth inUf.sign)
      else
        -- just right in magnitude, so return the truncated number
        EUnpackedFloat.mkNumber {
          sig := finalSigTruncated
          sign := inUf.sign
          ex := inUf.ex.signExtend _
        }
  where
    outSig := sigWithHidden &&& (~~~(ctx.guardBitMask ||| ctx.stickyBitsMask))
    sigWithHidden := inUf.sig
    finalSigTruncated := outSig.extractMsb' 0 _
    ctx := mkRoundingContext targetExponentWidth targetSignificandWidth inUf


/-- The magnitude-larger candidate: truncation + 1 ULP in magnitude.
Mirrors `smtLibUpper.upper` (the representable value one step further from zero).
When the value is exact (guard=0, sticky=0), upper = lower.
When inexact, increments the magnitude by adding `lsbMask` to the cleared sig.
Handles sig overflow (carry → exp+1) and late overflow (exp exceeds max → ±∞). -/
@[bv_normalize]
def computeUpperNonneg (targetExponentWidth targetSignificandWidth : Nat)
  (uf : UnpackedFloat expWidth sigWidth) :
  EUnpackedFloat  (exponentWidth targetExponentWidth (targetSignificandWidth))
  (targetSignificandWidth + 1) :=
  if uf.isZero
  then EUnpackedFloat.mkNumber (UnpackedFloat.mkZero true)
  else -- nonzero, see if we are too small
    if uf.ex.slt (BitVec.ofInt expWidth (minSubnormalExp targetExponentWidth targetSignificandWidth))
    then EUnpackedFloat.mkNumber (UnpackedFloat.mkZero uf.sign)
    else
      -- not too small in magnitude. See if too big
      if (BitVec.ofInt expWidth (maxNormalExp targetExponentWidth)).slt uf.ex
      then
        -- Overflow: return largest representable (toward zero direction).
        -- This is the magnitude-smaller candidate; `computeUpper` returns ±∞.
        EUnpackedFloat.mkNumber (UnpackedFloat.mkLargestRepresentable targetExponentWidth uf.sign)
  else
    -- Normal inexact case: increment magnitude by 1 ULP
    let sigCleared := uf.sig &&& (~~~(ctx.guardBitMask ||| ctx.stickyBitsMask))
    let sigWithOverflow : BitVec (sigWidth + 1) :=
      if sigCleared = 0#sigWidth && ctx.lsbMask = 0#sigWidth then
        BitVec.oneHotBV (w := sigWidth + 1) sigWidth
      else
        sigCleared.zeroExtend (sigWidth + 1) + ctx.lsbMask.zeroExtend (sigWidth + 1)
    let sigOverflow := sigWithOverflow.msb
    let roundedSig := sigWithOverflow.setWidth sigWidth
    let adjustedSig := if sigOverflow then BitVec.leadingOne sigWidth else roundedSig
    let adjustedExp : BitVec (expWidth + 1) :=
      if sigOverflow then uf.ex.signExtend (expWidth + 1) + 1#(expWidth + 1)
      else uf.ex.signExtend (expWidth + 1)
    -- Late overflow check
    let maxExpBV := BitVec.ofInt (expWidth + 1) (maxNormalExp targetExponentWidth)
    if maxExpBV.slt adjustedExp then
      EUnpackedFloat.mkInfinity uf.sign
    else
      EUnpackedFloat.mkNumber {
        sign := uf.sign
        sig := adjustedSig.extractMsb' 0 (targetSignificandWidth + 1)
        ex := adjustedExp.truncate (exponentWidth targetExponentWidth targetSignificandWidth)
      }
  where
    ctx := mkRoundingContext targetExponentWidth targetSignificandWidth uf



@[bv_normalize]
def computeLowerNeg
    (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat  (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let out := computeLowerNonneg targetExponentWidth targetSignificandWidth uf.neg
  out.neg

@[bv_normalize]
def computeUpperNeg
    (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat  (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let out := computeUpperNonneg targetExponentWidth targetSignificandWidth uf.neg
  out.neg


@[bv_normalize]
def computeLower
    (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat  (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  if uf.sign
  then computeLowerNeg targetExponentWidth targetSignificandWidth uf
  else computeLowerNonneg targetExponentWidth targetSignificandWidth uf

@[bv_normalize]
def computeUpper
    (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat  (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  if uf.sign
  then computeUpperNeg targetExponentWidth targetSignificandWidth uf
  else computeUpperNonneg targetExponentWidth targetSignificandWidth uf

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
def roundNaiveRNE (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth)
     :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := computeLower targetExponentWidth targetSignificandWidth uf
  let upper := computeUpper targetExponentWidth targetSignificandWidth uf
  let ctx := mkRoundingContext targetExponentWidth targetSignificandWidth uf
  if uf.isZero then (if uf.sign then upper else lower) -- rounderForSign
  else if ctx.lowerHalf then lower
  else if ctx.tieBreak && ctx.isEven then lower
  else if ctx.tieBreak && !ctx.isEven then upper
  else if !ctx.lowerHalf && !ctx.tieBreak then upper
  else lower -- unreachable

/-- RNA: Round to nearest, ties away from zero.
Mirrors correct IEEE 754 RNA semantics.
- `lowerHalf` → lower (value closer to truncation = nearest)
- `tieBreak` → upper (tie → away from zero = increase magnitude)
- `¬lowerHalf ∧ ¬tieBreak` → upper (value closer to increment = nearest) -/
@[bv_normalize]
def roundNaiveRNA (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth)
     :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let ctx := mkRoundingContext targetExponentWidth targetSignificandWidth uf
  let lower := computeLower targetExponentWidth targetSignificandWidth uf
  let upper := computeUpper targetExponentWidth targetSignificandWidth uf
  if uf.isZero then (if uf.sign then upper else lower)
  else if ctx.lowerHalf then lower
  else if ctx.tieBreak then upper
  else upper

/-- RTP: Round toward positive infinity.
Mirrors `RoundMethod.roundRTP` from `SmtLibSemantics.lean`.
- positive → upper (increase magnitude = toward +∞)
- negative → lower (decrease magnitude = toward +∞) -/
@[bv_normalize]
def roundNaiveRTP (targetExponentWidth targetSignificandWidth : Nat)
     (uf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    let lower := computeLower targetExponentWidth targetSignificandWidth uf
    let upper := computeUpper targetExponentWidth targetSignificandWidth uf
  if uf.isZero then (if uf.sign then upper else lower)
  else if !uf.sign then upper  -- positive: toward +∞ = increase magnitude
  else lower                          -- negative: toward +∞ = decrease magnitude

/-- RTN: Round toward negative infinity.
Mirrors `RoundMethod.roundRTN` from `SmtLibSemantics.lean`.
- negative → upper (increase magnitude = toward -∞)
- positive → lower (decrease magnitude = toward -∞) -/
@[bv_normalize]
def roundNaiveRTN (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth)
     :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := computeLower targetExponentWidth targetSignificandWidth uf
  let upper := computeUpper targetExponentWidth targetSignificandWidth uf
  if uf.isZero then (if uf.sign then upper else lower)
  else if uf.sign then upper   -- negative: toward -∞ = increase magnitude
  else lower                          -- positive: toward -∞ = decrease magnitude

/-- RTZ: Round toward zero (truncation).
Mirrors `RoundMethod.roundRTZ` from `SmtLibSemantics.lean`.
Always picks the magnitude-smaller candidate. -/
@[bv_normalize]
def roundNaiveRTZ (targetExponentWidth targetSignificandWidth : Nat)
    (uf : UnpackedFloat expWidth sigWidth) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  let lower := computeLower targetExponentWidth targetSignificandWidth uf
  let upper := computeUpper targetExponentWidth targetSignificandWidth uf
  if uf.isZero then (if uf.sign then upper else lower)
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
  if hmodeRNE : mode = .RNE then roundNaiveRNE targetExponentWidth targetSignificandWidth inUf
  else if hmodeRNA : mode = .RNA then roundNaiveRNA targetExponentWidth targetSignificandWidth inUf
  else if hmodeRTP : mode = .RTP then roundNaiveRTP targetExponentWidth targetSignificandWidth inUf
  else if hmodeRTN : mode = .RTN then roundNaiveRTN targetExponentWidth targetSignificandWidth inUf
  else if hmodeRTZ : mode = .RTZ then roundNaiveRTZ targetExponentWidth targetSignificandWidth inUf
  else
    let unreachable : False := by grind [RoundingMode]
    False.elim unreachable

/-! ### Circuit Equivalence

`roundNaive` is definitionally equal to `round` since it computes the same thing
with named intermediates.

Helper lemmas for reconciling the bitvector representations used by `round` (which
sign-extends the exponent to width+1 before comparison) against `computeLower/Upper`
(which compare directly at width `expWidth`).
-/

/-- Sign-extending and then truncating back is a no-op when the target width ≤ original. -/
private theorem setWidth_signExtend_succ {w n : Nat} (hn : n ≤ w) (x : BitVec w) :
    (x.signExtend (w + 1)).setWidth n = x.setWidth n := by
  ext i; rename_i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]
  simp [show i < w by omega, show i < w + 1 by omega]

/-- Used to prove 2^(w-1) ≤ 2^w for casting `pow_le_pow` from Nat to Int. -/
private theorem two_pow_pred_le_pow_int {w : Nat} : (2:Int)^(w-1) ≤ (2:Int)^w := by
  have : (2:Nat)^(w-1) ≤ (2:Nat)^w := Nat.pow_le_pow_right (by omega) (Nat.sub_le w 1)
  exact_mod_cast this

/-- `slt` against a constant that fits in `w` bits is the same whether the LHS is `w`-wide
or sign-extended to `w+1` bits, as long as `0 < w` and the constant is in range. -/
theorem slt_signExtend_succ_ofInt_range {w : Nat} (hw : 0 < w) (x : BitVec w) (n : Int)
    (hn_lo : -(2:Int)^(w-1) ≤ n) (hn_hi : n < (2:Int)^(w-1)) :
    (x.signExtend (w + 1)).slt (BitVec.ofInt (w + 1) n) = x.slt (BitVec.ofInt w n) := by
  have hpow := @two_pow_pred_le_pow_int w
  have h1 : (BitVec.ofInt w n).toInt = n :=
    BitVec.toInt_ofInt_eq_self hw hn_lo hn_hi
  have h2 : (BitVec.ofInt (w + 1) n).toInt = n := by
    refine BitVec.toInt_ofInt_eq_self (by omega) ?_ ?_
    · simp only [Nat.add_sub_cancel]; omega
    · simp only [Nat.add_sub_cancel]; omega
  simp only [BitVec.slt_eq_decide,
    BitVec.toInt_signExtend_of_le (by omega : w ≤ w + 1), h1, h2]


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
-- #guard_msgs in #eval checkRoundNaiveCorrect 4 5 4 2 .RNA
/--
info:
Failed ❌ | original { state := num, num := { sign := true, ex := 0x10#5, sig := 0x00#6 } }
  original (packed) { sign := -, ex := 0x0#4, sig := 0x00#5 }
  naive result (packed) { sign := +, ex := 0x0#4, sig := 0x0#2 }
  round result (packed) { sign := -, ex := 0x0#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x18#5, sig := 0x30#6 } }
  original (packed) { sign := -, ex := 0x0#4, sig := 0x0c#5 }
  naive result (packed) { sign := -, ex := 0x0#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x0#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x18#5, sig := 0x30#6 } }
  original (packed) { sign := +, ex := 0x0#4, sig := 0x0c#5 }
  naive result (packed) { sign := +, ex := 0x0#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x0#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x19#5, sig := 0x38#6 } }
  original (packed) { sign := -, ex := 0x0#4, sig := 0x1c#5 }
  naive result (packed) { sign := -, ex := 0x0#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x1#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x19#5, sig := 0x38#6 } }
  original (packed) { sign := +, ex := 0x0#4, sig := 0x1c#5 }
  naive result (packed) { sign := +, ex := 0x0#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x1#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x1#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x1#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x1#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x1#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x1#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x1#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x1#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x1#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x1#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x1#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x1#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x1#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x2#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x2#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x2#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x2#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x2#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x2#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x2#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x2#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x2#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x2#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x2#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x2#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x3#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x3#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x3#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x3#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x3#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x3#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x3#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x3#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x3#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x3#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x3#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x3#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x4#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x4#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x4#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x4#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x4#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x4#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x4#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x4#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x4#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x4#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x4#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x4#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x5#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x5#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x5#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x5#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x5#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x5#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x5#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x5#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x5#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x5#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x5#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x5#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x6#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x6#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x6#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x6#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x6#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x6#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x6#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x6#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x6#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x6#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x6#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x6#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x00#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x7#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x7#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x7#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x00#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x7#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x7#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x7#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x00#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x7#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x7#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x7#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x00#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x7#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x7#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x7#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x01#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x8#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x8#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x8#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x01#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x8#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x8#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x8#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x01#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x8#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x8#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x8#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x01#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x8#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x8#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x8#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x02#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0x9#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0x9#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0x9#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x02#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0x9#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0x9#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0x9#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x02#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0x9#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0x9#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0x9#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x02#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0x9#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0x9#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0x9#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x03#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0xa#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0xa#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0xa#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x03#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0xa#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0xa#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0xa#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x03#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0xa#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0xa#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0xa#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x03#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0xa#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0xa#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0xa#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x04#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0xb#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0xb#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0xb#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x04#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0xb#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0xb#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0xb#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x04#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0xb#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0xb#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0xb#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x04#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0xb#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0xb#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0xb#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x05#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0xc#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0xc#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0xc#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x05#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0xc#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0xc#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0xc#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x05#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0xc#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0xc#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0xc#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x05#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0xc#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0xc#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0xc#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x06#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0xd#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0xd#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0xd#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x06#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0xd#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0xd#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0xd#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x06#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0xd#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0xd#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0xd#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x06#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0xd#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0xd#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0xd#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x07#5, sig := 0x24#6 } }
  original (packed) { sign := -, ex := 0xe#4, sig := 0x04#5 }
  naive result (packed) { sign := -, ex := 0xe#4, sig := 0x1#2 }
  round result (packed) { sign := -, ex := 0xe#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x07#5, sig := 0x24#6 } }
  original (packed) { sign := +, ex := 0xe#4, sig := 0x04#5 }
  naive result (packed) { sign := +, ex := 0xe#4, sig := 0x1#2 }
  round result (packed) { sign := +, ex := 0xe#4, sig := 0x0#2 }

Failed ❌ | original { state := num, num := { sign := true, ex := 0x07#5, sig := 0x34#6 } }
  original (packed) { sign := -, ex := 0xe#4, sig := 0x14#5 }
  naive result (packed) { sign := -, ex := 0xe#4, sig := 0x3#2 }
  round result (packed) { sign := -, ex := 0xe#4, sig := 0x2#2 }

Failed ❌ | original { state := num, num := { sign := false, ex := 0x07#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0xe#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0xe#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0xe#4, sig := 0x2#2 }
---
error: (899 succeeded / 960 total) (93.645833% succeeded) (61 failures) ❌

Failed ❌ | original { state := num, num := { sign := false, ex := 0x07#5, sig := 0x34#6 } }
  original (packed) { sign := +, ex := 0xe#4, sig := 0x14#5 }
  naive result (packed) { sign := +, ex := 0xe#4, sig := 0x3#2 }
  round result (packed) { sign := +, ex := 0xe#4, sig := 0x2#2 }
-/
#guard_msgs in #eval checkRoundNaiveCorrect 4 5 4 2 .RNE
-- #guard_msgs in #eval checkRoundNaiveCorrect 4 5 4 2 .RTZ
-- #guard_msgs in #eval checkRoundNaiveCorrect 4 5 4 2 .RTP
-- #guard_msgs in #eval checkRoundNaiveCorrect 4 5 4 2 .RTN
-- #guard_msgs in #eval checkRoundNaiveCorrect 2 6 2 4 .RTP

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

def EUnpackedFloat.roundNaive {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inEuf : EUnpackedFloat expWidth sigWidth)
  (mode : RoundingMode) :
  EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  if inEuf.isNumber then
    Fp.UnpackedRoundNaive.UnpackedFloat.roundNaive (targetExponentWidth := targetExponentWidth) (targetSignificandWidth := targetSignificandWidth)
      inEuf.num mode
  else if inEuf.isNaN then EUnpackedFloat.mkNaN
  else EUnpackedFloat.mkInfinity inEuf.sign
