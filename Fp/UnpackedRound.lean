import Fp.Basic
import Fp.Rounding
import Fp.MulInv
import Fp.Proofs.Grind
import Fp.ForLean.Rat

@[bv_normalize]
def BitVec.leadingOne (w : Nat) : BitVec w :=
  1#w <<< (w - 1)

@[simp]
def BitVec.getElem_leadingOne (w : Nat) (i : Nat) (hi : i < w ) : (BitVec.leadingOne w)[i] = decide (i = w - 1) := by
  simp [leadingOne]
  grind

@[bv_normalize]
def BitVec.decrement (x : BitVec w) : BitVec w := x - 1#w

@[bv_normalize]
def BitVec.extendAtMsb (x : BitVec w) (δ : Nat) : BitVec (δ + w) :=
  x.zeroExtend _

/-- Extract from the MSB, starting at msb 'hi', going downward for 'len' bits. -/
@[bv_normalize]
def BitVec.extractMsb' (x : BitVec w) (hi : Nat) (len : Nat) : BitVec len :=
  x.extractLsb' (w - (hi + len)) len

@[simp]
theorem BitVec.getMsbD_extractMsb' {w hi len} (h : hi + len ≤ w) (x : BitVec w) (hi' : i < len) :
  (x.extractMsb' hi len).getMsbD i = (x.getMsbD (hi + i)) := by
  simp [extractMsb', BitVec.getMsbD_eq_getLsbD]
  grind

@[bv_normalize]
def BitVec.expandingSubtract {w} (a b : BitVec w) : BitVec (w + 1) :=
  let a' : BitVec (w + 1) := a.signExtend (w + 1)
  let b' : BitVec (w + 1) := b.signExtend (w + 1)
  a' - b'


@[simp]
theorem BitVec.toInt_expandingSubtract {w} (a b : BitVec w) :
  (expandingSubtract a b).toInt = a.toInt - b.toInt := by
  simp [expandingSubtract, toInt_signExtend]
  have : 2 ^ (w + 1) / 2 = 2^w := by grind
  apply Int.bmod_eq_of_le <;> grind


@[bv_normalize]
def BitVec.width {w : Nat} (_x : BitVec w) : Nat := w

/-- Convert a binary number into a unary encoding of the number. -/
@[bv_normalize]
def BitVec.orderEncode (x : BitVec w) : BitVec w :=
  (1#w <<< x) - 1

@[bv_normalize]
def BitVec.scollar (x : BitVec w) (minVal : BitVec w) (maxVal : BitVec w) : BitVec w :=
  if x.slt minVal then minVal
  else if maxVal.slt x then maxVal
  else x

@[bv_normalize]
def BitVec.extractMsb (x : BitVec w) (hi : Nat) (lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb' (w - 1 - hi) (hi - lo + 1)

#check BitVec.getLsbD_extractLsb

/-
theorem BitVec.getMsbD_extractMsb {w hi lo : Nat} (x : BitVec w)
  (i : Nat) :
  (x.extractMsb hi lo).getMsbD i =
  (x.getMsbD (lo + i) && decide (i < hi - lo + 1)) := by
  simp [extractMsb, BitVec.getMsbD_eq_getLsbD]
  by_cases h1 : i < hi - lo + 1
  · simp [h1]
    by_cases h2 : lo + i < w
    · simp [h2]
      sorry
    · simp [h2]

      sorry
  · grind
-/

-- roundingDecision mode inUf.sign significandEven choosenGuardBit choosenStickyBit false
-- bollu: TODO: port rounding mode for real.
@[bv_normalize]
def roundingDecision (mode : RoundingMode) (sign : Bool) (significandEven : Bool)
  (guardBit : Bool) (stickyBit : Bool) (exact : Bool) : Bool :=
  match mode with
  | RoundingMode.RNE =>
      (guardBit && (stickyBit || !significandEven))
  | _ => false

/-
  // The final reconstruction of the rounded result
  // Handles the overflow and underflow conditions
  template <class t>
  unpackedFloat<t> rounderSpecialCases (const typename t::fpt &format,
					const typename t::rm &roundingMode,
					const unpackedFloat<t> &roundedResult,
					const typename t::prop &overflow,
					const typename t::prop &underflow,
					const typename t::prop &isZero)
-/
@[bv_normalize]
def rounderSpecialCases
  (roundingMode : RoundingMode)
  (roundedResult : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1))
  (overflow : Bool)
  (underflow : Bool)
  (isZero : Bool) : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
/-
    /*** Underflow and overflow ***/

    // On overflow either return inf or max
    prop returnInf(roundingMode == t::RNE() ||
		   roundingMode == t::RNA() ||
		   (roundingMode == t::RTP() && !roundedResult.getSign()) ||
		   (roundingMode == t::RTN() &&  roundedResult.getSign()));
    probabilityAnnotation<t>(returnInf, LIKELY);  // Inf is more likely than max in most application scenarios
-/
  let returnInf : Bool :=
    match roundingMode with
    | RoundingMode.RNE => true
    | RoundingMode.RNA => true
    | RoundingMode.RTP => !roundedResult.sign
    | RoundingMode.RTN => roundedResult.sign
    | _ => false
/-
    // On underflow either return 0 or minimum subnormal
    prop returnZero(roundingMode == t::RNE() ||
		    roundingMode == t::RNA() ||
		    roundingMode == t::RTZ() ||
		    (roundingMode == t::RTP() &&  roundedResult.getSign()) ||
		    (roundingMode == t::RTN() && !roundedResult.getSign()));
    probabilityAnnotation<t>(returnZero, LIKELY);   // 0 is more likely than min in most application scenarios
-/
  let returnZero : Bool :=
    match roundingMode with
    | RoundingMode.RNE => true
    | RoundingMode.RNA => true
    | RoundingMode.RTZ => true
    | RoundingMode.RTP => roundedResult.sign
    | RoundingMode.RTN => !roundedResult.sign

/-
    /*** Reconstruct ***/
    unpackedFloat<t> inf(unpackedFloat<t>::makeInf(format, roundedResult.getSign()));
    unpackedFloat<t> max(roundedResult.getSign(), unpackedFloat<t>::maxNormalExponent(format), ubv::allOnes(unpackedFloat<t>::significandWidth(format)));
    unpackedFloat<t> min(roundedResult.getSign(), unpackedFloat<t>::minSubnormalExponent(format), unpackedFloat<t>::leadingOne(unpackedFloat<t>::significandWidth(format)));
    unpackedFloat<t> zero(unpackedFloat<t>::makeZero(format, roundedResult.getSign()));
-/
  let inf : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkInfinity roundedResult.sign
  let max : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkNumber <|
    { sign := roundedResult.sign,
      ex := BitVec.ofInt (exponentWidth targetExponentWidth targetSignificandWidth) (maxNormalExp targetExponentWidth),
      sig := BitVec.allOnes (targetSignificandWidth + 1) }
  let min : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkNumber <|
    { sign := roundedResult.sign,
      ex := BitVec.ofInt (exponentWidth targetExponentWidth targetSignificandWidth) (minSubnormalExp targetExponentWidth targetSignificandWidth),
      sig := BitVec.leadingOne (targetSignificandWidth + 1) }
  let zero : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    EUnpackedFloat.mkZero roundedResult.sign
/-
    unpackedFloat<t> result(ITE(isZero,
				zero,
				ITE(underflow,
				    ITE(returnZero, zero, min),
				    ITE(overflow,
					ITE(returnInf, inf, max),
					roundedResult))));
    return result;
  }
-/
  if isZero then
    zero
  else if underflow then
    if returnZero then
      zero
    else
      min
  else if overflow then
    if returnInf then
      inf
    else
      max
  else
    EUnpackedFloat.mkNumber <| roundedResult

axiom AxRoundPreconditions {P : Prop} : P

-- https://github.com/martin-cs/symfpu/blob/aeaa3fa62730148c855f5a9e0a9b7040d48e0b7e/core/rounder.h#L299
@[bv_normalize]
def UnpackedFloat.round {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : UnpackedFloat expWidth sigWidth)
  (mode : RoundingMode)
  (hs : sigWidth >= targetSignificandWidth + 3 := AxRoundPreconditions)
  (he : expWidth >= targetExponentWidth := AxRoundPreconditions)
  (hs' : sigWidth >= 1 := AxRoundPreconditions) :
  EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
/-
  //PRECONDITION(uf.valid(format));
  // Not a precondition because
  //  1. Exponent and significand may be extended.
  //  2. Their values may also be outside of the correct range.
  //
  // However this weaker condition will hold:
  sbv exp(uf.getExponent());
  bwt expWidth(exp.getWidth());
  PRECONDITION(uf.wellFormed(sbv::minValue(expWidth), sbv::maxValue(expWidth)));
-/
  let exp := inUf.ex

/-
  // Also there are some conditions on how the rounder is used.
  // * Must have round and sticky bits
  ubv psig(uf.getSignificand());
  bwt sigWidth(psig.getWidth());
  ubv sig(psig | unpackedFloat<t>::leadingOne(sigWidth));
-/
  -- @bollu: ORing with a leading 1 is nonsensical?
  let psig := inUf.sig
  let sig := psig ||| (BitVec.leadingOne sigWidth) --  @abdal: this seems wrong. For us, does 'sigWidth' have the leading one?
/-
  bwt targetSignificandWidth(unpackedFloat<t>::significandWidth(format));
  PRECONDITION(sigWidth >= targetSignificandWidth + 2);
-/
/-
  bwt targetExponentWidth(unpackedFloat<t>::exponentWidth(format));
  PRECONDITION(expWidth >= targetExponentWidth);
-/
/-
  /*** Early underflow and overflow detection ***/
  bwt exponentExtension(expWidth - targetExponentWidth);
  prop earlyOverflow(exp > unpackedFloat<t>::maxNormalExponent(format).extend(exponentExtension));
  prop earlyUnderflow(exp < unpackedFloat<t>::minSubnormalExponent(format).extend(exponentExtension).decrement());
  // Optimisation : if the precondition on sigWidth and targetSignificandWidth is removed
  //                then can change to:
  //                   exponent >= minSubnormalExponent - 1
  //                && sigWidth > targetSignificandBits
  probabilityAnnotation<t>(earlyOverflow, UNLIKELY);  // (over,under)flows are generally rare events
  probabilityAnnotation<t>(earlyUnderflow, UNLIKELY);

  prop potentialLateOverflow(exp == unpackedFloat<t>::maxNormalExponent(format).extend(exponentExtension));
  prop potentialLateUnderflow(exp == unpackedFloat<t>::minSubnormalExponent(format).extend(exponentExtension).decrement());
  probabilityAnnotation<t>(potentialLateOverflow, VERYUNLIKELY);
  probabilityAnnotation<t>(potentialLateUnderflow, VERYUNLIKELY);
-/
  let earlyOverflow : Bool := exp > BitVec.ofInt expWidth (maxNormalExp targetExponentWidth)
  let earlyUnderflow : Bool := exp < (BitVec.ofInt expWidth (subnormalExp targetExponentWidth)).decrement
  let potentialLateOverflow := exp == BitVec.ofInt expWidth (maxNormalExp targetExponentWidth)
  let potentialLateUnderflow := exp == (BitVec.ofInt expWidth (subnormalExp targetExponentWidth)).decrement
/-
  /*** Normal or subnormal rounding? ***/
  prop normalRoundingRange(exp >= unpackedFloat<t>::minNormalExponent(format).extend(exponentExtension));
  probabilityAnnotation<t>(normalRoundingRange, LIKELY);
  prop normalRounding(normalRoundingRange || known.subnormalExact);
-/
  let normalRoundingRange : Bool :=
    exp >= BitVec.ofInt expWidth (minNormalExp targetExponentWidth)
  let normalRounding : Bool := normalRoundingRange -- || known.subnormalExact
/-
  /*** Round to correct significand. ***/
  ubv extractedSignificand(sig.extract(sigWidth - 1, sigWidth - targetSignificandWidth).extend(1)); // extended to catch the overflow
-/
  -- @bollu: deviation.
  let extractedSignificand : BitVec (targetSignificandWidth + 2) :=
    ((sig.extractMsb' 0 (targetSignificandWidth + 1)).zeroExtend (targetSignificandWidth + 2)).cast (by omega)
/-
  // Normal guard and sticky bits
  bwt guardBitPosition(sigWidth - (targetSignificandWidth + 1));
  prop guardBit(sig.extract(guardBitPosition, guardBitPosition).isAllOnes());
-/
  let guardBitPosition : Nat := sigWidth - (targetSignificandWidth + 2)
  let guardBit : Bool := sig.getLsbD guardBitPosition
/-
  prop stickyBit(!sig.extract(guardBitPosition - 1,0).isAllZeros());
-/
  let stickyBit : Bool := (sig.extractLsb (guardBitPosition - 1) 0) ≠ (BitVec.ofNat (guardBitPosition) 0).cast (by omega)
/-
  // For subnormals, locating the guard and stick bits is a bit more involved
  //sbv subnormalAmount(uf.getSubnormalAmount(format)); // Catch is, uf isn't in the given format, so this doesn't work
  sbv subnormalAmount(expandingSubtract<t>(unpackedFloat<t>::minNormalExponent(format).matchWidth(exp),exp));
  INVARIANT((subnormalAmount < sbv(expWidth + 1, sigWidth - 1)) || earlyUnderflow);
-/
  -- @bollu: I would have expected the subtraction in 'subnormalAmount' to be in the 'opposite' direction!
  let subnormalAmount : BitVec (expWidth + 1) :=
    BitVec.expandingSubtract (BitVec.ofInt (expWidth) (minNormalExp targetExponentWidth)) exp
/-
  // Note that this is negative if normal, giving a full subnormal mask
  // but the result will be ignored (see the next invariant)


  // Care is needed if the exponents are longer than the significands
  // In the case when data is lost it is negative and not used
  bwt extractedSignificandWidth(extractedSignificand.getWidth());
  ubv subnormalShiftPrepared((extractedSignificandWidth >= expWidth + 1) ?
			     subnormalAmount.toUnsigned().matchWidth(extractedSignificand) :
			     subnormalAmount.toUnsigned().extract(extractedSignificandWidth - 1, 0));
  -/
  let extractedSignificandWidth : Nat := extractedSignificand.width
  -- bollu: 'extractedSignificandWidth = targetSignificandWidth + 2'
  let subnormalShiftPrepared : BitVec extractedSignificandWidth :=
    subnormalAmount.signExtend extractedSignificandWidth
    /- bollu: deviatioon
    if extractedSignificandWidth >= expWidth + 1 then
      subnormalAmount.setWidth extractedSignificandWidth
    else
      (subnormalAmount.extractLsb (extractedSignificandWidth - 1) 0).cast (by simp [extractedSignificandWidth, BitVec.width])
    -/
/-
  // Compute masks
  ubv subnormalMask(orderEncode<t>(subnormalShiftPrepared)); // Invariant implies this if all ones, it will not be used
  ubv subnormalStickyMask(subnormalMask >> ubv::one(targetSignificandWidth + 1)); // +1 as the exponent is extended
-/
  let subnormalMask : BitVec (targetSignificandWidth + 2) :=
    BitVec.orderEncode subnormalShiftPrepared
  let subnormalStickyMask : BitVec (targetSignificandWidth + 2) :=
    subnormalMask >>> 1#(targetSignificandWidth + 2)
/-
  // Apply
  ubv subnormalMaskedSignificand(extractedSignificand & (~subnormalMask));
  ubv subnormalMaskRemoved(extractedSignificand & subnormalMask);
  // Optimisation : remove the masking with a single orderEncodeBitwise style construct
-/
  let subnormalMaskedSignificand : BitVec (targetSignificandWidth + 2) :=
    extractedSignificand &&& (~~~subnormalMask)
  let subnormalMaskRemoved : BitVec (targetSignificandWidth + 2) :=
    extractedSignificand &&& subnormalMask
/-
  prop subnormalGuardBit(!(subnormalMaskRemoved & (~subnormalStickyMask)).isAllZeros());
  prop subnormalStickyBit(guardBit || stickyBit ||
			  !((subnormalMaskRemoved & subnormalStickyMask).isAllZeros()));
-/
  let subnormalGuardBV : BitVec (targetSignificandWidth + 2) :=
    subnormalMaskRemoved &&& (~~~subnormalStickyMask)
  let subnormalGuardBit : Bool :=
    subnormalGuardBV ≠ BitVec.ofNat (targetSignificandWidth + 2) 0
  let subnormalStickyBV : BitVec (targetSignificandWidth + 2) :=
    subnormalMaskRemoved &&& subnormalStickyMask
  let subnormalStickyBit : Bool :=
    guardBit || stickyBit || (subnormalStickyBV ≠ BitVec.ofNat (targetSignificandWidth + 2) 0)
/-
  ubv subnormalIncrementAmount((subnormalMask.modularLeftShift(ubv::one(targetSignificandWidth + 1))) & ~subnormalMask); // The only case when this looses info is earlyUnderflow
  INVARIANT(IMPLIES(subnormalIncrementAmount.isAllZeros(), earlyUnderflow || normalRounding));
-/
  let subnormalIncrementAmount : BitVec (targetSignificandWidth + 2) :=
    ((subnormalMask <<< 1#(targetSignificandWidth + 2)) &&& (~~~subnormalMask))
/-
  // Have to choose the right one dependent on rounding mode
  prop choosenGuardBit(ITE(normalRounding, guardBit, subnormalGuardBit));
  prop choosenStickyBit(ITE(normalRounding, stickyBit, subnormalStickyBit));
-/
  let choosenGuardBit : Bool := if normalRounding then guardBit else subnormalGuardBit
  let choosenStickyBit : Bool := if normalRounding then stickyBit else subnormalStickyBit
/-
  prop significandEven(ITE(normalRounding,
			   extractedSignificand.extract(0,0).isAllZeros(),
			   ((extractedSignificand & subnormalIncrementAmount).isAllZeros())));
-/
  let significandEven : Bool := if normalRounding then
    extractedSignificand.getLsbD 0 == false
  else
    (extractedSignificand &&& subnormalIncrementAmount) == BitVec.ofNat (targetSignificandWidth + 2) 0
/-
  prop roundUp(roundingDecision<t>(roundingMode, uf.getSign(), significandEven,
				   choosenGuardBit, choosenStickyBit,
				   known.exact || (known.subnormalExact && !normalRoundingRange)));
-/
  let roundUp : Bool :=
    roundingDecision mode inUf.sign significandEven choosenGuardBit choosenStickyBit false
/-
  // Perform the increment as needed
  ubv leadingOne(unpackedFloat<t>::leadingOne(targetSignificandWidth));
  // Not actually true, consider minSubnormalExponent - 1 : not an early underfow and empty significand
  //INVARIANT(!(subnormalMaskedSignificand & leadingOne).isAllZeros() ||
  //          earlyUnderflow); // This one really matters, it means only the early underflow path is wrong

-/
  let leadingOne : BitVec (targetSignificandWidth + 1) :=
    BitVec.leadingOne (targetSignificandWidth + 1)
/-
  // Convert the round up flag to a mask
  ubv normalRoundUpAmount(ubv(roundUp).matchWidth(extractedSignificand));
  ubv subnormalRoundUpMask(ubv(roundUp).append(ubv::zero(targetSignificandWidth)).signExtendRightShift(ubv(targetSignificandWidth + 1, targetSignificandWidth)));
  ubv subnormalRoundUpAmount(subnormalRoundUpMask & subnormalIncrementAmount);
-/
  let normalRoundUpAmount : BitVec (targetSignificandWidth + 2) :=
    (BitVec.ofBool roundUp).setWidth (targetSignificandWidth + 2)
  -- bollu : 'subnormalRoundUpMask' should just be allOnes or zero.
  let subnormalRoundUpMask : BitVec (targetSignificandWidth + 2) :=
    let b := BitVec.ofBool roundUp
    let appended := b.append (BitVec.ofNat (targetSignificandWidth + 1) 0)
    let out := appended >>> targetSignificandWidth
    out.cast (by omega)
  let subnormalRoundUpAmount : BitVec (targetSignificandWidth + 2) :=
    subnormalRoundUpMask &&& subnormalIncrementAmount
/-
  ubv rawRoundedSignificand((ITE(normalRounding,
				 extractedSignificand,
				 subnormalMaskedSignificand)
			     +
			     ITE(normalRounding,
				 normalRoundUpAmount,
				 subnormalRoundUpAmount)));
-/
  let rawRoundedSignificand : BitVec (targetSignificandWidth + 2) :=
    (if normalRounding then
      extractedSignificand
    else
      subnormalMaskedSignificand) +
    (if normalRounding then
      normalRoundUpAmount
    else
      subnormalRoundUpAmount)
/-
  // We might have lost the leading one, if so, re-add and note that we need to increment the significand
  prop significandOverflow(rawRoundedSignificand.extract(targetSignificandWidth, targetSignificandWidth).isAllOnes());
  INVARIANT(IMPLIES(significandOverflow, roundUp));
-/
  let significandOverflow : Bool :=
    rawRoundedSignificand.msb == true
/-
  ubv extractedRoundedSignificand(rawRoundedSignificand.extract(targetSignificandWidth - 1, 0));
  ubv roundedSignificand(extractedRoundedSignificand | leadingOne);
  INVARIANT(IMPLIES(significandOverflow, extractedRoundedSignificand.isAllZeros()));
-/
  let extractedRoundedSignificand : BitVec (targetSignificandWidth + 1) :=
    rawRoundedSignificand.extractLsb' 0 (targetSignificandWidth + 1)
  let roundedSignificand : BitVec (targetSignificandWidth + 1) :=
    extractedRoundedSignificand ||| leadingOne
/-
  /*** Round to correct exponent. ***/

  // The extend is almost certainly unnecessary (see specialised rounders)
  sbv extendedExponent(exp.extend(1));
-/
  let extendedExponent : BitVec ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) :=
    exp.signExtend ((exponentWidth targetExponentWidth targetSignificandWidth) + 1)
/-
  prop incrementExponentNeeded(roundUp && significandOverflow);  // The roundUp is implied but kept for signal forwarding
  probabilityAnnotation<t>(incrementExponentNeeded, VERYUNLIKELY);
  prop incrementExponent(!known.noSignificandOverflow && incrementExponentNeeded);
  INVARIANT(IMPLIES(known.noSignificandOverflow, !incrementExponentNeeded));
-/
  let incrementExponentNeeded : Bool := roundUp && significandOverflow
  let incrementExponent : Bool := incrementExponentNeeded -- && !known.noSignificandOverflow
/-
  sbv correctedExponent(conditionalIncrement<t>(incrementExponent, extendedExponent));
-/
  let correctedExponent : BitVec ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) :=
    if incrementExponent then
      extendedExponent + 1#((exponentWidth targetExponentWidth targetSignificandWidth) + 1)
    else
      extendedExponent
/-
  // Track overflows and underflows
  sbv maxNormal(unpackedFloat<t>::maxNormalExponent(format).matchWidth(correctedExponent));
  sbv minSubnormal(unpackedFloat<t>::minSubnormalExponent(format).matchWidth(correctedExponent));
-/
  let maxNormal : BitVec ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) :=
    BitVec.ofInt ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) (maxNormalExp targetExponentWidth)
  let minSubnormal : BitVec ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) :=
    BitVec.ofInt ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) (minSubnormalExp targetExponentWidth targetSignificandWidth)
/-
  sbv correctedExponentInRange(collar<t>(correctedExponent, minSubnormal, maxNormal));
-/
  let correctedExponentInRange : BitVec ((exponentWidth targetExponentWidth targetSignificandWidth) + 1) :=
    BitVec.scollar correctedExponent minSubnormal maxNormal
/-
  bwt currentExponentWidth(correctedExponentInRange.getWidth());
  sbv roundedExponent(correctedExponentInRange.contract(currentExponentWidth - targetExponentWidth));
-/
  let currentExponentWidth : Nat := correctedExponentInRange.width
  let roundedExponent : BitVec (exponentWidth targetExponentWidth targetSignificandWidth) :=
    correctedExponentInRange.extractLsb' 0 (exponentWidth targetExponentWidth targetSignificandWidth)
/-
  /*** Finish ***/

  prop computedOverflow(potentialLateOverflow && incrementExponentNeeded);
  prop computedUnderflow(potentialLateUnderflow && !incrementExponentNeeded);
  probabilityAnnotation<t>(computedOverflow, UNLIKELY);
  probabilityAnnotation<t>(computedUnderflow, UNLIKELY);
-/
  let computedOverflow : Bool := potentialLateOverflow && incrementExponentNeeded
  let computedUnderflow : Bool := potentialLateUnderflow && !incrementExponentNeeded
/-
  prop lateOverflow(!earlyOverflow && computedOverflow);
  prop lateUnderflow(!earlyUnderflow && computedUnderflow);
  probabilityAnnotation<t>(lateOverflow, VERYUNLIKELY);
  probabilityAnnotation<t>(lateUnderflow, VERYUNLIKELY);
-/
  let lateOverflow : Bool := (!earlyOverflow) && computedOverflow
  let lateUnderflow : Bool := (!earlyUnderflow) && computedUnderflow
/-
  // So that ITE abstraction works...
  prop overflow(!known.noOverflow && ITE(lateOverflow, prop(true), earlyOverflow));
  prop underflow(!known.noUnderflow && ITE(lateUnderflow, prop(true), earlyUnderflow));

-/
  let overflow : Bool := lateOverflow || earlyOverflow
  let underflow : Bool := lateUnderflow || earlyUnderflow

/-
  unpackedFloat<t> roundedResult(uf.getSign(), roundedExponent, roundedSignificand);
  unpackedFloat<t> result(rounderSpecialCases<t>(format, roundingMode, roundedResult,
						 overflow, underflow, uf.getZero()));
-/
  let roundedResult : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
    { sign := inUf.sign,
      ex := roundedExponent,
      sig := roundedSignificand }
  let result : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1)  :=
    rounderSpecialCases mode roundedResult overflow underflow inUf.isZero
  result

def EUnpackedFloat.round {targetExponentWidth targetSignificandWidth : Nat}
    (self : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 3))
    (mode : RoundingMode) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  if self.isNumber then
    UnpackedFloat.round (self.num) mode
  else if self.isInfinite then
    EUnpackedFloat.mkInfinity self.sign
  else if self.isZero then
    EUnpackedFloat.mkZero self.sign
  else -- if self.isNaN then
    EUnpackedFloat.mkNaN

def EUnpackedFloat.normalizeAndRound {targetExponentWidth targetSignificandWidth : Nat}
    (self : EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 3))
    (mode : RoundingMode) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) :=
  self.normalize |>.round mode



-- e = 5
-- s = 3
-- exponentWidth 5 3 = 6

def mkPackedFloats (E : Nat) (S : Nat) : Array (PackedFloat E S) := Id.run do
  let mut res := #[]
  for expVal in [0:Nat.pow 2 E] do
    for sigVal in [0:Nat.pow 2 S] do
      for sign in [true, false] do
        let pf : PackedFloat E S :=
          { sign := sign,
            ex := BitVec.ofNat E expVal,
            sig := BitVec.ofNat S sigVal }
        res := res.push pf
  res

def BitVec.toBitsStr {w : Nat} (bv : BitVec w) : String := Id.run do
  let mut s := "0b"
  for i in [0:w] do
    let bit := if bv.getMsbD i then "1" else "0"
    s := s.append bit
  s

@[bv_normalize]
def BitVec.isZero {w : Nat} (bv : BitVec w) : Bool :=
  bv = BitVec.ofNat w 0

/-- conditionally increment, and return flag of whether overflow was observed -/
@[bv_normalize]
def conditionalIncrementWithFlags (cond : Bool) (x : BitVec w) : BitVec w × Bool :=
  if cond then
    let x' := x.zeroExtend (w + 1) + 1#(w + 1)
    (x'.setWidth w, x'.msb)
  else
    (x, false)

@[bv_normalize]
def UnpackedFloat.roundNormal {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : UnpackedFloat expWidth sigWidth)
  (mode : RoundingMode)
  (hs : sigWidth >= targetSignificandWidth + 3 := AxRoundPreconditions)
  (he : expWidth >= (exponentWidth targetExponentWidth targetSignificandWidth) := AxRoundPreconditions)
  (hs' : sigWidth >= 1 := AxRoundPreconditions) :
  IO (EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1)) := do
  -- round a normalized, normal float.
  println! "--- rounding: {repr inUf} ---"
  println! "val: {inUf.toRat}"
  let exp := inUf.ex
  let sig : BitVec sigWidth := inUf.sig
  println! "sig: {sig.toBitsStr} | ex: {exp.toBitsStr} = {exp.toInt}"
  let sigNoHidden := sig.truncate (sigWidth - 1)
  let targetSigNoHidden : BitVec (targetSignificandWidth) :=
      sigNoHidden.extractMsb' 0 (targetSignificandWidth)
  let guardBit : Bool :=
    targetSigNoHidden.getMsbD (targetSignificandWidth + 1)
  let stickyBits :=
    targetSigNoHidden.extractMsb (targetSignificandWidth + 2) 0
  let sticky := ! stickyBits.isZero

  let isEven := targetSigNoHidden.getLsbD 0 == false
  let shouldRoundUp := roundingDecision
    (mode := mode)
    (sign := inUf.sign)
    (significandEven := isEven)
    (guardBit := guardBit)
    (stickyBit := sticky)
    (exact := false)
  let (roundedTargetSigNoHidden, sigDidOverflow) :=
    conditionalIncrementWithFlags
      (cond := shouldRoundUp)
      (x := targetSigNoHidden)
  let roundedTargetSigWithHidden := roundedTargetSigNoHidden.zeroExtend (targetSignificandWidth + 1)
      ||| (BitVec.leadingOne (targetSignificandWidth + 1))
  -- let targetExp := exp.signExtend targetExponentWidth
  let (roundedExp, expDidOverflow) :=
    conditionalIncrementWithFlags
      (cond := sigDidOverflow)
      (x := exp)

  -- I find this width stuff confusing, which width should we use?
  have : expWidth ≥ exponentWidth targetExponentWidth targetSignificandWidth := by
    grind
  let minExp : BitVec (expWidth) :=
    BitVec.ofInt (expWidth)
      ((subnormalExp targetExponentWidth) - (targetSignificandWidth)) -- TODO: do I need a +1 or sth?
  let maxExp : BitVec (expWidth) :=
    BitVec.ofInt (expWidth)
      (maxNormalExp targetExponentWidth)
  let underflow : Bool :=
    roundedExp.slt minExp
  let overflow : Bool :=
    maxExp.slt roundedExp || expDidOverflow

  if underflow then
    return EUnpackedFloat.mkZero inUf.sign
  else if overflow then
    return EUnpackedFloat.mkInfinity inUf.sign
  else
    return EUnpackedFloat.mkNumber
      { sign := inUf.sign,
        ex := roundedExp.truncate (exponentWidth targetExponentWidth targetSignificandWidth),
        sig := roundedTargetSigWithHidden
      }
  -- relevantSig ++ guardBit ++ stickyBits = original.

  -- grab the significand bits that are relevant.
  -- This is annoying, because I actually don't care about the hidden bit, so making it explicit is just redundant computation?
  -- return UnpackedFloat.round inUf mode



/--
info: --- rounding: { sign := true, ex := 0x32#6, sig := 0x8#4 } ---
val: -1/16384
sig: 0b1000 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0x8#4 } ---
val: 1/16384
sig: 0b1000 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0x9#4 } ---
val: -9/131072
sig: 0b1001 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0x9#4 } ---
val: 9/131072
sig: 0b1001 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0xa#4 } ---
val: -5/65536
sig: 0b1010 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0xa#4 } ---
val: 5/65536
sig: 0b1010 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0xb#4 } ---
val: -11/131072
sig: 0b1011 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0xb#4 } ---
val: 11/131072
sig: 0b1011 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0xc#4 } ---
val: -3/32768
sig: 0b1100 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0xc#4 } ---
val: 3/32768
sig: 0b1100 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0xd#4 } ---
val: -13/131072
sig: 0b1101 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0xd#4 } ---
val: 13/131072
sig: 0b1101 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0xe#4 } ---
val: -7/65536
sig: 0b1110 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0xe#4 } ---
val: 7/65536
sig: 0b1110 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x32#6, sig := 0xf#4 } ---
val: -15/131072
sig: 0b1111 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := false, ex := 0x32#6, sig := 0xf#4 } ---
val: 15/131072
sig: 0b1111 | ex: 0b110010 = -14
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0x8#4 } ---
val: -1/8192
sig: 0b1000 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0x8#4 } ---
val: 1/8192
sig: 0b1000 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0x9#4 } ---
val: -9/65536
sig: 0b1001 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0x9#4 } ---
val: 9/65536
sig: 0b1001 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0xa#4 } ---
val: -5/32768
sig: 0b1010 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0xa#4 } ---
val: 5/32768
sig: 0b1010 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0xb#4 } ---
val: -11/65536
sig: 0b1011 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0xb#4 } ---
val: 11/65536
sig: 0b1011 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0xc#4 } ---
val: -3/16384
sig: 0b1100 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0xc#4 } ---
val: 3/16384
sig: 0b1100 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0xd#4 } ---
val: -13/65536
sig: 0b1101 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0xd#4 } ---
val: 13/65536
sig: 0b1101 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0xe#4 } ---
val: -7/32768
sig: 0b1110 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0xe#4 } ---
val: 7/32768
sig: 0b1110 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x33#6, sig := 0xf#4 } ---
val: -15/65536
sig: 0b1111 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := false, ex := 0x33#6, sig := 0xf#4 } ---
val: 15/65536
sig: 0b1111 | ex: 0b110011 = -13
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0x8#4 } ---
val: -1/4096
sig: 0b1000 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0x8#4 } ---
val: 1/4096
sig: 0b1000 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0x9#4 } ---
val: -9/32768
sig: 0b1001 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0x9#4 } ---
val: 9/32768
sig: 0b1001 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0xa#4 } ---
val: -5/16384
sig: 0b1010 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0xa#4 } ---
val: 5/16384
sig: 0b1010 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0xb#4 } ---
val: -11/32768
sig: 0b1011 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0xb#4 } ---
val: 11/32768
sig: 0b1011 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0xc#4 } ---
val: -3/8192
sig: 0b1100 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0xc#4 } ---
val: 3/8192
sig: 0b1100 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0xd#4 } ---
val: -13/32768
sig: 0b1101 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0xd#4 } ---
val: 13/32768
sig: 0b1101 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0xe#4 } ---
val: -7/16384
sig: 0b1110 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0xe#4 } ---
val: 7/16384
sig: 0b1110 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x34#6, sig := 0xf#4 } ---
val: -15/32768
sig: 0b1111 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := false, ex := 0x34#6, sig := 0xf#4 } ---
val: 15/32768
sig: 0b1111 | ex: 0b110100 = -12
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0x8#4 } ---
val: -1/2048
sig: 0b1000 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0x8#4 } ---
val: 1/2048
sig: 0b1000 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0x9#4 } ---
val: -9/16384
sig: 0b1001 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0x9#4 } ---
val: 9/16384
sig: 0b1001 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0xa#4 } ---
val: -5/8192
sig: 0b1010 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0xa#4 } ---
val: 5/8192
sig: 0b1010 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0xb#4 } ---
val: -11/16384
sig: 0b1011 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0xb#4 } ---
val: 11/16384
sig: 0b1011 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0xc#4 } ---
val: -3/4096
sig: 0b1100 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0xc#4 } ---
val: 3/4096
sig: 0b1100 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0xd#4 } ---
val: -13/16384
sig: 0b1101 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0xd#4 } ---
val: 13/16384
sig: 0b1101 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0xe#4 } ---
val: -7/8192
sig: 0b1110 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0xe#4 } ---
val: 7/8192
sig: 0b1110 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x35#6, sig := 0xf#4 } ---
val: -15/16384
sig: 0b1111 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := false, ex := 0x35#6, sig := 0xf#4 } ---
val: 15/16384
sig: 0b1111 | ex: 0b110101 = -11
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0x8#4 } ---
val: -1/1024
sig: 0b1000 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0x8#4 } ---
val: 1/1024
sig: 0b1000 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0x9#4 } ---
val: -9/8192
sig: 0b1001 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0x9#4 } ---
val: 9/8192
sig: 0b1001 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0xa#4 } ---
val: -5/4096
sig: 0b1010 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0xa#4 } ---
val: 5/4096
sig: 0b1010 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0xb#4 } ---
val: -11/8192
sig: 0b1011 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0xb#4 } ---
val: 11/8192
sig: 0b1011 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0xc#4 } ---
val: -3/2048
sig: 0b1100 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0xc#4 } ---
val: 3/2048
sig: 0b1100 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0xd#4 } ---
val: -13/8192
sig: 0b1101 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0xd#4 } ---
val: 13/8192
sig: 0b1101 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0xe#4 } ---
val: -7/4096
sig: 0b1110 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0xe#4 } ---
val: 7/4096
sig: 0b1110 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x36#6, sig := 0xf#4 } ---
val: -15/8192
sig: 0b1111 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := false, ex := 0x36#6, sig := 0xf#4 } ---
val: 15/8192
sig: 0b1111 | ex: 0b110110 = -10
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0x8#4 } ---
val: -1/512
sig: 0b1000 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0x8#4 } ---
val: 1/512
sig: 0b1000 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0x9#4 } ---
val: -9/4096
sig: 0b1001 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0x9#4 } ---
val: 9/4096
sig: 0b1001 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0xa#4 } ---
val: -5/2048
sig: 0b1010 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0xa#4 } ---
val: 5/2048
sig: 0b1010 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0xb#4 } ---
val: -11/4096
sig: 0b1011 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0xb#4 } ---
val: 11/4096
sig: 0b1011 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0xc#4 } ---
val: -3/1024
sig: 0b1100 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0xc#4 } ---
val: 3/1024
sig: 0b1100 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0xd#4 } ---
val: -13/4096
sig: 0b1101 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0xd#4 } ---
val: 13/4096
sig: 0b1101 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0xe#4 } ---
val: -7/2048
sig: 0b1110 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0xe#4 } ---
val: 7/2048
sig: 0b1110 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x37#6, sig := 0xf#4 } ---
val: -15/4096
sig: 0b1111 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := false, ex := 0x37#6, sig := 0xf#4 } ---
val: 15/4096
sig: 0b1111 | ex: 0b110111 = -9
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0x8#4 } ---
val: -1/256
sig: 0b1000 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0x8#4 } ---
val: 1/256
sig: 0b1000 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0x9#4 } ---
val: -9/2048
sig: 0b1001 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0x9#4 } ---
val: 9/2048
sig: 0b1001 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0xa#4 } ---
val: -5/1024
sig: 0b1010 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0xa#4 } ---
val: 5/1024
sig: 0b1010 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0xb#4 } ---
val: -11/2048
sig: 0b1011 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0xb#4 } ---
val: 11/2048
sig: 0b1011 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0xc#4 } ---
val: -3/512
sig: 0b1100 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0xc#4 } ---
val: 3/512
sig: 0b1100 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0xd#4 } ---
val: -13/2048
sig: 0b1101 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0xd#4 } ---
val: 13/2048
sig: 0b1101 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0xe#4 } ---
val: -7/1024
sig: 0b1110 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0xe#4 } ---
val: 7/1024
sig: 0b1110 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x38#6, sig := 0xf#4 } ---
val: -15/2048
sig: 0b1111 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := false, ex := 0x38#6, sig := 0xf#4 } ---
val: 15/2048
sig: 0b1111 | ex: 0b111000 = -8
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0x8#4 } ---
val: -1/128
sig: 0b1000 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0x8#4 } ---
val: 1/128
sig: 0b1000 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0x9#4 } ---
val: -9/1024
sig: 0b1001 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0x9#4 } ---
val: 9/1024
sig: 0b1001 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0xa#4 } ---
val: -5/512
sig: 0b1010 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0xa#4 } ---
val: 5/512
sig: 0b1010 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0xb#4 } ---
val: -11/1024
sig: 0b1011 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0xb#4 } ---
val: 11/1024
sig: 0b1011 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0xc#4 } ---
val: -3/256
sig: 0b1100 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0xc#4 } ---
val: 3/256
sig: 0b1100 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0xd#4 } ---
val: -13/1024
sig: 0b1101 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0xd#4 } ---
val: 13/1024
sig: 0b1101 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0xe#4 } ---
val: -7/512
sig: 0b1110 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0xe#4 } ---
val: 7/512
sig: 0b1110 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x39#6, sig := 0xf#4 } ---
val: -15/1024
sig: 0b1111 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := false, ex := 0x39#6, sig := 0xf#4 } ---
val: 15/1024
sig: 0b1111 | ex: 0b111001 = -7
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0x8#4 } ---
val: -1/64
sig: 0b1000 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0x8#4 } ---
val: 1/64
sig: 0b1000 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0x9#4 } ---
val: -9/512
sig: 0b1001 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0x9#4 } ---
val: 9/512
sig: 0b1001 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0xa#4 } ---
val: -5/256
sig: 0b1010 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0xa#4 } ---
val: 5/256
sig: 0b1010 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0xb#4 } ---
val: -11/512
sig: 0b1011 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0xb#4 } ---
val: 11/512
sig: 0b1011 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0xc#4 } ---
val: -3/128
sig: 0b1100 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0xc#4 } ---
val: 3/128
sig: 0b1100 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0xd#4 } ---
val: -13/512
sig: 0b1101 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0xd#4 } ---
val: 13/512
sig: 0b1101 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0xe#4 } ---
val: -7/256
sig: 0b1110 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0xe#4 } ---
val: 7/256
sig: 0b1110 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3a#6, sig := 0xf#4 } ---
val: -15/512
sig: 0b1111 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := false, ex := 0x3a#6, sig := 0xf#4 } ---
val: 15/512
sig: 0b1111 | ex: 0b111010 = -6
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0x8#4 } ---
val: -1/32
sig: 0b1000 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0x8#4 } ---
val: 1/32
sig: 0b1000 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0x9#4 } ---
val: -9/256
sig: 0b1001 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0x9#4 } ---
val: 9/256
sig: 0b1001 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0xa#4 } ---
val: -5/128
sig: 0b1010 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0xa#4 } ---
val: 5/128
sig: 0b1010 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0xb#4 } ---
val: -11/256
sig: 0b1011 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0xb#4 } ---
val: 11/256
sig: 0b1011 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0xc#4 } ---
val: -3/64
sig: 0b1100 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0xc#4 } ---
val: 3/64
sig: 0b1100 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0xd#4 } ---
val: -13/256
sig: 0b1101 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0xd#4 } ---
val: 13/256
sig: 0b1101 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0xe#4 } ---
val: -7/128
sig: 0b1110 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0xe#4 } ---
val: 7/128
sig: 0b1110 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3b#6, sig := 0xf#4 } ---
val: -15/256
sig: 0b1111 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := false, ex := 0x3b#6, sig := 0xf#4 } ---
val: 15/256
sig: 0b1111 | ex: 0b111011 = -5
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0x8#4 } ---
val: -1/16
sig: 0b1000 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0x8#4 } ---
val: 1/16
sig: 0b1000 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0x9#4 } ---
val: -9/128
sig: 0b1001 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0x9#4 } ---
val: 9/128
sig: 0b1001 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0xa#4 } ---
val: -5/64
sig: 0b1010 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0xa#4 } ---
val: 5/64
sig: 0b1010 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0xb#4 } ---
val: -11/128
sig: 0b1011 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0xb#4 } ---
val: 11/128
sig: 0b1011 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0xc#4 } ---
val: -3/32
sig: 0b1100 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0xc#4 } ---
val: 3/32
sig: 0b1100 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0xd#4 } ---
val: -13/128
sig: 0b1101 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0xd#4 } ---
val: 13/128
sig: 0b1101 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0xe#4 } ---
val: -7/64
sig: 0b1110 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0xe#4 } ---
val: 7/64
sig: 0b1110 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3c#6, sig := 0xf#4 } ---
val: -15/128
sig: 0b1111 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := false, ex := 0x3c#6, sig := 0xf#4 } ---
val: 15/128
sig: 0b1111 | ex: 0b111100 = -4
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0x8#4 } ---
val: -1/8
sig: 0b1000 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0x8#4 } ---
val: 1/8
sig: 0b1000 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0x9#4 } ---
val: -9/64
sig: 0b1001 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0x9#4 } ---
val: 9/64
sig: 0b1001 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0xa#4 } ---
val: -5/32
sig: 0b1010 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0xa#4 } ---
val: 5/32
sig: 0b1010 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0xb#4 } ---
val: -11/64
sig: 0b1011 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0xb#4 } ---
val: 11/64
sig: 0b1011 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0xc#4 } ---
val: -3/16
sig: 0b1100 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0xc#4 } ---
val: 3/16
sig: 0b1100 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0xd#4 } ---
val: -13/64
sig: 0b1101 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0xd#4 } ---
val: 13/64
sig: 0b1101 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0xe#4 } ---
val: -7/32
sig: 0b1110 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0xe#4 } ---
val: 7/32
sig: 0b1110 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3d#6, sig := 0xf#4 } ---
val: -15/64
sig: 0b1111 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := false, ex := 0x3d#6, sig := 0xf#4 } ---
val: 15/64
sig: 0b1111 | ex: 0b111101 = -3
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0x8#4 } ---
val: -1/4
sig: 0b1000 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0x8#4 } ---
val: 1/4
sig: 0b1000 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0x9#4 } ---
val: -9/32
sig: 0b1001 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0x9#4 } ---
val: 9/32
sig: 0b1001 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0xa#4 } ---
val: -5/16
sig: 0b1010 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0xa#4 } ---
val: 5/16
sig: 0b1010 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0xb#4 } ---
val: -11/32
sig: 0b1011 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0xb#4 } ---
val: 11/32
sig: 0b1011 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0xc#4 } ---
val: -3/8
sig: 0b1100 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0xc#4 } ---
val: 3/8
sig: 0b1100 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0xd#4 } ---
val: -13/32
sig: 0b1101 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0xd#4 } ---
val: 13/32
sig: 0b1101 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0xe#4 } ---
val: -7/16
sig: 0b1110 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0xe#4 } ---
val: 7/16
sig: 0b1110 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3e#6, sig := 0xf#4 } ---
val: -15/32
sig: 0b1111 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := false, ex := 0x3e#6, sig := 0xf#4 } ---
val: 15/32
sig: 0b1111 | ex: 0b111110 = -2
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0x8#4 } ---
val: -1/2
sig: 0b1000 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0x8#4 } ---
val: 1/2
sig: 0b1000 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0x9#4 } ---
val: -9/16
sig: 0b1001 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0x9#4 } ---
val: 9/16
sig: 0b1001 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0xa#4 } ---
val: -5/8
sig: 0b1010 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0xa#4 } ---
val: 5/8
sig: 0b1010 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0xb#4 } ---
val: -11/16
sig: 0b1011 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0xb#4 } ---
val: 11/16
sig: 0b1011 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0xc#4 } ---
val: -3/4
sig: 0b1100 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0xc#4 } ---
val: 3/4
sig: 0b1100 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0xd#4 } ---
val: -13/16
sig: 0b1101 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0xd#4 } ---
val: 13/16
sig: 0b1101 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0xe#4 } ---
val: -7/8
sig: 0b1110 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0xe#4 } ---
val: 7/8
sig: 0b1110 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x3f#6, sig := 0xf#4 } ---
val: -15/16
sig: 0b1111 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := false, ex := 0x3f#6, sig := 0xf#4 } ---
val: 15/16
sig: 0b1111 | ex: 0b111111 = -1
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0x8#4 } ---
val: -1
sig: 0b1000 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0x8#4 } ---
val: 1
sig: 0b1000 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0x9#4 } ---
val: -9/8
sig: 0b1001 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0x9#4 } ---
val: 9/8
sig: 0b1001 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0xa#4 } ---
val: -5/4
sig: 0b1010 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0xa#4 } ---
val: 5/4
sig: 0b1010 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0xb#4 } ---
val: -11/8
sig: 0b1011 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0xb#4 } ---
val: 11/8
sig: 0b1011 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0xc#4 } ---
val: -3/2
sig: 0b1100 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0xc#4 } ---
val: 3/2
sig: 0b1100 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0xd#4 } ---
val: -13/8
sig: 0b1101 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0xd#4 } ---
val: 13/8
sig: 0b1101 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0xe#4 } ---
val: -7/4
sig: 0b1110 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0xe#4 } ---
val: 7/4
sig: 0b1110 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x00#6, sig := 0xf#4 } ---
val: -15/8
sig: 0b1111 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := false, ex := 0x00#6, sig := 0xf#4 } ---
val: 15/8
sig: 0b1111 | ex: 0b000000 = 0
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0x8#4 } ---
val: -2
sig: 0b1000 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0x8#4 } ---
val: 2
sig: 0b1000 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0x9#4 } ---
val: -9/4
sig: 0b1001 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0x9#4 } ---
val: 9/4
sig: 0b1001 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0xa#4 } ---
val: -5/2
sig: 0b1010 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0xa#4 } ---
val: 5/2
sig: 0b1010 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0xb#4 } ---
val: -11/4
sig: 0b1011 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0xb#4 } ---
val: 11/4
sig: 0b1011 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0xc#4 } ---
val: -3
sig: 0b1100 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0xc#4 } ---
val: 3
sig: 0b1100 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0xd#4 } ---
val: -13/4
sig: 0b1101 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0xd#4 } ---
val: 13/4
sig: 0b1101 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0xe#4 } ---
val: -7/2
sig: 0b1110 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0xe#4 } ---
val: 7/2
sig: 0b1110 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x01#6, sig := 0xf#4 } ---
val: -15/4
sig: 0b1111 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := false, ex := 0x01#6, sig := 0xf#4 } ---
val: 15/4
sig: 0b1111 | ex: 0b000001 = 1
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0x8#4 } ---
val: -4
sig: 0b1000 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0x8#4 } ---
val: 4
sig: 0b1000 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0x9#4 } ---
val: -9/2
sig: 0b1001 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0x9#4 } ---
val: 9/2
sig: 0b1001 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0xa#4 } ---
val: -5
sig: 0b1010 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0xa#4 } ---
val: 5
sig: 0b1010 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0xb#4 } ---
val: -11/2
sig: 0b1011 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0xb#4 } ---
val: 11/2
sig: 0b1011 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0xc#4 } ---
val: -6
sig: 0b1100 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0xc#4 } ---
val: 6
sig: 0b1100 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0xd#4 } ---
val: -13/2
sig: 0b1101 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0xd#4 } ---
val: 13/2
sig: 0b1101 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0xe#4 } ---
val: -7
sig: 0b1110 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0xe#4 } ---
val: 7
sig: 0b1110 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x02#6, sig := 0xf#4 } ---
val: -15/2
sig: 0b1111 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := false, ex := 0x02#6, sig := 0xf#4 } ---
val: 15/2
sig: 0b1111 | ex: 0b000010 = 2
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0x8#4 } ---
val: -8
sig: 0b1000 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0x8#4 } ---
val: 8
sig: 0b1000 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0x9#4 } ---
val: -9
sig: 0b1001 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0x9#4 } ---
val: 9
sig: 0b1001 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0xa#4 } ---
val: -10
sig: 0b1010 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0xa#4 } ---
val: 10
sig: 0b1010 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0xb#4 } ---
val: -11
sig: 0b1011 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0xb#4 } ---
val: 11
sig: 0b1011 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0xc#4 } ---
val: -12
sig: 0b1100 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0xc#4 } ---
val: 12
sig: 0b1100 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0xd#4 } ---
val: -13
sig: 0b1101 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0xd#4 } ---
val: 13
sig: 0b1101 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0xe#4 } ---
val: -14
sig: 0b1110 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0xe#4 } ---
val: 14
sig: 0b1110 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x03#6, sig := 0xf#4 } ---
val: -15
sig: 0b1111 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := false, ex := 0x03#6, sig := 0xf#4 } ---
val: 15
sig: 0b1111 | ex: 0b000011 = 3
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0x8#4 } ---
val: -16
sig: 0b1000 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0x8#4 } ---
val: 16
sig: 0b1000 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0x9#4 } ---
val: -18
sig: 0b1001 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0x9#4 } ---
val: 18
sig: 0b1001 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0xa#4 } ---
val: -20
sig: 0b1010 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0xa#4 } ---
val: 20
sig: 0b1010 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0xb#4 } ---
val: -22
sig: 0b1011 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0xb#4 } ---
val: 22
sig: 0b1011 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0xc#4 } ---
val: -24
sig: 0b1100 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0xc#4 } ---
val: 24
sig: 0b1100 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0xd#4 } ---
val: -26
sig: 0b1101 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0xd#4 } ---
val: 26
sig: 0b1101 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0xe#4 } ---
val: -28
sig: 0b1110 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0xe#4 } ---
val: 28
sig: 0b1110 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x04#6, sig := 0xf#4 } ---
val: -30
sig: 0b1111 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := false, ex := 0x04#6, sig := 0xf#4 } ---
val: 30
sig: 0b1111 | ex: 0b000100 = 4
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0x8#4 } ---
val: -32
sig: 0b1000 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0x8#4 } ---
val: 32
sig: 0b1000 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0x9#4 } ---
val: -36
sig: 0b1001 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0x9#4 } ---
val: 36
sig: 0b1001 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0xa#4 } ---
val: -40
sig: 0b1010 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0xa#4 } ---
val: 40
sig: 0b1010 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0xb#4 } ---
val: -44
sig: 0b1011 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0xb#4 } ---
val: 44
sig: 0b1011 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0xc#4 } ---
val: -48
sig: 0b1100 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0xc#4 } ---
val: 48
sig: 0b1100 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0xd#4 } ---
val: -52
sig: 0b1101 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0xd#4 } ---
val: 52
sig: 0b1101 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0xe#4 } ---
val: -56
sig: 0b1110 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0xe#4 } ---
val: 56
sig: 0b1110 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x05#6, sig := 0xf#4 } ---
val: -60
sig: 0b1111 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := false, ex := 0x05#6, sig := 0xf#4 } ---
val: 60
sig: 0b1111 | ex: 0b000101 = 5
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0x8#4 } ---
val: -64
sig: 0b1000 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0x8#4 } ---
val: 64
sig: 0b1000 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0x9#4 } ---
val: -72
sig: 0b1001 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0x9#4 } ---
val: 72
sig: 0b1001 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0xa#4 } ---
val: -80
sig: 0b1010 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0xa#4 } ---
val: 80
sig: 0b1010 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0xb#4 } ---
val: -88
sig: 0b1011 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0xb#4 } ---
val: 88
sig: 0b1011 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0xc#4 } ---
val: -96
sig: 0b1100 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0xc#4 } ---
val: 96
sig: 0b1100 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0xd#4 } ---
val: -104
sig: 0b1101 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0xd#4 } ---
val: 104
sig: 0b1101 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0xe#4 } ---
val: -112
sig: 0b1110 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0xe#4 } ---
val: 112
sig: 0b1110 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x06#6, sig := 0xf#4 } ---
val: -120
sig: 0b1111 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := false, ex := 0x06#6, sig := 0xf#4 } ---
val: 120
sig: 0b1111 | ex: 0b000110 = 6
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0x8#4 } ---
val: -128
sig: 0b1000 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0x8#4 } ---
val: 128
sig: 0b1000 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0x9#4 } ---
val: -144
sig: 0b1001 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0x9#4 } ---
val: 144
sig: 0b1001 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0xa#4 } ---
val: -160
sig: 0b1010 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0xa#4 } ---
val: 160
sig: 0b1010 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0xb#4 } ---
val: -176
sig: 0b1011 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0xb#4 } ---
val: 176
sig: 0b1011 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0xc#4 } ---
val: -192
sig: 0b1100 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0xc#4 } ---
val: 192
sig: 0b1100 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0xd#4 } ---
val: -208
sig: 0b1101 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0xd#4 } ---
val: 208
sig: 0b1101 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0xe#4 } ---
val: -224
sig: 0b1110 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0xe#4 } ---
val: 224
sig: 0b1110 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x07#6, sig := 0xf#4 } ---
val: -240
sig: 0b1111 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := false, ex := 0x07#6, sig := 0xf#4 } ---
val: 240
sig: 0b1111 | ex: 0b000111 = 7
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0x8#4 } ---
val: -256
sig: 0b1000 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0x8#4 } ---
val: 256
sig: 0b1000 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0x9#4 } ---
val: -288
sig: 0b1001 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0x9#4 } ---
val: 288
sig: 0b1001 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0xa#4 } ---
val: -320
sig: 0b1010 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0xa#4 } ---
val: 320
sig: 0b1010 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0xb#4 } ---
val: -352
sig: 0b1011 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0xb#4 } ---
val: 352
sig: 0b1011 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0xc#4 } ---
val: -384
sig: 0b1100 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0xc#4 } ---
val: 384
sig: 0b1100 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0xd#4 } ---
val: -416
sig: 0b1101 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0xd#4 } ---
val: 416
sig: 0b1101 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0xe#4 } ---
val: -448
sig: 0b1110 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0xe#4 } ---
val: 448
sig: 0b1110 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x08#6, sig := 0xf#4 } ---
val: -480
sig: 0b1111 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := false, ex := 0x08#6, sig := 0xf#4 } ---
val: 480
sig: 0b1111 | ex: 0b001000 = 8
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0x8#4 } ---
val: -512
sig: 0b1000 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0x8#4 } ---
val: 512
sig: 0b1000 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0x9#4 } ---
val: -576
sig: 0b1001 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0x9#4 } ---
val: 576
sig: 0b1001 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0xa#4 } ---
val: -640
sig: 0b1010 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0xa#4 } ---
val: 640
sig: 0b1010 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0xb#4 } ---
val: -704
sig: 0b1011 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0xb#4 } ---
val: 704
sig: 0b1011 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0xc#4 } ---
val: -768
sig: 0b1100 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0xc#4 } ---
val: 768
sig: 0b1100 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0xd#4 } ---
val: -832
sig: 0b1101 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0xd#4 } ---
val: 832
sig: 0b1101 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0xe#4 } ---
val: -896
sig: 0b1110 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0xe#4 } ---
val: 896
sig: 0b1110 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x09#6, sig := 0xf#4 } ---
val: -960
sig: 0b1111 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := false, ex := 0x09#6, sig := 0xf#4 } ---
val: 960
sig: 0b1111 | ex: 0b001001 = 9
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0x8#4 } ---
val: -1024
sig: 0b1000 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0x8#4 } ---
val: 1024
sig: 0b1000 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0x9#4 } ---
val: -1152
sig: 0b1001 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0x9#4 } ---
val: 1152
sig: 0b1001 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0xa#4 } ---
val: -1280
sig: 0b1010 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0xa#4 } ---
val: 1280
sig: 0b1010 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0xb#4 } ---
val: -1408
sig: 0b1011 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0xb#4 } ---
val: 1408
sig: 0b1011 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0xc#4 } ---
val: -1536
sig: 0b1100 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0xc#4 } ---
val: 1536
sig: 0b1100 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0xd#4 } ---
val: -1664
sig: 0b1101 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0xd#4 } ---
val: 1664
sig: 0b1101 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0xe#4 } ---
val: -1792
sig: 0b1110 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0xe#4 } ---
val: 1792
sig: 0b1110 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0a#6, sig := 0xf#4 } ---
val: -1920
sig: 0b1111 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := false, ex := 0x0a#6, sig := 0xf#4 } ---
val: 1920
sig: 0b1111 | ex: 0b001010 = 10
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0x8#4 } ---
val: -2048
sig: 0b1000 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0x8#4 } ---
val: 2048
sig: 0b1000 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0x9#4 } ---
val: -2304
sig: 0b1001 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0x9#4 } ---
val: 2304
sig: 0b1001 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0xa#4 } ---
val: -2560
sig: 0b1010 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0xa#4 } ---
val: 2560
sig: 0b1010 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0xb#4 } ---
val: -2816
sig: 0b1011 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0xb#4 } ---
val: 2816
sig: 0b1011 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0xc#4 } ---
val: -3072
sig: 0b1100 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0xc#4 } ---
val: 3072
sig: 0b1100 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0xd#4 } ---
val: -3328
sig: 0b1101 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0xd#4 } ---
val: 3328
sig: 0b1101 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0xe#4 } ---
val: -3584
sig: 0b1110 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0xe#4 } ---
val: 3584
sig: 0b1110 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0b#6, sig := 0xf#4 } ---
val: -3840
sig: 0b1111 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := false, ex := 0x0b#6, sig := 0xf#4 } ---
val: 3840
sig: 0b1111 | ex: 0b001011 = 11
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0x8#4 } ---
val: -4096
sig: 0b1000 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0x8#4 } ---
val: 4096
sig: 0b1000 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0x9#4 } ---
val: -4608
sig: 0b1001 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0x9#4 } ---
val: 4608
sig: 0b1001 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0xa#4 } ---
val: -5120
sig: 0b1010 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0xa#4 } ---
val: 5120
sig: 0b1010 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0xb#4 } ---
val: -5632
sig: 0b1011 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0xb#4 } ---
val: 5632
sig: 0b1011 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0xc#4 } ---
val: -6144
sig: 0b1100 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0xc#4 } ---
val: 6144
sig: 0b1100 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0xd#4 } ---
val: -6656
sig: 0b1101 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0xd#4 } ---
val: 6656
sig: 0b1101 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0xe#4 } ---
val: -7168
sig: 0b1110 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0xe#4 } ---
val: 7168
sig: 0b1110 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0c#6, sig := 0xf#4 } ---
val: -7680
sig: 0b1111 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := false, ex := 0x0c#6, sig := 0xf#4 } ---
val: 7680
sig: 0b1111 | ex: 0b001100 = 12
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0x8#4 } ---
val: -8192
sig: 0b1000 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0x8#4 } ---
val: 8192
sig: 0b1000 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0x9#4 } ---
val: -9216
sig: 0b1001 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0x9#4 } ---
val: 9216
sig: 0b1001 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0xa#4 } ---
val: -10240
sig: 0b1010 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0xa#4 } ---
val: 10240
sig: 0b1010 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0xb#4 } ---
val: -11264
sig: 0b1011 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0xb#4 } ---
val: 11264
sig: 0b1011 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0xc#4 } ---
val: -12288
sig: 0b1100 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0xc#4 } ---
val: 12288
sig: 0b1100 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0xd#4 } ---
val: -13312
sig: 0b1101 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0xd#4 } ---
val: 13312
sig: 0b1101 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0xe#4 } ---
val: -14336
sig: 0b1110 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0xe#4 } ---
val: 14336
sig: 0b1110 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0d#6, sig := 0xf#4 } ---
val: -15360
sig: 0b1111 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := false, ex := 0x0d#6, sig := 0xf#4 } ---
val: 15360
sig: 0b1111 | ex: 0b001101 = 13
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0x8#4 } ---
val: -16384
sig: 0b1000 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0x8#4 } ---
val: 16384
sig: 0b1000 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0x9#4 } ---
val: -18432
sig: 0b1001 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0x9#4 } ---
val: 18432
sig: 0b1001 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0xa#4 } ---
val: -20480
sig: 0b1010 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0xa#4 } ---
val: 20480
sig: 0b1010 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0xb#4 } ---
val: -22528
sig: 0b1011 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0xb#4 } ---
val: 22528
sig: 0b1011 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0xc#4 } ---
val: -24576
sig: 0b1100 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0xc#4 } ---
val: 24576
sig: 0b1100 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0xd#4 } ---
val: -26624
sig: 0b1101 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0xd#4 } ---
val: 26624
sig: 0b1101 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0xe#4 } ---
val: -28672
sig: 0b1110 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0xe#4 } ---
val: 28672
sig: 0b1110 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0e#6, sig := 0xf#4 } ---
val: -30720
sig: 0b1111 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := false, ex := 0x0e#6, sig := 0xf#4 } ---
val: 30720
sig: 0b1111 | ex: 0b001110 = 14
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0x8#4 } ---
val: -32768
sig: 0b1000 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0x8#4 } ---
val: 32768
sig: 0b1000 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0x9#4 } ---
val: -36864
sig: 0b1001 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0x9#4 } ---
val: 36864
sig: 0b1001 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0xa#4 } ---
val: -40960
sig: 0b1010 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0xa#4 } ---
val: 40960
sig: 0b1010 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0xb#4 } ---
val: -45056
sig: 0b1011 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0xb#4 } ---
val: 45056
sig: 0b1011 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0xc#4 } ---
val: -49152
sig: 0b1100 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0xc#4 } ---
val: 49152
sig: 0b1100 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0xd#4 } ---
val: -53248
sig: 0b1101 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0xd#4 } ---
val: 53248
sig: 0b1101 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0xe#4 } ---
val: -57344
sig: 0b1110 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0xe#4 } ---
val: 57344
sig: 0b1110 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := true, ex := 0x0f#6, sig := 0xf#4 } ---
val: -61440
sig: 0b1111 | ex: 0b001111 = 15
Succeeded ✅
--- rounding: { sign := false, ex := 0x0f#6, sig := 0xf#4 } ---
val: 61440
sig: 0b1111 | ex: 0b001111 = 15
Succeeded ✅
done.
-/
#guard_msgs in #eval show IO Unit from do
  for originalPacked in mkPackedFloats 5 3 do
    if ! originalPacked.isNorm then continue -- we only need to think about the normal case for now.
    let originalEUnpacked := originalPacked.unpack
    -- if ! originalEUnpacked.isNumber then continue
    let originalUnpacked := originalEUnpacked.num
    let originalUnpackedNormalized := originalUnpacked.normalize
    let outputUnpacked ← UnpackedFloat.roundNormal (targetExponentWidth := 5) (targetSignificandWidth := 3) originalUnpackedNormalized RoundingMode.RNE
    let outputPacked := outputUnpacked.pack
    if ! originalPacked.equal_denotation outputPacked then
      IO.println s!"Failed ❌ | original {repr originalPacked.toRat?} → output {repr outputPacked.unpack} | {repr outputPacked.toRat?}"
      break
    else
      IO.println "Succeeded ✅"
    -- else
    --   IO.println s!"Succeeded ✅ | original {repr originalPacked.toRat?} → output {repr outputPacked.toRat?}"

  IO.println "done."


-- Test that 'normalize' works correctly.
/-- info: done. -/
#guard_msgs in #eval show IO Unit from do
  for originalPacked in mkPackedFloats 5 3 do
    if ! originalPacked.isNorm then continue -- we only need to think about the normal case for now.
    let originalEUnpacked := originalPacked.unpack
    -- if ! originalEUnpacked.isNumber then continue
    let originalUnpacked := originalEUnpacked.num
    let originalUnpackedNormalized := originalUnpacked.normalize

    let outputUnpacked := EUnpackedFloat.mkNumber originalUnpackedNormalized
    -- let outputUnpacked := UnpackedFloat.round (targetExponentWidth := 5) (targetSignificandWidth := 3) originalEUnpacked.num RoundingMode.RNE
    let outputPacked := outputUnpacked.pack
    if ! originalPacked.equal_denotation outputPacked then
      IO.println s!"Failed ❌ | original {repr originalPacked.toRat?} → output {repr outputPacked.toRat?}"
    -- else
    --   IO.println s!"Succeeded ✅ | original {repr originalPacked.toRat?} → output {repr outputPacked.toRat?}"

  IO.println "done."


theorem round_idem' (uf : UnpackedFloat 6 4)
    (huf : (EUnpackedFloat.pack (e := 5) (s := 3) (EUnpackedFloat.mkNumber uf)).isNorm) :
    (UnpackedFloat.round (targetExponentWidth := 5) (targetSignificandWidth := 3) uf RoundingMode.RNE) = EUnpackedFloat.mkNumber uf := by
  bv_normalize
  -- simp_all
  -- bv_decide
  sorry

theorem round_idem (uf : UnpackedFloat (exponentWidth e s) (s + 1))
    (huf : (EUnpackedFloat.pack (e := e) (s := s) (EUnpackedFloat.mkNumber uf)).isNorm) :
    UnpackedFloat.round  uf RoundingMode.RNE == EUnpackedFloat.mkNumber uf := by
  have he : e = 5 := by sorry
  have hs : s = 3 := by sorry
  subst e s
  revert huf
  simp at uf
  -- bv_normalize
  -- bv_decide
  sorry

theorem foo (x y : BitVec 5) (b : Bool) :
  let z := if b then x else y
  let w := if ! b then y else x
  z = w := by bv_decide

theorem xx (uf : UnpackedFloat (exponentWidth 5 3) (3 + 1)) :
    EUnpackedFloat.mkNumber uf = EUnpackedFloat.mkNumber uf := by
  -- bv_decide
  sorry
