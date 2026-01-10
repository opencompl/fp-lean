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

/--
Return all representable packed floats of given exponent and significand widths,
in ascending order by their rational value.
-/
def mkPackedFloatNumsSorted (E : Nat) (S : Nat) :
    Array (PackedFloat E S × Rat) := Id.run do
  let pfs ← mkPackedFloats E S
  let mut res := #[]
  for pf in pfs do
    if let .some r := pf.toRat? then
      res := res.push (pf, r)
  res.qsort (fun a b => a.2 < b.2)

/-
Implementation of RNE rounding by finding the closest representable float, exhaustively.
-/
def getClosestRNEResult {expWidth sigWidth : Nat}
    (targetExponentWidth targetSignificandWidth : Nat)
    (inUf : UnpackedFloat expWidth sigWidth) :
    -- (mode : RoundingMode) :
    EUnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1) := Id.run do
  let inRat := inUf.toRat
  let candidates := mkPackedFloatNumsSorted targetExponentWidth targetSignificandWidth
  if inRat < (candidates.getD 0 default).2 then
    EUnpackedFloat.mkInfinity true
  else if inRat > (candidates.getD (candidates.size - 1) default).2 then
    EUnpackedFloat.mkInfinity false
  else
    let candidatesWithDist := candidates.map (fun (pf, r) =>
      (pf, r, (inRat - r).abs))
    let candidatesSorted := candidatesWithDist.qsort (fun a b => a.2.2 < b.2.2)
    let out1 := candidatesSorted.getD 0 default
    let out2 := candidatesSorted.getD 1 default
    let (pf1, r1, dist1) := out1
    let (pf2, _r2, dist2) := out2
    if dist1 < dist2 then
      pf1.unpack
    else if dist2 < dist1 then
      pf2.unpack
    else
      -- round to the nearest even number
      if r1.num % 2 == 0 then
        pf1.unpack
      else
        pf2.unpack
      -- round to nearest even.

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

def checkRoundIdem (E S : Nat): IO Bool := do
  -- let E := 5
  -- let S := 3
  let mut success : Bool := true
  for originalPacked in mkPackedFloats E S do
    if ! originalPacked.isNorm then continue -- we only need to think about the normal case for now.
    let originalEUnpacked := originalPacked.unpack
    -- if ! originalEUnpacked.isNumber then continue
    let originalUnpacked := originalEUnpacked.num
    let originalUnpackedNormalized := originalUnpacked.normalize
    let outputUnpacked ← UnpackedFloat.roundNormal
        (targetExponentWidth := E) (targetSignificandWidth := S)
        originalUnpackedNormalized RoundingMode.RNE
    let outputPacked : PackedFloat E S := outputUnpacked.pack
    if ! originalPacked.equal_denotation outputPacked then
      IO.println s!"Failed ❌ | original {repr originalPacked.toRat?} → output {repr outputPacked.unpack} | {repr outputPacked.toRat?}"
      success:= false
  if success then
    IO.println "All succeeded ✅"
  else
    IO.println "Some failures ❌"
  return success

#guard_msgs(error) in #eval checkRoundIdem 5 3

def checkNormalizeIdem : IO Bool := do
  let mut allSucceeded := true
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
      allSucceeded := false
    -- else
    --   IO.println s!"Succeeded ✅ | original {repr originalPacked.toRat?} → output {repr outputPacked.toRat?}"
  if allSucceeded then
    IO.println "All succeeded ✅"
  else
    IO.println "Some failed ❌"
  return allSucceeded

/--
info: All succeeded ✅
---
info: true
-/
#guard_msgs in #eval checkNormalizeIdem

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
