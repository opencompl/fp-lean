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
def EUnpackedFloat.round {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
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

-- e = 5
-- s = 3
-- exponentWidth 5 3 = 6

/--
info: Failed ❌ on exp=0, sig=1: got some 0, expected some (1 : Rat)/8
Failed ❌ on exp=0, sig=2: got some 0, expected some (1 : Rat)/4
Failed ❌ on exp=0, sig=3: got some 0, expected some (3 : Rat)/8
Failed ❌ on exp=0, sig=4: got some 0, expected some (1 : Rat)/2
Failed ❌ on exp=0, sig=5: got some 0, expected some (5 : Rat)/8
Failed ❌ on exp=0, sig=6: got some 0, expected some (3 : Rat)/4
Failed ❌ on exp=0, sig=7: got some 0, expected some (7 : Rat)/8
Failed ❌ on exp=0, sig=8: got some 0, expected some 1
Failed ❌ on exp=0, sig=9: got some 0, expected some (9 : Rat)/8
Failed ❌ on exp=0, sig=10: got some 0, expected some (5 : Rat)/4
Failed ❌ on exp=0, sig=11: got some 0, expected some (11 : Rat)/8
Failed ❌ on exp=0, sig=12: got some 0, expected some (3 : Rat)/2
Failed ❌ on exp=0, sig=13: got some 0, expected some (13 : Rat)/8
Failed ❌ on exp=0, sig=14: got some 0, expected some (7 : Rat)/4
Failed ❌ on exp=0, sig=15: got some 0, expected some (15 : Rat)/8
Failed ❌ on exp=1, sig=0: got some 0, expected some 0
Failed ❌ on exp=1, sig=1: got some 0, expected some (1 : Rat)/4
Failed ❌ on exp=1, sig=2: got some 0, expected some (1 : Rat)/2
Failed ❌ on exp=1, sig=3: got some 0, expected some (3 : Rat)/4
Failed ❌ on exp=1, sig=4: got some 0, expected some 1
Failed ❌ on exp=1, sig=5: got some 0, expected some (5 : Rat)/4
Failed ❌ on exp=1, sig=6: got some 0, expected some (3 : Rat)/2
Failed ❌ on exp=1, sig=7: got some 0, expected some (7 : Rat)/4
Failed ❌ on exp=1, sig=8: got some 0, expected some 2
Failed ❌ on exp=1, sig=9: got some 0, expected some (9 : Rat)/4
Failed ❌ on exp=1, sig=10: got some 0, expected some (5 : Rat)/2
Failed ❌ on exp=1, sig=11: got some 0, expected some (11 : Rat)/4
Failed ❌ on exp=1, sig=12: got some 0, expected some 3
Failed ❌ on exp=1, sig=13: got some 0, expected some (13 : Rat)/4
Failed ❌ on exp=1, sig=14: got some 0, expected some (7 : Rat)/2
Failed ❌ on exp=1, sig=15: got some 0, expected some (15 : Rat)/4
Failed ❌ on exp=2, sig=0: got some 0, expected some 0
Failed ❌ on exp=2, sig=1: got some 0, expected some (1 : Rat)/2
Failed ❌ on exp=2, sig=2: got some 0, expected some 1
Failed ❌ on exp=2, sig=3: got some 0, expected some (3 : Rat)/2
Failed ❌ on exp=2, sig=4: got some 0, expected some 2
Failed ❌ on exp=2, sig=5: got some 0, expected some (5 : Rat)/2
Failed ❌ on exp=2, sig=6: got some 0, expected some 3
Failed ❌ on exp=2, sig=7: got some 0, expected some (7 : Rat)/2
Failed ❌ on exp=2, sig=8: got some 0, expected some 4
Failed ❌ on exp=2, sig=9: got some 0, expected some (9 : Rat)/2
Failed ❌ on exp=2, sig=10: got some 0, expected some 5
Failed ❌ on exp=2, sig=11: got some 0, expected some (11 : Rat)/2
Failed ❌ on exp=2, sig=12: got some 0, expected some 6
Failed ❌ on exp=2, sig=13: got some 0, expected some (13 : Rat)/2
Failed ❌ on exp=2, sig=14: got some 0, expected some 7
Failed ❌ on exp=2, sig=15: got some 0, expected some (15 : Rat)/2
Failed ❌ on exp=3, sig=0: got some 0, expected some 0
Failed ❌ on exp=3, sig=1: got some 0, expected some 1
Failed ❌ on exp=3, sig=2: got some 0, expected some 2
Failed ❌ on exp=3, sig=3: got some 0, expected some 3
Failed ❌ on exp=3, sig=4: got some 0, expected some 4
Failed ❌ on exp=3, sig=5: got some 0, expected some 5
Failed ❌ on exp=3, sig=6: got some 0, expected some 6
Failed ❌ on exp=3, sig=7: got some 0, expected some 7
Failed ❌ on exp=3, sig=8: got some 0, expected some 8
Failed ❌ on exp=3, sig=9: got some 0, expected some 9
Failed ❌ on exp=3, sig=10: got some 0, expected some 10
Failed ❌ on exp=3, sig=11: got some 0, expected some 11
Failed ❌ on exp=3, sig=12: got some 0, expected some 12
Failed ❌ on exp=3, sig=13: got some 0, expected some 13
Failed ❌ on exp=3, sig=14: got some 0, expected some 14
Failed ❌ on exp=3, sig=15: got some 0, expected some 15
Failed ❌ on exp=4, sig=0: got some 0, expected some 0
Failed ❌ on exp=4, sig=1: got some 0, expected some 2
Failed ❌ on exp=4, sig=2: got some 0, expected some 4
Failed ❌ on exp=4, sig=3: got some 0, expected some 6
Failed ❌ on exp=4, sig=4: got some 0, expected some 8
Failed ❌ on exp=4, sig=5: got some 0, expected some 10
Failed ❌ on exp=4, sig=6: got some 0, expected some 12
Failed ❌ on exp=4, sig=7: got some 0, expected some 14
Failed ❌ on exp=4, sig=8: got some 0, expected some 16
Failed ❌ on exp=4, sig=9: got some 0, expected some 18
Failed ❌ on exp=4, sig=10: got some 0, expected some 20
Failed ❌ on exp=4, sig=11: got some 0, expected some 22
Failed ❌ on exp=4, sig=12: got some 0, expected some 24
Failed ❌ on exp=4, sig=13: got some 0, expected some 26
Failed ❌ on exp=4, sig=14: got some 0, expected some 28
Failed ❌ on exp=4, sig=15: got some 0, expected some 30
Failed ❌ on exp=5, sig=0: got some 0, expected some 0
Failed ❌ on exp=5, sig=1: got some 0, expected some 4
Failed ❌ on exp=5, sig=2: got some 0, expected some 8
Failed ❌ on exp=5, sig=3: got some 0, expected some 12
Failed ❌ on exp=5, sig=4: got some 0, expected some 16
Failed ❌ on exp=5, sig=5: got some 0, expected some 20
Failed ❌ on exp=5, sig=6: got some 0, expected some 24
Failed ❌ on exp=5, sig=7: got some 0, expected some 28
Failed ❌ on exp=5, sig=8: got some 0, expected some 32
Failed ❌ on exp=5, sig=9: got some 0, expected some 36
Failed ❌ on exp=5, sig=10: got some 0, expected some 40
Failed ❌ on exp=5, sig=11: got some 0, expected some 44
Failed ❌ on exp=5, sig=12: got some 0, expected some 48
Failed ❌ on exp=5, sig=13: got some 0, expected some 52
Failed ❌ on exp=5, sig=14: got some 0, expected some 56
Failed ❌ on exp=5, sig=15: got some 0, expected some 60
Failed ❌ on exp=6, sig=0: got some 0, expected some 0
Failed ❌ on exp=6, sig=1: got some 0, expected some 8
Failed ❌ on exp=6, sig=2: got some 0, expected some 16
Failed ❌ on exp=6, sig=3: got some 0, expected some 24
Failed ❌ on exp=6, sig=4: got some 0, expected some 32
Failed ❌ on exp=6, sig=5: got some 0, expected some 40
Failed ❌ on exp=6, sig=6: got some 0, expected some 48
Failed ❌ on exp=6, sig=7: got some 0, expected some 56
Failed ❌ on exp=6, sig=8: got some 0, expected some 64
Failed ❌ on exp=6, sig=9: got some 0, expected some 72
Failed ❌ on exp=6, sig=10: got some 0, expected some 80
Failed ❌ on exp=6, sig=11: got some 0, expected some 88
Failed ❌ on exp=6, sig=12: got some 0, expected some 96
Failed ❌ on exp=6, sig=13: got some 0, expected some 104
Failed ❌ on exp=6, sig=14: got some 0, expected some 112
Failed ❌ on exp=6, sig=15: got some 0, expected some 120
Failed ❌ on exp=7, sig=0: got some 0, expected some 0
Failed ❌ on exp=7, sig=1: got some 0, expected some 16
Failed ❌ on exp=7, sig=2: got some 0, expected some 32
Failed ❌ on exp=7, sig=3: got some 0, expected some 48
Failed ❌ on exp=7, sig=4: got some 0, expected some 64
Failed ❌ on exp=7, sig=5: got some 0, expected some 80
Failed ❌ on exp=7, sig=6: got some 0, expected some 96
Failed ❌ on exp=7, sig=7: got some 0, expected some 112
Failed ❌ on exp=7, sig=8: got some 0, expected some 128
Failed ❌ on exp=7, sig=9: got some 0, expected some 144
Failed ❌ on exp=7, sig=10: got some 0, expected some 160
Failed ❌ on exp=7, sig=11: got some 0, expected some 176
Failed ❌ on exp=7, sig=12: got some 0, expected some 192
Failed ❌ on exp=7, sig=13: got some 0, expected some 208
Failed ❌ on exp=7, sig=14: got some 0, expected some 224
Failed ❌ on exp=7, sig=15: got some 0, expected some 240
Failed ❌ on exp=8, sig=0: got some 0, expected some 0
Failed ❌ on exp=8, sig=1: got some 0, expected some 32
Failed ❌ on exp=8, sig=2: got some 0, expected some 64
Failed ❌ on exp=8, sig=3: got some 0, expected some 96
Failed ❌ on exp=8, sig=4: got some 0, expected some 128
Failed ❌ on exp=8, sig=5: got some 0, expected some 160
Failed ❌ on exp=8, sig=6: got some 0, expected some 192
Failed ❌ on exp=8, sig=7: got some 0, expected some 224
Failed ❌ on exp=8, sig=8: got some 0, expected some 256
Failed ❌ on exp=8, sig=9: got some 0, expected some 288
Failed ❌ on exp=8, sig=10: got some 0, expected some 320
Failed ❌ on exp=8, sig=11: got some 0, expected some 352
Failed ❌ on exp=8, sig=12: got some 0, expected some 384
Failed ❌ on exp=8, sig=13: got some 0, expected some 416
Failed ❌ on exp=8, sig=14: got some 0, expected some 448
Failed ❌ on exp=8, sig=15: got some 0, expected some 480
Failed ❌ on exp=9, sig=0: got some 0, expected some 0
Failed ❌ on exp=9, sig=1: got some 0, expected some 64
Failed ❌ on exp=9, sig=2: got some 0, expected some 128
Failed ❌ on exp=9, sig=3: got some 0, expected some 192
Failed ❌ on exp=9, sig=4: got some 0, expected some 256
Failed ❌ on exp=9, sig=5: got some 0, expected some 320
Failed ❌ on exp=9, sig=6: got some 0, expected some 384
Failed ❌ on exp=9, sig=7: got some 0, expected some 448
Failed ❌ on exp=9, sig=8: got some 0, expected some 512
Failed ❌ on exp=9, sig=9: got some 0, expected some 576
Failed ❌ on exp=9, sig=10: got some 0, expected some 640
Failed ❌ on exp=9, sig=11: got some 0, expected some 704
Failed ❌ on exp=9, sig=12: got some 0, expected some 768
Failed ❌ on exp=9, sig=13: got some 0, expected some 832
Failed ❌ on exp=9, sig=14: got some 0, expected some 896
Failed ❌ on exp=9, sig=15: got some 0, expected some 960
Failed ❌ on exp=10, sig=0: got some 0, expected some 0
Failed ❌ on exp=10, sig=1: got some 0, expected some 128
Failed ❌ on exp=10, sig=2: got some 0, expected some 256
Failed ❌ on exp=10, sig=3: got some 0, expected some 384
Failed ❌ on exp=10, sig=4: got some 0, expected some 512
Failed ❌ on exp=10, sig=5: got some 0, expected some 640
Failed ❌ on exp=10, sig=6: got some 0, expected some 768
Failed ❌ on exp=10, sig=7: got some 0, expected some 896
Failed ❌ on exp=10, sig=8: got some 0, expected some 1024
Failed ❌ on exp=10, sig=9: got some 0, expected some 1152
Failed ❌ on exp=10, sig=10: got some 0, expected some 1280
Failed ❌ on exp=10, sig=11: got some 0, expected some 1408
Failed ❌ on exp=10, sig=12: got some 0, expected some 1536
Failed ❌ on exp=10, sig=13: got some 0, expected some 1664
Failed ❌ on exp=10, sig=14: got some 0, expected some 1792
Failed ❌ on exp=10, sig=15: got some 0, expected some 1920
Failed ❌ on exp=11, sig=0: got some 0, expected some 0
Failed ❌ on exp=11, sig=1: got some 0, expected some 256
Failed ❌ on exp=11, sig=2: got some 0, expected some 512
Failed ❌ on exp=11, sig=3: got some 0, expected some 768
Failed ❌ on exp=11, sig=4: got some 0, expected some 1024
Failed ❌ on exp=11, sig=5: got some 0, expected some 1280
Failed ❌ on exp=11, sig=6: got some 0, expected some 1536
Failed ❌ on exp=11, sig=7: got some 0, expected some 1792
Failed ❌ on exp=11, sig=8: got some 0, expected some 2048
Failed ❌ on exp=11, sig=9: got some 0, expected some 2304
Failed ❌ on exp=11, sig=10: got some 0, expected some 2560
Failed ❌ on exp=11, sig=11: got some 0, expected some 2816
Failed ❌ on exp=11, sig=12: got some 0, expected some 3072
Failed ❌ on exp=11, sig=13: got some 0, expected some 3328
Failed ❌ on exp=11, sig=14: got some 0, expected some 3584
Failed ❌ on exp=11, sig=15: got some 0, expected some 3840
Failed ❌ on exp=12, sig=0: got some 0, expected some 0
Failed ❌ on exp=12, sig=1: got some 0, expected some 512
Failed ❌ on exp=12, sig=2: got some 0, expected some 1024
Failed ❌ on exp=12, sig=3: got some 0, expected some 1536
Failed ❌ on exp=12, sig=4: got some 0, expected some 2048
Failed ❌ on exp=12, sig=5: got some 0, expected some 2560
Failed ❌ on exp=12, sig=6: got some 0, expected some 3072
Failed ❌ on exp=12, sig=7: got some 0, expected some 3584
Failed ❌ on exp=12, sig=8: got some 0, expected some 4096
Failed ❌ on exp=12, sig=9: got some 0, expected some 4608
Failed ❌ on exp=12, sig=10: got some 0, expected some 5120
Failed ❌ on exp=12, sig=11: got some 0, expected some 5632
Failed ❌ on exp=12, sig=12: got some 0, expected some 6144
Failed ❌ on exp=12, sig=13: got some 0, expected some 6656
Failed ❌ on exp=12, sig=14: got some 0, expected some 7168
Failed ❌ on exp=12, sig=15: got some 0, expected some 7680
Failed ❌ on exp=13, sig=0: got some 0, expected some 0
Failed ❌ on exp=13, sig=1: got some 0, expected some 1024
Failed ❌ on exp=13, sig=2: got some 0, expected some 2048
Failed ❌ on exp=13, sig=3: got some 0, expected some 3072
Failed ❌ on exp=13, sig=4: got some 0, expected some 4096
Failed ❌ on exp=13, sig=5: got some 0, expected some 5120
Failed ❌ on exp=13, sig=6: got some 0, expected some 6144
Failed ❌ on exp=13, sig=7: got some 0, expected some 7168
Failed ❌ on exp=13, sig=8: got some 0, expected some 8192
Failed ❌ on exp=13, sig=9: got some 0, expected some 9216
Failed ❌ on exp=13, sig=10: got some 0, expected some 10240
Failed ❌ on exp=13, sig=11: got some 0, expected some 11264
Failed ❌ on exp=13, sig=12: got some 0, expected some 12288
Failed ❌ on exp=13, sig=13: got some 0, expected some 13312
Failed ❌ on exp=13, sig=14: got some 0, expected some 14336
Failed ❌ on exp=13, sig=15: got some 0, expected some 15360
Failed ❌ on exp=14, sig=0: got some 0, expected some 0
Failed ❌ on exp=14, sig=1: got some 0, expected some 2048
Failed ❌ on exp=14, sig=2: got some 0, expected some 4096
Failed ❌ on exp=14, sig=3: got some 0, expected some 6144
Failed ❌ on exp=14, sig=4: got some 0, expected some 8192
Failed ❌ on exp=14, sig=5: got some 0, expected some 10240
Failed ❌ on exp=14, sig=6: got some 0, expected some 12288
Failed ❌ on exp=14, sig=7: got some 0, expected some 14336
Failed ❌ on exp=14, sig=8: got some 0, expected some 16384
Failed ❌ on exp=14, sig=9: got some 0, expected some 18432
Failed ❌ on exp=14, sig=10: got some 0, expected some 20480
Failed ❌ on exp=14, sig=11: got some 0, expected some 22528
Failed ❌ on exp=14, sig=12: got some 0, expected some 24576
Failed ❌ on exp=14, sig=13: got some 0, expected some 26624
Failed ❌ on exp=14, sig=14: got some 0, expected some 28672
Failed ❌ on exp=14, sig=15: got some 0, expected some 30720
Failed ❌ on exp=15, sig=0: got some 0, expected some 0
Failed ❌ on exp=15, sig=1: got some 0, expected some 4096
Failed ❌ on exp=15, sig=2: got some 0, expected some 8192
Failed ❌ on exp=15, sig=3: got some 0, expected some 12288
Failed ❌ on exp=15, sig=4: got some 0, expected some 16384
Failed ❌ on exp=15, sig=5: got some 0, expected some 20480
Failed ❌ on exp=15, sig=6: got some 0, expected some 24576
Failed ❌ on exp=15, sig=7: got some 0, expected some 28672
Failed ❌ on exp=15, sig=8: got some 0, expected some 32768
Failed ❌ on exp=15, sig=9: got some 0, expected some 36864
Failed ❌ on exp=15, sig=10: got some 0, expected some 40960
Failed ❌ on exp=15, sig=11: got some 0, expected some 45056
Failed ❌ on exp=15, sig=12: got some 0, expected some 49152
Failed ❌ on exp=15, sig=13: got some 0, expected some 53248
Failed ❌ on exp=15, sig=14: got some 0, expected some 57344
Failed ❌ on exp=15, sig=15: got some 0, expected some 61440
Failed ❌ on exp=18, sig=0: got some 0, expected some 0
Failed ❌ on exp=18, sig=1: got some 0, expected some 32768
Failed ❌ on exp=18, sig=2: got some 0, expected some 65536
Failed ❌ on exp=18, sig=3: got some 0, expected some 98304
Failed ❌ on exp=18, sig=4: got some 0, expected some 131072
Failed ❌ on exp=18, sig=5: got some 0, expected some 163840
Failed ❌ on exp=18, sig=6: got some 0, expected some 196608
Failed ❌ on exp=18, sig=7: got some 0, expected some 229376
Failed ❌ on exp=18, sig=8: got some 0, expected some 262144
Failed ❌ on exp=18, sig=9: got some 0, expected some 294912
Failed ❌ on exp=18, sig=10: got some 0, expected some 327680
Failed ❌ on exp=18, sig=11: got some 0, expected some 360448
Failed ❌ on exp=18, sig=12: got some 0, expected some 393216
Failed ❌ on exp=18, sig=13: got some 0, expected some 425984
Failed ❌ on exp=18, sig=14: got some 0, expected some 458752
Failed ❌ on exp=18, sig=15: got some 0, expected some 491520
Failed ❌ on exp=19, sig=0: got some 0, expected some 0
Failed ❌ on exp=19, sig=1: got some 0, expected some 65536
Failed ❌ on exp=19, sig=2: got some 0, expected some 131072
Failed ❌ on exp=19, sig=3: got some 0, expected some 196608
Failed ❌ on exp=19, sig=4: got some 0, expected some 262144
Failed ❌ on exp=19, sig=5: got some 0, expected some 327680
Failed ❌ on exp=19, sig=6: got some 0, expected some 393216
Failed ❌ on exp=19, sig=7: got some 0, expected some 458752
Failed ❌ on exp=19, sig=8: got some 0, expected some 524288
Failed ❌ on exp=19, sig=9: got some 0, expected some 589824
Failed ❌ on exp=19, sig=10: got some 0, expected some 655360
Failed ❌ on exp=19, sig=11: got some 0, expected some 720896
Failed ❌ on exp=19, sig=12: got some 0, expected some 786432
Failed ❌ on exp=19, sig=13: got some 0, expected some 851968
Failed ❌ on exp=19, sig=14: got some 0, expected some 917504
Failed ❌ on exp=19, sig=15: got some 0, expected some 983040
Failed ❌ on exp=20, sig=0: got some 0, expected some 0
Failed ❌ on exp=20, sig=1: got some 0, expected some 131072
Failed ❌ on exp=20, sig=2: got some 0, expected some 262144
Failed ❌ on exp=20, sig=3: got some 0, expected some 393216
Failed ❌ on exp=20, sig=4: got some 0, expected some 524288
Failed ❌ on exp=20, sig=5: got some 0, expected some 655360
Failed ❌ on exp=20, sig=6: got some 0, expected some 786432
Failed ❌ on exp=20, sig=7: got some 0, expected some 917504
Failed ❌ on exp=20, sig=8: got some 0, expected some 1048576
Failed ❌ on exp=20, sig=9: got some 0, expected some 1179648
Failed ❌ on exp=20, sig=10: got some 0, expected some 1310720
Failed ❌ on exp=20, sig=11: got some 0, expected some 1441792
Failed ❌ on exp=20, sig=12: got some 0, expected some 1572864
Failed ❌ on exp=20, sig=13: got some 0, expected some 1703936
Failed ❌ on exp=20, sig=14: got some 0, expected some 1835008
Failed ❌ on exp=20, sig=15: got some 0, expected some 1966080
Failed ❌ on exp=21, sig=0: got some 0, expected some 0
Failed ❌ on exp=21, sig=1: got some 0, expected some 262144
Failed ❌ on exp=21, sig=2: got some 0, expected some 524288
Failed ❌ on exp=21, sig=3: got some 0, expected some 786432
Failed ❌ on exp=21, sig=4: got some 0, expected some 1048576
Failed ❌ on exp=21, sig=5: got some 0, expected some 1310720
Failed ❌ on exp=21, sig=6: got some 0, expected some 1572864
Failed ❌ on exp=21, sig=7: got some 0, expected some 1835008
Failed ❌ on exp=21, sig=8: got some 0, expected some 2097152
Failed ❌ on exp=21, sig=9: got some 0, expected some 2359296
Failed ❌ on exp=21, sig=10: got some 0, expected some 2621440
Failed ❌ on exp=21, sig=11: got some 0, expected some 2883584
Failed ❌ on exp=21, sig=12: got some 0, expected some 3145728
Failed ❌ on exp=21, sig=13: got some 0, expected some 3407872
Failed ❌ on exp=21, sig=14: got some 0, expected some 3670016
Failed ❌ on exp=21, sig=15: got some 0, expected some 3932160
Failed ❌ on exp=22, sig=0: got some 0, expected some 0
Failed ❌ on exp=22, sig=1: got some 0, expected some 524288
Failed ❌ on exp=22, sig=2: got some 0, expected some 1048576
Failed ❌ on exp=22, sig=3: got some 0, expected some 1572864
Failed ❌ on exp=22, sig=4: got some 0, expected some 2097152
Failed ❌ on exp=22, sig=5: got some 0, expected some 2621440
Failed ❌ on exp=22, sig=6: got some 0, expected some 3145728
Failed ❌ on exp=22, sig=7: got some 0, expected some 3670016
Failed ❌ on exp=22, sig=8: got some 0, expected some 4194304
Failed ❌ on exp=22, sig=9: got some 0, expected some 4718592
Failed ❌ on exp=22, sig=10: got some 0, expected some 5242880
Failed ❌ on exp=22, sig=11: got some 0, expected some 5767168
Failed ❌ on exp=22, sig=12: got some 0, expected some 6291456
Failed ❌ on exp=22, sig=13: got some 0, expected some 6815744
Failed ❌ on exp=22, sig=14: got some 0, expected some 7340032
Failed ❌ on exp=22, sig=15: got some 0, expected some 7864320
Failed ❌ on exp=23, sig=0: got some 0, expected some 0
Failed ❌ on exp=23, sig=1: got some 0, expected some 1048576
Failed ❌ on exp=23, sig=2: got some 0, expected some 2097152
Failed ❌ on exp=23, sig=3: got some 0, expected some 3145728
Failed ❌ on exp=23, sig=4: got some 0, expected some 4194304
Failed ❌ on exp=23, sig=5: got some 0, expected some 5242880
Failed ❌ on exp=23, sig=6: got some 0, expected some 6291456
Failed ❌ on exp=23, sig=7: got some 0, expected some 7340032
Failed ❌ on exp=23, sig=8: got some 0, expected some 8388608
Failed ❌ on exp=23, sig=9: got some 0, expected some 9437184
Failed ❌ on exp=23, sig=10: got some 0, expected some 10485760
Failed ❌ on exp=23, sig=11: got some 0, expected some 11534336
Failed ❌ on exp=23, sig=12: got some 0, expected some 12582912
Failed ❌ on exp=23, sig=13: got some 0, expected some 13631488
Failed ❌ on exp=23, sig=14: got some 0, expected some 14680064
Failed ❌ on exp=23, sig=15: got some 0, expected some 15728640
Failed ❌ on exp=24, sig=0: got some 0, expected some 0
Failed ❌ on exp=24, sig=1: got some 0, expected some 2097152
Failed ❌ on exp=24, sig=2: got some 0, expected some 4194304
Failed ❌ on exp=24, sig=3: got some 0, expected some 6291456
Failed ❌ on exp=24, sig=4: got some 0, expected some 8388608
Failed ❌ on exp=24, sig=5: got some 0, expected some 10485760
Failed ❌ on exp=24, sig=6: got some 0, expected some 12582912
Failed ❌ on exp=24, sig=7: got some 0, expected some 14680064
Failed ❌ on exp=24, sig=8: got some 0, expected some 16777216
Failed ❌ on exp=24, sig=9: got some 0, expected some 18874368
Failed ❌ on exp=24, sig=10: got some 0, expected some 20971520
Failed ❌ on exp=24, sig=11: got some 0, expected some 23068672
Failed ❌ on exp=24, sig=12: got some 0, expected some 25165824
Failed ❌ on exp=24, sig=13: got some 0, expected some 27262976
Failed ❌ on exp=24, sig=14: got some 0, expected some 29360128
Failed ❌ on exp=24, sig=15: got some 0, expected some 31457280
Failed ❌ on exp=25, sig=0: got some 0, expected some 0
Failed ❌ on exp=25, sig=1: got some 0, expected some 4194304
Failed ❌ on exp=25, sig=2: got some 0, expected some 8388608
Failed ❌ on exp=25, sig=3: got some 0, expected some 12582912
Failed ❌ on exp=25, sig=4: got some 0, expected some 16777216
Failed ❌ on exp=25, sig=5: got some 0, expected some 20971520
Failed ❌ on exp=25, sig=6: got some 0, expected some 25165824
Failed ❌ on exp=25, sig=7: got some 0, expected some 29360128
Failed ❌ on exp=25, sig=8: got some 0, expected some 33554432
Failed ❌ on exp=25, sig=9: got some 0, expected some 37748736
Failed ❌ on exp=25, sig=10: got some 0, expected some 41943040
Failed ❌ on exp=25, sig=11: got some 0, expected some 46137344
Failed ❌ on exp=25, sig=12: got some 0, expected some 50331648
Failed ❌ on exp=25, sig=13: got some 0, expected some 54525952
Failed ❌ on exp=25, sig=14: got some 0, expected some 58720256
Failed ❌ on exp=25, sig=15: got some 0, expected some 62914560
Failed ❌ on exp=26, sig=0: got some 0, expected some 0
Failed ❌ on exp=26, sig=1: got some 0, expected some 8388608
Failed ❌ on exp=26, sig=2: got some 0, expected some 16777216
Failed ❌ on exp=26, sig=3: got some 0, expected some 25165824
Failed ❌ on exp=26, sig=4: got some 0, expected some 33554432
Failed ❌ on exp=26, sig=5: got some 0, expected some 41943040
Failed ❌ on exp=26, sig=6: got some 0, expected some 50331648
Failed ❌ on exp=26, sig=7: got some 0, expected some 58720256
Failed ❌ on exp=26, sig=8: got some 0, expected some 67108864
Failed ❌ on exp=26, sig=9: got some 0, expected some 75497472
Failed ❌ on exp=26, sig=10: got some 0, expected some 83886080
Failed ❌ on exp=26, sig=11: got some 0, expected some 92274688
Failed ❌ on exp=26, sig=12: got some 0, expected some 100663296
Failed ❌ on exp=26, sig=13: got some 0, expected some 109051904
Failed ❌ on exp=26, sig=14: got some 0, expected some 117440512
Failed ❌ on exp=26, sig=15: got some 0, expected some 125829120
Failed ❌ on exp=27, sig=0: got some 0, expected some 0
Failed ❌ on exp=27, sig=1: got some 0, expected some 16777216
Failed ❌ on exp=27, sig=2: got some 0, expected some 33554432
Failed ❌ on exp=27, sig=3: got some 0, expected some 50331648
Failed ❌ on exp=27, sig=4: got some 0, expected some 67108864
Failed ❌ on exp=27, sig=5: got some 0, expected some 83886080
Failed ❌ on exp=27, sig=6: got some 0, expected some 100663296
Failed ❌ on exp=27, sig=7: got some 0, expected some 117440512
Failed ❌ on exp=27, sig=8: got some 0, expected some 134217728
Failed ❌ on exp=27, sig=9: got some 0, expected some 150994944
Failed ❌ on exp=27, sig=10: got some 0, expected some 167772160
Failed ❌ on exp=27, sig=11: got some 0, expected some 184549376
Failed ❌ on exp=27, sig=12: got some 0, expected some 201326592
Failed ❌ on exp=27, sig=13: got some 0, expected some 218103808
Failed ❌ on exp=27, sig=14: got some 0, expected some 234881024
Failed ❌ on exp=27, sig=15: got some 0, expected some 251658240
Failed ❌ on exp=28, sig=0: got some 0, expected some 0
Failed ❌ on exp=28, sig=1: got some 0, expected some 33554432
Failed ❌ on exp=28, sig=2: got some 0, expected some 67108864
Failed ❌ on exp=28, sig=3: got some 0, expected some 100663296
Failed ❌ on exp=28, sig=4: got some 0, expected some 134217728
Failed ❌ on exp=28, sig=5: got some 0, expected some 167772160
Failed ❌ on exp=28, sig=6: got some 0, expected some 201326592
Failed ❌ on exp=28, sig=7: got some 0, expected some 234881024
Failed ❌ on exp=28, sig=8: got some 0, expected some 268435456
Failed ❌ on exp=28, sig=9: got some 0, expected some 301989888
Failed ❌ on exp=28, sig=10: got some 0, expected some 335544320
Failed ❌ on exp=28, sig=11: got some 0, expected some 369098752
Failed ❌ on exp=28, sig=12: got some 0, expected some 402653184
Failed ❌ on exp=28, sig=13: got some 0, expected some 436207616
Failed ❌ on exp=28, sig=14: got some 0, expected some 469762048
Failed ❌ on exp=28, sig=15: got some 0, expected some 503316480
Failed ❌ on exp=29, sig=0: got some 0, expected some 0
Failed ❌ on exp=29, sig=1: got some 0, expected some 67108864
Failed ❌ on exp=29, sig=2: got some 0, expected some 134217728
Failed ❌ on exp=29, sig=3: got some 0, expected some 201326592
Failed ❌ on exp=29, sig=4: got some 0, expected some 268435456
Failed ❌ on exp=29, sig=5: got some 0, expected some 335544320
Failed ❌ on exp=29, sig=6: got some 0, expected some 402653184
Failed ❌ on exp=29, sig=7: got some 0, expected some 469762048
Failed ❌ on exp=29, sig=8: got some 0, expected some 536870912
Failed ❌ on exp=29, sig=9: got some 0, expected some 603979776
Failed ❌ on exp=29, sig=10: got some 0, expected some 671088640
Failed ❌ on exp=29, sig=11: got some 0, expected some 738197504
Failed ❌ on exp=29, sig=12: got some 0, expected some 805306368
Failed ❌ on exp=29, sig=13: got some 0, expected some 872415232
Failed ❌ on exp=29, sig=14: got some 0, expected some 939524096
Failed ❌ on exp=29, sig=15: got some 0, expected some 1006632960
Failed ❌ on exp=30, sig=0: got some 0, expected some 0
Failed ❌ on exp=30, sig=1: got some 0, expected some 134217728
Failed ❌ on exp=30, sig=2: got some 0, expected some 268435456
Failed ❌ on exp=30, sig=3: got some 0, expected some 402653184
Failed ❌ on exp=30, sig=4: got some 0, expected some 536870912
Failed ❌ on exp=30, sig=5: got some 0, expected some 671088640
Failed ❌ on exp=30, sig=6: got some 0, expected some 805306368
Failed ❌ on exp=30, sig=7: got some 0, expected some 939524096
Failed ❌ on exp=30, sig=8: got some 0, expected some 1073741824
Failed ❌ on exp=30, sig=9: got some 0, expected some 1207959552
Failed ❌ on exp=30, sig=10: got some 0, expected some 1342177280
Failed ❌ on exp=30, sig=11: got some 0, expected some 1476395008
Failed ❌ on exp=30, sig=12: got some 0, expected some 1610612736
Failed ❌ on exp=30, sig=13: got some 0, expected some 1744830464
Failed ❌ on exp=30, sig=14: got some 0, expected some 1879048192
Failed ❌ on exp=30, sig=15: got some 0, expected some 2013265920
Failed ❌ on exp=31, sig=0: got some 0, expected some 0
Failed ❌ on exp=31, sig=1: got some 0, expected some 268435456
Failed ❌ on exp=31, sig=2: got some 0, expected some 536870912
Failed ❌ on exp=31, sig=3: got some 0, expected some 805306368
Failed ❌ on exp=31, sig=4: got some 0, expected some 1073741824
Failed ❌ on exp=31, sig=5: got some 0, expected some 1342177280
Failed ❌ on exp=31, sig=6: got some 0, expected some 1610612736
Failed ❌ on exp=31, sig=7: got some 0, expected some 1879048192
Failed ❌ on exp=31, sig=8: got some 0, expected some 2147483648
Failed ❌ on exp=31, sig=9: got some 0, expected some 2415919104
Failed ❌ on exp=31, sig=10: got some 0, expected some 2684354560
Failed ❌ on exp=31, sig=11: got some 0, expected some 2952790016
Failed ❌ on exp=31, sig=12: got some 0, expected some 3221225472
Failed ❌ on exp=31, sig=13: got some 0, expected some 3489660928
Failed ❌ on exp=31, sig=14: got some 0, expected some 3758096384
Failed ❌ on exp=31, sig=15: got some 0, expected some 4026531840
Failed ❌ on exp=50, sig=0: got none, expected some 0
Failed ❌ on exp=50, sig=1: got none, expected some (1 : Rat)/131072
Failed ❌ on exp=50, sig=2: got none, expected some (1 : Rat)/65536
Failed ❌ on exp=50, sig=3: got none, expected some (3 : Rat)/131072
Failed ❌ on exp=50, sig=4: got none, expected some (1 : Rat)/32768
Failed ❌ on exp=50, sig=5: got none, expected some (5 : Rat)/131072
Failed ❌ on exp=50, sig=6: got none, expected some (3 : Rat)/65536
Failed ❌ on exp=50, sig=7: got none, expected some (7 : Rat)/131072
Failed ❌ on exp=50, sig=8: got none, expected some (1 : Rat)/16384
Failed ❌ on exp=50, sig=9: got none, expected some (9 : Rat)/131072
Failed ❌ on exp=50, sig=10: got none, expected some (5 : Rat)/65536
Failed ❌ on exp=50, sig=11: got none, expected some (11 : Rat)/131072
Failed ❌ on exp=50, sig=12: got none, expected some (3 : Rat)/32768
Failed ❌ on exp=50, sig=13: got none, expected some (13 : Rat)/131072
Failed ❌ on exp=50, sig=14: got none, expected some (7 : Rat)/65536
Failed ❌ on exp=50, sig=15: got none, expected some (15 : Rat)/131072
Failed ❌ on exp=51, sig=0: got none, expected some 0
Failed ❌ on exp=51, sig=1: got none, expected some (1 : Rat)/65536
Failed ❌ on exp=51, sig=2: got none, expected some (1 : Rat)/32768
Failed ❌ on exp=51, sig=3: got none, expected some (3 : Rat)/65536
Failed ❌ on exp=51, sig=4: got none, expected some (1 : Rat)/16384
Failed ❌ on exp=51, sig=5: got none, expected some (5 : Rat)/65536
Failed ❌ on exp=51, sig=6: got none, expected some (3 : Rat)/32768
Failed ❌ on exp=51, sig=7: got none, expected some (7 : Rat)/65536
Failed ❌ on exp=51, sig=8: got none, expected some (1 : Rat)/8192
Failed ❌ on exp=51, sig=9: got none, expected some (9 : Rat)/65536
Failed ❌ on exp=51, sig=10: got none, expected some (5 : Rat)/32768
Failed ❌ on exp=51, sig=11: got none, expected some (11 : Rat)/65536
Failed ❌ on exp=51, sig=12: got none, expected some (3 : Rat)/16384
Failed ❌ on exp=51, sig=13: got none, expected some (13 : Rat)/65536
Failed ❌ on exp=51, sig=14: got none, expected some (7 : Rat)/32768
Failed ❌ on exp=51, sig=15: got none, expected some (15 : Rat)/65536
Failed ❌ on exp=52, sig=0: got none, expected some 0
Failed ❌ on exp=52, sig=1: got none, expected some (1 : Rat)/32768
Failed ❌ on exp=52, sig=2: got none, expected some (1 : Rat)/16384
Failed ❌ on exp=52, sig=3: got none, expected some (3 : Rat)/32768
Failed ❌ on exp=52, sig=4: got none, expected some (1 : Rat)/8192
Failed ❌ on exp=52, sig=5: got none, expected some (5 : Rat)/32768
Failed ❌ on exp=52, sig=6: got none, expected some (3 : Rat)/16384
Failed ❌ on exp=52, sig=7: got none, expected some (7 : Rat)/32768
Failed ❌ on exp=52, sig=8: got none, expected some (1 : Rat)/4096
Failed ❌ on exp=52, sig=9: got none, expected some (9 : Rat)/32768
Failed ❌ on exp=52, sig=10: got none, expected some (5 : Rat)/16384
Failed ❌ on exp=52, sig=11: got none, expected some (11 : Rat)/32768
Failed ❌ on exp=52, sig=12: got none, expected some (3 : Rat)/8192
Failed ❌ on exp=52, sig=13: got none, expected some (13 : Rat)/32768
Failed ❌ on exp=52, sig=14: got none, expected some (7 : Rat)/16384
Failed ❌ on exp=52, sig=15: got none, expected some (15 : Rat)/32768
Failed ❌ on exp=53, sig=0: got none, expected some 0
Failed ❌ on exp=53, sig=1: got none, expected some (1 : Rat)/16384
Failed ❌ on exp=53, sig=2: got none, expected some (1 : Rat)/8192
Failed ❌ on exp=53, sig=3: got none, expected some (3 : Rat)/16384
Failed ❌ on exp=53, sig=4: got none, expected some (1 : Rat)/4096
Failed ❌ on exp=53, sig=5: got none, expected some (5 : Rat)/16384
Failed ❌ on exp=53, sig=6: got none, expected some (3 : Rat)/8192
Failed ❌ on exp=53, sig=7: got none, expected some (7 : Rat)/16384
Failed ❌ on exp=53, sig=8: got none, expected some (1 : Rat)/2048
Failed ❌ on exp=53, sig=9: got none, expected some (9 : Rat)/16384
Failed ❌ on exp=53, sig=10: got none, expected some (5 : Rat)/8192
Failed ❌ on exp=53, sig=11: got none, expected some (11 : Rat)/16384
Failed ❌ on exp=53, sig=12: got none, expected some (3 : Rat)/4096
Failed ❌ on exp=53, sig=13: got none, expected some (13 : Rat)/16384
Failed ❌ on exp=53, sig=14: got none, expected some (7 : Rat)/8192
Failed ❌ on exp=53, sig=15: got none, expected some (15 : Rat)/16384
Failed ❌ on exp=54, sig=0: got none, expected some 0
Failed ❌ on exp=54, sig=1: got none, expected some (1 : Rat)/8192
Failed ❌ on exp=54, sig=2: got none, expected some (1 : Rat)/4096
Failed ❌ on exp=54, sig=3: got none, expected some (3 : Rat)/8192
Failed ❌ on exp=54, sig=4: got none, expected some (1 : Rat)/2048
Failed ❌ on exp=54, sig=5: got none, expected some (5 : Rat)/8192
Failed ❌ on exp=54, sig=6: got none, expected some (3 : Rat)/4096
Failed ❌ on exp=54, sig=7: got none, expected some (7 : Rat)/8192
Failed ❌ on exp=54, sig=8: got none, expected some (1 : Rat)/1024
Failed ❌ on exp=54, sig=9: got none, expected some (9 : Rat)/8192
Failed ❌ on exp=54, sig=10: got none, expected some (5 : Rat)/4096
Failed ❌ on exp=54, sig=11: got none, expected some (11 : Rat)/8192
Failed ❌ on exp=54, sig=12: got none, expected some (3 : Rat)/2048
Failed ❌ on exp=54, sig=13: got none, expected some (13 : Rat)/8192
Failed ❌ on exp=54, sig=14: got none, expected some (7 : Rat)/4096
Failed ❌ on exp=54, sig=15: got none, expected some (15 : Rat)/8192
Failed ❌ on exp=55, sig=0: got none, expected some 0
Failed ❌ on exp=55, sig=1: got none, expected some (1 : Rat)/4096
Failed ❌ on exp=55, sig=2: got none, expected some (1 : Rat)/2048
Failed ❌ on exp=55, sig=3: got none, expected some (3 : Rat)/4096
Failed ❌ on exp=55, sig=4: got none, expected some (1 : Rat)/1024
Failed ❌ on exp=55, sig=5: got none, expected some (5 : Rat)/4096
Failed ❌ on exp=55, sig=6: got none, expected some (3 : Rat)/2048
Failed ❌ on exp=55, sig=7: got none, expected some (7 : Rat)/4096
Failed ❌ on exp=55, sig=8: got none, expected some (1 : Rat)/512
Failed ❌ on exp=55, sig=9: got none, expected some (9 : Rat)/4096
Failed ❌ on exp=55, sig=10: got none, expected some (5 : Rat)/2048
Failed ❌ on exp=55, sig=11: got none, expected some (11 : Rat)/4096
Failed ❌ on exp=55, sig=12: got none, expected some (3 : Rat)/1024
Failed ❌ on exp=55, sig=13: got none, expected some (13 : Rat)/4096
Failed ❌ on exp=55, sig=14: got none, expected some (7 : Rat)/2048
Failed ❌ on exp=55, sig=15: got none, expected some (15 : Rat)/4096
Failed ❌ on exp=56, sig=0: got none, expected some 0
Failed ❌ on exp=56, sig=1: got none, expected some (1 : Rat)/2048
Failed ❌ on exp=56, sig=2: got none, expected some (1 : Rat)/1024
Failed ❌ on exp=56, sig=3: got none, expected some (3 : Rat)/2048
Failed ❌ on exp=56, sig=4: got none, expected some (1 : Rat)/512
Failed ❌ on exp=56, sig=5: got none, expected some (5 : Rat)/2048
Failed ❌ on exp=56, sig=6: got none, expected some (3 : Rat)/1024
Failed ❌ on exp=56, sig=7: got none, expected some (7 : Rat)/2048
Failed ❌ on exp=56, sig=8: got none, expected some (1 : Rat)/256
Failed ❌ on exp=56, sig=9: got none, expected some (9 : Rat)/2048
Failed ❌ on exp=56, sig=10: got none, expected some (5 : Rat)/1024
Failed ❌ on exp=56, sig=11: got none, expected some (11 : Rat)/2048
Failed ❌ on exp=56, sig=12: got none, expected some (3 : Rat)/512
Failed ❌ on exp=56, sig=13: got none, expected some (13 : Rat)/2048
Failed ❌ on exp=56, sig=14: got none, expected some (7 : Rat)/1024
Failed ❌ on exp=56, sig=15: got none, expected some (15 : Rat)/2048
Failed ❌ on exp=57, sig=0: got none, expected some 0
Failed ❌ on exp=57, sig=1: got none, expected some (1 : Rat)/1024
Failed ❌ on exp=57, sig=2: got none, expected some (1 : Rat)/512
Failed ❌ on exp=57, sig=3: got none, expected some (3 : Rat)/1024
Failed ❌ on exp=57, sig=4: got none, expected some (1 : Rat)/256
Failed ❌ on exp=57, sig=5: got none, expected some (5 : Rat)/1024
Failed ❌ on exp=57, sig=6: got none, expected some (3 : Rat)/512
Failed ❌ on exp=57, sig=7: got none, expected some (7 : Rat)/1024
Failed ❌ on exp=57, sig=8: got none, expected some (1 : Rat)/128
Failed ❌ on exp=57, sig=9: got none, expected some (9 : Rat)/1024
Failed ❌ on exp=57, sig=10: got none, expected some (5 : Rat)/512
Failed ❌ on exp=57, sig=11: got none, expected some (11 : Rat)/1024
Failed ❌ on exp=57, sig=12: got none, expected some (3 : Rat)/256
Failed ❌ on exp=57, sig=13: got none, expected some (13 : Rat)/1024
Failed ❌ on exp=57, sig=14: got none, expected some (7 : Rat)/512
Failed ❌ on exp=57, sig=15: got none, expected some (15 : Rat)/1024
Failed ❌ on exp=58, sig=0: got none, expected some 0
Failed ❌ on exp=58, sig=1: got none, expected some (1 : Rat)/512
Failed ❌ on exp=58, sig=2: got none, expected some (1 : Rat)/256
Failed ❌ on exp=58, sig=3: got none, expected some (3 : Rat)/512
Failed ❌ on exp=58, sig=4: got none, expected some (1 : Rat)/128
Failed ❌ on exp=58, sig=5: got none, expected some (5 : Rat)/512
Failed ❌ on exp=58, sig=6: got none, expected some (3 : Rat)/256
Failed ❌ on exp=58, sig=7: got none, expected some (7 : Rat)/512
Failed ❌ on exp=58, sig=8: got none, expected some (1 : Rat)/64
Failed ❌ on exp=58, sig=9: got none, expected some (9 : Rat)/512
Failed ❌ on exp=58, sig=10: got none, expected some (5 : Rat)/256
Failed ❌ on exp=58, sig=11: got none, expected some (11 : Rat)/512
Failed ❌ on exp=58, sig=12: got none, expected some (3 : Rat)/128
Failed ❌ on exp=58, sig=13: got none, expected some (13 : Rat)/512
Failed ❌ on exp=58, sig=14: got none, expected some (7 : Rat)/256
Failed ❌ on exp=58, sig=15: got none, expected some (15 : Rat)/512
Failed ❌ on exp=59, sig=0: got none, expected some 0
Failed ❌ on exp=59, sig=1: got none, expected some (1 : Rat)/256
Failed ❌ on exp=59, sig=2: got none, expected some (1 : Rat)/128
Failed ❌ on exp=59, sig=3: got none, expected some (3 : Rat)/256
Failed ❌ on exp=59, sig=4: got none, expected some (1 : Rat)/64
Failed ❌ on exp=59, sig=5: got none, expected some (5 : Rat)/256
Failed ❌ on exp=59, sig=6: got none, expected some (3 : Rat)/128
Failed ❌ on exp=59, sig=7: got none, expected some (7 : Rat)/256
Failed ❌ on exp=59, sig=8: got none, expected some (1 : Rat)/32
Failed ❌ on exp=59, sig=9: got none, expected some (9 : Rat)/256
Failed ❌ on exp=59, sig=10: got none, expected some (5 : Rat)/128
Failed ❌ on exp=59, sig=11: got none, expected some (11 : Rat)/256
Failed ❌ on exp=59, sig=12: got none, expected some (3 : Rat)/64
Failed ❌ on exp=59, sig=13: got none, expected some (13 : Rat)/256
Failed ❌ on exp=59, sig=14: got none, expected some (7 : Rat)/128
Failed ❌ on exp=59, sig=15: got none, expected some (15 : Rat)/256
Failed ❌ on exp=60, sig=0: got none, expected some 0
Failed ❌ on exp=60, sig=1: got none, expected some (1 : Rat)/128
Failed ❌ on exp=60, sig=2: got none, expected some (1 : Rat)/64
Failed ❌ on exp=60, sig=3: got none, expected some (3 : Rat)/128
Failed ❌ on exp=60, sig=4: got none, expected some (1 : Rat)/32
Failed ❌ on exp=60, sig=5: got none, expected some (5 : Rat)/128
Failed ❌ on exp=60, sig=6: got none, expected some (3 : Rat)/64
Failed ❌ on exp=60, sig=7: got none, expected some (7 : Rat)/128
Failed ❌ on exp=60, sig=8: got none, expected some (1 : Rat)/16
Failed ❌ on exp=60, sig=9: got none, expected some (9 : Rat)/128
Failed ❌ on exp=60, sig=10: got none, expected some (5 : Rat)/64
Failed ❌ on exp=60, sig=11: got none, expected some (11 : Rat)/128
Failed ❌ on exp=60, sig=12: got none, expected some (3 : Rat)/32
Failed ❌ on exp=60, sig=13: got none, expected some (13 : Rat)/128
Failed ❌ on exp=60, sig=14: got none, expected some (7 : Rat)/64
Failed ❌ on exp=60, sig=15: got none, expected some (15 : Rat)/128
Failed ❌ on exp=61, sig=0: got none, expected some 0
Failed ❌ on exp=61, sig=1: got none, expected some (1 : Rat)/64
Failed ❌ on exp=61, sig=2: got none, expected some (1 : Rat)/32
Failed ❌ on exp=61, sig=3: got none, expected some (3 : Rat)/64
Failed ❌ on exp=61, sig=4: got none, expected some (1 : Rat)/16
Failed ❌ on exp=61, sig=5: got none, expected some (5 : Rat)/64
Failed ❌ on exp=61, sig=6: got none, expected some (3 : Rat)/32
Failed ❌ on exp=61, sig=7: got none, expected some (7 : Rat)/64
Failed ❌ on exp=61, sig=8: got none, expected some (1 : Rat)/8
Failed ❌ on exp=61, sig=9: got none, expected some (9 : Rat)/64
Failed ❌ on exp=61, sig=10: got none, expected some (5 : Rat)/32
Failed ❌ on exp=61, sig=11: got none, expected some (11 : Rat)/64
Failed ❌ on exp=61, sig=12: got none, expected some (3 : Rat)/16
Failed ❌ on exp=61, sig=13: got none, expected some (13 : Rat)/64
Failed ❌ on exp=61, sig=14: got none, expected some (7 : Rat)/32
Failed ❌ on exp=61, sig=15: got none, expected some (15 : Rat)/64
Failed ❌ on exp=62, sig=0: got none, expected some 0
Failed ❌ on exp=62, sig=1: got none, expected some (1 : Rat)/32
Failed ❌ on exp=62, sig=2: got none, expected some (1 : Rat)/16
Failed ❌ on exp=62, sig=3: got none, expected some (3 : Rat)/32
Failed ❌ on exp=62, sig=4: got none, expected some (1 : Rat)/8
Failed ❌ on exp=62, sig=5: got none, expected some (5 : Rat)/32
Failed ❌ on exp=62, sig=6: got none, expected some (3 : Rat)/16
Failed ❌ on exp=62, sig=7: got none, expected some (7 : Rat)/32
Failed ❌ on exp=62, sig=8: got none, expected some (1 : Rat)/4
Failed ❌ on exp=62, sig=9: got none, expected some (9 : Rat)/32
Failed ❌ on exp=62, sig=10: got none, expected some (5 : Rat)/16
Failed ❌ on exp=62, sig=11: got none, expected some (11 : Rat)/32
Failed ❌ on exp=62, sig=12: got none, expected some (3 : Rat)/8
Failed ❌ on exp=62, sig=13: got none, expected some (13 : Rat)/32
Failed ❌ on exp=62, sig=14: got none, expected some (7 : Rat)/16
Failed ❌ on exp=62, sig=15: got none, expected some (15 : Rat)/32
Failed ❌ on exp=63, sig=0: got none, expected some 0
Failed ❌ on exp=63, sig=1: got none, expected some (1 : Rat)/16
Failed ❌ on exp=63, sig=2: got none, expected some (1 : Rat)/8
Failed ❌ on exp=63, sig=3: got none, expected some (3 : Rat)/16
Failed ❌ on exp=63, sig=4: got none, expected some (1 : Rat)/4
Failed ❌ on exp=63, sig=5: got none, expected some (5 : Rat)/16
Failed ❌ on exp=63, sig=6: got none, expected some (3 : Rat)/8
Failed ❌ on exp=63, sig=7: got none, expected some (7 : Rat)/16
Failed ❌ on exp=63, sig=8: got none, expected some (1 : Rat)/2
Failed ❌ on exp=63, sig=9: got none, expected some (9 : Rat)/16
Failed ❌ on exp=63, sig=10: got none, expected some (5 : Rat)/8
Failed ❌ on exp=63, sig=11: got none, expected some (11 : Rat)/16
Failed ❌ on exp=63, sig=12: got none, expected some (3 : Rat)/4
Failed ❌ on exp=63, sig=13: got none, expected some (13 : Rat)/16
Failed ❌ on exp=63, sig=14: got none, expected some (7 : Rat)/8
Failed ❌ on exp=63, sig=15: got none, expected some (15 : Rat)/16
foo
-/
#guard_msgs in #eval show IO Unit from do
  let E : Nat := 5
  let S : Nat := 3
  let ExpWidth := exponentWidth E S
  let SigWidth := S + 1

  for expVal in [0:Nat.pow 2 ExpWidth] do
    for sigVal in [0:Nat.pow 2 SigWidth] do
      let uf : UnpackedFloat ExpWidth SigWidth :=
        { sign := false,
          ex := BitVec.ofNat ExpWidth expVal,
          sig := BitVec.ofNat SigWidth sigVal }
      let packed := EUnpackedFloat.pack (e := E) (s := S) (EUnpackedFloat.mkNumber uf)
      if packed.isNorm then
        let rounded := EUnpackedFloat.round (targetExponentWidth := E) (targetSignificandWidth := S) uf RoundingMode.RNE
        let expected := EUnpackedFloat.mkNumber uf
        if rounded ≠ expected then
          IO.println s!"Failed ❌ on exp={expVal}, sig={sigVal}: got {repr rounded.toRat?}, expected {repr expected.toRat?}"
        else
          IO.println "Succeeded ✅"

  IO.println "foo"

theorem round_idem' (uf : UnpackedFloat 6 4)
    (huf : (EUnpackedFloat.pack (e := 5) (s := 3) (EUnpackedFloat.mkNumber uf)).isNorm) :
    (EUnpackedFloat.round (targetExponentWidth := 5) (targetSignificandWidth := 3) uf RoundingMode.RNE) = EUnpackedFloat.mkNumber uf := by
  bv_normalize
  -- simp_all
  -- bv_decide
  sorry

theorem round_idem (uf : UnpackedFloat (exponentWidth e s) (s + 1))
    (huf : (EUnpackedFloat.pack (e := e) (s := s) (EUnpackedFloat.mkNumber uf)).isNorm) :
    EUnpackedFloat.round  uf RoundingMode.RNE == EUnpackedFloat.mkNumber uf := by
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
