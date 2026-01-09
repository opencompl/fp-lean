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

def BitVec.extendAtMsb (x : BitVec w) (δ : Nat) : BitVec (δ + w) :=
  0#δ ++ x

/-- Extract from the MSB, starting at msb 'hi', going downward for 'len' bits. -/
def BitVec.extractMsb' (x : BitVec w) (hi : Nat) (len : Nat) : BitVec len :=
  x.extractLsb' (w - (hi + len)) len

@[simp]
theorem BitVec.getMsbD_extractMsb' {w hi len} (h : hi + len ≤ w) (x : BitVec w) (hi' : i < len) :
  (x.extractMsb' hi len).getMsbD i = (x.getMsbD (hi + i)) := by
  simp [extractMsb', BitVec.getMsbD_eq_getLsbD]
  grind


-- https://github.com/martin-cs/symfpu/blob/aeaa3fa62730148c855f5a9e0a9b7040d48e0b7e/core/rounder.h#L299
@[bv_normalize]
def EUnpackedFloat.round {expWidth sigWidth : Nat} {targetExponentWidth targetSignificandWidth : Nat}
  (inUf : EUnpackedFloat expWidth sigWidth) (mode : RoundingMode)
  (hs : sigWidth >= targetSignificandWidth + 2) (he : expWidth >= targetExponentWidth)
  (hs' : sigWidth >= 1) :
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
  let exp := inUf.exp

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
  let extractedSignificand : BitVec (targetSignificandWidth + 1) :=
    ((sig.extractMsb' 0 targetSignificandWidth).extendAtMsb 1).cast (by omega)
/-
  // Normal guard and sticky bits
  bwt guardBitPosition(sigWidth - (targetSignificandWidth + 1));
  prop guardBit(sig.extract(guardBitPosition, guardBitPosition).isAllOnes());
-/
  let guardBitPosition : Nat := sigWidth - (targetSignificandWidth + 1)
  let guardBit : Bool := sig.getLsbD guardBitPosition
/-
  prop stickyBit(!sig.extract(guardBitPosition - 1,0).isAllZeros());
-/
  let stickyBit : Bool := (sig.extractLsb guardBitPosition 0) ≠ BitVec.ofNat (guardBitPosition + 1) 0
/-
  // For subnormals, locating the guard and stick bits is a bit more involved
  //sbv subnormalAmount(uf.getSubnormalAmount(format)); // Catch is, uf isn't in the given format, so this doesn't work
  sbv subnormalAmount(expandingSubtract<t>(unpackedFloat<t>::minNormalExponent(format).matchWidth(exp),exp));
  INVARIANT((subnormalAmount < sbv(expWidth + 1, sigWidth - 1)) || earlyUnderflow);
-/
  sorry
