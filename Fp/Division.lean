import Fp.Basic
import Fp.Rounding
import Fp.MulInv

/-
PLAN:

1. Prove that the mantissa, exponent value is correct upto some precision for 'div_on_packedFloat'.
2. Axiomatize what the rounder does for this level of precision.
3. Use these to prove that 'div' is correct.
4. Replace rounder with better rounder that doesn't need the expansion to fixed point.
5. Prove that better rounder is correct.
-/


@[bv_normalize]
def f_div (a : FixedPoint v e) (b : FixedPoint w f) : FixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.hExOffset b.hExOffset
  let a' : BitVec (v+w) := a.val.setWidth' (by omega)
  let b' : BitVec (v+w) := b.val.setWidth' (by omega)
  {
    sign := a.sign ^^ b.sign
    -- | TODO: this needs alignment, no?
    val := a' / b'
    hExOffset
  }


/-- Unpacked significand, which will be 1xxxxxx or 0xxxx depending on whether the exponent is zero or not. -/
@[bv_normalize]
def PackedFloat.unpackedSignificand (x : PackedFloat e s) : BitVec (1 + s) :=
  BitVec.ofBool (x.ex ≠ 0) ++ x.sig

/-- Subtract b from a, but return 0 if a ≤ b. Mimics natural number subtraction. -/
def BitVec.monus (a : BitVec w) (b : BitVec w) : BitVec w :=
  if a ≤ b then 0#w else a - b


@[bv_normalize]
def div_on_packedFloat (a b : PackedFloat e s) (mode : RoundingMode) : PackedFloat e s :=
  let sign := a.sign ^^ b.sign
  -- 1.0000 vs 0.0000
  let sig_a := a.unpackedSignificand
  let sig_b := b.unpackedSignificand
  let div_len := 3*(s+1) -- (s + 1) because we add the bit.
  let unit_pos := 2*(s+1)
  -- let dividend := (sig_a.setWidth div_len <<< unit_pos)
  -- let divisor := sig_b.setWidth div_len
  -- Do division, collapse remainder to a single sticky bit
  -- let quot_with_sticky := (dividend / divisor) ++ BitVec.ofBool ((dividend % divisor) ≠ 0)
  -- Calculate shifts
  let divResult := fixedWidthDivideAtPrecision sig_a sig_b (prec := 2 * (s + 1)) (outw := 3 * (s + 1))
  let quot_with_sticky := divResult.quotWithSticky
  let shiftNumerator := if a.ex > 0 then a.ex - 1 else 0
  let shiftDenominator := if b.ex > 0 then b.ex - 1 else 0
  -- Shift and round
  -- | TODO: For the rounding, we still expand out into fixed point.
  -- We should instead use the cleverer rounder.
  if shiftNumerator ≥ shiftDenominator then
    let quot_lshift : EFixedPoint (2^e+div_len+1) (unit_pos+1) := {
      state := .Number
      num := {
        sign
        -- numerator is larger than denominator, so multiply by the correct amount.
        val := quot_with_sticky.setWidth _ <<< (shiftNumerator - shiftDenominator)
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right]
          apply Nat.lt_add_left
          omega
      }
    }
    round _ _ mode quot_lshift
  else
    let quot_rshift : EFixedPoint (2^e+div_len+1) (2^e+unit_pos+1) := {
      state := .Number
      num := {
        sign
        -- denominator is larger than numerator, so divide by the correct amount, but first increase the
        -- exponent to (2^e), so that the round function rounds correctly.
        -- TODO: understand the bounds on our rounding.
        val := (quot_with_sticky.setWidth _ <<< 2^e) >>> (shiftDenominator - shiftNumerator)
        hExOffset := by
          rewrite [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_left]
          omega
      }
    }
    round _ _ mode quot_rshift

/-
  // x and y are fixed-point numbers in the range [1,2)
  // Compute o \in [0.5,2), r \in [0,\delta) such that:  x = o*y + r
  // Return (o, r != 0)
  template <class t>
  resultWithRemainderBit<t> fixedPointDivide (const typename t::ubv &x, const typename t::ubv &y) {
    typename t::bwt w(x.getWidth());

    // Same width and both have MSB ones
    PRECONDITION(y.getWidth() == w);
    PRECONDITION(x.extract(w - 1, w - 1).isAllOnes());
    PRECONDITION(y.extract(w - 1, w - 1).isAllOnes());

    typedef typename t::ubv ubv;

    // Not the best way of doing this but pretty universal
    ubv ex(x.append(ubv::zero(w - 1)));
    ubv ey(y.extend(w - 1));

    ubv div(ex / ey);
    ubv rem(ex % ey);

    return resultWithRemainderBit<t>(div.extract(w - 1, 0), !(rem.isAllZeros()));
  }
-/
-- Does the single extra bit matter? Isn't it way better to just write 'w + w'?
-- I'm not 100% sure, but it does feel off to me.
def fixed_point_divide (x : BitVec w) (y : BitVec w)  : (BitVec (w-1) × Bool) :=
  -- PRECONDITION(x.extract(w - 1, w - 1).isAllOnes());
  -- PRECONDITION(y.extract(w - 1, w - 1).isAllOnes());
  let ex : BitVec (w + (w - 1)) := x ++ BitVec.ofNat (w - 1) 0
  let ey : BitVec (w + (w - 1)) := y.zeroExtend _ -- TODO: check that I need zeroExtend and not signExtend here.
  let div : BitVec (w + (w - 1)) := ex / ey
  let rem : BitVec (w + (w - 1)) := ex % ey
  (div.extractLsb' 0 (w - 1), rem ≠ 0)

  -- let ex : BitVec (2*w - 1) := a ++ 0#(w - 1)
  -- let ey : BitVec (2*w - 1) := b.extend (w - 1)
  -- let div : BitVec (2*w - 1) := ex / ey
  -- let rem : BitVec (2*w - 1) := ex % ey
  -- (div.extract (w - 2) 0, ¬ rem.isAllZeros)

/-

 template <class t>
  unpackedFloat<t> arithmeticDivide (const typename t::fpt &format,
				       const unpackedFloat<t> &left,
				       const unpackedFloat<t> &right) {
  typedef typename t::bwt bwt;
  typedef typename t::prop prop;
  typedef typename t::ubv ubv;
  typedef typename t::sbv sbv;
  //typedef typename t::fpt fpt;

  PRECONDITION(left.valid(format));
  PRECONDITION(right.valid(format));

  // Compute sign
  prop divideSign(left.getSign() ^ right.getSign());

  // Divide the significands
  // We need significandWidth() + 1 bits in the result but the top one may cancel, so add two bits
  ubv extendedNumerator(left.getSignificand().append(ubv::zero(2)));
  ubv extendedDenominator(right.getSignificand().append(ubv::zero(2)));

  resultWithRemainderBit<t> divided(fixedPointDivide<t>(extendedNumerator, extendedDenominator));


  bwt resWidth(divided.result.getWidth());
  ubv topBit(divided.result.extract(resWidth - 1, resWidth - 1));
  ubv nextBit(divided.result.extract(resWidth - 2, resWidth - 2));

  // Alignment of inputs means at least one of the two MSB is 1
  //  i.e. [1,2) / [1,2) = [0.5,2)
  // Top bit is set by the first round of the divide and thus is 50/50 1 or 0
  prop topBitSet(topBit.isAllOnes());
  INVARIANT(topBitSet || nextBit.isAllOnes());
  INVARIANT(topBitSet == (left.getSignificand() >= right.getSignificand()));

  // Re-align
  ubv alignedSignificand(conditionalLeftShiftOne<t>(!topBitSet, divided.result)); // Will not loose information

  // Subtract up exponents
  // Optimisation : use the if-then-lazy-else to avoid dividing for underflow and overflow
  //                subnormal / greater-than-2^sigwidth does not need to be evaluated
  sbv alignedExponent(expandingSubtractWithBorrowIn<t>(left.getExponent(),right.getExponent(), !topBitSet));

  // Create the sticky bit, it is important that this is after alignment
  ubv finishedSignificand(alignedSignificand | ubv(divided.remainderBit).extend(resWidth - 1));

  // Put back together
  unpackedFloat<t> divideResult(divideSign, alignedExponent, finishedSignificand);

  sbv min(unpackedFloat<t>::minSubnormalExponent(format));
  sbv max(unpackedFloat<t>::maxNormalExponent(format));
  sbv divideResultExponentUpperBound(expandingSubtractWithBorrowIn<t>(max, min, false));
  sbv divideResultExponentLowerBound(expandingSubtractWithBorrowIn<t>(min, max, true));  // -1 for renormalisation of the top bit

  POSTCONDITION(divideResult.wellFormed(divideResultExponentLowerBound, divideResultExponentUpperBound));

  // A brief word about formats.
  // Most operations adding one bit to the exponent format is enough to represent the result.
  // +1 is sufficient in almost all cases.  However:
  //    very large normal / very small subnormal
  // can have an exponent greater than very large normal * 2 ( + 1)
  // because the exponent range is asymmetric with more subnormal than normal.

  return divideResult;
 }
-/

/--
Multiplication of two extended fixed-point numbers.
-/
@[bv_normalize]
def e_div (a : EFixedPoint v e) (b : EFixedPoint w f) : EFixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.num.hExOffset b.num.hExOffset
  open EFixedPoint in
  if hN : a.state = .NaN || b.state = .NaN ||
      (a.state = .Infinity && b.state = .Infinity) ||
      (a.isZero && b.isZero) then getNaN hExOffset
  else if hI1 : a.state = .Infinity || b.isZero  then
    getInfinity (a.num.sign ^^ b.num.sign) hExOffset
  else if h2 : b.state = .Infinity then
    getZero (a.num.sign ^^ b.num.sign) hExOffset
  else
    let _ : a.state = .Number && b.state = .Number := by
      cases ha : a.state <;> cases hb : b.state <;> simp_all
    {
      state := .Number
      num := f_div a.num b.num
    }

/--
Division of two floating-point numbers, rounded to a floating point number
using the provided rounding mode.
-/
@[bv_normalize]
def div (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  div_on_packedFloat a b m
