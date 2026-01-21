import Fp.Basic
import Fp.UnpackedRound

def UnpackedFloat.add (sign : Bool) (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  -- Compute absolute exponent difference to determine significant shift amount.
  let expDiff : BitVec (e + 1)  := x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1)
  let absExpDiff := bif expDiff.msb then -expDiff else expDiff
  -- Determine the smaller number whose significant we are going to shift.
  let (x, y) := bif expDiff.msb || absExpDiff == 0 && x.sig.ult y.sig then (y, x) else (x, y)
  -- Extend by 1 bit to the left to account for overflow and two bits to the right to account for
  -- round and sticky bits.
  let xSig := x.sig.setWidth' (by omega) ++ 0#2
  let ySig := y.sig.setWidth' (by omega) ++ 0#2
  -- Reuse the same circuit for both addition and subtraction by negating the smaller significant.
  -- Note: we always treat significants as unsigned integers. However, we make an exception here
  -- to reuse the same adder circuit for both addition and subtraction.
  let ySig := bif x.sign == y.sign then ySig else -ySig
  -- Cap the right shift at `s + 3` in case `absExpDiff` is too big.
  let shiftAmount := bif absExpDiff.ult (s + 3) then absExpDiff.setWidth (s + 3) else (s + 3)
  -- Note: we use signed shift for `ySig` here to preserve its sign since it's now a signed integer.
  let sigSum : BitVec (s + 3) := xSig + ySig.sshiftRight' shiftAmount
  -- Sticky bit depends on bits we lose when we right shift `ySig` and `sigSum` (in case of an overflow).
  let sticky := ySig &&& shiftAmount.orderEncode != 0 || sigSum.msb && sigSum.getLsb 0
  let sumResult :=
    {
      -- Sign of sum is sign of the bigger number!
      sign := x.sign
      -- Exponent of sum is exponent of bigger number (`+1` if there is an overflow).
      ex := x.ex.signExtend (e + 1) + (BitVec.ofBool sigSum.msb).setWidth' (by omega)
      -- Renormalize `sigSum` if there is an overflow.
      sig := (sigSum >>> BitVec.ofBool sigSum.msb ||| (BitVec.ofBool sticky).setWidth' (by omega)).truncate (s + 2)
    }
  bif sigSum == 0 then
    -- Full cancellation: return zero. This case could have been merged with the second branch if not
    -- for the sign, which depends on the rounding mode.
    .mkZero sign
  else bif !sigSum.getMsb 0 && !sigSum.getMsb 1 then
    -- Catastrophic cancellation: we have to normalize.
    sumResult.normalize
  else
    sumResult

def EUnpackedFloat.add (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isZero && !y.isZero then
    y
  else bif !x.isZero && y.isZero then
    x
  else bif x.isNaN || y.isNaN || x.isInfinite && y.isInfinite && x.sign != y.sign then
    .mkNaN
  else bif x.isInfinite && y.isInfinite && x.sign == y.sign ||
           x.isInfinite && !y.isInfinite || !x.isInfinite && y.isInfinite then
    .mkInfinity (bif x.isInfinite then x.sign else y.sign)
  else bif x.isZero && y.isZero then
    .mkZero (bif m == .RTN then x.sign || y.sign else x.sign && y.sign)
  else
    UnpackedFloat.round (.add (m == .RTN) x.num y.num) m

namespace PackedFloat

def add (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.add m x.unpack y.unpack).pack

instance : Add (PackedFloat e s) where
  add := .add .RNE

end PackedFloat

/-- info: ExtRat.Number (-1 : Rat)/16384 -/
#guard_msgs in #eval (PackedFloat.ofBits 5 2 0b10000100#8).toExtRat
/-- info: ExtRat.Number (5 : Rat)/8192 -/
#guard_msgs in #eval (PackedFloat.ofBits 5 2 0b00010001#8).toExtRat

/-- info: 9 / 16384 -/
#guard_msgs in #eval (-1 : Rat)/16384 + (5 : Rat)/8192

/-- info: ExtRat.Number (1 : Rat)/2048 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 9 16384).toExtRat

/-- info: ExtRat.Number (5 : Rat)/8192 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNA 9 16384).toExtRat

/-- info: ExtRat.Number (1 : Rat)/2048 -/
#guard_msgs in #eval (PackedFloat.add .RNE (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat
/-- info: ExtRat.Number (5 : Rat)/8192 -/
#guard_msgs in #eval (PackedFloat.add .RNA (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat

/-- info: ExtRat.Infinity true -/
#guard_msgs in #eval (PackedFloat.add .RNE (PackedFloat.ofBits 5 2 0b11111100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat
/-- info: ExtRat.Infinity false -/
#guard_msgs in #eval (PackedFloat.add .RNE (PackedFloat.ofBits 5 2 0b01111100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat
