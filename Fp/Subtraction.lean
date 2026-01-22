import Fp.Addition
import Fp.Negation

def UnpackedFloat.sub (sign : Bool) (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  .add sign x y.neg

def EUnpackedFloat.sub (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isZero && !y.isZero then
    y.neg
  else bif !x.isZero && y.isZero then
    x
  else bif x.isNaN || y.isNaN || x.isInfinite && y.isInfinite && x.sign == y.sign then
    .mkNaN
  else bif x.isInfinite && y.isInfinite && x.sign != y.sign ||
           x.isInfinite && !y.isInfinite || !x.isInfinite && y.isInfinite then
    .mkInfinity (bif x.isInfinite then x.sign else !y.sign)
  else bif x.isZero && y.isZero then
    .mkZero (bif m == .RTN then x.sign || !y.sign else x.sign && !y.sign)
  else
    UnpackedFloat.round (.sub (m == .RTN) x.num y.num) m

namespace PackedFloat

def sub (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.sub m x.unpack y.unpack).pack

instance : Sub (PackedFloat e s) where
  sub := .sub .RNE

end PackedFloat

/-- info: ExtRat.Number (-1 : Rat)/16384 -/
#guard_msgs in #eval (PackedFloat.ofBits 5 2 0b10000100#8).toExtRat
/-- info: ExtRat.Number (5 : Rat)/8192 -/
#guard_msgs in #eval (PackedFloat.ofBits 5 2 0b00010001#8).toExtRat

/-- info: -11 / 16384 -/
#guard_msgs in #eval (-1 : Rat)/16384 - (5 : Rat)/8192

/-- info: ExtRat.Number (-3 : Rat)/4096 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE (-11) 16384).toExtRat

/-- info: ExtRat.Number (-3 : Rat)/4096 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNA (-11) 16384).toExtRat

/-- info: ExtRat.Number (-3 : Rat)/4096 -/
#guard_msgs in #eval (PackedFloat.sub .RNE (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat
/-- info: ExtRat.Number (-3 : Rat)/4096 -/
#guard_msgs in #eval (PackedFloat.sub .RNA (PackedFloat.ofBits 5 2 0b10000100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat

/-- info: ExtRat.Infinity true -/
#guard_msgs in #eval (PackedFloat.sub .RNE (PackedFloat.ofBits 5 2 0b11111100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat
/-- info: ExtRat.Infinity false -/
#guard_msgs in #eval (PackedFloat.sub .RNE (PackedFloat.ofBits 5 2 0b01111100#8) (PackedFloat.ofBits 5 2 0b00010001#8)).toExtRat
