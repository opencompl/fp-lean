import Fp.Addition
import Fp.Negation

@[bv_normalize]
def UnpackedFloat.sub (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  .add x y.neg

@[bv_normalize]
def EUnpackedFloat.sub (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  EUnpackedFloat.add m x y.neg

namespace PackedFloat

@[bv_normalize]
def sub (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.sub m x.unpack y.unpack).pack

instance : Sub (PackedFloat e s) where
  sub := .sub .RNE

@[bv_normalize]
theorem PackedFloat.sub_def {x y : PackedFloat e s} : x - y = PackedFloat.sub .RNE x y := rfl

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
