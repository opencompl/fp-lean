import Fp.Basic
import Fp.UnpackedRound
import Fp.Rounding

def UnpackedFloat.div (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  -- Extend sig width by 2 bits to account for two things:
  -- - Potential normalization at first, then
  -- - Guard and sticky bits after normalization.
  -- `x.sig / y.sig` is either `0` or `1`. Multiply `x.sig` by `2 ^ (s + 1)` to get
  -- `s + 2` bits of precision from the division.
  let divident : BitVec (s + 2 + (s + 1)) := x.sig.setWidth' (by omega) ++ 0#(s + 1)
  let divisor : BitVec (s + 2 + (s + 1)) := y.sig.setWidth' (by omega)
  -- Optimization: have `quotrem` circuit
  let quot := (divident / divisor).truncate (s + 2)
  let rem := divident % divisor
  {
    sign := x.sign ^^ y.sign
    -- Exponent guaranteed to fit in e+1 bits (no overflow):
    -- max: (2^(e-1) - 1) - -2^(e-1) - 0 = 2^e - 1 < 2^e
    -- min: -2^(e-1) - (2^(e-1) - 1) - 1 = -2^e
    -- `BitVec.adc` optimization does not seem to work here.
    ex := x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1) - (BitVec.ofBool !quot.msb).setWidth' (by omega)
    -- If quotient in range [1,2)  (i.e., 1x...x), then it is already normalized.
    -- If quotient in range [.5,1) (i.e., 01x..x), then normalize by shifting left once.
    -- Add sticky bit to lsb of significant for rounding
    sig := (quot <<< BitVec.ofBool !quot.msb) ||| (BitVec.ofBool (rem != 0)).setWidth' (by omega)
  }

def EUnpackedFloat.div (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isNaN || y.isNaN || x.isInfinite && y.isInfinite || x.isZero && y.isZero then
    mkNaN
  else bif x.isInfinite || y.isZero then
    mkInfinity (x.num.sign ^^ y.num.sign)
  else bif x.isZero || y.isInfinite then
    mkZero (x.num.sign ^^ y.num.sign)
  else
    UnpackedFloat.round (.div x.num y.num) m

namespace PackedFloat

def div (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.div m x.unpack y.unpack).pack

instance : Div (PackedFloat e s) where
  div := .div .RNE

end PackedFloat

/-- info: some 4 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 8 1 / PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some (5 / 2) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 5 1 / PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 1 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 2 1 / PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some (1 / 2) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 1 / PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some (1 / 4) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 / PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 1 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 / PackedFloat.ofRat 5 2 .RNE 1 2).toRat?
/-- info: some 2 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 / PackedFloat.ofRat 5 2 .RNE 1 4).toRat?
