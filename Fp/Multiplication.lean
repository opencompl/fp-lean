import Fp.Basic
import Fp.UnpackedRound
import Fp.Rounding

@[bv_normalize]
def UnpackedFloat.mul (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (2 * s) :=
  let sigProd := x.sig.setWidth' (by omega) * y.sig.setWidth' (by omega)
  {
    sign := x.sign ^^ y.sign
    -- Exponent guaranteed to fit in e+1 bits (no overflow):
    -- max: (2^(e-1) - 1) + (2^(e-1) - 1) + 1 = 2^e - 1 < 2^e
    -- min: -2^(e-1) + -2^(e-1) + 0 = -2^e
    -- Optimization: consider using `Bitvec.adc`
    ex := x.ex.signExtend (e + 1) + y.ex.signExtend (e + 1) + (BitVec.ofBool sigProd.msb).setWidth' (by omega)
    -- If product in range [2,4) (i.e., 1x...x), then it is already normalized.
    -- If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
    sig := sigProd <<< BitVec.ofBool !sigProd.msb
  }

@[bv_normalize]
def EUnpackedFloat.mul (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isNaN || y.isNaN || x.isInfinite && y.isZero || y.isInfinite && x.isZero then
    mkNaN
  else bif x.isInfinite || y.isInfinite then
    mkInfinity (x.num.sign ^^ y.num.sign)
  else bif x.isZero || y.isZero then
    mkZero (x.num.sign ^^ y.num.sign)
  else
    UnpackedFloat.round (.mul x.num y.num) m

namespace PackedFloat

@[bv_normalize]
def mul (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.mul m x.unpack y.unpack).pack

instance : Mul (PackedFloat e s) where
  mul := .mul .RNE

@[bv_normalize]
theorem PackedFloat.mul_def {x y : PackedFloat e s} : x * y = PackedFloat.mul .RNE x y := rfl

end PackedFloat

/-- info: some 16 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 8 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 10 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 5 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 4 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 2 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 2 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 1 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some 1 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 * PackedFloat.ofRat 5 2 .RNE 2 1).toRat?
/-- info: some (1 / 4) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 * PackedFloat.ofRat 5 2 .RNE 1 2).toRat?
/-- info: some (1 / 8) -/
#guard_msgs in #eval (PackedFloat.ofRat 5 2 .RNE 1 2 * PackedFloat.ofRat 5 2 .RNE 1 4).toRat?
