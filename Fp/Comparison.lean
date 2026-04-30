import Fp.Basic
import Fp.Unpacking

namespace UnpackedFloat

@[bv_normalize]
def bltAux (xLTyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bif x.sign && y.sign then
    BitVec.slt y.ex x.ex ||
    y.ex == x.ex && BitVec.ult y.sig x.sig
  else bif x.sign && !y.sign then
    xLTyOnDiffZeros || !x.isZero || !y.isZero
  else bif !x.sign && y.sign then
    xLTyOnDiffZeros && x.isZero && y.isZero
  else
    BitVec.slt x.ex y.ex ||
    x.ex == y.ex && BitVec.ult x.sig y.sig

@[bv_normalize]
def bleAux (xLEyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bif x.sign && y.sign then
    BitVec.slt y.ex x.ex ||
    y.ex == x.ex && BitVec.ule y.sig x.sig
  else bif x.sign && !y.sign then
    xLEyOnDiffZeros || !x.isZero || !y.isZero
  else bif !x.sign && y.sign then
    xLEyOnDiffZeros && x.isZero && y.isZero
  else
    BitVec.slt x.ex y.ex ||
    x.ex == y.ex && BitVec.ule x.sig y.sig

@[bv_normalize]
def structBeq (x y : UnpackedFloat e s) : Bool :=
  x.sign == y.sign && x.ex == y.ex && x.sig == y.sig

@[bv_normalize]
def beq (x y : UnpackedFloat e s) : Bool :=
  x.isZero && y.isZero ||
  x.sign == y.sign && x.ex == y.ex && x.sig == y.sig

@[bv_normalize]
def bgeAux (xGEyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bleAux (!xGEyOnDiffZeros) y x

@[bv_normalize]
def bgtAux (xGTyOnDiffZeros : Bool) (x y : UnpackedFloat e s) : Bool :=
  bltAux (!xGTyOnDiffZeros) y x

@[bv_normalize]
def minAux (xOnDiffZeros : Bool) (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif bgtAux xOnDiffZeros x y then y else x

@[bv_normalize]
def maxAux (xOnDiffZeros : Bool) (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif bltAux xOnDiffZeros x y then y else x

end UnpackedFloat

namespace EUnpackedFloat

@[bv_normalize]
def bltAux (xLTyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN || y.isNaN then
    false
  else bif x.isInfinite || y.isInfinite then
    x.isInfinite && x.sign && (!y.isInfinite || !y.sign) ||
    (!x.isInfinite || x.sign) && y.isInfinite && !y.sign
  else
    UnpackedFloat.bltAux xLTyOnDiffZeros x.num y.num

@[bv_normalize]
def bleAux (xLEyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bif x.isNaN || y.isNaN then
    false
  else bif x.isInfinite || y.isInfinite then
    x.isInfinite && x.sign ||
    y.isInfinite && !y.sign
  else
    UnpackedFloat.bleAux xLEyOnDiffZeros x.num y.num

@[bv_normalize]
def smtBeq (x y : EUnpackedFloat e s) : Bool :=
  x.isNaN && y.isNaN ||
  x.isInfinite && y.isInfinite && x.sign == y.sign ||
  !x.isNaN && !y.isNaN && !x.isInfinite && !y.isInfinite && UnpackedFloat.beq x.num y.num

@[bv_normalize]
def smtBne (x y : EUnpackedFloat e s) : Bool :=
  !smtBeq x y

@[bv_normalize]
def ieeeBeq (x y : EUnpackedFloat e s) : Bool :=
  !x.isNaN && !y.isNaN &&
  (x.isInfinite && y.isInfinite && x.sign == y.sign ||
   !x.isInfinite && !y.isInfinite && UnpackedFloat.beq x.num y.num)

@[bv_normalize]
def bgeAux (xGEyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bleAux (!xGEyOnDiffZeros) y x

@[bv_normalize]
def bgtAux (xGTyOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : Bool :=
  bltAux (!xGTyOnDiffZeros) y x

@[bv_normalize]
def minAux (xOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif x.isNaN || bgtAux xOnDiffZeros x y then y else x

@[bv_normalize]
def maxAux (xOnDiffZeros : Bool) (x y : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif x.isNaN || bltAux xOnDiffZeros x y then y else x

end EUnpackedFloat

namespace PackedFloat

@[bv_normalize]
def bltAux (xLTyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.bltAux xLTyOnDiffZeros x.unpack y.unpack

@[bv_normalize]
def bleAux (xLEyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.bleAux xLEyOnDiffZeros x.unpack y.unpack

@[bv_normalize]
def smtBeq (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.smtBeq x.unpack y.unpack

@[bv_normalize]
def smtBne (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.smtBne x.unpack y.unpack

@[bv_normalize]
def ieeeBeq (x y : PackedFloat e s) : Bool :=
  EUnpackedFloat.ieeeBeq x.unpack y.unpack

@[bv_normalize]
def bgeAux (xGEyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  bleAux (!xGEyOnDiffZeros) y x

@[bv_normalize]
def bgtAux (xGTyOnDiffZeros : Bool) (x y : PackedFloat e s) : Bool :=
  bltAux (!xGTyOnDiffZeros) y x

@[bv_normalize]
def minAux (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.minAux xOnDiffZeros x.unpack y.unpack).pack

@[bv_normalize]
def maxAux (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.maxAux xOnDiffZeros x.unpack y.unpack).pack

@[bv_normalize]
def smtBlt (x y : PackedFloat e s) : Bool :=
  bltAux false x y

@[bv_normalize]
def smtBle (x y : PackedFloat e s) : Bool :=
  bleAux true x y

@[bv_normalize]
def smtBge (x y : PackedFloat e s) : Bool :=
  bgeAux true x y

@[bv_normalize]
def smtBgt (x y : PackedFloat e s) : Bool :=
  bgtAux false x y

@[bv_normalize]
def smtMin (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  minAux xOnDiffZeros x y

@[bv_normalize]
def smtMax (xOnDiffZeros : Bool) (x y : PackedFloat e s) : PackedFloat e s :=
  maxAux xOnDiffZeros x y

def smtIsNeg (x : PackedFloat e s) : Bool :=
  !x.isNaN && x.sign

def smtIsPos (x : PackedFloat e s) : Bool :=
  !x.isNaN && x.sign

end PackedFloat
