import Fp.Addition
import Fp.Convert
import Fp.Multiplication

@[bv_normalize]
def UnpackedFloat.fma (x y z : UnpackedFloat e s) : UnpackedFloat (e + 2) (2 * s + 2) :=
  -- TODO: the renormalization step in `UnpackedFloat.add` requires `e + 2` to be large enough
  -- to store `-(2 ^ (e + 1) + 2 * s + 1)`. Is the `e` we get here from `exponentWidth` in
  -- `EUnpackedFloat.fma` large enough for the following inequality to hold?
  -- `-(2 ^ (e + 1) + 2 * s + 1) ≥ -2 ^ (e + 2)`
  -- After Substituting for `e` and `s`, we get:
  -- `-(2 ^ (exponentWidth e s + 1) + 2 * (s + 1) + 1) ≥ -2 ^ (exponentWidth e s + 2)`
  -- It seems to hold for up to `1000` bits.
  UnpackedFloat.add (UnpackedFloat.mul x y) (z.extendWidths (by omega) (by omega))

@[bv_normalize]
def EUnpackedFloat.fma (m : RoundingMode) (x y z : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  let xySign := x.num.sign ^^ y.num.sign
  -- Some of the cases below are subtle. So, we cannot simply copy the cases from `mul` and/or `add`.
  bif x.isNaN || y.isNaN || z.isNaN || x.isInfinite && y.isZero || y.isInfinite && x.isZero ||
      (x.isInfinite || y.isInfinite) && z.isInfinite && xySign != z.sign then
    mkNaN
  else bif x.isInfinite || y.isInfinite || z.isInfinite then
    mkInfinity (bif z.isInfinite then z.sign else xySign)
  else bif (x.isZero || y.isZero) && z.isZero then
    -- Result of the operation is an exact `0`. So, the sign depends on whether or not the signs agree.
    -- If they agree, return the input sign. Otherwise, return the sign according to the rounding mode.
    mkZero (bif xySign == z.sign then z.sign else m == .RTN)
  else bif x.isZero || y.isZero then
    z
  else bif z.isZero then
    (UnpackedFloat.mul x.num y.num) |>.blastSmtLibRound e s  m
  else bif UnpackedFloat.structBeq (.mul x.num y.num) (z.num.neg.extendWidths (by omega) (by omega)) then
    -- None of `x`, `y`, `x * y`, and `z` is an exact `0`. However, `x * y + z` is
    -- *still* exactly `0`! We must follow addition rules for sign of `0` in that case.
    -- Since `UnpackedFloat.mul` always returns exact results and extending ex/sig widths
    -- also returns exact results, we can directly check if `x * y == -z`.
    -- Note: this case can absorb the other `mkZero` case above (with a simpler sign!).
    -- However, we keep it seperate as it's more expensive to check.
    mkZero (m == .RTN)
  else
    (UnpackedFloat.fma x.num y.num z.num) |>.blastSmtLibRound e s m

@[bv_normalize]
def PackedFloat.fma (m : RoundingMode) (x y z : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.fma m x.unpack y.unpack z.unpack).pack
