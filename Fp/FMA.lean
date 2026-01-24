import Fp.Addition
import Fp.Convert
import Fp.Multiplication

def UnpackedFloat.fma (sign : Bool) (x y z : UnpackedFloat e s) : UnpackedFloat (e + 2) (2 * s + 2) :=
  -- TODO: the renormalization step in `UnpackedFloat.add` requires `e + 2` to be large enough
  -- to store `-(2 ^ (e + 1) + 2 * s + 1)`. Is the `e` we get here from `exponentWidth` in
  -- `EUnpackedFloat.fma` large enough for the following inequality to hold?
  -- `-(2 ^ (e + 1) + 2 * s + 1) ≥ -2 ^ (e + 2)`
  -- After Substituting for `e` and `s`, we get:
  -- `-(2 ^ (exponentWidth e s + 1) + 2 * (s + 1) + 1) ≥ -2 ^ (exponentWidth e s + 2)`
  -- It seems to hold for up to `1000` bits.
  UnpackedFloat.add sign (UnpackedFloat.mul x y) (z.extendWidths (by omega) (by omega))

def EUnpackedFloat.fma (m : RoundingMode) (x y z : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  let xySign := x.num.sign ^^ y.num.sign
  -- Some of the cases below are subtle. So, we cannot simply copy the cases from `mul` and `add`.
  -- Nesting the conditions helps us navigate the cases and ensure that we covered all of them.
  bif x.isNaN || y.isNaN || x.isInfinite && y.isZero || y.isInfinite && x.isZero then
    mkNaN
  else bif x.isInfinite || y.isInfinite then
    bif z.isNaN || z.isInfinite && xySign != z.sign then
      mkNaN
    else
      mkInfinity xySign
  else bif x.isZero || y.isZero then
    bif z.isNaN then
      mkNaN
    else bif z.isInfinite then
      mkInfinity z.sign
    else bif z.isZero then
      -- Follow addition rules for the sign of an exact `0`.
      mkZero (bif m == .RTN then xySign || z.sign else xySign && z.sign)
    else
      -- No rounding is needed here!
      z
  else
    bif z.isNaN then
      mkNaN
    else bif z.isInfinite then
      mkInfinity z.sign
    else bif z.isZero then
      -- Since `x` and `y` are not `0`, their exact product is also not `0`. However,
      -- the product *could* round to `0`. Use the rounding sign in this case!
      UnpackedFloat.round (.mul x.num y.num) m
    else
      -- None of `x`, `y`, `x * y`, and `z` is an exact `0`. However, `x * y + z` could
      -- *still* be exactly `0`! We must follow addition rules for sign of `0` in that case.
      -- If, however, `x * y + z` rounds to `0`, then we must return the sign of `x * y + z`.
      -- Since `UnpackedFloat.mul` always returns exact results and `UnpackedFloat.add`
      -- returns exact results when the exponents are the same (what happens when `expDiff` is `1`?),
      -- So, we can leave it to `UnpackedFloat.add` to give the right sign to the resulting `0`.
      -- TODO: why not just check if `x * y == -z` (and similarly for addition)?
      UnpackedFloat.round (.fma (m == .RTN) x.num y.num z.num) m

def PackedFloat.fma (m : RoundingMode) (x y z : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.fma m x.unpack y.unpack z.unpack).pack
