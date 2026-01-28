import Fp.Comparison
import Fp.Negation
import Fp.UnpackedRound

@[bv_normalize]
def UnpackedFloat.add (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
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
  let sticky := ySig &&& shiftAmount.orderEncode != 0 || sigSum.msb && sigSum[0]
  let sum : UnpackedFloat (e + 1) (s + 2) :=
    {
      -- Sign of sum is sign of the bigger number!
      sign := x.sign
      -- Exponent of sum is exponent of bigger number (`+1` if there is an overflow).
      ex := x.ex.signExtend (e + 1) + (BitVec.ofBool sigSum.msb).setWidth' (by omega)
      -- Renormalize `sigSum` if there is an overflow.
      sig := (sigSum >>> BitVec.ofBool sigSum.msb).truncate (s + 2)
    }
  -- If a catastrophic cancellation occured, we have to normalize. In case the sum is `0` (i.e., full
  -- cancellation), the sign depends on the rounding mode.
  let normSum := bif !sum.sig.msb then sum.normalize else sum
  -- Sticky bit is independent of normalization: add it at the very end.
  { normSum with sig := normSum.sig ||| (BitVec.ofBool sticky).setWidth' (by omega) }

@[bv_normalize]
theorem Prod.fst_cond_eq_cond_fst {t e : α × β} : (bif b then t else e).fst = bif b then t.fst else e.fst :=
  Bool.apply_cond Prod.fst

@[bv_normalize]
theorem Prod.snd_cond_eq_cond_snd {t e : α × β} : (bif b then t else e).snd = bif b then t.snd else e.snd :=
  Bool.apply_cond Prod.snd

@[bv_normalize]
def EUnpackedFloat.add (m : RoundingMode) (x y : EUnpackedFloat (exponentWidth e s) (s + 1))
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif x.isNaN || y.isNaN || x.isInfinite && y.isInfinite && x.sign != y.sign then
    .mkNaN
  else bif x.isInfinite && y.isInfinite && x.sign == y.sign ||
           x.isInfinite && !y.isInfinite || !x.isInfinite && y.isInfinite then
    .mkInfinity (bif x.isInfinite then x.sign else y.sign)
  else bif UnpackedFloat.structBeq x.num y.num.neg then
    -- Sum is exactly `0`: follow the special sign rules for `0`.
    -- Even if both `x` and `y` are `0`, their signs are still different. So, we don't
    -- need to propegate the sign!
    .mkZero (m == .RTN)
  else bif x.isZero then
    y
  else bif y.isZero then
    x
  else
    UnpackedFloat.round (.add x.num y.num) m

namespace PackedFloat

@[bv_normalize]
def add (m : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
  (EUnpackedFloat.add m x.unpack y.unpack).pack

instance : Add (PackedFloat e s) where
  add := .add .RNE

@[bv_normalize]
theorem PackedFloat.add_def {x y : PackedFloat e s} : x + y = PackedFloat.add .RNE x y := rfl

end PackedFloat

-- Minor cancellation with rounding

/-- info: ExtRat.Number (5 : Rat)/64 -/
#guard_msgs in #eval (PackedFloat.ofBits 3 4 0b00000101).toExtRat
/-- info: ExtRat.Number -2 -/
#guard_msgs in #eval (PackedFloat.ofBits 3 4 0b11000000).toExtRat
/-- info: -123 / 64 -/
#guard_msgs in #eval (5 : Rat)/64 + -2
/-- info: ExtRat.Number (-31 : Rat)/16 -/
#guard_msgs in #eval (PackedFloat.ofRat 3 4 .RNE (-123) 64).toExtRat
/-- info: ExtRat.Number (-31 : Rat)/16 -/
#guard_msgs in #eval (PackedFloat.add .RNE (PackedFloat.ofBits 3 4 0b00000101) (PackedFloat.ofBits 3 4 0b11000000)).toExtRat

-- Minor cancellation without rounding

/-- info: ExtRat.Number (5 : Rat)/64 -/
#guard_msgs in #eval (PackedFloat.ofBits 3 4 0b00000101).toExtRat
/-- info: ExtRat.Number -4 -/
#guard_msgs in #eval (PackedFloat.ofBits 3 4 0b11010000).toExtRat
/-- info: -251 / 64 -/
#guard_msgs in #eval (5 : Rat)/64 + -4
/-- info: ExtRat.Number (-31 : Rat)/8 -/
#guard_msgs in #eval (PackedFloat.ofRat 3 4 .RNE (-251) 64).toExtRat
/-- info: ExtRat.Number (-31 : Rat)/8 -/
#guard_msgs in #eval (PackedFloat.add .RNE (PackedFloat.ofBits 3 4 0b00000101) (PackedFloat.ofBits 3 4 0b11010000)).toExtRat

-- Rounding Modes

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
