import Fp.Comparison
import Fp.Negation
import Fp.UnpackedRound

namespace UnpackedFloat

variable {e s : Nat}

/-- Signed exponent difference (widened by one bit) — used to pick the larger operand and the shift. -/
@[bv_normalize]
def addExpDiff (x y : UnpackedFloat e s) : BitVec (e + 1) :=
  x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1)

/-- Absolute exponent difference. -/
@[bv_normalize]
def addAbsExpDiff (x y : UnpackedFloat e s) : BitVec (e + 1) :=
  bif (addExpDiff x y).msb then -(addExpDiff x y) else addExpDiff x y

/-- The circuit swaps operands so the first is the larger; this is that condition. -/
@[bv_normalize]
def addSwapCond (x y : UnpackedFloat e s) : Bool :=
  (addExpDiff x y).msb || ((addAbsExpDiff x y == 0) && x.sig.ult y.sig)

/-- Post-swap larger operand (the circuit's rebound `x`). -/
@[bv_normalize]
def addBig (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif addSwapCond x y then y else x

/-- Post-swap smaller operand (the circuit's rebound `y`). -/
@[bv_normalize]
def addSmall (x y : UnpackedFloat e s) : UnpackedFloat e s :=
  bif addSwapCond x y then x else y

/-- Larger significand, extended (1 overflow bit on the left, 2 round/sticky bits on the right). -/
@[bv_normalize]
def addXSig (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  (addBig x y).sig.setWidth' (by grind) ++ 0#2

/-- Smaller significand, similarly extended and negated when the signs differ (so one adder serves
both addition and subtraction). -/
@[bv_normalize]
def addYSig (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  bif (addBig x y).sign == (addSmall x y).sign
    then (addSmall x y).sig.setWidth' (by grind) ++ 0#2
    else -((addSmall x y).sig.setWidth' (by grind) ++ 0#2)

/-- Right-shift amount for alignment, capped at `s + 3`. -/
@[bv_normalize]
def addShiftAmount (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  bif (addAbsExpDiff x y).ult (s + 3) then (addAbsExpDiff x y).setWidth (s + 3) else (s + 3)

/-- The aligned (signed) significand sum. -/
@[bv_normalize]
def addSigSum (x y : UnpackedFloat e s) : BitVec (s + 3) :=
  addXSig x y + (addYSig x y).sshiftRight' (addShiftAmount x y)

/-- Sticky bit: set if the alignment shift dropped a nonzero bit, or an overflow folded a bit out. -/
@[bv_normalize]
def addSticky (x y : UnpackedFloat e s) : Bool :=
  (addYSig x y &&& (addShiftAmount x y).orderEncode != 0)
    || ((addSigSum x y).msb && (addSigSum x y)[0])

/-- The pre-normalisation result (sign of the larger; exponent bumped on overflow; significand
right-shifted on overflow). -/
@[bv_normalize]
def addSum (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  { sign := (addBig x y).sign
    ex := (addBig x y).ex.signExtend (e + 1) + (BitVec.ofBool (addSigSum x y).msb).setWidth' (by grind)
    sig := ((addSigSum x y) >>> BitVec.ofBool (addSigSum x y).msb).truncate (s + 2) }

/-- Normalised result: on catastrophic cancellation (`!sum.sig.msb`) renormalise. -/
@[bv_normalize]
def addNormSum (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  bif !(addSum x y).sig.msb then (addSum x y).normalize else (addSum x y)

/-- Floating-point addition. The intermediates are the named `add*` definitions above (each marked
`@[bv_normalize]` so `bv_decide` still flattens the whole circuit, and so proofs can `unfold` the
circuit one layer at a time). The sticky bit is OR-ed into the bottom bit at the very end, after
normalisation. -/
@[bv_normalize]
def add (x y : UnpackedFloat e s) : UnpackedFloat (e + 1) (s + 2) :=
  { addNormSum x y with
    sig := (addNormSum x y).sig ||| (BitVec.ofBool (addSticky x y)).setWidth' (by grind) }

end UnpackedFloat

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
    (UnpackedFloat.add x.num y.num) |>.blastSmtLibRound e s m
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
