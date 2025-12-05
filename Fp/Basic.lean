import Fp.Utils

/-!
## Packed Floating Point Numbers

This is a test module description
-/
/-
inductive Sign : Type
| Positive : Sign
| Negative : Sign
deriving DecidableEq, Repr
-/

/--
A packed floating point number,
whose exponent and significand width are encoded at the type level.
-/
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit. -/
    sign : Bool
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Significand (mantissa) of the packed float. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr

instance : Repr (PackedFloat exWidth sigWidth) where
  reprPrec x _prec :=
    f!"\{ sign := {if x.sign then "-" else "+"}, ex := {x.ex}, sig := {x.sig} }"


/--
A fixed point number with specified exponent offset.
-/
structure FixedPoint (width exOffset : Nat) where
    sign : Bool
    val : BitVec width
    hExOffset : exOffset < width
deriving DecidableEq

instance : Repr (FixedPoint width ExOffset) where
  reprPrec (x : FixedPoint _ _) _prec :=
    f!"{if x.sign then "-" else "+"} {x.val}"

-- Concretely, any enum we have must look like a C enum, so we must flatten
-- all our state into a single enum.

/--
The "state" of an extended fixed-point number: either NaN, infinity, or a
number.
-/
inductive State : Type
| NaN : State
| Infinity : State
| Number : State
deriving DecidableEq

instance : Repr State where
  reprPrec s _prec :=
    match s with
    | .NaN => "NaN"
    | .Infinity => "∞"
    | .Number => "num"

/--
A fixed point number extended with infinity and NaN.
-/
structure EFixedPoint (width exOffset : Nat) where
  state : State
  num : FixedPoint width exOffset
deriving DecidableEq, Repr

namespace FixedPoint

def toRat (a : FixedPoint w e) : Rat :=
  let n := a.val.toNat
  (-1)^(a.sign.toNat) * (n : Rat) / (2 ^ e : Rat)

@[simp, bv_float_normalize]
def equal (a b : FixedPoint w e) : Bool :=
  (a.val == 0#_ && b.val == 0#_)
  || (a.sign == b.sign && a.val == b.val)

@[bv_float_normalize]
theorem injEq (a b : FixedPoint w e)
  : (a = b) = (a.sign = b.sign ∧ a.val = b.val) := by
  cases a
  cases b
  simp only [mk.injEq]

theorem inj (a b : FixedPoint w e)
  : (a.sign = b.sign ∧ a.val = b.val) → (a = b) := by
  intro h
  simp_all only [← injEq]

theorem equal_refl (a : FixedPoint w e)
  : (a.equal a) = true := by
  simp [FixedPoint.equal]

theorem equal_comm (a b : FixedPoint w e)
  : (a.equal b) = (b.equal a) := by
  simp [equal, Bool.beq_comm]
  ac_nf

@[simp, bv_float_normalize]
def expand (a : FixedPoint w e) (w' e' : Nat)
  (he : e' ≥ e) (hw : w' + e ≥ w + e')
  : FixedPoint w' e' where
  sign := a.sign
  val := a.val.setWidth' (by omega) <<< (e' - e)
  hExOffset := by
    have hExOffset' := a.hExOffset
    omega

end FixedPoint

namespace EFixedPoint
@[bv_float_normalize]
theorem injEq (a b : EFixedPoint w e)
  : (a = b) = (a.state = b.state ∧ a.num.sign = b.num.sign ∧ a.num.val = b.num.val)
    := by
  cases a
  cases b
  simp only [FixedPoint.injEq, mk.injEq]

theorem inj (a b : EFixedPoint w e)
  : (a.state = b.state ∧ a.num.sign = b.num.sign ∧ a.num.val = b.num.val)
      → (a = b) := by
  intro h
  simp_all only [← injEq]

@[simp, bv_float_normalize]
def getNaN (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .NaN
  num := {
    sign := False
    val := 0
    hExOffset
  }

/-- Get a fixed-point number from the extended format. -/
def getFixedPoint (fixed : FixedPoint exWidth sigWidth) : EFixedPoint exWidth sigWidth where
  state := .Number
  num := fixed

-- Sign = true ↔ negative
@[simp, bv_float_normalize]
def getInfinity (sign : Bool) (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Infinity
  num := {
    sign
    val := 0
    hExOffset
  }

@[simp, bv_float_normalize]
def zero (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Number
  num := {
    sign := False
    val := 0
    hExOffset
  }

/--
Floating point equality test.
Recall that `NaN ≠ Nan` under the floating point semantics.
-/
@[simp, bv_float_normalize]
def equal (a b : EFixedPoint w e) : Bool :=
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number && a.num.equal b.num)

@[simp, bv_float_normalize]
def equal_or_nan (a b : EFixedPoint w e) : Bool :=
  a.state = .NaN || b.state = .NaN || a.equal b

/--
Floating point equality test,
where we check up to denotation. So, under this definition:
- NaN = Nan iff the states are both Nan.
- +Infinity = +Infinity, -Infinity = -Infinity.
- Number equality is reflexive.
-/
@[simp, bv_float_normalize]
def equal_denotation (a b : EFixedPoint w e) : Bool :=
  (a.state = .NaN && b.state = .NaN) ||
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number &&
   a.num.sign == b.num.sign && a.num.val == b.num.val)

@[simp, bv_float_normalize]
def isNaN (a : EFixedPoint w e) : Bool :=
  a.state = .NaN

@[simp, bv_float_normalize]
def isZero (a : EFixedPoint w e) : Bool :=
  a.state = .Number && a.num.val == 0

@[simp, bv_float_normalize]
def expand (a : EFixedPoint w e) (w' e' : Nat)
  (he : e' ≥ e) (hw : w' + e ≥ w + e')
  : EFixedPoint w' e' where
  state := a.state
  num := a.num.expand w' e' he hw

/--
Returns the maximum (magnitude) value for the given sign.
-/
@[simp, bv_float_normalize]
def getMax (w e : Nat) (sign : Bool) (he : e < w)
  : EFixedPoint w e where
  state := .Number
  num := FixedPoint.mk
    sign
    (BitVec.allOnes w)
    (by omega)


end EFixedPoint

namespace PackedFloat

/--
Returns the "canonical" NaN for the given floating point format. For example,
the canonical NaN for `exWidth = 3` and `sigWidth = 4` is `0.111.1000`.
-/
@[simp, bv_float_normalize]
def getNaN (exWidth sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := False
  ex := BitVec.allOnes exWidth
  sig := BitVec.ofNat sigWidth (2 ^ (sigWidth - 1))

/--
Returns the infinity value of the specified sign for the given floating point
format.
-/
@[simp, bv_float_normalize]
def getInfinity (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth
  sig := 0

/--
Returns the (positive) zero value for the given floating point format.
-/
@[simp, bv_float_normalize]
def getZero (exWidth sigWidth : Nat)
  : PackedFloat exWidth sigWidth where
  sign := False
  ex := 0
  sig := 0

/--
Returns the maximum (magnitude) value for the given sign.
-/
@[simp, bv_float_normalize]
def getMax (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth - 1
  sig := BitVec.allOnes sigWidth

@[bv_float_normalize]
theorem injEq (a b : PackedFloat e s)
  : (a = b) = (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) := by
  cases a
  cases b
  simp [mk.injEq]

theorem inj (a b : PackedFloat e s)
  : (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) → (a = b) := by
  intro h
  simp_all only [← injEq]

@[simp, bv_float_normalize]
def isInfinite (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig == 0

@[simp, bv_float_normalize]
def isNaN (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig != 0

@[simp, bv_float_normalize]
def isNormOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex != BitVec.allOnes e

@[simp, bv_float_normalize]
def isZeroOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex == 0

@[simp, bv_float_normalize]
def isZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0

@[simp, bv_float_normalize]
def isNZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0 && pf.sign

@[simp, bv_float_normalize]
def isPZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0 && !pf.sign

@[simp, bv_float_normalize]
def isSignMinus (pf : PackedFloat e s) : Bool :=
  pf.sign

/--
Returns the `PackedFloat` representation for the given `BitVec`.
-/
@[simp, bv_float_normalize]
def ofBits (e s : Nat) (b : BitVec (1+e+s)) : PackedFloat e s where
  sign := b.msb
  ex := (b >>> s).truncate e
  sig := b.truncate s

/--
Returns the `BitVec` representation for the given `PackedFloat`.
-/
@[simp, bv_float_normalize]
def toBits (x : PackedFloat e s) : BitVec (1+e+s) :=
  BitVec.ofBool x.sign ++ x.ex ++ x.sig

/--
Convert from a packed float to a fixed point number.

Conversion function assumes IEEE compliance. For output `FixedPoint` number to
have a non-degenerate exponent offset, we need two or more bits in the
exponent.

NOTE: Assuming IEEE compliance, you technically only need 2^e + s - 2 bits to
cover the entire range of representable values.
-/
@[bv_float_normalize]
def toEFixed (pf : PackedFloat e s)
  -- | Why is it '- 2'?
  : EFixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2) :=
  let hExOffset := toEFixed_hExOffset e s
  if pf.isNaN then EFixedPoint.getNaN hExOffset --   pf.ex == BitVec.allOnes e && pf.sig != 0 (pf.sign can be anything.)
  else if pf.isInfinite then EFixedPoint.getInfinity pf.sign hExOffset -- pf.ex == BitVec.allOnes e && pf.sig == 0
  else {
    state := .Number
    num := {
      sign := pf.sign
      val :=
        -- If the value is zero/subnormal, then we append a leading '0' bit to 'pf.sig'.
        -- Otherwise, we append a leading '1' bit to 'pf.sig', which is the representation of
        -- 1.<significand> for regular numbers, and 0.<significand> for denormal numbers.
        let unshifted : BitVec (1+s) :=
          (BitVec.ofBool !pf.isZeroOrSubnorm) ++ pf.sig;
        -- If the exponent is zero, let's think about IEEE floating point.
        -- exponent = 8bit, manitssa = 23 bit.
        -- When exponent is zero, we are representing subnormal numbers.
        -- so this is 2^-126 * 0.mantissa
        -- This is <mantissa> * 2^-126 * 2^-23 = 2^-(126 + 23) * <mantissa>
        -- Now, 126 + 23 = (128 - 2) + 23 = (2^(8-1) - 2) + 23.
        -- When exponent is 0, then we don't shift.
        -- When exponent is nonzero, then we shift by exponent minus one.
        -- For example, when exponent is 1, then the number is 1.<mantissa>, so we shift by 0.
        let shiftAmt : BitVec e := if pf.ex = 0 then 0 else pf.ex - 1
        -- When shift amount is zero, then see that we produce the number
        -- mantissa * 2^(128 + 23)
        -- which is indeed what we want.
        let hs : 1 + s <= 2^e + s := by
          exact Nat.add_le_add_right Nat.one_le_two_pow s
        -- now that we have the value, shift by the shift amount, which could at most shift by '2^e - 1'.
        -- we shift left to counteract the bias that comes from 2 ^ (e - 1) + s - 2.
        let out : BitVec (2^e + s) := (BitVec.setWidth' (w := 2^e + s) hs (unshifted)) <<< shiftAmt -- could shift by 2^e.
        out
      hExOffset := hExOffset
    }
  }

/--
Build a PackedFloat from an EFixedPoint.
NOTE: This does not play well with bv_decide,
but is purely for reasoning.
Hence, we mark this noncomputable.
-/
noncomputable def ofEFixed (x : EFixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2))
  : PackedFloat e s :=
  sorry

theorem toEFixed_ofEFixed (x : EFixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2))
  : (ofEFixed x).toEFixed = x := by
  sorry

@[simp, bv_float_normalize]
def equal_denotation (a b : PackedFloat e s) : Bool :=
  (a.sign == b.sign && a.ex == b.ex && a.sig == b.sig) ||
  (a.isNaN && b.isNaN)

theorem isNumber_of_isNormOrSubnorm (a : PackedFloat e s)
  : a.isNormOrSubnorm → a.toEFixed.state = .Number := by
  simp_all [toEFixed]

end PackedFloat

namespace ExamplesE5M2
-- Constants

/-- E5M2 floating point representation of 1.0 -/
@[bv_float_normalize]
def oneE5M2       : PackedFloat 5 2 := PackedFloat.ofBits 5 2 0b00111100#8

def oneE5M2Fixed  : EFixedPoint 34 16 := oneE5M2.toEFixed
/-- E5M2 floating point representation of 2.0 -/
@[bv_float_normalize]
def twoE5M2       := PackedFloat.ofBits 5 2 0b01000000#8
/-- Smallest (positive) normal number in E5M2 floating point. -/
@[bv_float_normalize]
def minNormE5M2   := PackedFloat.ofBits 5 2 0b00000100#8
/-- Smallest (positive) subnormal number in E5M2 floating point. -/
@[bv_float_normalize]
def minSubnormE5M2 := PackedFloat.ofBits 5 2 0b00000001#8

/-- info: { sign := +, ex := 0x0f#5, sig := 0x0#2 } -/
#guard_msgs in #eval (repr oneE5M2)

/-- info: 65536#34 -/ -- 1 << 16
#guard_msgs in #eval (oneE5M2Fixed.num.val)



/-- info: { state := num, num := + 0x000010000#34 } -/
#guard_msgs in #eval (repr oneE5M2Fixed)

/-- info: { sign := +, ex := 0x1f#5, sig := 0x2#2 } -/
#guard_msgs in #eval (PackedFloat.getNaN 5 2)
/-- info: { state := num, num := + 0x000010000#34 } -/
#guard_msgs in #eval oneE5M2.toEFixed
/-- info: { state := num, num := + 0x000000001#34 } -/
#guard_msgs in #eval minSubnormE5M2.toEFixed
/-- info: { state := num, num := + 0x000000004#34 } -/
#guard_msgs in #eval minNormE5M2.toEFixed

/-
- (@bollu's thought): We may like to have `FixedPoint.toRat : FixedPoint → ℚ`, which
  interprets the FP as a rational.
-/

end ExamplesE5M2

namespace ExamplesE3M2

/-#
https://en.wikipedia.org/wiki/Single-precision_floating-point_format

MAXEXP = 2^8 - 1 = 256 - 1 = 255
MAXEXP//2 = 127


0 is reserved for subnomrmals, 255 is reserved for inf and NaNs.
range is [1-127, 254-127] =  [-126, 127].

exponent all zeroes = subnormal numbers and zero.
exponent all ones = infinities and NaNs.

When exponent is 0, equation is:           (-1)^sign * 2^(-MAXEXP//2+1)) * 0.fraction
When exponent is nonzero, equation is:     (-1)^sign * 2^(exponent-MAXEXP//2) * 1.fraction
When exponent is all1s:                    if fraction is zero, then infinity, else NaN.
-/

/-#

In E3M2, we have:
MAXEXP = 2^3 - 1 = 8 - 1 = 7
MAXEXP//2 = 7 // 2 = 3

0 is reserved for subnomrmals, 7 is reserved for inf and NaNs.
range is [1-3, 6-3] =  [-2, 3].

exponent all zeroes = subnormal numbers and zero.
exponent all ones = infinities and NaNs.
-/

def pf0 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000000#6)
/-- info: { sign := +, ex := 0x0#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf0)
/-- info: { state := num, num := + 0x000#10 } -/
#guard_msgs in #eval pf0.toEFixed
/-- info: 0 -/
#guard_msgs in #eval pf0.toEFixed.num.toRat

def pf1 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000001#6)
/-- info: { sign := +, ex := 0x0#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf1)
/-- info: { state := num, num := + 0x001#10 } -/
#guard_msgs in #eval pf1.toEFixed
/-- info: 1 / 16 -/
#guard_msgs in #eval pf1.toEFixed.num.toRat
-- pf1: since exponent is zero, value is subnormal. Value is 2^-2 * 0.01 = 1/16.


def pf2 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000010#6)
/-- info: { sign := +, ex := 0x0#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf2)
/-- info: { state := num, num := + 0x002#10 } -/
#guard_msgs in #eval pf2.toEFixed
/-- info: 1 / 8 -/
#guard_msgs in #eval pf2.toEFixed.num.toRat
-- pf2: since exponent is zero, value is subnormal. Value is 2^-2 * 0.10 = 2/16 = 1/8.

def pf3 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000011#6)
/-- info: { sign := +, ex := 0x0#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf3)
/-- info: { state := num, num := + 0x003#10 } -/
#guard_msgs in #eval pf3.toEFixed
/-- info: 3 / 16 -/
#guard_msgs in #eval pf3.toEFixed.num.toRat
-- pf3: since exponent is zero, value is subnormal. Value is 2^-2 * 0.11 = 3/16.


def pf4 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000100#6)
/-- info: { sign := +, ex := 0x1#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf4)
/-- info: { state := num, num := + 0x004#10 } -/
#guard_msgs in #eval pf4.toEFixed
/-- info: 1 / 4 -/
#guard_msgs in #eval pf4.toEFixed.num.toRat
-- pf4: since exponent is nonzero, value is normal. Value is 2^(1-3) * 1.00 = 1/4.

def pf5 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000101#6)
/-- info: { sign := +, ex := 0x1#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf5)
/-- info: { state := num, num := + 0x005#10 } -/
#guard_msgs in #eval pf5.toEFixed
/-- info: 5 / 16 -/
#guard_msgs in #eval pf5.toEFixed.num.toRat
-- pf5: since exponent is nonzero, value is normal. Value is 2^(1-3) * 1.01 = 5/16.

def pf6 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000110#6)
/-- info: { sign := +, ex := 0x1#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf6)
/-- info: { state := num, num := + 0x006#10 } -/
#guard_msgs in #eval pf6.toEFixed
/-- info: 3 / 8 -/
#guard_msgs in #eval pf6.toEFixed.num.toRat
-- pf6: since exponent is nonzero, value is normal. Value is 2^(1-3) * 1.10 = 6/16 = 3/8.

def pf7 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b000111#6)
/-- info: { sign := +, ex := 0x1#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf7)
/-- info: { state := num, num := + 0x007#10 } -/
#guard_msgs in #eval pf7.toEFixed
/-- info: 7 / 16 -/
#guard_msgs in #eval pf7.toEFixed.num.toRat
-- pf7: since exponent is nonzero, value is normal. Value is 2^(1-3) * 1.11 = 7/16.

def pf8 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001000#6)
/-- info: { sign := +, ex := 0x2#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf8)
/-- info: { state := num, num := + 0x008#10 } -/
#guard_msgs in #eval pf8.toEFixed
/-- info: 1 / 2 -/
#guard_msgs in #eval pf8.toEFixed.num.toRat
-- pf8: since exponent is nonzero, value is normal. Value is 2^(2-3) * 1.00 = 1/2.

def pf9 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001001#6)
/-- info: { sign := +, ex := 0x2#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf9)
/-- info: { state := num, num := + 0x00a#10 } -/
#guard_msgs in #eval pf9.toEFixed
/-- info: 5 / 8 -/
#guard_msgs in #eval pf9.toEFixed.num.toRat
-- pf9: since exponent is nonzero, value is normal. Value is 2^(2-3) * 1.01 = 5/8.

def pf10 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001010#6)
/-- info: { sign := +, ex := 0x2#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf10)
/-- info: { state := num, num := + 0x00c#10 } -/
#guard_msgs in #eval pf10.toEFixed
/-- info: 3 / 4 -/
#guard_msgs in #eval pf10.toEFixed.num.toRat
-- pf10: since exponent is nonzero, value is normal. Value is 2^(2-3) * 1.10 = 2^-1 * (1 + 2/4) = 2^(-1) * 6/4 = 3/4.

def pf11 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001011#6)
/-- info: { sign := +, ex := 0x2#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf11)
/-- info: { state := num, num := + 0x00e#10 } -/
#guard_msgs in #eval pf11.toEFixed
/-- info: 7 / 8 -/
#guard_msgs in #eval pf11.toEFixed.num.toRat
-- pf11: since exponent is nonzero, value is normal. Value is 2^(2-3) * 1.11 = 2^-1 * (7/4) = 7/8.

def pf12 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001100#6)
/-- info: { sign := +, ex := 0x3#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf12)
/-- info: { state := num, num := + 0x010#10 } -/
#guard_msgs in #eval pf12.toEFixed
/-- info: 1 -/
#guard_msgs in #eval pf12.toEFixed.num.toRat

def pf13 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001101#6)
/-- info: { sign := +, ex := 0x3#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf13)
/-- info: { state := num, num := + 0x014#10 } -/
#guard_msgs in #eval pf13.toEFixed
/-- info: 5 / 4 -/
#guard_msgs in #eval pf13.toEFixed.num.toRat

def pf14 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001110#6)
/-- info: { sign := +, ex := 0x3#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf14)
/-- info: { state := num, num := + 0x018#10 } -/
#guard_msgs in #eval pf14.toEFixed
/-- info: 3 / 2 -/
#guard_msgs in #eval pf14.toEFixed.num.toRat


def pf15 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b001111#6)
/-- info: { sign := +, ex := 0x3#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf15)
/-- info: { state := num, num := + 0x01c#10 } -/
#guard_msgs in #eval pf15.toEFixed
/-- info: 7 / 4 -/
#guard_msgs in #eval pf15.toEFixed.num.toRat

def pf16 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010000#6)
/-- info: { sign := +, ex := 0x4#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf16)
/-- info: { state := num, num := + 0x020#10 } -/
#guard_msgs in #eval pf16.toEFixed
/-- info: 2 -/
#guard_msgs in #eval pf16.toEFixed.num.toRat

def pf17 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010001#6)
/-- info: { sign := +, ex := 0x4#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf17)
/-- info: { state := num, num := + 0x028#10 } -/
#guard_msgs in #eval pf17.toEFixed
/-- info: 5 / 2 -/
#guard_msgs in #eval pf17.toEFixed.num.toRat

def pf18 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010010#6)
/-- info: { sign := +, ex := 0x4#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf18)
/-- info: { state := num, num := + 0x030#10 } -/
#guard_msgs in #eval pf18.toEFixed
/-- info: 3 -/
#guard_msgs in #eval pf18.toEFixed.num.toRat

def pf19 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010011#6)
/-- info: { sign := +, ex := 0x4#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf19)
/-- info: { state := num, num := + 0x038#10 } -/
#guard_msgs in #eval pf19.toEFixed
/-- info: 7 / 2 -/
#guard_msgs in #eval pf19.toEFixed.num.toRat

def pf20 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010100#6)
/-- info: { sign := +, ex := 0x5#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf20)
/-- info: { state := num, num := + 0x040#10 } -/
#guard_msgs in #eval pf20.toEFixed
/-- info: 4 -/
#guard_msgs in #eval pf20.toEFixed.num.toRat

def pf21 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010101#6)
/-- info: { sign := +, ex := 0x5#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf21)
/-- info: { state := num, num := + 0x050#10 } -/
#guard_msgs in #eval pf21.toEFixed
/-- info: 5 -/
#guard_msgs in #eval pf21.toEFixed.num.toRat

def pf22 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010110#6)
/-- info: { sign := +, ex := 0x5#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf22)
/-- info: { state := num, num := + 0x060#10 } -/
#guard_msgs in #eval pf22.toEFixed
/-- info: 6 -/
#guard_msgs in #eval pf22.toEFixed.num.toRat

def pf23 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b010111#6)
/-- info: { sign := +, ex := 0x5#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf23)
/-- info: { state := num, num := + 0x070#10 } -/
#guard_msgs in #eval pf23.toEFixed
/-- info: 7 -/
#guard_msgs in #eval pf23.toEFixed.num.toRat

def pf24 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011000#6)
/-- info: { sign := +, ex := 0x6#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf24)
/-- info: { state := num, num := + 0x080#10 } -/
#guard_msgs in #eval pf24.toEFixed
/-- info: 8 -/
#guard_msgs in #eval pf24.toEFixed.num.toRat


def pf25 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011001#6)
/-- info: { sign := +, ex := 0x6#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf25)
/-- info: { state := num, num := + 0x0a0#10 } -/
#guard_msgs in #eval pf25.toEFixed
/-- info: 10 -/
#guard_msgs in #eval pf25.toEFixed.num.toRat

def pf26 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011010#6)
/-- info: { sign := +, ex := 0x6#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf26)
/-- info: { state := num, num := + 0x0c0#10 } -/
#guard_msgs in #eval pf26.toEFixed
/-- info: 12 -/
#guard_msgs in #eval pf26.toEFixed.num.toRat

def pf27 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011011#6)
/-- info: { sign := +, ex := 0x6#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf27)
/-- info: { state := num, num := + 0x0e0#10 } -/
#guard_msgs in #eval pf27.toEFixed
/-- info: 14 -/
#guard_msgs in #eval pf27.toEFixed.num.toRat

def pf28 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011100#6)
/-- info: { sign := +, ex := 0x7#3, sig := 0x0#2 } -/
#guard_msgs in #eval (repr pf28)
/-- info: { state := ∞, num := + 0x000#10 } -/
#guard_msgs in #eval pf28.toEFixed
/-- info: 0 -/
#guard_msgs in #eval pf28.toEFixed.num.toRat


def pf29 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011101#6)
/-- info: { sign := +, ex := 0x7#3, sig := 0x1#2 } -/
#guard_msgs in #eval (repr pf29)
/-- info: { state := NaN, num := + 0x000#10 } -/
#guard_msgs in #eval pf29.toEFixed
/-- info: 0 -/
#guard_msgs in #eval pf29.toEFixed.num.toRat

def pf30 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011110#6)
/-- info: { sign := +, ex := 0x7#3, sig := 0x2#2 } -/
#guard_msgs in #eval (repr pf30)
/-- info: { state := NaN, num := + 0x000#10 } -/
#guard_msgs in #eval pf30.toEFixed
/-- info: 0 -/
#guard_msgs in #eval pf30.toEFixed.num.toRat


def pf31 : PackedFloat 3 2 := PackedFloat.ofBits 3 2 (0b011111#6)
/-- info: { sign := +, ex := 0x7#3, sig := 0x3#2 } -/
#guard_msgs in #eval (repr pf31)
/-- info: { state := NaN, num := + 0x000#10 } -/
#guard_msgs in #eval pf31.toEFixed
/-- info: 0 -/
#guard_msgs in #eval pf31.toEFixed.num.toRat

end ExamplesE3M2
