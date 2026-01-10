import Fp.Utils
import Fp.ForLean.Dyadic

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
@[ext]
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit. -/
    sign : Bool
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Significand (mantissa) of the packed float. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr, Inhabited

attribute [bv_normalize] PackedFloat.ext_iff

@[bv_normalize]
theorem PackedFloat.ext_iff_beq {x y : PackedFloat exWidth sigWidth}
  : (x == y) = (x.sign == y.sign && x.ex == y.ex && x.sig == y.sig) := by
  cases h : (x == y) <;> simp_all [PackedFloat.ext_iff]

@[bv_normalize]
theorem PackedFloat.bne_to_beq {x y : PackedFloat exWidth sigWidth}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [PackedFloat.ext_iff]

@[bv_normalize]
theorem PackedFloat.eq_cond_sign {x y : PackedFloat exWidth sigWidth} :
  (bif b then x else y).sign = bif b then x.sign else y.sign := by
  cases b <;> rfl

@[bv_normalize]
theorem PackedFloat.eq_cond_ex {x y : PackedFloat exWidth sigWidth} :
  (bif b then x else y).ex = bif b then x.ex else y.ex := by
  cases b <;> rfl

@[bv_normalize]
theorem PackedFloat.eq_cond_sig {x y : PackedFloat exWidth sigWidth} :
  (bif b then x else y).sig = bif b then x.sig else y.sig := by
  cases b <;> rfl

instance : Repr (PackedFloat exWidth sigWidth) where
  reprPrec x _prec :=
    f!"\{ sign := {if x.sign then "-" else "+"}, ex := {x.ex}, sig := {x.sig} }"


/--
A fixed point number with specified exponent offset.
-/
@[ext]
structure FixedPoint (width exOffset : Nat) where
    sign : Bool
    val : BitVec width
    -- | This should not be part of the structure, but a side invariant we keep in mind.
    hExOffset : exOffset < width
deriving DecidableEq

attribute [bv_normalize] FixedPoint.ext_iff

@[bv_normalize]
theorem FixedPoint.ext_iff_beq {x y : FixedPoint width exOffset}
  : (x == y) = (x.sign == y.sign && x.val == y.val) := by
  cases h : (x == y) <;> simp_all [FixedPoint.ext_iff]

@[bv_normalize]
theorem FixedPoint.bne_to_beq {x y : FixedPoint width exOffset}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [FixedPoint.ext_iff]

@[bv_normalize]
theorem FixedPoint.eq_cond_sign {x y : FixedPoint width exOffset} :
  (bif b then x else y).sign = bif b then x.sign else y.sign := by
  cases b <;> rfl

@[bv_normalize]
theorem FixedPoint.eq_cond_val {x y : FixedPoint width exOffset} :
  (bif b then x else y).val = bif b then x.val else y.val := by
  cases b <;> rfl

instance : Repr (FixedPoint width ExOffset) where
  reprPrec (x : FixedPoint _ _) _prec :=
    f!"{if x.sign then "-" else "+"} {x.val}"

-- Concretely, any enum we have must look like a C enum, so we must flatten
-- all our state into a single enum.

/--
The "state" of an extended fixed-point number: either NaN, infinity, or a
number.
-/
@[grind]
inductive State : Type
| NaN : State
| Infinity : State
| Number : State
deriving DecidableEq

attribute [bv_normalize] State.eq_iff_enumToBitVec_eq

@[bv_normalize]
theorem State.beq_iff_enumToBitVec_beq {x y : State}
  : (x == y) = (x.enumToBitVec == y.enumToBitVec) := by
  cases h : (x == y) <;> simp_all [eq_iff_enumToBitVec_eq]

@[bv_normalize]
theorem State.bne_to_beq {x y : State}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [eq_iff_enumToBitVec_eq]

@[bv_normalize]
theorem State.NaN_enumToBitVec_eq : enumToBitVec NaN = 0b00#2 := rfl
@[bv_normalize]
theorem State.Infinity_enumToBitVec_eq : enumToBitVec Infinity = 0b01#2 := rfl
@[bv_normalize]
theorem State.Number_enumToBitVec_eq : enumToBitVec Number = 0b10#2 := rfl

@[bv_normalize]
theorem State.eq_cond_enumToBitVec {x y : State} :
  (bif b then x else y).enumToBitVec = bif b then x.enumToBitVec else y.enumToBitVec := by
  cases b <;> rfl

instance : Repr State where
  reprPrec s _prec :=
    match s with
    | .NaN => "NaN"
    | .Infinity => "∞"
    | .Number => "num"

/--
A fixed point number extended with infinity and NaN.
-/
@[ext]
structure EFixedPoint (width exOffset : Nat) where
  state : State
  num : FixedPoint width exOffset
deriving DecidableEq, Repr

attribute [bv_normalize] EFixedPoint.ext_iff

@[bv_normalize]
theorem EFixedPoint.ext_iff_beq {x y : EFixedPoint width exOffset}
  : (x == y) = (x.state == y.state && x.num == y.num) := by
  cases h : (x == y) <;> simp_all [EFixedPoint.ext_iff]

@[bv_normalize]
theorem EFixedPoint.bne_to_beq {x y : EFixedPoint width exOffset}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [EFixedPoint.ext_iff]

@[bv_normalize]
theorem EFixedPoint.eq_cond_state {x y : EFixedPoint width exOffset} :
  (bif b then x else y).state = bif b then x.state else y.state := by
  cases b <;> rfl

@[bv_normalize]
theorem EFixedPoint.eq_cond_num {x y : EFixedPoint width exOffset} :
  (bif b then x else y).num = bif b then x.num else y.num := by
  cases b <;> rfl

class HExOffset (e : Nat) (m : Nat) where
  h : e < m

instance HExOffsetSucc [hex : HExOffset e m] :
    HExOffset e (m + 1) where
  h := by
    have := hex.h
    omega

instance HExOffsetAdd [hex : HExOffset e m] (k : Nat) :
    HExOffset (e + k) (m + k) where
  h := by
    have := hex.h
    omega

instance HExOffsetDouble [hex : HExOffset e m] :
    HExOffset (e + e) (m + m) where
  h := by
    have := hex.h
    omega

namespace FixedPoint


/-- Build a fixed point number from an integer. -/
def ofInt (i : Int) [HExOffset e m] : FixedPoint m e :=
  {
    sign := i < 0
    val := BitVec.ofNat m (i.natAbs)
    hExOffset := HExOffset.h
  }

/-- Convert a fixed point number to an integer. -/
def toInt [HExOffset e m] (f : FixedPoint m e) : Int :=
  let n := f.val.toNat
  if f.sign then
    -Int.ofNat n
  else
    Int.ofNat n

/-- Truncate a dyadic number to a fixed-point number. -/
def ofDyadic [HExOffset e m] (d : Dyadic) : FixedPoint m e :=
  FixedPoint.ofInt <| (Dyadic.mul d (Dyadic.twoPow e)).toRat.num

/-- Convert a dyadic number to a fixed-point number. -/
def toDyadic {m e} (f : FixedPoint m e) : Dyadic :=
  Dyadic.ofIntWithPrec (f.val.toNat * (signToInt f.sign)) e

/-- Convert a fixed point number into a rational number. -/
def toRat (f : FixedPoint m e) : Rat :=
  f.toDyadic.toRat

@[simp, bv_normalize]
def equal (a b : FixedPoint w e) : Bool :=
  (a.val == 0#_ && b.val == 0#_)
  || (a.sign == b.sign && a.val == b.val)

@[bv_normalize]
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

@[simp, bv_normalize]
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
@[bv_normalize]
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

@[simp, bv_normalize]
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


def toDyadic? (ef : EFixedPoint e s) : Option Dyadic :=
  bif ef.state == .Number then some (ef.num.toDyadic)
  else none

def toRat? (ef : EFixedPoint e s) : Option Rat :=
  ef.toDyadic?.map Dyadic.toRat


-- Sign = true ↔ negative
@[simp, bv_normalize]
def getInfinity (sign : Bool) (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Infinity
  num := {
    sign
    val := 0
    hExOffset
  }

def getZero (sign : Bool) (hExOffset : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Number
  num := {
    sign
    val := 0
    hExOffset
  }

@[simp, bv_normalize]
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
@[simp, bv_normalize]
def equal (a b : EFixedPoint w e) : Bool :=
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number && a.num.equal b.num)

@[simp, bv_normalize]
def equal_or_nan (a b : EFixedPoint w e) : Bool :=
  a.state = .NaN || b.state = .NaN || a.equal b

/--
Floating point equality test,
where we check up to denotation. So, under this definition:
- NaN = Nan iff the states are both Nan.
- +Infinity = +Infinity, -Infinity = -Infinity.
- Number equality is reflexive.
-/
@[simp, bv_normalize]
def equal_denotation (a b : EFixedPoint w e) : Bool :=
  (a.state = .NaN && b.state = .NaN) ||
  (a.state = .Infinity && b.state = .Infinity && a.num.sign == b.num.sign) ||
  (a.state = .Number && b.state = .Number &&
   a.num.sign == b.num.sign && a.num.val == b.num.val)

@[simp, bv_normalize]
def isNaN (a : EFixedPoint w e) : Bool :=
  a.state = .NaN

@[simp, bv_normalize]
def isZero (a : EFixedPoint w e) : Bool :=
  a.state = .Number && a.num.val == 0

@[simp, bv_normalize]
def expand (a : EFixedPoint w e) (w' e' : Nat)
  (he : e' ≥ e) (hw : w' + e ≥ w + e')
  : EFixedPoint w' e' where
  state := a.state
  num := a.num.expand w' e' he hw

end EFixedPoint

namespace PackedFloat


/--
Returns the "canonical" NaN for the given floating point format. For example,
the canonical NaN for `exWidth = 3` and `sigWidth = 4` is `0.111.1000`.
-/
@[simp, bv_normalize]
def getNaN (exWidth sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := False
  ex := BitVec.allOnes exWidth
  sig := BitVec.ofNat sigWidth (2 ^ (sigWidth - 1))

/--
Returns the infinity value of the specified sign for the given floating point
format.
-/
@[simp, bv_normalize]
def getInfinity (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth
  sig := 0

/--
Returns the (positive) zero value for the given floating point format.
-/
@[simp, bv_normalize]
def getZero (exWidth sigWidth : Nat)
  : PackedFloat exWidth sigWidth where
  sign := False
  ex := 0
  sig := 0

/--
Returns the maximum (magnitude) value for the given sign.
-/
@[simp, bv_normalize]
def getMax (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth - 1
  sig := BitVec.allOnes sigWidth

@[bv_normalize]
theorem injEq (a b : PackedFloat e s)
  : (a = b) = (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) := by
  cases a
  cases b
  simp [mk.injEq]

theorem inj (a b : PackedFloat e s)
  : (a.sign = b.sign ∧ a.ex = b.ex ∧ a.sig = b.sig) → (a = b) := by
  intro h
  simp_all only [← injEq]

@[simp, bv_normalize]
def isNorm (pf : PackedFloat e s) : Bool :=
  pf.ex != BitVec.allOnes e && pf.ex != 0

@[simp, bv_normalize]
def isSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex != BitVec.allOnes e && pf.sig != 0

@[simp, bv_normalize]
def isInfinite (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig == 0

@[simp, bv_normalize]
def isNaN (pf : PackedFloat e s) : Bool :=
  pf.ex == BitVec.allOnes e && pf.sig != 0

@[simp, bv_normalize]
def isNormOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex != BitVec.allOnes e

@[simp, bv_normalize]
def isZeroOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex == 0

@[simp, bv_normalize]
def isZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0

@[simp, bv_normalize]
def isNZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0 && pf.sign

@[simp, bv_normalize]
def isPZero (pf : PackedFloat e s) : Bool :=
  pf.ex == 0 && pf.sig == 0 && !pf.sign

@[simp, bv_normalize]
def isSignMinus (pf : PackedFloat e s) : Bool :=
  pf.sign

/--
Returns the `PackedFloat` representation for the given `BitVec`.
-/
@[simp, bv_normalize]
def ofBits (e s : Nat) (b : BitVec (1+e+s)) : PackedFloat e s where
  sign := b.msb
  ex := b.extractLsb' s e
  sig := b.truncate s

/--
Returns the `BitVec` representation for the given `PackedFloat`.
-/
@[simp, bv_normalize]
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
@[bv_normalize]
def toEFixed (pf : PackedFloat e s)
  : EFixedPoint (2 ^ e + s) (2 ^ (e - 1) + s - 2) :=
  let hExOffset := toEFixed_hExOffset e s
  if pf.isNaN then EFixedPoint.getNaN hExOffset
  else if pf.isInfinite then EFixedPoint.getInfinity pf.sign hExOffset
  else {
    state := .Number
    num := {
      sign := pf.sign
      val :=
        let unshifted : BitVec (1+s) :=
          (BitVec.ofBool !pf.isZeroOrSubnorm) ++ pf.sig;
        let shift : BitVec e := if pf.ex = 0 then 0 else pf.ex - 1
        let hs : 1 + s <= 2^e + s := by
          exact Nat.add_le_add_right Nat.one_le_two_pow s
        (BitVec.setWidth' hs (unshifted)) <<< shift
      hExOffset
    }
  }

@[simp, bv_normalize]
def equal_denotation (a b : PackedFloat e s) : Bool :=
  (a.sign == b.sign && a.ex == b.ex && a.sig == b.sig) ||
  (a.isNaN && b.isNaN)

theorem isNumber_of_isNormOrSubnorm (a : PackedFloat e s)
  : a.isNormOrSubnorm → a.toEFixed.state = .Number := by
  simp_all [toEFixed]

def toDyadic? (pf : PackedFloat e s) : Option Dyadic :=
  pf.toEFixed.toDyadic?

def toRat? (pf : PackedFloat e s) : Option Rat :=
  pf.toEFixed.toRat?


end PackedFloat

/--
`UnpackedFloat e s` is the *working* (unpacked) representation of a floating-point
number with exponent width `e` and significand width `s`.

This representation is intentionally different from the IEEE *packed* format
(sign bit, biased exponent field, trailing significand field).  It is designed
to make floating-point algorithms (addition, normalization, rounding, etc.)
uniform and easy to express using bitvector operations.

Mathematically, an `UnpackedFloat e s` represents the real value

  (-1)^sign · sig · 2^(ex - (s - 1))

where:
* `sign : Bool` is the sign bit,
* `sig  : BitVec s` is an **integer significand**,
* `ex   : BitVec e` is a **signed exponent**.

### Key invariants and design choices

* **Explicit hidden bit**:
  The significand includes the hidden bit explicitly.
  For normal numbers, the MSB of `sig` (bit `s-1`) is `1`.

* **Binary point after the MSB**:
  The binary point is conceptually located immediately after the most
  significant bit of `sig`.  This means `sig` is treated as an integer, and the
  scaling by `2^(s-1)` is absorbed into the exponent when interpreting the value.

* **Normalized subnormals**:
  Subnormal packed numbers are *normalized* during unpacking.
  This may require additional exponent bits beyond the packed exponent width.
  The exponent width `e` of `UnpackedFloat` is therefore chosen large enough to
  represent:
    - the smallest subnormal exponent after normalization, and
    - all normal finite exponents.

* **Uniform arithmetic**:
  By using an integer significand with a fixed MSB position, normalization,
  alignment, addition, and rounding can be implemented using only:
    - bit shifts,
    - integer addition/subtraction,
    - MSB tests,
  without fractional arithmetic.

This representation closely follows the `unpackedFloat` design used in `symfpu`
and in hardware floating-point pipelines.
-/
@[ext]
structure UnpackedFloat (e s : Nat) where
  sign : Bool
  ex : BitVec e
  sig : BitVec s
  deriving DecidableEq, Inhabited, Repr

attribute [bv_normalize] UnpackedFloat.ext_iff


/--
`EUnpackedFloat e s` extends `UnpackedFloat e s` with explicit floating-point
classification flags.

The `_state` field records whether the value is:
* NaN,
* ±Infinity,
* ±Zero,
* or a finite number.

When `state` indicates a finite number, the `num` field contains a valid
`UnpackedFloat` satisfying the invariants described in `UnpackedFloat`.

Separating exceptional states from the numeric payload avoids illegal bit-level
states and simplifies reasoning about floating-point operations, since each
operation can:
1. handle NaN/Inf/Zero cases explicitly, and
2. perform uniform arithmetic on normalized finite numbers.

This mirrors the structure used by `symfpu`, where unpacking converts the packed
IEEE representation into a uniform working format suitable for algorithmic
manipulation.
-/
@[ext]
structure EUnpackedFloat (e s : Nat) where
  state : State
  num   : UnpackedFloat e s
deriving DecidableEq, Repr


namespace UnpackedFloat

@[bv_normalize]
theorem ext_iff_beq {x y : UnpackedFloat e s}
  : (x == y) = (x.sign == y.sign && x.ex == y.ex && (x.sig == y.sig)) := by
  cases h : (x == y) <;> simp_all [UnpackedFloat.ext_iff]

@[bv_normalize]
theorem bne_to_beq {x y : UnpackedFloat e s}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [UnpackedFloat.ext_iff]

@[bv_normalize]
theorem eq_cond_sign {x y : UnpackedFloat e s} :
  (bif b then x else y).sign = bif b then x.sign else y.sign := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_cond_ex {x y : UnpackedFloat e s} :
  (bif b then x else y).ex = bif b then x.ex else y.ex := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_cond_sig {x y : UnpackedFloat e s} :
  (bif b then x else y).sig = bif b then x.sig else y.sig := by
  cases b <;> rfl

@[bv_normalize]
def mkZero (sign : Bool) : UnpackedFloat e s :=
  {
    sign := sign
    ex := 0
    sig := 0
  }

@[bv_normalize]
def isZero (uf : UnpackedFloat e s) : Bool :=
  uf.ex == 0 && uf.sig == 0

@[bv_normalize]
def normalize (uf : UnpackedFloat e s) : UnpackedFloat e s :=
  bif uf.sig.clz == s then
    -- zero case: make it explicit!
    mkZero uf.sign
  else
    {
      sign := uf.sign
      ex := uf.ex - uf.sig.clz.setWidth _
      sig := uf.sig <<< uf.sig.clz
    }

@[bv_normalize]
def toEUnpackedFloat (uf : UnpackedFloat e s) : EUnpackedFloat e s :=
  EUnpackedFloat.mk .Number uf

def toDyadic (uf : UnpackedFloat e s) : Dyadic :=
  let sig : BitVec (s + 1) := uf.sig.setWidth' (Nat.le.step Nat.le.refl)
  let sig := bif uf.sign then sig.neg else sig
  Dyadic.ofIntWithPrec sig.toInt ((s - 1) - uf.ex.toInt)

def toRat (uf : UnpackedFloat e s) : Rat :=
  uf.toDyadic.toRat

end UnpackedFloat

namespace EUnpackedFloat

@[bv_normalize]
theorem ext_iff_beq {x y : EUnpackedFloat e s}
  : (x == y) = (x.state == y.state && x.num == y.num) := by
  cases h : (x == y) <;> simp_all [EUnpackedFloat.ext_iff]

@[bv_normalize]
theorem bne_to_beq {x y : EUnpackedFloat e s}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [EUnpackedFloat.ext_iff]

@[bv_normalize]
theorem eq_state_ex {x y : EUnpackedFloat e s} :
  (bif b then x else y).state = bif b then x.state else y.state := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_num_ex {x y : EUnpackedFloat e s} :
  (bif b then x else y).num = bif b then x.num else y.num := by
  cases b <;> rfl



@[bv_normalize]
def isNaN (x : EUnpackedFloat e s) : Bool :=
  x.state == .NaN

@[bv_normalize]
def isInfinite (x : EUnpackedFloat e s) : Bool :=
  x.state == .Infinity

@[bv_normalize]
def isNumber (x : EUnpackedFloat e s) : Bool :=
  x.state == .Number

@[bv_normalize]
def isZero (x : EUnpackedFloat e s) : Bool :=
  x.isNumber && x.num.isZero

@[bv_normalize]
def sign (x : EUnpackedFloat e s) : Bool :=
  x.num.sign

@[bv_normalize]
def exp (x : EUnpackedFloat e s) : BitVec e :=
  x.num.ex

@[bv_normalize]
def sig (x : EUnpackedFloat e s) : BitVec s :=
  x.num.sig

@[bv_normalize]
def mkNaN : EUnpackedFloat e s :=
  {
    state := .NaN
    num := {
      sign := false
      ex := 0
      sig := 0
    }
  }

@[bv_normalize]
def mkInfinity (sign : Bool) : EUnpackedFloat e s :=
  {
    state := .Infinity
    num := {
      sign := sign
      ex := 0
      sig := 0
    }
  }

@[bv_normalize]
def mkNumber (num : UnpackedFloat e s) : EUnpackedFloat e s :=
  {
    state := .Number
    num := num
  }

@[bv_normalize]
def mkZero (sign : Bool) : EUnpackedFloat e s :=
  {
    state := .Number
    num := UnpackedFloat.mkZero sign
  }

@[bv_normalize]
def normalize (uf : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif uf.isNumber then
    uf.num.normalize.toEUnpackedFloat
  else
    uf

def toDyadic? (ef : EUnpackedFloat e s) : Option Dyadic :=
  if ef.isNaN || ef.isInfinite then
    none
  else
    some ef.num.toDyadic

def toRat? (ef : EUnpackedFloat e s) : Option Rat :=
  if ef.isNaN || ef.isInfinite then
    none
  else
    some ef.num.toRat

end EUnpackedFloat

@[bv_normalize]
def Nat.ceilLog2 (n : Nat) : Nat :=
  if n.log2 * 2 = n then n.log2 else n.log2 + 1

@[bv_normalize]
def bias (e : Nat) : Nat :=
  2 ^ (e - 1) - 1

/-- The minimum value the exponent can take when unbiased. -/
@[bv_normalize]
def minNormalExp (e : Nat) : Int :=
  -(bias e - 1)

/-- The max value the exponent can take when unbiased. -/
@[bv_normalize]
def maxNormalExp (e : Nat) : Int := (bias e)


/-- The value the subnormal exponent can take. -/
@[bv_normalize]
def subnormalExp (e : Nat) : Int :=
  minNormalExp e - 1

@[bv_normalize]
def minSubnormalExp (e : Nat) (s : Nat) : Int :=
  (subnormalExp e) - (s : Int)

-- This is a simpler (but less tight) bound than `exponentWidth`.
-- It's logarithmically larger.
@[bv_normalize, simp]
def exponentWidth' (e s : Nat) : Nat :=
  e + s.ceilLog2

@[bv_normalize, simp]
def exponentWidth (e s : Nat) : Nat :=
  (2 ^ (e - 1) + s - 2).log2 + 2

-- Constants

/-- E5M2 floating point representation of 1.0 -/
@[bv_normalize]
def oneE5M2       := PackedFloat.ofBits 5 2 0b00111100#8
/-- E5M2 floating point representation of 2.0 -/
@[bv_normalize]
def twoE5M2       := PackedFloat.ofBits 5 2 0b01000000#8
/-- Smallest (positive) normal number in E5M2 floating point. -/
@[bv_normalize]
def minNormE5M2   := PackedFloat.ofBits 5 2 0b00000100#8
/-- Smallest (positive) subnormal number in E5M2 floating point. -/
@[bv_normalize]
def minSubnormE5M2 := PackedFloat.ofBits 5 2 0b00000001#8

/-- info: { sign := +, ex := 0x0f#5, sig := 0x0#2 } -/
#guard_msgs in #eval (repr oneE5M2)
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
