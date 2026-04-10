import Fp.Utils
import Fp.ForLean.Dyadic
import Fp.Grind
import Fp.ForLean.Rat

@[bv_normalize]
def bias (e : Nat) : Nat :=
  2 ^ (e - 1) - 1

@[simp]
theorem bias_zero_eq : bias 0 = 0 := rfl
@[simp]
theorem bias_one_eq : bias 1 = 0 := rfl
@[simp]
theorem bias_two_eq : bias 2 = 1 := rfl

@[simp]
theorem bias_pos_of_one_lt (e : Nat) (he : 1 < e) : 0 < bias e := by
  simp [bias]
  rcases e with rfl | e
  · grind only
  · simp; grind

/-- Bias is weakly monotone with respect to its argument. -/
@[simp]
theorem bias_le_of_le {e1 e2 : Nat} (he : e1 ≤ e2) : bias e1 ≤ bias e2 := by
  simp [bias]
  have : 0 < 2 ^ (e2 - 1) := by grind only [!Nat.two_pow_pos]
  suffices 2 ^ (e1 - 1) ≤ 2 ^ (e2 - 1) by grind only
  apply Nat.pow_le_pow_of_le (by decide)
  · grind only [#2ce3]

/-- Bias is strictly monotone for exponents over 0. -/
@[simp]
theorem bias_lt_of_lt {e1 e2 : Nat} (he' : 0 < e1) (he : e1 < e2) : bias e1 < bias e2 := by
  simp [bias]
  have : 0 < 2 ^ (e2 - 1) := by grind only [!Nat.two_pow_pos]
  have : 0 < 2 ^ (e1 - 1) := by grind only [!Nat.two_pow_pos]
  suffices 2 ^ (e1 - 1) < 2 ^ (e2 - 1) by grind only
  apply Nat.pow_lt_pow_of_lt (by decide)
  grind only

/--
The biases are equal if either the exponents are equal and at least 2,
or if both exponents are at most 1, in which case the bias is 0.
-/
@[simp]
theorem bias_eq_bias_iff {e1 e2 : Nat}  :
    bias e1 = bias e2 ↔ ((e1 = e2 ∧ e1 ≥ 2) ∨ (e1 ≤ 1 ∧ e2 ≤ 1)) := by
  simp [bias]
  have : 0 < 2 ^ (e2 - 1) := by grind only [!Nat.two_pow_pos]
  have : 0 < 2 ^ (e1 - 1) := by grind only [!Nat.two_pow_pos]
  by_cases he1 : e1 ≤ 1 <;> by_cases he2 : e2 ≤ 1
  · simp [he1, he2]
  · simp [he1, he2]
    grind => instantiate approx
  · simp [he1, he2]
    grind =>
      instantiate approx
      cases #70e3
  · simp [he1, he2]
    constructor
    · intros heq
      have : 2 ^ (e1 - 1) = 2 ^ (e2 - 1) := by grind only
      have : e1 - 1 = e2 - 1 := by grind only [Nat.pow_right_inj]
      grind only
    · grind only

@[bv_normalize]
def Nat.ceilLog2 (n : Nat) : Nat :=
  if n.log2 * 2 = n then n.log2 else n.log2 + 1

@[bv_normalize]
def minNormalExp (e : Nat) : Int :=
  -(bias e - 1 : Nat)

/-- The max value the exponent can take when unbiased. -/
@[bv_normalize]
def maxNormalExp (e : Nat) : Int := (bias e)


/-- The value the subnormal exponent can take. -/
@[bv_normalize]
def subnormalExp (e : Nat) : Int :=
  minNormalExp e - 1

/-- For unpacked floats, the *minimum* the subnormal exponent can take,
which can "steal" bits from the significand to be smaller than minNormalExp. -/
@[bv_normalize]
def minSubnormalExp (e : Nat) (s : Nat) : Int :=
  (subnormalExp e) - (s : Int)

/--
This is a simpler (but less tight) bound than `exponentWidth`.
It's logarithmically larger.
-/
@[bv_normalize, simp]
def exponentWidth' (e s : Nat) : Nat :=
  e + s.ceilLog2

/--
The required exponent width to represent all exponents of an `e`-bit
floating-point number with `s`-bit significand, including normalized
subnormals. Note that this slightly differs from symfpu's definition,
which uses `s - 2` instead of `s - 1`. The reason is that symfpu assumes
`e ≥ 2` while we want to support the degenerate case of `e = 1`,
mainly to minimize our proof assumptions. The correctness
proof of `unpack` relies on this difference which ensures that `uf.sig.clz`
does not overflow when its width is set to `exponentWidth 1 s` (where
`s = 2 ^ n` for some `n`).
-/
@[bv_normalize]
def exponentWidth (e s : Nat) : Nat :=
  (2 ^ (e - 1) + s - 1).log2 + 2


@[simp]
theorem zero_lt_exponentWidth : 0 < exponentWidth e s  := by
  simp [exponentWidth]

@[simp]
theorem one_lt_exponentWidth : 1 < exponentWidth e s  := by
  simp [exponentWidth]


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
structure FixedPoint (width prec : Nat) where
    sign : Bool
    val : BitVec width
    -- | This should not be part of the structure, but a side invariant we keep in mind.
    hPrec : prec < width
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

instance {P : State → Prop} [∀ (s : State), Decidable (P s)] :
    Decidable (∀ (s : State), P s) :=
  if hnan : P .NaN then
    if hinf : P .Infinity then
      if hnum : P .Number then
        isTrue (by grind only [#0000])
      else
        isFalse (by grind only [#b4e6])
    else
      isFalse (by grind only [#b4e6])
  else
    isFalse (by grind only [#b4e6])

instance {P : State → Prop} [∀ (s : State), Decidable (P s)] :
    Decidable (∃ (s : State), P s) :=
  if hnan : P .NaN then
    isTrue (by grind only [#5c30])
  else
    if hinf : P .Infinity then
      isTrue (by grind only [#5c30])
    else
      if hnum : P .Number then
        isTrue (by grind only [#5c30])
      else
        isFalse (by grind only [#0000])

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
structure EFixedPoint (width prec : Nat) where
  state : State
  num : FixedPoint width prec
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
    hPrec := HExOffset.h
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
  hPrec := by
    have hPrec' := a.hPrec
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
def getNaN (hPrec : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .NaN
  num := {
    sign := False
    val := 0
    hPrec
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
def getInfinity (sign : Bool) (hPrec : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Infinity
  num := {
    sign
    val := 0
    hPrec
  }

def getZero (sign : Bool) (hPrec : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Number
  num := {
    sign
    val := 0
    hPrec
  }

@[simp, bv_normalize]
def zero (hPrec : sigWidth < exWidth)
  : EFixedPoint exWidth sigWidth where
  state := .Number
  num := {
    sign := False
    val := 0
    hPrec
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

theorem BitVec.allOnes_ne_zero {e : Nat} :
    e = 0 ∨ BitVec.allOnes e ≠ BitVec.zero e := by
  match e with
  | 0     => left; rfl
  | e + 1 =>
    right
    simp only [BitVec.allOnes, BitVec.zero, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNatLT]
    grind only [!Nat.two_pow_pos]

namespace PackedFloat

/--
Returns the "canonical" NaN for the given floating point format. For example,
the canonical NaN for `exWidth = 3` and `sigWidth = 4` is `0.111.1000`.
-/
@[bv_normalize]
def getNaN (exWidth sigWidth : Nat) : PackedFloat exWidth sigWidth where
  sign := false
  ex := BitVec.allOnes exWidth
  sig := BitVec.intMin sigWidth

@[simp]
theorem sign_getNaN (exWidth sigWidth : Nat) :
    (PackedFloat.getNaN exWidth sigWidth).sign = false := rfl

@[simp]
theorem ex_getNaN (exWidth sigWidth : Nat) :
    (PackedFloat.getNaN exWidth sigWidth).ex = BitVec.allOnes exWidth := rfl

@[simp]
theorem sig_getNaN (exWidth sigWidth : Nat) :
    (PackedFloat.getNaN exWidth sigWidth).sig = BitVec.intMin sigWidth := rfl

/--
Returns the infinity value of the specified sign for the given floating point
format.
-/
@[bv_normalize]
def getInfinity (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth
  sig := 0

@[simp]
theorem sign_getInfinity (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getInfinity exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_getInfinity (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getInfinity exWidth sigWidth sign).sig = 0 := rfl

@[simp]
theorem ex_getInfinity (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getInfinity exWidth sigWidth sign).ex = BitVec.allOnes exWidth := rfl

/--
Returns the (positive) zero value for the given floating point format.
-/
@[bv_normalize]
def getZero (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign := sign
  ex := 0
  sig := 0

@[simp, grind =]
theorem sign_getZero (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getZero exWidth sigWidth sign).sign = sign := rfl

@[simp, grind =]
theorem sig_getZero (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getZero exWidth sigWidth sign).sig = 0 := rfl

@[simp, grind =]
theorem ex_getZero (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getZero exWidth sigWidth sign).ex = 0 := rfl


@[bv_normalize]
def minNormalNumber (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := 1
  sig := 0

@[simp]
theorem sign_minNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minNormalNumber exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_minNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minNormalNumber exWidth sigWidth sign).sig = 0 := rfl

@[simp]
theorem ex_minNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minNormalNumber exWidth sigWidth sign).ex = 1 := rfl

/--
Returns the maximum (magnitude) value for the given sign.
-/
@[bv_normalize]
def maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.intMax exWidth - 1
  sig := BitVec.allOnes sigWidth

@[simp]
theorem sign_maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).sig = BitVec.allOnes sigWidth := rfl

@[simp]
theorem ex_maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).ex = BitVec.intMax exWidth - 1 := rfl

-- TODO: write toRat_getMax

/--
the smallest nonzero subnormal number.
-/
@[bv_normalize]
def minSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.ofInt exWidth 0
  sig := 1#sigWidth

@[simp]
theorem sign_minSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minSubnormalNumber exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_minSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minSubnormalNumber exWidth sigWidth sign).sig = 1#sigWidth := rfl

@[simp]
theorem ex_minSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.minSubnormalNumber exWidth sigWidth sign).ex =
    BitVec.ofInt exWidth 0 := rfl

@[bv_normalize]
def maxSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.ofInt exWidth 0
  sig := BitVec.allOnes sigWidth

@[simp]
theorem sign_maxSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxSubnormalNumber exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_maxSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxSubnormalNumber exWidth sigWidth sign).sig = BitVec.allOnes sigWidth := rfl

@[simp]
theorem ex_maxSubnormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxSubnormalNumber exWidth sigWidth sign).ex =
    BitVec.ofInt exWidth 0 := rfl

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

@[bv_normalize]
def isNaN (pf : PackedFloat e s) : Bool :=
  -- Prioritize `NaN` over `Infinity`.
  pf.ex == .allOnes e && (s == 0 || pf.sig != .zero s)

@[grind .]
private theorem BitVec.eq_allOnes_iff_toNat_eq (x : BitVec w) :
    x = .allOnes w ↔ x.toNat = 2 ^ w - 1 := by
  constructor
  · intros h
    subst h
    simp
  · intros h
    apply BitVec.toNat_inj.mp
    simp [h]


@[grind .]
private theorem BitVec.eq_zero_iff_toNat_eq (x : BitVec w) :
    x = .zero w ↔ x.toNat = 0 := by
  constructor
  · intros h
    subst h
    simp
  · intros h
    apply BitVec.toNat_inj.mp
    simp [h]

@[grind =>]
theorem isNaN_iff_ex_eq_sig_eq (pf : PackedFloat e s) (hs : 0 < s) :
    pf.isNaN ↔ (pf.ex = .allOnes e ∧ pf.sig ≠ 0#s) := by
  simp [isNaN]
  grind

@[grind =>]
theorem not_isNaN_iff_ex_ne_or_sig_ne (pf : PackedFloat e s) (hs : 0 < s) :
    (¬ pf.isNaN) ↔ (pf.ex ≠ .allOnes e ∨ pf.sig = 0#s) := by
  simp [isNaN]
  grind

@[bv_normalize]
def isInfinite (pf : PackedFloat e s) : Bool :=
  -- Prioritize `Infinity` over `0`. This is somewhat arbitrary.
  pf.ex == .allOnes e && (s != 0 && pf.sig == .zero s)

@[simp, grind →]
theorem eq_mkInfinity_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite →  ∃ (sign : Bool), pf = PackedFloat.getInfinity e s sign := by
  intro h
  simp [isInfinite] at h
  simp [PackedFloat.getInfinity]
  rcases pf with ⟨sign, ex, sig⟩
  simp_all


@[bv_normalize]
def isZero (pf : PackedFloat e s) : Bool :=
  -- Prioritize `0` over `Subnormals`.
  e != 0 && pf.ex == .zero e && pf.sig == .zero s

@[simp, grind →]
theorem eq_mkZero_of_isZero {pf : PackedFloat e s} :
    pf.isZero → ∃ (sign : Bool), pf = PackedFloat.getZero e s sign := by
  intro h
  simp [isZero] at h
  simp [PackedFloat.getZero]
  rcases pf with ⟨sign, ex, sig⟩
  simp_all


@[simp, grind .]
theorem isZero_getZero {exWidth sigWidth : Nat} (sign : Bool) :
    (PackedFloat.getZero exWidth sigWidth sign).isZero = decide (0 < exWidth) := by
  simp [PackedFloat.getZero, isZero]
  grind

@[simp, grind .]
theorem eq_mkZero_of_isZero' {pf : PackedFloat e s} {sign : Bool} (he : 0 < e):
    (pf.isZero ∧ sign = pf.sign) ↔  pf = PackedFloat.getZero e s sign := by
  constructor
  · intros h
    simp [isZero] at h
    simp [PackedFloat.getZero]
    rcases pf with ⟨sign, ex, sig⟩
    simp_all
  · intros h
    rw [h]
    simp [he]
@[simp, grind =]
theorem zero_eq_allOnes_eq_decide (e : Nat) :
    (0#e = BitVec.allOnes e) = decide (e = 0) := by
  by_cases he : 0 = e
  · subst he
    simp
  · simp [show ¬ e = 0 by omega]
    intros hcontra
    have := BitVec.toInt_inj.mpr hcontra
    grind

@[simp, grind =]
theorem allOnes_eq_zero_eq_decide (e : Nat) :
    (BitVec.allOnes e = 0#e) = decide (e = 0) := by
  have := zero_eq_allOnes_eq_decide e
  grind

@[simp, grind =]
theorem zero_ne_allOnes_eq_decide (e : Nat) :
    (0#e ≠ BitVec.allOnes e) = decide (0 < e) := by
  grind

@[simp]
theorem isZero_getInfinity {exWidth sigWidth : Nat} (sign : Bool) :
    (PackedFloat.getInfinity exWidth sigWidth sign).isZero = false := by
  simp [PackedFloat.getInfinity, isZero]

@[bv_normalize]
def isNonzeroSubnorm (pf : PackedFloat e s) : Bool :=
  e != 0 && pf.ex == .zero e && pf.sig != .zero s

@[simp]
theorem exp_eq_of_isNonzeroSubnorm {pf : PackedFloat e s}
    (h : pf.isNonzeroSubnorm := by solve | simp | grind) :
    pf.ex = 0#e := by
  simp [isNonzeroSubnorm] at h
  simp [h]



-- See that this means that it is a number.
-- We need a different one to say that it is nonzero.
-- | does this also need a 'e != 0' condition?
@[bv_normalize]
def isNorm {e s} (pf : PackedFloat e s) : Bool :=
  pf.ex != .allOnes e && pf.ex != .zero e


@[grind .]
theorem ex_ne_zero_if_isNorm {pf : PackedFloat e s} (h : pf.isNorm := by solve | simp | grind) :
    pf.ex != .zero e := by
  simp [isNorm] at h
  simp [h]

@[simp, bv_normalize]
def isNormOrNonzeroSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex != .allOnes e && (pf.ex != .zero e || pf.sig != .zero s)
  -- e != 0 && pf.ex != BitVec.allOnes e
@[simp]
theorem sig_ne_zero_of_isNormOrNonzeroSubnorm_of_isNorm
    (pf : PackedFloat e s)
    (hnorm : pf.isNorm)
    (hsubnorm : ¬ pf.isNormOrNonzeroSubnorm) :
    pf.sig ≠ 0#s := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at hsubnorm
  grind

@[simp]
theorem ex_ne_zero_of_isNormOrNonzeroSubnorm_of_isNorm
    (pf : PackedFloat e s)
    (hnorm : pf.isNorm)
    (hsubnorm : ¬ pf.isNormOrNonzeroSubnorm) :
    pf.ex ≠ 0#e := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at hsubnorm
  grind


@[simp, bv_normalize]
def isZeroOrSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex == 0

@[simp, bv_normalize]
def isNZero (pf : PackedFloat e s) : Bool :=
  e != 0 && pf.ex == 0 && pf.sig == 0 && pf.sign

@[simp, bv_normalize]
def isPZero (pf : PackedFloat e s) : Bool :=
  e != 0 && pf.ex == 0 && pf.sig == 0 && !pf.sign


@[simp, bv_normalize]
def isSignMinus (pf : PackedFloat e s) : Bool :=
  pf.sign

@[grind →]
theorem isZeroOrSubnorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → pf.isZeroOrSubnorm := by
  grind [isZero, isZeroOrSubnorm]

@[grind →]
theorem isZeroOrSubnorm_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → pf.isZeroOrSubnorm := by
  grind [isNonzeroSubnorm, isZeroOrSubnorm]


-- TODO: delete 'isNZero',
@[grind →]
theorem isZero_of_isNZero {pf : PackedFloat e s} :
    pf.isNZero → pf.isZero := by
  grind [isNZero, isZero]

@[grind →]
theorem isZero_of_isPZero {pf : PackedFloat e s} :
    pf.isPZero → pf.isZero := by
  grind [isPZero, isZero]

@[grind .]
theorem isZero_iff_isNZero_or_isPZero {pf : PackedFloat e s} :
    pf.isZero ↔ pf.isNZero ∨ pf.isPZero := by
  grind [isZero, isNZero, isPZero]


@[grind →]
theorem isNormOrSubnorm_of_isNorm (pf : PackedFloat e s) :
    pf.isNorm → pf.isNormOrNonzeroSubnorm := by
  grind [isNorm, isNormOrNonzeroSubnorm]


@[grind →]
theorem isNormOrSubnorm_of_isSubnorm (pf : PackedFloat e s) :
    pf.isNonzeroSubnorm → pf.isNormOrNonzeroSubnorm := by
  simp only [isNonzeroSubnorm, BitVec.zero_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    isNormOrNonzeroSubnorm, and_imp]
  intros he hex hsig
  simp [hex, hsig]
  grind

@[grind .]
theorem isNormOrSubnorm_eq_isNorm_or_isSubnorm (pf : PackedFloat e s) :
    pf.isNormOrNonzeroSubnorm = (pf.isNorm ∨ pf.isNonzeroSubnorm) := by
  simp [isNorm, isNonzeroSubnorm, isNormOrNonzeroSubnorm]
  by_cases he : e = 0
  · subst he
    grind
  · grind

@[grind →]
theorem not_isNaN_of_isNormOrSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isNaN := by
  grind [isNaN, isNormOrNonzeroSubnorm]

@[grind →]
theorem not_isInfinite_of_isNormOrSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isInfinite := by
  grind [isInfinite, isNormOrNonzeroSubnorm]

@[grind →]
theorem not_isZero_of_isNormOrSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isZero := by
  grind [isZero, isNormOrNonzeroSubnorm, BitVec.allOnes_ne_zero]

-- Theorems about classification

theorem classification_exhaustive (pf : PackedFloat e s) :
    pf.isNaN || pf.isInfinite || pf.isZero || pf.isNonzeroSubnorm || pf.isNorm := by
  grind [isNaN, isInfinite, isZero, isNonzeroSubnorm, isNorm]

@[grind →]
theorem not_isInfinite_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isInfinite := by
  grind [isNaN, isInfinite]

@[grind →]
theorem not_isZero_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isZero := by
  grind [isNaN, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isSubnorm_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isNonzeroSubnorm := by
  grind [isNaN, isNonzeroSubnorm, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isNorm_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isNorm := by
  grind [isNaN, isNorm]

@[grind →]
theorem not_isNaN_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isNaN := by
  grind [isNaN, isInfinite]

@[grind →]
theorem not_isZero_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isZero := by
  grind [isInfinite, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isSubnorm_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isNonzeroSubnorm := by
  grind [isInfinite, isNonzeroSubnorm]

@[grind →]
theorem not_isNorm_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isNorm := by
  grind [isInfinite, isNorm]

@[grind →]
theorem not_isNaN_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isNaN := by
  grind [isNaN, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isInfinite_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isInfinite := by
  grind [isInfinite, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isSubnorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isNonzeroSubnorm := by
  grind [isNonzeroSubnorm, isZero]

@[grind →]
theorem not_isNorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isNorm := by
  grind [isZero, isNorm]

@[grind →]
theorem not_isNaN_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isNaN := by
  grind [isNaN, isNonzeroSubnorm, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isInfinite_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isInfinite := by
  grind [isInfinite, isNonzeroSubnorm]

@[grind →]
theorem not_isZero_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isZero := by
  grind [isNonzeroSubnorm, isZero]

@[grind →]
theorem not_isNorm_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isNorm := by
  grind [isNonzeroSubnorm, isNorm]

@[grind →]
theorem not_isNaN_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isNaN := by
  grind [isNaN, isNorm]

@[grind →]
theorem not_isInfinite_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isInfinite := by
  grind [isInfinite, isNorm]

@[grind →]
theorem not_isInfinite_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isInfinite := by
  grind [isInfinite, isNormOrNonzeroSubnorm]

@[grind →]
theorem not_isZero_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isZero := by
  grind [isZero, isNorm]

@[grind →]
theorem not_isSubnorm_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isNonzeroSubnorm := by
  grind [isNonzeroSubnorm, isNorm]

@[simp, grind! .]
theorem isInfinite_getInfinity (e s : Nat) (sign : Bool)  :
    (PackedFloat.getInfinity e s sign).isInfinite = decide (0 < s) := by
  simp only [isInfinite, getInfinity, BitVec.ofNat_eq_ofNat, BEq.rfl, BitVec.zero_eq, Bool.and_true,
    Bool.true_and]
  grind

@[simp, grind! .]
theorem isInfinite_getZero (e s : Nat) (sign : Bool):
    (PackedFloat.getZero e s sign).isInfinite = decide (e = 0 ∧ s ≠ 0) := by
  simp only [isInfinite, getZero, BitVec.zero_eq]
  grind

@[simp]
theorem isNaN_getInfinity_eq_false (sign : Bool) :
    (PackedFloat.getInfinity e s sign).isNaN = !(0 < s) := by
  simp [PackedFloat.getInfinity, isNaN]
  grind

theorem sigWidth_ge_one_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → s ≥ 1 := by
  grind [isInfinite]

theorem expWidth_ge_one_of_isZero {pf : PackedFloat e s} :
    pf.isZero → e ≥ 1 := by
  grind [isZero]

theorem expWidth_ge_one_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → e ≥ 1 := by
  grind [isNonzeroSubnorm]

theorem sigWidth_ge_one_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → s ≥ 1 := by
  grind [isNonzeroSubnorm]

theorem expWidth_ge_two_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → e ≥ 2 := by
  grind [isNorm]

@[simp]
theorem isNaN_getZero {e s : Nat} (sign : Bool) :
  (PackedFloat.getZero e s sign).isNaN  = decide (e = 0 ∧ s = 0) := by
  simp [PackedFloat.getZero, isNaN]
  grind

@[simp]
theorem isNaN_getNaN {e s : Nat}  :
    (PackedFloat.getNaN e s).isNaN = true := by
  simp [getNaN, isNaN]
  grind

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
  let hPrec := toEFixed_hPrec e s
  if pf.isNaN then EFixedPoint.getNaN hPrec
  else if pf.isInfinite then EFixedPoint.getInfinity pf.sign hPrec
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
      hPrec
    }
  }

@[simp, bv_normalize]
def equal_denotation (a b : PackedFloat e s) : Bool :=
  (a.sign == b.sign && a.ex == b.ex && a.sig == b.sig) ||
  (a.isNaN && b.isNaN)

theorem isNumber_of_isNormOrSubnorm (a : PackedFloat e s)
  : a.isNormOrNonzeroSubnorm → a.toEFixed.state = .Number := by
  simp_all [toEFixed, isNaN, isInfinite]

def toDyadic? (pf : PackedFloat e s) : Option Dyadic :=
  pf.toEFixed.toDyadic?

def toRat? (pf : PackedFloat e s) : Option Rat :=
  pf.toEFixed.toRat?

/--
Raw negation directly on the packedFloat representation.
-/
@[bv_normalize]
def neg (x : PackedFloat e s) : PackedFloat e s :=
  { x with sign := !x.sign }

instance : Neg (PackedFloat e s) where
  neg := .neg

@[bv_normalize]
theorem neg_def {x : PackedFloat e s} : -x = PackedFloat.neg x := rfl

@[simp]
theorem neg_neg (x : PackedFloat e s) : -(-x) = x := by
  simp [neg_def, neg, PackedFloat.ext_iff]

@[simp]
theorem neg_sign (x : PackedFloat e s) : (-x).sign = !x.sign := rfl

@[simp]
theorem neg_ex (x : PackedFloat e s) : (-x).ex = x.ex := rfl

@[simp]
theorem neg_sig (x : PackedFloat e s) : (-x).sig = x.sig := rfl

/--
Raw abs directly on the packedFloat representation.
-/
@[bv_normalize]
def abs (x : PackedFloat e s) : PackedFloat e s :=
  { x with sign := false }

@[simp]
theorem abs_sign (x : PackedFloat e s) : x.abs.sign = false := rfl

@[simp]
theorem abs_ex (x : PackedFloat e s) : x.abs.ex = x.ex := rfl

@[simp]
theorem abs_sig (x : PackedFloat e s) : x.abs.sig = x.sig := rfl

@[simp]
theorem abs_abs (x : PackedFloat e s) : x.abs.abs = x.abs := rfl

@[simp]
theorem abs_neg (x : PackedFloat e s) : (-x).abs = x.abs := by
  simp [abs, neg_def, neg, PackedFloat.ext_iff]

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
  deriving Inhabited, Repr

attribute [bv_normalize] UnpackedFloat.ext_iff

namespace UnpackedFloat

@[bv_normalize]
def neg (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := !x.sign }

@[bv_normalize]
def abs (x : UnpackedFloat e s) : UnpackedFloat e s :=
  { x with sign := false }

instance : Neg (UnpackedFloat e s) where
  neg := .neg

@[bv_normalize]
theorem neg_def {x : UnpackedFloat e s} : -x = UnpackedFloat.neg x := rfl

@[simp]
theorem neg_neg (x : UnpackedFloat e s) : -(-x) = x := by
  simp [neg_def, neg]

@[simp]
theorem neg_sign (x : UnpackedFloat e s) : (-x).sign = !x.sign := rfl

@[simp]
theorem neg_ex (x : UnpackedFloat e s) : (-x).ex = x.ex := rfl

@[simp]
theorem neg_sig (x : UnpackedFloat e s) : (-x).sig = x.sig := rfl

end UnpackedFloat

/--
`EUnpackedFloat e s` extends `UnpackedFloat e s` with explicit floating-point
classification flags.

The `state` field records whether the value is:
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
deriving Repr

attribute [bv_normalize] EUnpackedFloat.ext_iff


inductive ExtDyadic where
  | NaN : ExtDyadic
  | Infinity : Bool → ExtDyadic
  | Number : Dyadic → ExtDyadic
deriving DecidableEq

inductive ExtRat where
  | NaN : ExtRat
  | Infinity : Bool → ExtRat
  | Number : Rat → ExtRat
deriving DecidableEq, Repr

namespace ExtRat

instance : Zero ExtRat where
  zero := .Number 0

@[simp ←]
theorem ExtRat.zero_def : ExtRat.Number 0 = (0 : ExtRat) := rfl

@[simp ←]
theorem ExtRat.zero_def' : ExtRat.Number 0 = Zero.zero := rfl

@[match_pattern]
abbrev plusInfinity : ExtRat :=
  .Infinity False

@[match_pattern]
abbrev minusInfinity : ExtRat :=
  .Infinity True


def add (x y : ExtRat) : ExtRat :=
  match x, y with
  | .NaN, _ => .NaN
  | _, .NaN => .NaN
  | .Infinity s1, .Infinity s2 =>
    if s1 == s2 then .Infinity s1 else .NaN
  | .Infinity s, _ => .Infinity s
  | _, .Infinity s => .Infinity s
  | .Number r1, .Number r2 => .Number (r1 + r2)

instance : Add ExtRat where
  add a b := add a b

@[simp]
theorem ExtRat.add_def {a b : ExtRat} : a.add b = a + b := rfl

@[simp]
theorem ExtRat.NaN_add (x : ExtRat) : (.NaN + x) = .NaN := rfl

@[simp]
theorem ExtRat.add_NaN (x : ExtRat) : (x + .NaN) = .NaN := by
  simp [← add_def, add]
  grind [ExtRat]

@[simp]
theorem ExtRat.add_Number (x y : Rat) :
    (ExtRat.Number x + .Number y) = .Number (x + y) := by
  simp [← add_def, add]

-- TODO: write theorems for addition for infinity and such.

def neg (x : ExtRat) : ExtRat :=
  match x with
  | .NaN => .NaN
  | .Infinity s => .Infinity (!s)
  | .Number r => .Number (-r)

def sub (x y : ExtRat) : ExtRat :=
  x.add (y.neg)


instance : Neg ExtRat where
  neg a := neg a

@[simp]
theorem ExtRat.neg_def {a : ExtRat} : a.neg = -a := rfl

@[simp]
theorem ExtRat.neg_NaN : (-.NaN : ExtRat) = .NaN := rfl

@[simp]
theorem ExtRat.neg_infinity (s : Bool) : (-.Infinity s : ExtRat) = .Infinity (!s) := rfl

@[simp]
theorem ExtRat.neg_number (r : Rat) : (-.Number r : ExtRat) = .Number (-r) := rfl


instance : Sub ExtRat where
  sub a b := sub a b

@[simp]
theorem sub_def {a b : ExtRat} : a.sub b = a - b := rfl

@[simp]
theorem number_sub_number {r1 r2 : Rat} :
    (ExtRat.Number r1 - ExtRat.Number r2) = ExtRat.Number (r1 - r2) := by
  rw [← sub_def, sub]
  simp
  grind only

def mul (x y : ExtRat) : ExtRat :=
  match x, y with
  | .NaN, _ => .NaN
  | _, .NaN => .NaN
  | .Infinity isInfNeg, .Infinity isInfNeg' => .Infinity (isInfNeg ^^ isInfNeg')
  | .Infinity isInfNeg, .Number r =>
    if r = 0 then .NaN else
      let isNumNeg := r < 0
      .Infinity (isInfNeg ^^ isNumNeg)
  | .Number r, .Infinity isInfNeg =>
    if r = 0 then .NaN else
      let isNumNeg := r < 0
      .Infinity (isInfNeg ^^ isNumNeg)
  | .Number r1, .Number r2 => .Number (r1 * r2)

instance : Mul ExtRat where
  mul a b := mul a b

@[simp]
theorem mul_def {a b : ExtRat} : a.mul b = a * b := rfl

def inv (x : ExtRat) : ExtRat :=
  match x with
  | .NaN => .NaN
  | .Infinity _sign => .Number 0
  | .Number r =>
    if r == 0 then .Infinity (False) -- +∞
    else .Number (1 / r)

def div (x y : ExtRat) : ExtRat :=
  x.mul (y.inv)

instance : Div ExtRat where
  div a b := div a b

@[simp] theorem div_def {a b : ExtRat} : a.div b = a / b := rfl

def le (x y : ExtRat) : Bool :=
  match x, y with
  | .NaN, .NaN => true -- NaN ≤ NaN only.
  | .NaN, _ => false
  | _, .NaN => false
  | .Infinity s1, .Infinity s2 =>
      if s1 == s2 then true else s1 -- +∞ ≤ -∞ is false, -∞ ≤ +∞ is true
  | .plusInfinity, .Number _ => false -- +∞ ≤ anything else is false
  | .Number _, .plusInfinity => true  -- no number is ≤ +∞
  | .minusInfinity, .Number _ => true   -- -∞ ≤ anything else is
  | .Number _, .minusInfinity => false -- no number is ≤ -∞
  | .Number r1, .Number r2 => r1 <= r2

instance : LE ExtRat where
  le a b := le a b



@[simp]
theorem le_def {a b : ExtRat} : a.le b = (a ≤ b) := rfl

@[simp]
theorem ExtRat.le_NaN_iff (x : ExtRat) : (x ≤ .NaN) = decide (x = .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.NaN_le_iff (x : ExtRat) : (.NaN ≤ x) = decide (x = .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.inf_false_le_iff (x : ExtRat) :
    -- +infty ≤ x ↔ x = +infty
    (.Infinity false ≤ x) = decide (x = .Infinity false) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.le_inf_false_iff (x : ExtRat) :
    -- x ≤ +infty ↔ x ≠ NaN
    (x ≤ ExtRat.Infinity false) ↔ (x ≠ .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.inf_true_le_iff (x : ExtRat) :
    -- -infty ≤ x ↔ x ≠ NaN
    (.Infinity true ≤ x) = decide (x ≠ .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.le_inf_true_iff (x : ExtRat) :
    -- x ≤ -infty ↔ x = -infty
    (x ≤ ExtRat.Infinity true) = decide (x = .Infinity true) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem number_le_infinity_iff {n : Rat} {sign : Bool}:
    (ExtRat.Number n ≤ ExtRat.Infinity sign) ↔ (sign = false) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem infinity_le_number_iff {n : Rat} {sign : Bool}:
    (ExtRat.Infinity sign ≤ ExtRat.Number n) ↔ (sign = true) := by
  simp [le, ← le_def]
  grind


@[simp]
theorem number_le_nan_iff {n : Rat} :
    (ExtRat.Number n ≤ ExtRat.NaN) = False := by
  simp [le, ← le_def]

@[simp]
theorem nan_le_number_iff {n : Rat} :
    (.NaN ≤ ExtRat.Number n) = False := by
  simp [le, ← le_def]

@[simp]
theorem nan_le_infinity_iff {sign : Bool}:
    (.NaN ≤ ExtRat.Infinity sign) = False := by
  simp [le, ← le_def]

@[simp]
theorem infinity_le_nan_iff {sign : Bool}:
    (ExtRat.Infinity sign ≤ .NaN) = False := by
  simp [le, ← le_def]



@[simp]
theorem ExtRat.num_le_num_iff (r1 r2 : Rat) :
  ((ExtRat.Number r1) ≤ (ExtRat.Number r2)) = decide (r1 ≤ r2) := by
  simp [le, ← le_def]

@[simp]
theorem ExtRat.le_refl {a : ExtRat} : a ≤ a := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.le_antisymm {a b : ExtRat} : (a ≤ b ∧ b ≤ a) ↔ a = b := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.eq_of_le_of_le {a b : ExtRat} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  simp [le, ← le_def] at h1 h2
  grind

@[simp]
theorem ExtRat.infinity_le_infinity_iff {s1 s2 : Bool} :
    (ExtRat.Infinity s1 ≤ ExtRat.Infinity s2) = decide (s1 = false → s2 = false) := by
  simp [le, ← le_def]
  grind

instance {a b : ExtRat}: Decidable (a ≤ b) := by
  simp only [← ExtRat.le_def]
  infer_instance

def eq (x y : ExtRat) : Bool :=
  match x, y with
  | .NaN, .NaN => true
  | .NaN, _ => false
  | _, .NaN => false
  | .Infinity s1, .Infinity s2 => s1 == s2
  | .Infinity _, _ => false
  | _, .Infinity _ => false
  | .Number r1, .Number r2 => r1 == r2


@[simp]
theorem eq_iff (x y : ExtRat) : x.eq y = decide (x = y) := by
  grind [ExtRat, eq]

def lt (x y : ExtRat) : Bool :=
  x.le y && !(x.eq y)

instance : LT ExtRat where
  lt a b := lt a b

@[simp]
theorem lt_def {a b : ExtRat} : a.lt b = (a < b) := rfl

@[simp, grind .]
theorem le_of_lt {a b : ExtRat} (h : a < b) : (a ≤ b) := by
  simp [← lt_def, lt] at h
  grind only

@[simp, grind .]
theorem ne_of_lt {a b : ExtRat} (h : a < b) : ¬ (a = b) := by
  simp [← lt_def, lt] at h
  grind only

theorem lt_iff {a b : ExtRat} : (a < b) ↔ (a ≤ b ∧ ¬ (a = b)) := by
  simp [← lt_def, lt]

@[simp]
theorem NaN_lt_elim {a : ExtRat} :  (.NaN < a) = False := by
  simp [lt_iff]
  grind only

@[simp]
theorem lt_NaN_elim {a : ExtRat} :  (a < .NaN) = False := by
  simp [lt_iff]

@[simp]
theorem lt_infty_true_elim {a : ExtRat} : (a < .Infinity true) = False := by
  simp [lt_iff]

@[simp]
theorem infty_true_lt_iff {a : ExtRat} : (.Infinity true < a) =
  decide (a ≠ .Infinity true ∧ a ≠ .NaN) := by
  simp [lt_iff]
  grind

@[simp]
theorem lt_infty_false_iff {a : ExtRat} : (a < .Infinity false) =
  decide (a ≠ .Infinity false ∧ a ≠ .NaN) := by
  simp [lt_iff]
  grind

@[simp]
theorem elim_infty_false_lt {a : ExtRat} : (.Infinity false < a) = False := by
  simp [lt_iff]
  grind

@[simp]
theorem num_lt_num_iff {r1 r2 : Rat} :
  ((ExtRat.Number r1) < (ExtRat.Number r2)) = decide (r1 < r2) := by
  simp [lt_iff]
  grind

instance {a b : ExtRat }: Decidable (a < b) := by
  simp only [· < ·]
  infer_instance

instance : Min ExtRat where
  min a b := if a ≤ b then a else b

/-- Unfold min into ite. Not a simp lemma, since we may want to rewrite
with higher level reasoning principles. -/
theorem min_eq_ite {a b : ExtRat} : min a b = if a ≤ b then a else b := rfl

instance : Max ExtRat where
  max a b := if a ≤ b then b else a

theorem max_eq_ite {a b : ExtRat} : max a b = if a ≤ b then b else a := rfl

section NanBehaviour

/-# Table 1 of SMT-LIB spec -/

@[simp]
theorem NaN_add (x : ExtRat) : (.NaN + x) = .NaN := by
  rw [← ExtRat.add_def, ExtRat.add]

@[simp]
theorem add_NaN (x : ExtRat) : (x + .NaN) = ExtRat.NaN := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

@[simp]
theorem neg_NaN : -ExtRat.NaN = ExtRat.NaN := by
  rw [← ExtRat.neg_def, ExtRat.neg]

@[simp]
theorem NaN_mul (x : ExtRat) : (.NaN * x) = .NaN := by
  rw [← ExtRat.mul_def, ExtRat.mul]

@[simp]
theorem mul_NaN (x : ExtRat) : (x * .NaN) = .NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind [ExtRat]

@[simp]
theorem le_NaN (x : ExtRat) : ExtRat.NaN ≤ x ↔ x = ExtRat.NaN := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

@[simp]
theorem NaN_le (x : ExtRat) : x ≤ ExtRat.NaN ↔ x = ExtRat.NaN := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

end NanBehaviour

section DefinedSymbolsBehaviour
/-# Table 2 -/

theorem sub_eq_add_neg (x y : ExtRat) : (x - y) = (x + -y) := by
  rw [← ExtRat.sub_def, ← ExtRat.add_def, ← ExtRat.neg_def]
  unfold ExtRat.sub
  grind

theorem div_eq_mul_inv (x y : ExtRat) : (x / y) = (x * y.inv) := by
  rw [← ExtRat.div_def, ← ExtRat.mul_def]
  unfold ExtRat.div
  grind

@[simp]
theorem ge_eq_le_symm (x y : ExtRat) : (x ≥ y) = (y ≤ x) := by
  simp only [(· ≥ ·)]

theorem lt_eq_le_and_not_eq (x y : ExtRat) : (x < y) = (x ≤ y ∧ ¬ (x = y)) := by
  simp only [(· < ·), (· ≤ ·)]
  unfold ExtRat.lt ExtRat.le ExtRat.eq
  grind

theorem gt_eq_ge_and_not_eq (x y : ExtRat) : (x > y) = (x ≥ y ∧ ¬ (x = y)) := by
  simp only [(· > ·), (· ≥ ·), (· < ·), (· ≤ ·)]
  unfold ExtRat.le ExtRat.lt ExtRat.le ExtRat.eq
  grind

end DefinedSymbolsBehaviour
section InfinityBehaviour
/-# Table 3 -/

@[simp]
theorem plus_inf_le_iff_eq (x : ExtRat) : (.Infinity false ≤ x) ↔ x = .Infinity false := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem le_neg_inf_iff_eq (x : ExtRat) : (x ≤ .Infinity true) ↔ x = .Infinity true := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem number_le_plus_inf (r : Rat) : (ExtRat.Number r ≤ ExtRat.Infinity false) := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem neg_inf_le_number (r : Rat) : (ExtRat.Infinity true ≤ ExtRat.Number r) := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

@[simp]
theorem neg_plus_inf_eq_minus_inf : - (ExtRat.Infinity false) = (ExtRat.Infinity true) := by
  rw [← ExtRat.neg_def]
  unfold ExtRat.neg
  grind

@[simp]
theorem neg_minus_inf_eq_plus_inf : - (ExtRat.Infinity true) = (ExtRat.Infinity false) := by
  rw [← ExtRat.neg_def]
  unfold ExtRat.neg
  grind

@[simp]
theorem inv_plus_inf_eq_zero : (ExtRat.Infinity false).inv = ExtRat.Number 0 := by
  unfold ExtRat.inv
  grind

@[simp]
theorem inv_minus_inf_eq_zero : (ExtRat.Infinity true).inv = ExtRat.Number 0 := by
  unfold ExtRat.inv
  grind

@[simp]
theorem inv_inf_eq_zero (s : Bool) : (ExtRat.Infinity s).inv = ExtRat.Number 0 := by
  unfold ExtRat.inv
  grind

theorem add_comm (x y : ExtRat) : x + y = y + x := by
  rw [← ExtRat.add_def, ← ExtRat.add_def]
  unfold ExtRat.add
  grind

@[simp]
theorem add_inf_eq_inf_of_ne_of_ne (x : ExtRat)
    (hxInf : x ≠ .Infinity true) (hxNan : x ≠ .NaN) :
    x + .Infinity false = .Infinity false := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

@[simp]
theorem add_inf_eq_nan_of_eq (x : ExtRat) (hxInf : x = .Infinity true) :
    x + .Infinity false = .NaN := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

theorem add_neg_inf_eq_nan_of_eq (x : ExtRat) (hxInf : x = .Infinity false) :
    x + .Infinity true = .NaN := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

theorem add_neg_inf_eq_neg_inf_of_ne_of_ne (x : ExtRat)
    (hxInf : x ≠ .Infinity false) (hxNan : x ≠ .NaN) :
    x + .Infinity true = .Infinity true := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

/-- +∞ × +∞ = +∞-/
@[simp]
theorem inf_mul_inf_eq_inf :
    ExtRat.Infinity false * ExtRat.Infinity false = ExtRat.Infinity false := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- +∞ × -∞ = -∞-/
@[simp]
theorem inf_mul_neg_inf_eq_neg_inf :
    ExtRat.Infinity false * ExtRat.Infinity true = ExtRat.Infinity true := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- -∞ × +∞ = -∞-/
@[simp]
theorem neg_inf_mul_inf_eq_neg_inf :
    ExtRat.Infinity true * ExtRat.Infinity false = ExtRat.Infinity true := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- -∞ × -∞ = +∞-/
@[simp]
theorem neg_inf_mul_neg_inf_eq_inf :
    ExtRat.Infinity true * ExtRat.Infinity true = ExtRat.Infinity false := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- ±∞ × 0 = NaN -/
@[simp]
theorem inf_mul_zero_eq_nan :
    ExtRat.Infinity b * ExtRat.Number 0 = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- ±∞ × NaN = NaN -/
@[simp]
theorem inf_mul_nan_eq_nan :
    ExtRat.Infinity b * ExtRat.NaN = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- positive × +∞ = +∞ -/
@[simp]
theorem mul_inf_eq_inf_of_lt (x : ExtRat)
    (hxNan : x ≠ .NaN) (hxZero : 0 < x) :
    x * .Infinity false = .Infinity false := by
  rw [← ExtRat.mul_def]
  rw [← ExtRat.lt_def, ← ExtRat.zero_def] at hxZero
  unfold ExtRat.mul
  unfold ExtRat.lt ExtRat.le ExtRat.eq at hxZero
  grind [ExtRat]

/-- negative × +∞ = -∞ -/
theorem mul_inf_eq_neg_inf_of_lt (x : ExtRat)
    (hxNan : x ≠ .NaN) (hxZero : x < 0) :
    x * .Infinity false = .Infinity true := by
  rw [← ExtRat.mul_def]
  rw [← ExtRat.lt_def, ← ExtRat.zero_def] at hxZero
  unfold ExtRat.mul
  unfold ExtRat.lt ExtRat.le ExtRat.eq at hxZero
  -- grind [ExtRat] TODO: why doesn't grind work here?
  cases x
  · grind
  · grind
  · -- grind -- theory propagation does not work properly here,
    -- the rational fact 'a < 0' is not deduced
    simp only [Bool.false_bne]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      beq_eq_false_iff_ne, ne_eq] at hxZero
    simp only [hxZero, ↓reduceIte, Infinity.injEq, decide_eq_true_eq]
    grind

@[simp]
theorem number_mul_number_eq : ExtRat.Number r1 * ExtRat.Number r2 = ExtRat.Number (r1 * r2) := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem zero_mul_inf_eq : ExtRat.Number 0 * ExtRat.Infinity sign = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem inf_mul_zero_eq : ExtRat.Infinity sign * ExtRat.Number 0 = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem zero_mul_zero_eq_zero : ExtRat.Number 0 * ExtRat.Number 0 = ExtRat.Number 0 := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem zero_inv_eq_inf : (ExtRat.Number 0).inv = ExtRat.Infinity false := by
  unfold ExtRat.inv
  grind


theorem mul_comm (x y : ExtRat) : x * y = y * x := by
  rw [← ExtRat.mul_def, ← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

end InfinityBehaviour

theorem le_refl (x : ExtRat) : x ≤ x := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem le_trans {x y z : ExtRat} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  rw [← ExtRat.le_def] at hxy hyz ⊢
  unfold ExtRat.le at hxy hyz ⊢
  grind

theorem le_antisymm {x y : ExtRat} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rw [← ExtRat.le_def] at hxy hyx
  unfold ExtRat.le at hxy hyx
  grind

instance : Std.IsPartialOrder ExtRat where
  le_refl := le_refl
  le_trans := by grind [le_trans]
  le_antisymm := by grind [le_antisymm]

/-! ## ExtRat negation theory -/

@[simp]
theorem neg_eq_NaN_iff (r : ExtRat) : -r = .NaN ↔ r = .NaN := by
  cases r <;> simp [← ExtRat.neg_def, ExtRat.neg]

@[simp, grind =]
theorem neg_neg (x : ExtRat) : -(-x) = x := by
  rw [← ExtRat.neg_def, ← ExtRat.neg_def]
  unfold ExtRat.neg
  grind

/--
Negation reverses the ordering on `ExtRat`: `x ≤ y ↔ -y ≤ -x`.
-/
theorem le_iff_neg_le_neg {x y : ExtRat} :
    x ≤ y ↔ -y ≤ -x := by
  cases x <;> cases y <;> simp [← ExtRat.le_def, ← ExtRat.neg_def, ExtRat.neg, ExtRat.le] <;> grind

/--
`x ≤ -y ↔ y ≤ -x`: move negation across `≤` from right to left.
-/
@[grind =]
theorem le_neg_iff_le_neg {x y : ExtRat} :
    x ≤ -y ↔ y ≤ -x := by
  rw [le_iff_neg_le_neg (x := x) (y := -y)]
  simp [neg_neg]

/--
`-x ≤ y ↔ -y ≤ x`: move negation across `≤` from left to right.
-/
@[grind =]
theorem neg_le_iff_neg_le {x y : ExtRat} :
    -x ≤ y ↔ -y ≤ x := by
  rw [le_iff_neg_le_neg (x := -x) (y := y)]
  simp [neg_neg]

/--
Negation is antitone: if `x ≤ y` then `-y ≤ -x`.
-/
@[simp]
theorem neg_le_neg {x y : ExtRat} (h : x ≤ y) : -y ≤ -x :=
  le_iff_neg_le_neg.mp h

def isNaN (r : ExtRat) : Bool :=
  r = .NaN

@[simp] theorem isNaN_NaN : isNaN ExtRat.NaN = true := rfl
@[simp] theorem isNaN_infinity (s : Bool) : isNaN (.Infinity s) = false := rfl
@[simp] theorem isNaN_number (r : Rat) : isNaN (.Number r) = false := rfl


/-- Absolute value of an extended rational number. -/
def abs (r : ExtRat) : ExtRat :=
  match r with
  | .NaN => .NaN
  | .Infinity _sign => .Infinity false
  | .Number n => .Number (n.abs)

@[simp]
theorem abs_NaN : abs ExtRat.NaN = ExtRat.NaN := by
  simp [abs]

theorem abs_infinity (s : Bool) : abs (.Infinity s) = .Infinity false := by
  simp [abs]

@[simp]
theorem abs_Number (n : Rat) : abs (.Number n) = .Number (n.abs) := by
  simp [abs]

end ExtRat

def ExtDyadic.toExtRat (ed : ExtDyadic) : ExtRat :=
  match ed with
  | .NaN => .NaN
  | .Infinity sign => .Infinity sign
  | .Number d => .Number d.toRat

@[grind .]
def Bool.toSign (b : Bool) : Int :=
  if b then -1 else 1

@[simp]
theorem toSign_true : Bool.toSign true = -1 := rfl

@[simp]
theorem toSign_false : Bool.toSign false = 1 := rfl

@[simp]
theorem Bool.toSign_ne_zero (b : Bool) : b.toSign ≠ 0 := by
  cases b <;> simp [Bool.toSign]

theorem Bool.toSign_lt_zero_iff (b : Bool) : b.toSign < 0 ↔ b = true := by
  cases b <;> simp [Bool.toSign]

@[simp]
theorem toSign_xor_eq_toSign_mul_toSign (a b : Bool) :
  (a ^^ b).toSign = a.toSign * b.toSign := by grind [Bool.toSign]

namespace PackedFloat


def toExtDyadic (pf : PackedFloat e s) : ExtDyadic :=
  bif pf.isNaN then
    .NaN
  else bif pf.isInfinite then
    .Infinity pf.sign
  else bif pf.isZero  then
    .Number 0
  else bif pf.isNorm then
    let sig : BitVec (s + 2) := (pf.sig.cons true).setWidth' (Nat.le.step Nat.le.refl)
    let sig := bif pf.sign then -sig else sig
    .Number (.ofIntWithPrec sig.toInt (bias e - pf.ex.toNat + s))
  else
    let sig : BitVec (s + 2) := (pf.sig.cons false).setWidth' (Nat.le.step Nat.le.refl)
    let sig := bif pf.sign then -sig else sig
    .Number (.ofIntWithPrec sig.toInt (bias e - 1 + s : Nat))

@[simp]
theorem toExtDyadic_eq_NaN_of_isNaN (pf : PackedFloat e s) (hp : pf.isNaN) :
    pf.toExtDyadic = .NaN := by
  simp [toExtDyadic, hp]

@[simp]
theorem toExtDyadic_eq_Infinity_of_isInfinite (pf : PackedFloat e s) (hp : pf.isInfinite) :
    pf.toExtDyadic = .Infinity pf.sign := by
  simp only [toExtDyadic, hp, BitVec.setWidth'_eq, Int.natCast_add, cond_true]
  grind [not_isNaN_of_isInfinite]

def toExtRat (pf : PackedFloat e s) : ExtRat :=
  pf.toExtDyadic.toExtRat


/--
'An Automatable Formal Semantics for IEEE-754 Floating-Point Arithmetic',
definition from the model of floating point.

We differ in one aspect: Since we have multiple NaNs,
we declare that two NaNs are equal iff they are bit-pattern
equivalent.

This changes the partial order, such that we have
one isolated NaN for each NaN bit-pattern,
along with the usual ordering for all other values.
-/
def le (x y : PackedFloat e s) : Prop :=
    (x.isNaN ∧ y.isNaN) ∨
    (¬ x.isNaN ∧ ¬ y.isNaN ∧
      ((x.sign = true ∧ y.sign = false) ∨ -- x negative, y positive.
      (x.sign = false ∧ y.sign = false ∧ x.ex.toNat < y.ex.toNat) ∨ -- both +ve, x smaller ex.
      (x.sign = false ∧ y.sign = false ∧ x.ex = y.ex ∧ x.sig.toNat ≤ y.sig.toNat) ∨ -- both +ve, x smaller sig.
      (x.sign = true ∧ y.sign = true ∧ y.ex.toNat < x.ex.toNat) ∨ -- both -ve, y smaller ex.
      (x.sign = true ∧ y.sign = true ∧ x.ex = y.ex ∧ y.sig.toNat ≤ x.sig.toNat))
    )

instance {x y : PackedFloat e s} : Decidable (le x y) := by
  simp [le]; infer_instance

instance : LE (PackedFloat exWidth sigWidth) where
  le x y := le x y

@[simp]
theorem le_def (x y : PackedFloat e s) :
  x.le y = (x ≤ y) := rfl

def lt (x y : PackedFloat e s) : Prop :=
  x ≤ y ∧ x ≠ y

instance : LT (PackedFloat e s) where
  lt x y := x.lt y

@[simp]
theorem lt_def (x y : PackedFloat e s) :
  x.lt y = (x < y) := rfl

@[simp, grind .]
theorem le_of_lt {a b : PackedFloat e s} (h : a < b) : (a ≤ b) := by
  rw [← lt_def, lt] at h
  grind only

@[simp, grind .]
theorem ne_of_lt {a b : PackedFloat e s} (h : a < b) : ¬ (a = b) := by
  simp [← lt_def, lt] at h
  grind only


@[simp, grind .]
theorem minus_zero_le_plus_zero {e s} (he : 0 < e) :
    (PackedFloat.getZero e s true ≤ PackedFloat.getZero e s false) := by
  simp [getZero, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.isNaN]
  grind

@[simp, grind .]
theorem plus_zero_not_le_minus_zero (he : 0 < e) :
    ¬ (PackedFloat.getZero e s false ≤ PackedFloat.getZero e s true) := by
  simp [getZero, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.isNaN]
  grind

instance {x y : PackedFloat e s} : Decidable (x ≤ y) := by
    simp only [← PackedFloat.le_def]
    infer_instance

/--
The successor is the least *strict* upper bound.
This is used to show that the ordering on 'PackedFloat' is a discrete ordering,
with adjacent elements having a gap of at least '2^-s'
-/
def IsSuccessor (p q : PackedFloat e s) : Prop :=
  p < q ∧ (∀ (r : PackedFloat e s), p < r → q ≤ r)

instance {x y : PackedFloat e s} : Decidable (x < y) := by
  simp only [← PackedFloat.lt_def, PackedFloat.lt]
  infer_instance

def toRatSig {e s} (pf : PackedFloat e s) : Rat :=
  if pf.isNorm then
    1 + pf.sig.toNat / 2 ^ s
  else
    0 + pf.sig.toNat / 2 ^ s

@[simp]
theorem Rat.one_lt_two_pow_iff (x : Nat) : 1 < (2 : Rat) ^ x ↔ 1 ≤ x := by
  constructor
  · intros hlt
    have : x = 0 ∨ 1 ≤ x := by grind
    rcases this with rfl | this
    · grind
    · grind
  · intros hlt
    norm_cast
    have : ∃ y, x = y + 1 := by exact Nat.exists_eq_add_one.mpr hlt
    obtain ⟨y, hy⟩ := this
    subst hy
    simp

theorem Rat.div_le_of_le_mul (a b c : Rat) (hc : 0 < c) (hle : a ≤ b * c) : a / c ≤ b := by
  rw [Rat.div_def]
  apply Rat.mul_le_mul_cancel_right_of_lt (c := c) .. |>.mp
  · rw [show a * c⁻¹ * c = a by grind only]
    grind only
  · grind only

/--
This gives precise bounds on `toRatSig` as being bounded above by one, when it's a nonzero subnormal.
-/
@[simp]
theorem toRatSig_plus_le_one_of_isNonzeroSubnorm (pf : PackedFloat e s)
  (hnorm : pf.isNonzeroSubnorm) :
    pf.toRatSig  + 1 / 2 ^ s ≤ 1 := by
  simp [toRatSig]
  simp [show ¬ pf.isNorm by grind only [→ not_isNorm_of_isSubnorm]]
  have : pf.sig.toNat < 2 ^ s := by
    grind only [usr BitVec.isLt]
  suffices ((pf.sig.toNat : Rat) + 1) / 2 ^ s ≤ 1 by
    grind only    -- grind?
  apply Rat.div_le_of_le_mul
  · grind only [Rat.pow_pos]
  · norm_cast; simp; grind only

/--
This gives precise bounds on `toRatSig` as being bounded above by one, when it's a nonzero subnormal.
-/
@[simp]
theorem toRatSig_le_one_sub_of_isNonzeroSubnorm (pf : PackedFloat e s)
  (hnorm : pf.isNonzeroSubnorm) :
    pf.toRatSig  ≤ 1 - 1 / 2 ^ s := by
  have := toRatSig_plus_le_one_of_isNonzeroSubnorm pf hnorm
  grind only

/--
This gives precise bounds on `toRatSig` as being bounded above by two.
-/
@[simp]
theorem toRatSig_plus_le_two_of_isNorm (pf : PackedFloat e s) (hnorm : pf.isNorm) :
    pf.toRatSig  + 1 / 2 ^ s ≤ 2 := by
  simp [toRatSig, hnorm]

  suffices (pf.sig.toNat : Rat) / 2 ^ s + 1 / 2 ^ s ≤ (1 : Rat) by
    grind only
  have : pf.sig.toNat < 2 ^ s := by
    grind only [usr BitVec.isLt]
  suffices ((pf.sig.toNat : Rat) + 1) / 2 ^ s ≤ 1 by
    grind only    -- grind?
  apply Rat.div_le_of_le_mul
  · grind only [Rat.pow_pos]
  · norm_cast; simp; grind only

/--
Gives imprecise  but quantitiatve bounds on `toRatSig` as being bounded above by two,
when it's nonzero. More precise bounds are given by
`toRatSig_le_two_sub_of_isNorm` and `lt_twoRatSig_of_sig_ne_zero`.
-/
@[simp]
theorem toRatSig_plus_le_two_of_isNormOrNonzeroSubnorm
    (pf : PackedFloat e s) (hnorm : pf.isNormOrNonzeroSubnorm) :
    pf.toRatSig  + 1 / 2 ^ s ≤ 2 := by
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
  · suffices pf.toRatSig + 1 / 2^s ≤ 1 by grind
    have : pf.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    simp [this]


/--
This gives precise bounds on `toRatSig` as being bounded above by two
-/
@[simp]
theorem toRatSig_le_two_sub_of_isNorm (pf : PackedFloat e s) (hnorm : pf.isNorm) :
    pf.toRatSig  ≤ 2 - 1 / 2 ^ s := by
  have := toRatSig_plus_le_two_of_isNorm pf hnorm
  grind only


/--
`1/2^s` is a lower bound on 'toRatSig` when it's nonzero.
-/
theorem lt_twoRatSig_of_sig_ne_zero (pf : PackedFloat e s)
    (hsig : pf.sig ≠ 0#_) :
    (1 : Rat) / 2^s ≤  pf.toRatSig := by
  rw [PackedFloat.toRatSig]
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
    apply Rat.le_add_of_le_of_nonneg
    · norm_cast
      apply Rat.div_le_self_of_nonneg_of_one_le
      · grind
      · grind
    · grind only [Fp.Rat.div_nonneg, Rat.pow_nonneg]
  · simp [hnorm]
    rw [Rat.div_le_div_self]
    · apply Classical.byContradiction
      intros hcontra
      simp at hcontra
      norm_cast at hcontra
      grind only [= BitVec.ofNat_toNat, = BitVec.getElem_zero, = BitVec.getElem_setWidth,
        = BitVec.getLsbD_eq_getElem, #4929]
    · grind only [Rat.pow_pos]

/-- info: Rat.add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b -/
#guard_msgs in #check Rat.add_le_add_left

@[simp]
theorem Rat.add_lt_add_left {a b c : Rat} : c + a < c + b ↔ a < b := by
  grind

@[simp]
theorem Rat.div_add_eq_div_add_div (a b c : Rat) : a / c + b / c = (a + b) / c := by
  grind

@[simp]
theorem Rat.div_lt_cancel {a b c : Rat} (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [Rat.div_def, Rat.div_def]
  constructor
  · intros hlt
    rw [Rat.mul_lt_mul_right ] at hlt
    · grind only
    · grind only [= Rat.inv_pos]
  · intros hlt
    rw [Rat.mul_lt_mul_right]
    · grind only
    · grind only [= Rat.inv_pos]

@[simp]
theorem Rat.div_le_cancel {a b c : Rat} (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b := by
  rw [Rat.div_def, Rat.div_def]
  constructor
  · intros hle
    rw [Rat.mul_le_mul_cancel_right_of_lt] at hle
    · grind only
    · grind only [= Rat.inv_pos]
  · intros hle
    rw [Rat.mul_le_mul_cancel_right_of_lt]
    · grind only
    · grind only [= Rat.inv_pos]


/--
If we have two floating point numbers
whose significands are ordered, and whose normality is the same,
then their `toRatSig` are ordered in the same way, up to a gap of `1/2^s`.
This gives us the 'gap' between floating point numbers.
-/
theorem toRatSig_add_le_toRatSig_of_lt_of_isNorm_eq_isNorm
    (x y : PackedFloat e s)
    (hnorm : x.isNorm = y.isNorm)
    (hsig : x.sig < y.sig) :
    x.toRatSig + (1 : Rat) / 2^s ≤ y.toRatSig := by
  rw [PackedFloat.toRatSig, PackedFloat.toRatSig]
  by_cases hnorm : x.isNorm
  · by_cases hnorm' : y.isNorm
    · simp only [hnorm, ↓reduceIte, hnorm']
      rw [Rat.add_assoc]
      simp only [Rat.div_add_eq_div_add_div, Rat.add_le_iff_le']
      rw [Rat.div_le_cancel]
      · suffices x.sig.toNat < y.sig.toNat from by
          norm_cast
        rw [← BitVec.lt_def]
        simp [hsig]
      · grind only [Rat.pow_pos]
    · grind only
  · by_cases hnorm' : y.isNorm
    · grind only
    · simp [hnorm, hnorm']
      rw [Rat.div_le_cancel]
      · suffices x.sig.toNat < y.sig.toNat from by
          norm_cast
        rw [← BitVec.lt_def]
        simp [hsig]
      · grind


theorem Rat.add_div_eq_add_div' (a b d : Rat)(hd : d ≠ 0) :
  a + b / d = (a * d + b) / d := by
  grind

/--
A subnormal number's signifiand interpretation is
smaller than a normal number's, by the same gap of `1/2^s`.
-/
theorem toRatSig_add_one_div_two_pow_lt_toRatSig_of_eq_isNorm_of_not_eq_isNorm
    (x y : PackedFloat e s)
    (hxnorm : x.isNonzeroSubnorm)
    (hynorm : y.isNorm)
    (hsig : x.sig < y.sig) :
    x.toRatSig + (1 : Rat) / 2^s ≤ y.toRatSig := by
  rw [PackedFloat.toRatSig, PackedFloat.toRatSig]
  simp only [show x.isNorm = false by grind, Bool.false_eq_true, ↓reduceIte, Rat.zero_add,
    Rat.div_add_eq_div_add_div, hynorm]
  rw [Rat.add_div_eq_add_div']
  · rw [Rat.div_le_cancel]
    · norm_cast
      simp only [Nat.one_mul]
      have : 1 ≤ 2^s := by grind
      have : x.sig.toNat < y.sig.toNat := by
        rw [← BitVec.lt_def]
        simp [hsig]
      grind only
    · grind only [Rat.pow_pos]
  · grind only [Rat.two_pow_nat_ne_zero]

@[grind .]
theorem one_le_toRatSig_of_isNorm {e s} (pf : PackedFloat e s) (hnorm : pf.isNorm) :
  1 ≤ pf.toRatSig := by
  simp [toRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : (1 + pf.sig.toNat / 2^s) ≥ 0 := by grind
  grind

/-- `PackedFloat.toRatSig` is nonnegative. -/
@[simp, grind .]
theorem nonneg_toRatSig (pf : PackedFloat e s) : 0 ≤ pf.toRatSig := by
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
    Rat.pow_nonneg]
  have : (0 + pf.sig.toNat / 2^s) ≥ 0 := by grind only
  have : pf.sig.toNat / 2^s ≥ 0 := by grind only
  have : pf.sig.toNat ≥ 0 := by grind only
  simp only [toRatSig, Rat.zero_add, ge_iff_le]
  grind only

/-- Alias for `PackedFloat.nonneg_toRatSig` -/
theorem zero_le_toRatSig (pf : PackedFloat e s) : 0 ≤ pf.toRatSig :=
  nonneg_toRatSig pf

@[grind .]
theorem zero_le_twoNumberRatSig {e s} (pf : PackedFloat e s) :
  0 ≤ pf.toRatSig := by
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
    Rat.pow_nonneg]
  have : (0 + pf.sig.toNat / 2^s) ≥ 0 := by grind only
  have : pf.sig.toNat / 2^s ≥ 0 := by grind only
  have : pf.sig.toNat ≥ 0 := by grind only
  simp only [toRatSig, Rat.zero_add, ge_iff_le]
  grind only

theorem toRatSig_eq_of_isNorm {e s} {pf : PackedFloat e s} (hnorm : pf.isNorm) :
  pf.toRatSig = 1 + pf.sig.toNat / 2 ^ s := by
  simp [toRatSig, hnorm]

theorem toRatSig_eq_of_not_isNorm {e s} {pf : PackedFloat e s} (hnorm : ¬ pf.isNorm) :
  pf.toRatSig = pf.sig.toNat / 2 ^ s := by
  simp [toRatSig, hnorm]

@[grind ., simp]
theorem toRatSig_lt_one_of_not_isNorm {e s} (pf : PackedFloat e s) (hnorm : ¬ pf.isNorm) :
  pf.toRatSig < 1 := by
  simp [toRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : pf.sig.toNat < 2^s := by grind
  apply Rat.div_lt_iff .. |>.mpr
  · simp
    norm_cast
  · grind => instantiate only [Rat.pow_pos]

@[simp]
theorem toRatSig_lt_two_of_not_isNorm {e s} (pf : PackedFloat e s) (hnorm : pf.isNorm):
  pf.toRatSig < 2 := by
  simp [toRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : pf.sig.toNat < 2^s := by grind
  suffices (pf.sig.toNat : Rat) / (2 : Rat) ^ s < 1 from by
    grind
  apply Rat.div_lt_iff .. |>.mpr
  · simp
    norm_cast
  · grind => instantiate only [Rat.pow_pos]

@[grind! .]
theorem toRatSig_lt_ite {e s} (pf : PackedFloat e s) :
  pf.toRatSig < 1 + pf.isNorm.toNat := by
  by_cases hnorm : pf.isNorm
  · simp [hnorm]; grind [toRatSig_lt_two_of_not_isNorm pf hnorm]
  · simp [hnorm];

@[grind .]
theorem toRatSig_lt_two {e s} (pf : PackedFloat e s) :
  pf.toRatSig < 2 := by
  have := toRatSig_lt_ite pf
  by_cases hnorm : pf.isNorm
  · grind [toRatSig_lt_two_of_not_isNorm pf hnorm]
  · grind [toRatSig_lt_one_of_not_isNorm pf hnorm]

def toRatExp {e s} (pf : PackedFloat e s) : Int :=
  if pf.isNorm then
    pf.ex.toNat - bias e
  else
    -(bias e - 1 : Nat)

/--
Amongst packed floats
the rational exponent is monotone in the exponent if the numbers are
both normal or both subnormal.
-/
theorem toRatExp_le_toRatExp_of_ex_le_ex_of_isNorm (x y : PackedFloat e s)
  (hle : x.ex ≤ y.ex) (hnorm : x.isNorm = y.isNorm) :
  x.toRatExp ≤ y.toRatExp := by
  rw [toRatExp, toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    have : x.ex.toNat ≤ y.ex.toNat := by grind only [BitVec.le_def]
    grind only
  · simp [hnorm, show ¬ y.isNorm by grind only]

/--
Amongst packed floatswith the same normality, the rational exponent is strictly monotone in the exponent.
-/
theorem toRatExp_lt_toRatExp_of_ex_lt_ex_of_isNorm (x y : PackedFloat e s)
  (hle : x.ex < y.ex) (hnorm : x.isNorm = y.isNorm)
  (hx : x.isNormOrNonzeroSubnorm)
  (hy : y.isNormOrNonzeroSubnorm):
  x.toRatExp < y.toRatExp := by
  rw [toRatExp, toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    have : x.ex.toNat < y.ex.toNat := by grind only [BitVec.lt_def]
    grind only
  · have := x.exp_eq_of_isNonzeroSubnorm
    simp [this] at hle
    have := y.exp_eq_of_isNonzeroSubnorm
    simp [this] at hle

theorem toRatExp_le_toRatExp (x y : PackedFloat e s)
  -- (hx : x.isNormOrNonzeroSubnorm)
  (hy : y.isNormOrNonzeroSubnorm)
  (hle : x.ex ≤ y.ex) :
  x.toRatExp ≤ y.toRatExp := by
  rw [toRatExp, toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    by_cases hnorm' : y.isNorm
    · simp [hnorm']
      have : x.ex.toNat ≤ y.ex.toNat := by grind only [BitVec.le_def]
      grind only
    · -- 'x' is normal, 'y' is subnormal.
      have hxex := x.ex_ne_zero_if_isNorm
      have hyex := y.exp_eq_of_isNonzeroSubnorm
      simp [hyex] at hle
      simp at hxex
      grind only
  · simp [hnorm]
    by_cases hnorm' : y.isNorm
    · simp [hnorm']
      simp [PackedFloat.isNorm] at hnorm hnorm'
      grind only [ex_ne_zero_if_isNorm, BitVec.eq_zero_iff_toNat_eq, = BitVec.zero_eq, #41d9]
    · simp [hnorm']

@[grind .]
theorem zero_lt_ex_of_isNorm {e s} {pf : PackedFloat e s}
  (hnorm : pf.isNorm) :
    0#_ < pf.ex := by
  simp [isNorm] at hnorm
  rw [BitVec.lt_def]
  simp
  have : pf.ex.toNat = 0 ∨ 0 < pf.ex.toNat  := by grind
  rcases this with (this | hpos)
  · have : pf.ex.toNat ≠ 0 := by grind only [ex_ne_zero_if_isNorm, BitVec.eq_zero_iff_toNat_eq,
    = BitVec.zero_eq]
    grind only
  · grind only

/--
If the packed floats have the same exponent bits,
then the rational exponent they compute is equal.
-/
@[simp]
theorem toRatExp_eq_of_ex_eq (x y : PackedFloat e s) (h : x.ex = y.ex) :
  x.toRatExp = y.toRatExp := by
  simp [toRatExp]
  by_cases hnorm : x.isNorm
  · simp [hnorm]
    by_cases hnorm' : y.isNorm
    · simp [hnorm']
      simp [h]
    · simp [hnorm']
      simp [PackedFloat.isNorm] at hnorm hnorm'
      grind only
  · simp [hnorm]
    intros hynorm
    simp [PackedFloat.isNorm] at hnorm hynorm
    grind only

theorem toRatExp_eq_of_not_isNorm {e s} {pf : PackedFloat e s} (hnorm : ¬ pf.isNorm) :
  pf.toRatExp = -(bias e - 1 : Nat) := by
  simp [toRatExp, hnorm]

theorem toRatExp_eq_of_isNorm {e s} {pf : PackedFloat e s} (hnorm : pf.isNorm) :
  pf.toRatExp = pf.ex.toNat - bias e := by
  simp [toRatExp, hnorm]

-- TODO: Give this definition a better name; It exists
-- to be a nicer version of 'toRat'.
def toRat {e s} (pf : PackedFloat e s) : Rat :=
    pf.sign.toSign * pf.toRatSig * 2 ^ (pf.toRatExp)

@[simp]
theorem toRatSig_eq_zero_of_isZero {e s} (pf : PackedFloat e s) (hzero : pf.isZero := by grind) :
  pf.toRatSig = 0 := by
  simp [toRatSig]
  have hnorm : ¬ pf.isNorm := by grind
  simp [hnorm]
  have : pf.sig = 0#s := by grind
  simp only [this, BitVec.toNat_ofNat, Nat.zero_mod, Rat.natCast_ofNat]
  grind

@[grind . ]
theorem sig_ne_zero_of_isNormOrNonzeroSubnorm_of_not_isNorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) (hnorm : ¬ pf.isNorm) :
    pf.sig ≠ 0#s := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at h
  grind

attribute [grind .] Rat.natCast_eq_zero_iff

@[simp, grind .]
theorem toRatSig_ne_zero_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
  pf.toRatSig ≠ 0 := by
  simp [toRatSig]
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
    have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
      Rat.pow_nonneg]
    simp only [ne_eq]
    grind
  · simp [hnorm]
    have := sig_ne_zero_of_isNormOrNonzeroSubnorm_of_not_isNorm h (hnorm := by grind)
    have : pf.sig.toNat ≠ 0 := by grind
    have : (pf.sig.toNat : Rat) ≠ 0 := by
      grind only [Rat.natCast_eq_zero_iff]
    grind only [Fp.Rat.div_pos, Rat.pow_pos]

@[simp, grind =]
theorem toRat_eq_Zero_of_isZero {e s} (pf : PackedFloat e s) (hp : pf.isZero) :
    pf.toRat = 0 := by
  rw [toRat]
  have : pf.toRatSig = 0 := by exact toRatSig_eq_zero_of_isZero pf hp
  grind

@[simp]
theorem Rat.natCast_ne_zero_iff {n : Nat} : ((n : Rat) ≠ 0) ↔ n ≠ 0 := by
  grind

theorem toRat_ne_zero {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
    pf.toRat ≠ 0 := by
  simp [toRat]
  have : pf.sign.toSign ≠ 0 := by grind only [Bool.toSign, #26b7]
  have : pf.toRatSig ≠ 0 := by exact toRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : (2 : Rat) ^ (pf.toRatExp) > 0 := by grind only [Fp.Rat.two_pow_pos]
  rw [Rat.mul_ne_zero_iff]
  simp only [ne_eq]
  rw [Rat.mul_ne_zero_iff]
  constructor
  · constructor
    · simp
    · grind only
  · grind only

@[simp, grind →, grind =]
theorem sign_iff_toRat_neg {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
    pf.sign = decide (pf.toRat < 0) := by
  rw  [toRat]
  have : pf.toRatSig ≠ 0 := by
    exact toRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : 0 ≤ pf.toRatSig := by exact zero_le_toRatSig pf
  have : (2 : Rat) ^ pf.toRatExp > 0 := by grind only [Fp.Rat.two_pow_pos]
  by_cases hsign : pf.sign <;> simp [hsign] <;> grind

@[simp, grind =, grind =_]
theorem isZero_iff_toRat_eq_zero_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s}
    (h : pf.isNormOrNonzeroSubnorm) (he : 0 < e) :
    pf.isZero ↔ pf.toRat = 0 := by
  constructor
  · grind only [→ not_isZero_of_isNormOrSubnorm]
  · intros hzero
    simp [isZero]
    simp [show ¬ e = 0 by grind]
    simp [toRat] at hzero
    have hsign_ne_zero : pf.sign.toSign ≠ (0 : Rat) := by
      simp
    have hcontra : pf.toRatSig * 2 ^ pf.toRatExp = 0 := by
      grind
    have : (2 : Rat) ^ pf.toRatExp ≠ 0 := by
      grind only [Rat.two_pow_ne_zero]
    grind only [toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]


def toExtRat' (pf : PackedFloat e s) : ExtRat :=
  bif pf.isNaN then
    .NaN
  else bif pf.isInfinite then
    .Infinity pf.sign
  else .Number pf.toRat


@[simp, grind =]
theorem toExtRat'_eq_toRat_of {pf : PackedFloat e s} (hp : pf.isNormOrNonzeroSubnorm := by grind) :
    pf.toExtRat' =
        .Number pf.toRat := by
  have hnan : pf.isNaN = false := by
    grind [isNaN, isNormOrNonzeroSubnorm]
  have hinf : pf.isInfinite = false := by
    grind [isInfinite, isNormOrNonzeroSubnorm]
  have hzero : pf.isZero = false := by
    grind [isZero, isNormOrNonzeroSubnorm]
  simp [toExtRat', hnan, hinf, toRat]


@[simp, grind =]
theorem toExtRat'_eq_zero_of_isZero (pf : PackedFloat e s) (hp : pf.isZero) :
    pf.toExtRat' = .Number 0 := by
  have hnan : pf.isNaN = false := by
    grind [isNaN, isZero]
  have hinf : pf.isInfinite = false := by
    grind [isInfinite, isZero]
  simp only [toExtRat', hnan, hinf, cond_false, ExtRat.Number.injEq]
  grind

@[simp, grind =]
theorem toExtRat'_eq_NaN_of_isNaN (pf : PackedFloat e s) (hp : pf.isNaN) :
    pf.toExtRat' = .NaN := by
  simp [toExtRat', hp]

@[simp, grind =]
theorem toExtRat'_eq_NaN_iff_isNaN (pf : PackedFloat e s) : pf.toExtRat' = .NaN ↔ pf.isNaN := by
  constructor
  · intros h
    simp [toExtRat'] at h
    grind only [#47ab]
  · intros h
    simp [toExtRat', h]

@[simp, grind =]
theorem toExtRat'_eq_Infinity_of_isInfinite (pf : PackedFloat e s) (hp : pf.isInfinite) :
    pf.toExtRat' = .Infinity pf.sign := by
  rw [toExtRat', hp]
  grind [not_isNaN_of_isInfinite]


@[simp, grind! .] -- aggressive?
theorem toExtRat'_getInfinity {sign : Bool} (hs : 0 < s := by grind) :
    (PackedFloat.getInfinity e s sign).toExtRat' = .Infinity sign := by
  have : (PackedFloat.getInfinity e s sign).isInfinite = true := by
    grind
  simp [hs]

@[simp, grind! .]
theorem isNaN_mkNaN : (PackedFloat.getNaN e s).isNaN = true := by
  simp [getNaN, isNaN]
  grind

@[simp]
theorem toExtRat'_mkNaN :
    (PackedFloat.getNaN e s).toExtRat' = .NaN := by
  rw [toExtRat']
  simp

@[simp, grind! .]
theorem toExtRat'_getZero (sign : Bool) (he : 0 < e := by grind) :
    (PackedFloat.getZero e s sign).toExtRat' = .Number 0 := by
  rw [toExtRat']
  simp [show ¬ e = 0 by grind]
  simp [he]

/--
Case splitting on the different values a packed float
can have: it can be nan, infinity, zero, or a nonzero normal/subnormal.+
-/
@[elab_as_elim]
theorem classification {P : PackedFloat e s → Prop}
    (x : PackedFloat e s)
    (nanCase : ∀ (n : PackedFloat e s), n.isNaN → P n)
    (infCase : ∀ sign, P (PackedFloat.getInfinity e s sign))
    (zeroCase : ∀ sign, P (PackedFloat.getZero e s sign))
    (numCase : ∀ (n : PackedFloat e s), n.isNormOrNonzeroSubnorm → P n) :
    P x := by
  have := x.classification_exhaustive
  simp at this
  by_cases h1 : x.isNaN
  · grind
  · by_cases h2 : x.isInfinite
    · grind
    · by_cases h3 : x.isZero
      · grind
      · by_cases h4 : x.isNonzeroSubnorm
        · grind
        · by_cases h5 : x.isNorm
          · grind only [→ isNormOrSubnorm_of_isNorm, #d1e2]
          · grind only

@[simp, grind .]
theorem le_refl (x : PackedFloat e s) : x ≤ x := by simp [← le_def, PackedFloat.le]

@[simp, grind .]
theorem le_NaN (x : PackedFloat e s) :
    x ≤ PackedFloat.getNaN e s ↔ x.isNaN := by
  by_cases hx : x.isNaN
  · simp only [← PackedFloat.le_def, PackedFloat.le, hx]
    simp only [isNaN_mkNaN, and_self, not_true_eq_false, false_and]
    grind
  · simp only [← PackedFloat.le_def, PackedFloat.le]
    simp [hx]

@[simp, grind .]
theorem NaN_le (x : PackedFloat e s)
    : PackedFloat.getNaN e s ≤ x ↔ x.isNaN := by
  simp only [← PackedFloat.le_def, PackedFloat.le]
  simp only [isNaN_getNaN]
  by_cases hx : x.isNaN
  · simp [hx]
  · simp [hx]

@[simp, grind .]
theorem le_iff_eq_of_isNaN (x y : PackedFloat e s)
  (hx : x.isNaN) : x ≤ y ↔ y.isNaN := by
  simp only [← PackedFloat.le_def, PackedFloat.le, hx]
  simp only [not_true_eq_false, false_and]
  grind

@[simp, grind .]
theorem le_iff_eq_of_isNaN' (x y : PackedFloat e s)
  (hy : y.isNaN) : x ≤ y ↔ x.isNaN := by
  simp only [← PackedFloat.le_def, PackedFloat.le, hy]
  simp only [not_true_eq_false]
  grind

@[simp]
theorem getInfinity_le_getInfinity_iff_of_lt (sign1 sign2 : Bool) (hs : 0 < s) :
    (PackedFloat.getInfinity e s sign1 ≤ PackedFloat.getInfinity e s sign2) ↔ (sign1 = false → sign2 = false) := by
  simp only [← PackedFloat.le_def, PackedFloat.le]
  simp [hs]
  grind


/--
x is infinite iff it is equal to the infinity value with the same sign.
TODO: mark this 'simp'.
-/
@[grind .]
theorem eq_getInfinity_iff_isInfinity (hs : 0 < s)
    {x : PackedFloat e s} :
    (x.isInfinite) ↔ x = .getInfinity e s x.sign := by
  simp [getInfinity, isInfinite]
  grind [PackedFloat]


-- recall that -0 ≤ +0. So if x has sign = false, then y also needs sign = false
@[simp]
theorem le_iff_sign_eq_of_isZero (x y : PackedFloat e s)
  (hx : x.isZero) (hy : y.isZero) : x ≤ y ↔ (x.sign = false → y.sign = false) := by
  rw [← PackedFloat.le_def, PackedFloat.le]
  have hxnan : ¬ x.isNaN := by grind [isNaN, isZero]
  have hynan : ¬ y.isNaN := by grind [isNaN, isZero]
  simp [hxnan, hynan]
  simp [PackedFloat.isZero] at hx hy
  by_cases hxsign : x.sign
  · simp [hxsign]
    by_cases hysign : y.sign
    · simp [hysign]
      -- both negative zero.
      grind
    · simp [hysign]
  · simp [hxsign]
    by_cases hysign : y.sign
    · simp [hysign]
    · simp [hysign]
      grind

@[simp]
theorem PackedFloat.getZero_le_getZero_iff
    (he : 0 < e) (sign1 sign2 : Bool) :
    (PackedFloat.getZero e s sign1 ≤ PackedFloat.getZero e s sign2) ↔ (sign1 = false → sign2 = false) := by
  simp only [PackedFloat.isZero_getZero, he, decide_true, PackedFloat.le_iff_sign_eq_of_isZero,
    PackedFloat.sign_getZero]


attribute [grind .] BitVec.toNat_inj
attribute [grind .] BitVec.toInt_inj

@[grind .]
theorem le_antisymm_of_ne_NaN
  {x y : PackedFloat e s}
  (hxy : x ≤ y) (hyx : y ≤ x) (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) :
    x = y := by
  simp only [← PackedFloat.le_def] at hxy hyx
  simp only [PackedFloat.le] at hxy hyx
  simp [hx] at hxy hyx
  simp [hy] at hxy hyx
  grind [PackedFloat]

theorem le_antisymm_iff {x y : PackedFloat e s}
  (hxy : x ≤ y) (hyx : y ≤ x) :
  (x.isNaN ∧ y.isNaN) ∨ (¬ x.isNaN ∧ ¬ y.isNaN ∧ x = y) := by
  by_cases hx : x.isNaN
  · simp [hx]
    simp [hx] at hxy hyx
    grind
  · simp [hx]
    by_cases hy : y.isNaN
    · simp [hy]
      simp [hy] at hxy hyx
      grind
    · simp [hy]
      grind only [PackedFloat.le_antisymm_of_ne_NaN hxy hyx hx hy]

theorem le_trans
    {x y z : PackedFloat e s} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  simp only [← PackedFloat.le_def] at hxy hyz ⊢
  simp only [PackedFloat.le] at hxy hyz ⊢
  by_cases hx : x.isNaN
  · simp [hx] at hxy
    simp at hyz
    grind
  · simp [hx] at hxy
    simp at hyz
    by_cases hy : y.isNaN
    · simp [hy] at hxy
    · simp [hy] at hxy hyz
      by_cases hz : z.isNaN
      · simp [hz] at hxy hyz
      · simp [hz] at hxy hyz
        grind (splits := 10)
           only [BitVec.toNat_inj, #fde2d389667160e9, #54fdc8e31fc2dc1c, #bf4f9097212d569d,
          #0ddaf51762ab63df, #8dc2e2b3e678dc39, #b28eea1a75158fe1, #71fd579644e57b0a,
          #ca7289c2a156499b, #8f9092e537ef6258, #ef1611d882ec5869, #e781b8f11c51b17b,
          #2d6d3bcdb3a3b35c, #31dd348e5c4aee2a, #a7908cd812b01724, #f811994cd6c34475,
          #7d54ade5a8b64ca3, #b35f21abfee2096d]

/--
If the numbers are notNaN, then 'x ≤ y' if the x is negative and y is positive.
TODO: tag as grind.
-/
@[simp]
theorem le_of_sign_eq_true_sign_eq_false {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN) (hxsign : x.sign = true) (hysign : y.sign = false) :
    (x ≤ y) := by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only

@[simp]
theorem sign_eq_false_of_le_of_sign_eq_false_of_not_isNaN
    (x y : PackedFloat e s) (hxy : x ≤ y)
    (hnan : ¬ x.isNaN)
    (ynan : ¬ y.isNaN)
    (hySign : x.sign = false) : y.sign = false := by
  simp only [← PackedFloat.le_def] at hxy
  simp only [PackedFloat.le, hySign] at hxy
  grind only

@[simp]
theorem sign_eq_true_of_le_of_sign_eq_true_of_not_isNaN
    (x y : PackedFloat e s) (hxy : x ≤ y)
    (hnan : ¬ x.isNaN)
    (ynan : ¬ y.isNaN)
    (hySign : y.sign = true) : x.sign = true := by
  simp only [← PackedFloat.le_def] at hxy
  simp only [PackedFloat.le, hySign] at hxy
  grind only

/--
positive numbers are not greater than negative numbers, if they are not NaN.
-/
@[simp]
theorem not_le_of_sign_eq_of_sign_eq
    (x y : PackedFloat e s) (hxy : x ≤ y)
    (ynan : ¬ y.isNaN)
    (hySign : y.sign = true) (hxSign : x.sign = false) : ¬ (x ≤ y) := by
  simp only [← PackedFloat.le_def] at hxy
  simp only [PackedFloat.le, hySign] at hxy
  grind only


/--
If the numbers are notNaN, then 'x ≤ y' if the x is negative and y is positive.
-/
@[simp, grind .]
theorem not_le_of_sign_eq_false_of_sign_eq_true {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN) (hxsign : x.sign = false) (hysign : y.sign = true) :
    ¬ (x ≤ y) := by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only

@[simp, grind .]
theorem le_eq_of_sign_eq_false_of_sign_eq_false {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN := by solve | simp | grind)
    (hynan : ¬ y.isNaN := by solve | simp | grind)
    (hxsign : x.sign = false := by solve | simp | grind)
    (hysign : y.sign = false := by solve | simp | grind) :
    (x ≤ y) = ((x.ex.toNat < y.ex.toNat) ∨ (x.ex.toNat = y.ex.toNat ∧ x.sig.toNat ≤ y.sig.toNat)):= by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only [BitVec.toNat_inj, #71d0eef1ae01d63f]

@[simp, grind .]
theorem le_eq_of_sign_eq_true_of_sign_eq_true {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN := by solve | simp | grind)
    (hynan : ¬ y.isNaN := by solve | simp | grind)
    (hxsign : x.sign = true := by solve | simp | grind)
    (hysign : y.sign = true := by solve | simp | grind) :
    (x ≤ y) = ((y.ex.toNat < x.ex.toNat) ∨ (x.ex.toNat = y.ex.toNat ∧  y.sig.toNat ≤ x.sig.toNat)):= by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only [BitVec.toNat_inj, #388592556a470371]

/--
Every number is less than +∞
-/
@[simp, grind =>]
theorem le_getInfinity_false_of_not_isNaN (hs : 0 < s) (y : PackedFloat e s) :
    (y ≤ PackedFloat.getInfinity e s false) ↔ ¬ y.isNaN := by
  by_cases hnan : y.isNaN
  · simp [hnan]
    grind only [→ not_isInfinite_of_isNaN, !isInfinite_getInfinity]
  · simp [hnan]
    rw [← PackedFloat.le_def, PackedFloat.le]
    simp [hnan, hs]
    by_cases hysign : y.sign
    · simp [hysign]
    · simp [hysign]
      grind only [=> isNaN_iff_ex_eq_sig_eq, usr Nat.pow_pos, usr BitVec.isLt,
        BitVec.eq_allOnes_iff_toNat_eq, = BitVec.toNat_ofNat, = BitVec.toNat_zero]

@[simp, grind →]
theorem eq_getInfinity_of_getInfinity_le (hs : 0 < s) (y : PackedFloat e s)
  (hle : PackedFloat.getInfinity e s false ≤ y) :
  y = .getInfinity e s false := by
  have : (getInfinity e s false).sign = false := by grind
  by_cases hysign : y.sign
  · have : ¬ ((getInfinity e s false) ≤ y) := by
      grind only [le_iff_eq_of_isNaN,
        le_antisymm_of_ne_NaN, not_le_of_sign_eq_false_of_sign_eq_true,
        => le_getInfinity_false_of_not_isNaN]
    grind only
  · simp at hysign
    have hle' := hle
    rw [le_eq_of_sign_eq_false_of_sign_eq_false] at hle'
    simp at hle'
    have : y.ex.toNat = 2 ^ e - 1 := by grind only [usr Nat.pow_pos, usr BitVec.isLt]
    have : y.sig = 0#s := by grind only [le_iff_eq_of_isNaN', !isInfinite_getInfinity,
      => isNaN_iff_ex_eq_sig_eq, eq_getInfinity_iff_isInfinity, → not_isNaN_of_isInfinite,
      BitVec.eq_allOnes_iff_toNat_eq]
    apply PackedFloat.ext <;> simp <;> grind


/--
If a number is +infty, then only +infty is larger than it.
-/
@[simp]
theorem PackedFloat.getInfinity_false_le_iff_eq (hs : 0 < s)
    (y : PackedFloat e s) :
    (PackedFloat.getInfinity e s false) ≤ y ↔ y = .getInfinity e s false := by
  constructor
  · intros h
    grind only [→ eq_getInfinity_of_getInfinity_le]
  · intros h
    subst h
    grind only [le_refl]


@[grind =>, simp]
theorem PackedFloat.getInfinity_true_le_of_not_isNaN (hs : 0 < s) (y : PackedFloat e s) :
    (PackedFloat.getInfinity e s true ≤ y) ↔ ¬ y.isNaN := by
  by_cases hnan : y.isNaN
  · simp [hnan]
    grind only [→ not_isInfinite_of_isNaN, !isInfinite_getInfinity]
  · simp [hnan]
    rw [← PackedFloat.le_def, PackedFloat.le]
    simp [hnan, hs]
    by_cases hysign : y.sign
    · simp [hysign]
      grind
    · simp [hysign]

@[simp, grind .]
theorem PackedFloat.sign_eq_of_toRat_eq {x y : PackedFloat e s}
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (heq : x.toRat = y.toRat) : x.sign = y.sign := by
  by_cases hxsign : x.sign <;> grind only [→ sign_iff_toRat_neg]

-- When normal, the bases are in [1, 2),
-- so we can use the fact that the function 'base * 2^pow' is injective on this domain.
-- This follows by a fairly simple argument.
theorem mul_two_pow_inj_aux (base0 base1 : Rat)
    (pow0 pow1 : Int) (h : base0 * (2 : Rat) ^ pow0 = base1 * (2 : Rat) ^ pow1)
    (hLtBase0 : 1 ≤ base0)
    (hLtBase1 : 1 ≤ base1)
    (hBase0Lt : base0 < 2)
    -- (hBase1Lt : base1 < 2)
    (hle : pow0 ≤ pow1):
    base0 = base1 ∧ pow0 = pow1 :=
  if heq : pow0 = pow1 then by
    subst heq
    simp only [and_true] at h ⊢
    rw [← Rat.mul_cancel_right (x := 2 ^ pow0)]
    · grind only
    · grind only [Rat.twoPowNeZero]
  else by
    have hlt : pow0 < pow1 := by grind only
    have : ∃ (k : Nat), pow0 + k = pow1 := by
      exact Int.le.dest hle
    obtain ⟨k, hk⟩ := this
    have : 0 < k := by grind
    have : (2 : Rat) ≤ 2 ^ k := by
      norm_cast
      rcases k with rfl | k
      · grind only
      · rw [Nat.pow_succ]
        have : 1 ≤ 2 ^ k := by grind only [usr Nat.pow_pos]
        grind
    subst hk
    rw [Rat.zpow_add (hq := by grind only)] at h
    rw [Rat.mul_comm (2 ^ pow0)] at h
    rw [← Rat.mul_assoc base1] at h
    simp only [Rat.zpow_natCast] at h
    rw [Rat.mul_cancel_right (by grind only [Rat.twoPowNeZero])] at h
    have : base1 * (2 : Rat) ^ k < 2 := by
      subst h
      grind
    have : base1 * 2 ^ k ≥ 2 := by
      simp only [ge_iff_le]
      rw [show (2 : Rat) = 1 * 2 by grind only]
      apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg <;> grind only
    grind only

theorem mul_two_pow_inj (base0 base1 : Rat)
    (pow0 pow1 : Int) (h : base0 * (2 : Rat) ^ pow0 = base1 * (2 : Rat) ^ pow1)
    (hLtBase0 : 1 ≤ base0)
    (hLtBase1 : 1 ≤ base1)
    (hBase0Lt : base0 < 2)
    (hBase1Lt : base1 < 2) :
    base0 = base1 ∧ pow0 = pow1 := by
  by_cases hle : pow0 ≤ pow1
  · apply mul_two_pow_inj_aux <;> grind only
  · have hgt : pow1 < pow0 := by grind only
    have := mul_two_pow_inj_aux base1 base0 pow1 pow0 h.symm hLtBase1 hLtBase0 hBase1Lt (by grind only)
    grind only

/--
Show that the exponents are equal
if their interpretation as Rats are equal.
-/
theorem exp_eq_of_toRatExp_eq
  (x y : PackedFloat e s)
  (h : x.toRatExp = y.toRatExp)
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (hnorm : x.isNorm = y.isNorm) : x.ex = y.ex := by
simp [toRatExp] at h
by_cases hxnorm : x.isNorm
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : (x.ex.toNat : Int) = (y.ex.toNat : Int) := by grind only
  simp only [Int.natCast_inj] at this
  apply BitVec.eq_of_toNat_eq
  grind
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : x.isNonzeroSubnorm := by grind
  simp [this]
  have : y.isNonzeroSubnorm := by grind
  simp [this]

/--
Show that the significands are equal
if their interpretation as Rats are equal.
-/
theorem sig_eq_of_toRatSig_eq_toRatSig
  {x y : PackedFloat e s}
  (h : x.toRatSig = y.toRatSig)
  (hnorm : x.isNorm = y.isNorm) : x.sig = y.sig := by
simp [toRatSig] at h
by_cases hxnorm : x.isNorm
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : (2 ^ s : Rat) ≠ 0 := by
    apply Rat.ne_zero_of_zero_lt
    grind only [Rat.pow_pos]
  have : (x.sig.toNat : Rat) = (y.sig.toNat : Rat) := by
   grind only
  simp only [Rat.natCast_inj] at this
  apply BitVec.eq_of_toNat_eq
  grind
· simp [hxnorm] at hnorm
  simp [hxnorm, hnorm] at h
  have : (2 ^ s : Rat) ≠ 0 := by grind
  have : (x.sig.toNat : Rat) = (y.sig.toNat : Rat) := by
    grind only
  simp only [Rat.natCast_inj] at this
  apply BitVec.eq_of_toNat_eq
  grind


@[simp]
theorem le_zero_iff_sign_eq_true {x : PackedFloat e s} (he : 0 < e):
    (x ≤ PackedFloat.getZero e s true) ↔ (x.sign = true ∧ ¬ x.isNaN) := by
  by_cases hxNaN : x.isNaN
  · grind only [→ not_isZero_of_isNaN, PackedFloat.le_iff_eq_of_isNaN, isZero_getZero]
  · simp [hxNaN]
    by_cases hxsign : x.sign
    · simp [hxsign]
      rw [← PackedFloat.le_def, PackedFloat.le]
      simp [hxNaN]
      simp [show ¬ e = 0 by grind]
      simp [hxsign]
      have := BitVec.toNat_inj (x := x.ex) (y := 0#_)
      simp at this
      grind
    · simp [hxsign]
      have : (getZero e s true).sign = true := by grind only [= sign_getZero]
      grind only [not_le_of_sign_eq_false_of_sign_eq_true]

@[simp]
theorem zero_le_iff_sign_eq_false {x : PackedFloat e s} (he : 0 < e) :
  (PackedFloat.getZero e s false ≤ x) ↔ (x.sign = false ∧ ¬ x.isNaN) := by
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
    grind
  · simp [hxNaN]
    by_cases hxsign : x.sign
    · simp [hxsign]
      rw [← PackedFloat.le_def, PackedFloat.le]
      simp [hxNaN]
      simp [show ¬ e = 0 by grind]
      simp [hxsign]
    · simp [hxsign]
      have : (getZero e s false).sign = false := by grind only [= sign_getZero]
      have := le_eq_of_sign_eq_false_of_sign_eq_false (x := (getZero e s false)) (y := x)
        (by grind) (by grind) (by grind) (by grind)
      simp at this
      grind



/-- Universal quantifiers over packed floats are decidable. -/
instance {P : PackedFloat e s → Prop} [∀ (pf : PackedFloat e s), Decidable (P pf)] : Decidable (∀ (x : PackedFloat e s), P x) := by
  rcases decideProp (fun sign e s => P (PackedFloat.mk sign e s))
  case isFalse h => exact isFalse (by
    grind only [#42c0]
  )
  case isTrue h => exact isTrue (by
    intro x
    rcases x with ⟨sign, e, s⟩
    have := h sign e s
    exact this)
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop) [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∀ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance

/-- Existential quantifiers over packed floats are decidable, for a pointwise decidable packed float. -/
instance {P : PackedFloat e s → Prop} [∀ (pf : PackedFloat e s), Decidable (P pf)] : Decidable (∃ (x : PackedFloat e s), P x) := by
  rcases decideProp (fun sign e s => P (PackedFloat.mk sign e s))
  case isFalse h => exact isFalse (by
    simp at h ⊢
    intros x
    rcases x with ⟨rfl | rfl, e, s⟩
    · grind only [#7a8e]
    · grind only [#7e49]
  )
  case isTrue h => exact isTrue (by
    obtain ⟨sign, e, s, h⟩ := h
    exists (PackedFloat.mk sign e s)
  )
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop) [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∃ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance

end PackedFloat

namespace UnpackedFloat

/-- Enumerate all UnpackedFloats of a given e and s. -/
def enumerate (e s : Nat) : Array (UnpackedFloat e s) := Id.run do
  let mut out := #[]
  for b in #[true, false] do
    for ex in [0:2^e] do
      for sig in [0:2^s] do
        out := out.push { sign := b, ex := ex, sig := sig }
  return out

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
    ex := BitVec.intMin e
    sig := 0#s
  }

 @[simp]
 theorem sign_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).sign = sign := rfl

@[simp]
theorem ex_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).ex = BitVec.intMin e := rfl

@[simp]
theorem sig_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).sig = 0#s := rfl

@[bv_normalize]
def isZero (uf : UnpackedFloat e s) : Bool :=
  uf.ex == BitVec.intMin e && uf.sig == 0#s

-- | Why does the 'ex' fit?
@[bv_normalize]
def normalize (uf : UnpackedFloat e s) (sign := uf.sign) : UnpackedFloat e s :=
  bif uf.sig == 0#s then
    -- zero case: make it explicit!
    mkZero sign
  else
    {
      sign := uf.sign
      ex := uf.ex - uf.sig.clz.setWidth _
      sig := uf.sig <<< uf.sig.clz
    }


@[simp]
theorem sign_normalize (uf : UnpackedFloat e s) : (normalize uf zsign).sign =
  if uf.sig == 0#s then zsign else uf.sign := by
  grind [normalize, mkZero]

@[simp]
theorem sig_normalize (uf : UnpackedFloat e s) : (normalize uf zsign).sig =
  if uf.sig == 0#s then 0#s else uf.sig <<< uf.sig.clz := by
  grind [normalize, mkZero]

@[simp]
theorem exp_normalize (uf : UnpackedFloat e s) : (normalize uf zsign).ex =
  if uf.sig == 0#s then BitVec.intMin e else uf.ex - uf.sig.clz.setWidth _ := by
  grind [normalize, mkZero]

/--
Normalize gives a number whose most significant bit is one,
iff the number is nonzero.
-/
@[simp]
theorem msb_normalize_eq_decide (uf : UnpackedFloat e s) :
    ((normalize uf zsign).sig.msb = decide (uf.sig ≠ 0)) := by
  simp
  by_cases hs : uf.sig = 0#s <;> simp [hs]

/-- When the number is nonzero,
the normalization is idempotent iff  and its most significant bit is one.
-/
theorem normalize_eq_self_iff (uf : UnpackedFloat e s) (huf : uf.sig ≠ 0#s) :
    normalize uf zsign = uf ↔ (uf.sig.msb = true) := by
  simp [normalize]
  by_cases hs : uf.sig == 0#s
  · simp [hs]
    grind only
  · simp only [hs, cond_false]
    rcases uf with ⟨sign, ex, sig⟩
    simp only [mk.injEq, true_and]
    constructor
    · intros h
      simp only [ne_eq, beq_iff_eq] at huf hs
      obtain ⟨hex, hsig⟩ := h
      have := BitVec.shiftLeft_eq_self_iff_eq_zero.mp hsig
      rcases this with this | this
      · have := BitVec.clz_eq_zero_iff_msb_of_lt sig |>.mp (by grind)
        simp [show s ≠ 0 by grind] at this
        exact this
      · grind only
    · intros hmsb
      have : sig.clz = 0#s := by grind [BitVec.clz_eq_zero_iff_msb_of_lt]
      rw [this]
      simp only [BitVec.setWidth_zero, BitVec.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod,
        BitVec.shiftLeft_zero, and_self]


@[bv_normalize]
def toEUnpackedFloat (uf : UnpackedFloat e s) : EUnpackedFloat e s :=
  .mk .Number uf

def toDyadic (uf : UnpackedFloat e s) : Dyadic :=
  let sig : BitVec (s + 1) := uf.sig.setWidth' (Nat.le.step Nat.le.refl)
  -- | this can lead to overflow in the case where
  -- sig = intMin. negating intMin causes overflow, so we need to be careful.
  .ofIntWithPrec (uf.sign.toSign * sig.toInt) ((s - 1 : Nat) - uf.ex.toInt)

def toRat (uf : UnpackedFloat e s) : Rat :=
  uf.toDyadic.toRat

@[simp]
theorem toRat_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).toRat = 0 := by
  simp [mkZero, toRat, toDyadic]


def toSigNat (uf : UnpackedFloat e s) : Nat :=
  let sig : BitVec (s + 1) := uf.sig.setWidth' (Nat.le.step Nat.le.refl)
  sig.toNat

@[simp]
theorem toNat_toSigNat_eq (uf : UnpackedFloat e s) :
    toSigNat uf = uf.sig.toNat := by
  simp [toSigNat]

@[simp]
theorem toSigNat_of_sig_eq_zero (uf : UnpackedFloat e s)  (h : uf.sig = 0#s) :
    uf.toSigNat = 0 := by
  simp [toSigNat, h]

def toExpInt {e s} (uf : UnpackedFloat e s) : Int :=
  - ((s - 1 : Nat) - uf.ex.toInt)

def toRat' (uf : UnpackedFloat e s) : Rat :=
  uf.sign.toSign * uf.toSigNat * (2 : Rat) ^ uf.toExpInt

theorem toInt_setWidth_succ_eq_toNat (x : BitVec w) :
    (x.setWidth (w + 1)).toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp
  · grind only [= BitVec.msb_eq_getMsbD_zero, = BitVec.getMsbD_setWidth]

theorem toRat_eq_toRat' (uf : UnpackedFloat e s) : uf.toRat = uf.toRat' := by
  rw [toRat, toRat']
  rw [UnpackedFloat.toDyadic]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  simp only [BitVec.setWidth'_eq]
  rw [toInt_setWidth_succ_eq_toNat (x := uf.sig)]
  simp [toExpInt]
  norm_cast

@[bv_normalize]
def maxNormal (eout sout : Nat) (e _s : Nat) (sign : Bool) :
    UnpackedFloat eout sout :=
  {
    sign := sign
    ex := BitVec.ofInt eout (maxNormalExp e)
    sig := (BitVec.allOnes sout).zeroExtend sout
  }

@[bv_normalize]
def minSubnormal (eout sout : Nat)
  (etarget starget : Nat) (sign : Bool) :
    UnpackedFloat eout sout :=
  {
    sign := sign
    ex := BitVec.ofInt eout (minSubnormalExp etarget starget)
    sig := (BitVec.leadingOne starget).zeroExtend sout
  }

instance {P : UnpackedFloat e s → Prop}
    [∀ (uf : UnpackedFloat e s), Decidable (P uf)] : Decidable (∀ (x : UnpackedFloat e s), P x) := by
  cases hp : decideProp (fun sign ex sig => P (UnpackedFloat.mk sign ex sig))
  case isFalse h => exact isFalse (by
    simp at h ⊢
    grind only [#f34e]
  )
  case isTrue h => exact isTrue (by
    intro x
    rcases x with ⟨sign, ex, sig⟩
    have := h sign ex sig
    exact this)
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop)
      [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∀ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance


instance {P : UnpackedFloat e s → Prop}
    [∀ (uf : UnpackedFloat e s), Decidable (P uf)] : Decidable (∃ (x : UnpackedFloat e s), P x) := by
  cases hp : decideProp (fun sign ex sig => P (UnpackedFloat.mk sign ex sig))
  case isFalse h => exact isFalse (by
    simp at h ⊢
    intros x
    rcases x with ⟨rfl | rfl, ex, sig⟩
    · grind only [#b5c5]
    · grind only [#b5c5]
  )
  case isTrue h => exact isTrue (by
    obtain ⟨sign, ex, sig, h⟩ := h
    exists (UnpackedFloat.mk sign ex sig)
  )
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop)
      [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∃ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance
end UnpackedFloat

namespace EUnpackedFloat

instance {P : EUnpackedFloat e s → Prop}
    [∀ (uf : EUnpackedFloat e s), Decidable (P uf)] : Decidable (∀ (x : EUnpackedFloat e s), P x) := by
  cases hp : decideProp (fun state num => P { state := state, num := num })
  case isFalse h => exact isFalse (by
    simp at h ⊢
    grind only [#a55c]
  )
  case isTrue h => exact isTrue (by
    intro x
    rcases x with ⟨state, num⟩
    have := h state num
    exact this)
  where
  decideProp (P : State → UnpackedFloat e s → Prop)
      [∀ (state : State) (num : UnpackedFloat e s), Decidable (P state num)] : Decidable (∀ (state : State) (num : UnpackedFloat e s), P state num) := by
    infer_instance

@[bv_normalize]
theorem eq_state_ex {e s b} {x y : EUnpackedFloat e s} :
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

@[simp, grind =]
theorem eq_of_mkInfinity_eq_mkInfinity {e s} (sign1 sign2 : Bool) :
    (mkInfinity sign1 : EUnpackedFloat e s) = mkInfinity sign2 ↔ sign1 = sign2 := by
  simp [mkInfinity]

@[simp]
theorem sign_num_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).num.sign = sign := rfl

@[simp]
theorem sign_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).sign = sign := by
  simp [EUnpackedFloat.sign, mkInfinity]

@[bv_normalize]
def mkNumber (num : UnpackedFloat e s) : EUnpackedFloat e s :=
  {
    state := .Number
    num := num
  }

@[simp]
theorem state_mkNumber (num : UnpackedFloat e s) : (mkNumber num : EUnpackedFloat e s).state = .Number := rfl

@[simp]
theorem num_mkNumber (num : UnpackedFloat e s) : (mkNumber num : EUnpackedFloat e s).num = num := rfl

@[simp]
theorem isNaN_mkNaN {e s} : isNaN (EUnpackedFloat.mkNaN : EUnpackedFloat e s)  = true := rfl

@[simp]
theorem isNaN_mkInfinity {e s} {sign : Bool} : isNaN (mkInfinity sign : EUnpackedFloat e s) = false := by
  simp [isNaN, mkInfinity]

@[simp]
theorem isNaN_mkNumber {e s} (num : UnpackedFloat e s) : isNaN (mkNumber num : EUnpackedFloat e s) = false := by
  simp [isNaN, mkNumber]

@[simp]
theorem isInfinite_mkNaN {e s} : isInfinite (EUnpackedFloat.mkNaN : EUnpackedFloat e s) = false := by
  simp [isInfinite, mkNaN]

@[simp]
theorem isInfinite_mkInfinity {e s} (sign : Bool) : isInfinite (mkInfinity sign : EUnpackedFloat e s) = true := rfl

@[simp]
theorem isInfinite_mkNumber {e s} (num : UnpackedFloat e s) : isInfinite (mkNumber num : EUnpackedFloat e s) = false := by
  simp [isInfinite, mkNumber]

@[simp]
theorem isNumber_mkNaN {e s} : isNumber (EUnpackedFloat.mkNaN : EUnpackedFloat e s) = false := by
  simp [isNumber, mkNaN]

@[simp]
theorem isNumber_mkInfinity {e s} (sign : Bool) : isNumber (mkInfinity sign : EUnpackedFloat e s) = false := by
  simp [isNumber, mkInfinity]

@[simp]
theorem isNumber_mkNumber {e s} (num : UnpackedFloat e s) : isNumber (mkNumber num : EUnpackedFloat e s) = true := rfl

@[bv_normalize]
def mkZero (sign : Bool) : EUnpackedFloat e s :=
  {
    state := .Number
    num := UnpackedFloat.mkZero sign
  }

@[simp, grind =]
theorem mkZero_sign {e s} (sign : Bool) : (mkZero sign : EUnpackedFloat e s).sign = sign := by
  simp [mkZero, EUnpackedFloat.sign, UnpackedFloat.mkZero]

@[simp, grind =]
theorem mkZero_num_sign {e s} (sign : Bool) : (mkZero sign : EUnpackedFloat e s).num.sign = sign := by
  simp [mkZero, UnpackedFloat.mkZero]

@[simp, grind! .]
theorem isZero_mkZero {e s} (sign : Bool) : isZero (mkZero sign : EUnpackedFloat e s) = true := by
  simp [isZero, mkZero, UnpackedFloat.mkZero, isNumber, UnpackedFloat.isZero]

@[simp, grind! . ]
theorem isZero_mkInfinity {e s} (sign : Bool) : isZero (mkInfinity sign : EUnpackedFloat e s) = false := by
  simp [isZero, mkInfinity, isNumber, mkInfinity]

@[simp, grind! .]
theorem isZero_mkNaN {e s} : isZero (EUnpackedFloat.mkNaN : EUnpackedFloat e s) = false := by
  simp [isZero, mkNaN, isNumber, mkNaN]

@[simp, grind! .]
theorem isZero_mkNumber {e s} (num : UnpackedFloat e s) : isZero (mkNumber num : EUnpackedFloat e s) = num.isZero := by
  simp [isZero, mkNumber, isNumber, UnpackedFloat.isZero]

@[simp, grind! .]
theorem isNaN_mkZero {e s} (sign : Bool) : isNaN (EUnpackedFloat.mkZero sign : EUnpackedFloat e s) = false := by
  simp [isNaN, mkZero]

@[simp, grind! .]
theorem isInfinite_mkZero {e s} (sign : Bool) : isInfinite (EUnpackedFloat.mkZero sign : EUnpackedFloat e s) = false := by
  simp [isInfinite, mkZero]

@[simp, grind! .]
theorem isNumber_mkZero {e s} (sign : Bool) : isNumber (mkZero sign : EUnpackedFloat e s) = true := by
  simp [mkZero, UnpackedFloat.mkZero, isNumber]

@[bv_normalize]
def normalize (uf : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif uf.isNumber then
    uf.num.normalize.toEUnpackedFloat
  else
    uf

def toExtDyadic (ef : EUnpackedFloat e s) : ExtDyadic :=
  bif ef.isNaN then
    .NaN
  else bif ef.isInfinite then
    .Infinity ef.num.sign
  else
    .Number ef.num.toDyadic

def toExtRat (ef : EUnpackedFloat e s) : ExtRat :=
  bif ef.isNaN then
    .NaN
  else bif ef.isInfinite then
    .Infinity ef.num.sign
  else
    .Number ef.num.toRat

@[simp]
theorem toExtRat_mkNan : toExtRat (mkNaN : EUnpackedFloat e s) = .NaN := by
  simp [toExtRat]

@[simp]
theorem toExtRat_mkInfinity (sign : Bool) : toExtRat (mkInfinity sign : EUnpackedFloat e s) = .Infinity sign := by
  simp [toExtRat]

@[simp]
theorem toExtRat_mkZero (sign : Bool) : toExtRat (mkZero sign : EUnpackedFloat e s) = .Number 0 := by
  simp [mkZero, toExtRat,
    isNaN, isInfinite,
    show (State.Number == State.NaN) = false by rfl,
    show (State.Number == State.Infinity) = false by rfl]

@[simp]
theorem toExtRat_mkNumber (num : UnpackedFloat e s) : toExtRat (mkNumber num : EUnpackedFloat e s) = .Number num.toRat := by
  simp [toExtRat]
end EUnpackedFloat

theorem Rat.lt_mul_self_of_lt_one {y} {x : Rat} (hx0 : 0 ≤ x ∧ x < 1) (hy : 0 < y)
    : x * y < y := by
  suffices x * y < 1 * y by grind only
  apply Rat.lt_of_le_of_ne
  · apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg <;> grind only
  · intros hcontra
    rw [Rat.mul_cancel_right] at hcontra <;> grind only


namespace PackedFloat

/--
Subnormal numbers are smaller than '2^minNormalExp'.
-/
@[simp, grind .]
theorem toRatSig_mul_toRatExp_lt_two_pow_minNormalExp_of_isNonzeroSubnorm {x : PackedFloat e s}
    (hx : x.isNonzeroSubnorm) :
      x.toRatSig * (2 : Rat) ^ x.toRatExp < (2 : Rat) ^ minNormalExp e := by
  rw [toRatExp_eq_of_not_isNorm]
  apply Rat.lt_mul_self_of_lt_one
  · grind only [zero_le_twoNumberRatSig, !toRatSig_lt_ite, → not_isSubnorm_of_isNorm,
    Rat.natCast_eq_zero_iff, = Bool.toNat.eq_1]
  · grind only [Fp.Rat.two_pow_pos]
  · grind only [→ not_isNorm_of_isSubnorm]



@[simp, grind .]
theorem two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm
    {x : PackedFloat e s}
    (hx : x.isNorm) :
    (2 : Rat) ^ minNormalExp e ≤ x.toRatSig * (2 : Rat) ^ x.toRatExp  := by
  rw [x.toRatExp_eq_of_isNorm (by grind only)]
  norm_cast
  -- rw [Rat.zpow_sub_eq_zpow_mul_zpow]
  have : 1 ≤ x.toRatSig := by grind only [one_le_toRatSig_of_isNorm]
  rw [minNormalExp]
  have : x.ex ≠ 0 := by grind only [ex_ne_zero_if_isNorm, = BitVec.ofNat_eq_ofNat,
    = BitVec.zero_eq]
  norm_cast
    -- 2 ^ - (bias e - 1) ≤ 2 ^ (- bias e)
  have : (2 : Rat) ^ ((- ((bias e - 1) : Nat)) : Int) ≤ (2 : Rat) ^ (((x.ex.toNat: Int) - (bias e : Int)) : Int) := by
    norm_cast
    apply Rat.two_pow_le_two_pow_of_le
    grind
  apply Rat.le_mul_of_one_le_of_le
  · grind only
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · grind only

/--
write being isNorm in terms of an arithmetic condition in terms of
the rational values of the significand and exponent.
-/
theorem isNorm_iff_toRatSig_times_toRatExp_ge
    {x : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) :
    x.isNorm ↔ decide ((2 : Rat) ^ minNormalExp e ≤ x.toRatSig * (2 : Rat) ^ x.toRatExp) := by
  simp only [decide_eq_true_eq]
  constructor
  · apply two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm
  · apply Classical.byContradiction
    intros h
    simp at h
    have := x.toRatSig_mul_toRatExp_lt_two_pow_minNormalExp_of_isNonzeroSubnorm (by grind)
    grind only

/--
This is true because we can separate out the
cases of normal and subnormal based on values,
and the largest subnormal is smaller than the smallest normal.
-/
@[simp, grind .]
theorem isNorm_eq_of_toRat_eq {x y : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
    (heq : x.toRat = y.toRat) :
    (x.isNorm = y.isNorm) := by
  have hsign : x.sign = y.sign := by
    apply PackedFloat.sign_eq_of_toRat_eq hx hy heq
  have h' := heq
  simp [toRat] at h'
  rw [hsign] at h'
  have : x.toRatSig * 2 ^ x.toRatExp = y.toRatSig * 2 ^ y.toRatExp := by
    rw [← Rat.mul_cancel_left (x := x.sign.toSign)]
    · grind
    · simp
  have xval := x.isNorm_iff_toRatSig_times_toRatExp_ge (by grind)
  have yval := y.isNorm_iff_toRatSig_times_toRatExp_ge (by grind)
  rcases hxnorm : x.isNorm
  · simp [hxnorm] at this xval
    rcases hynorm : y.isNorm
    · simp only
    · simp only [hynorm, two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm, decide_true,
      Bool.false_eq_true] at this yval ⊢
      grind only [two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm]
  · simp [hxnorm] at this xval
    rcases hynorm : y.isNorm
    · simp [hynorm] at this yval ⊢
      grind only [two_pow_minNormalExp_le_toRatSig_mul_two_pow_toRatExp_of_isNorm]
    · simp only


@[simp, grind .]
theorem sig_eq_and_ex_eq_of_toRat_eq {x y : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
    (heq : x.toRat = y.toRat) :
    x.sign = y.sign ∧ x.sig = y.sig ∧ x.ex = y.ex := by
  have hNormState := PackedFloat.isNorm_eq_of_toRat_eq hx hy heq
  have hSignEq : x.sign = y.sign := by
    apply PackedFloat.sign_eq_of_toRat_eq hx hy heq
  simp [toRat] at heq
  rw [hSignEq] at heq
  simp [hSignEq]
  have : x.toRatSig  * 2 ^ x.toRatExp = y.toRatSig * 2 ^ y.toRatExp := by
    rw [← Rat.mul_cancel_left (x := x.sign.toSign)]
    · grind
    · simp
  have xsigNeZero : x.toRatSig ≠ 0 := by grind only [toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
  have ySigNeZero : y.toRatSig ≠ 0 := by grind only [toRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
  by_cases hxnorm : x.isNorm
  · have := mul_two_pow_inj
      x.toRatSig
      y.toRatSig
      x.toRatExp
      y.toRatExp
      (by grind only)
      (by grind only [one_le_toRatSig_of_isNorm])
      (by grind only [one_le_toRatSig_of_isNorm])
      (by grind only [toRatSig_lt_two])
      (by grind only [toRatSig_lt_two])
    -- now I need to know that 'toRatSig', 'toRatExp' are equal.
    have hSigEq := sig_eq_of_toRatSig_eq_toRatSig
       (x := x) (y := y) (by grind) (by grind)
    simp [hSigEq]
    have hExpEq := exp_eq_of_toRatExp_eq
      (x := x) (y := y) (by grind) (by grind) (by grind) (by grind)
    simp [hExpEq]
  · have xSubnorm : x.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    have ySubnorm : y.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    have expEq : x.toRatExp = y.toRatExp := by
      simp [x.toRatExp_eq_of_not_isNorm (by grind only)]
      simp [y.toRatExp_eq_of_not_isNorm (by grind only)]
    have sigEq : x.toRatSig = y.toRatSig := by
      rw [← Rat.mul_cancel_right (x := 2 ^ x.toRatExp)]
      · rw [expEq]
        grind only
      · grind only [Rat.two_pow_int_ne_zero]
    have : x.sig = y.sig := by
      rw [x.toRatSig_eq_of_not_isNorm (by grind only)] at sigEq
      rw [y.toRatSig_eq_of_not_isNorm (by grind only)] at sigEq
      have hTwoPowNeZero : (2 : Rat) ^ s ≠ 0 := by norm_cast; grind only [usr Nat.pow_pos]
      rw [Rat.div_cancel hTwoPowNeZero] at sigEq
      simp at sigEq
      apply BitVec.eq_of_toNat_eq
      assumption
    simp [this]
    rw [exp_eq_of_isNonzeroSubnorm (by grind only)]
    rw [exp_eq_of_isNonzeroSubnorm (by grind only)]


@[simp, grind =>]
theorem le_getInfinity_true_iff_eq (hs : 0 < s)
    (y : PackedFloat e s) :
    y ≤ PackedFloat.getInfinity e s true ↔ y = .getInfinity e s true := by
  constructor
  · intros h
    grind only [PackedFloat.le_iff_eq_of_isNaN, PackedFloat.le_iff_eq_of_isNaN', le_antisymm_of_ne_NaN,
      => PackedFloat.getInfinity_true_le_of_not_isNaN]
  · intros h
    subst h
    grind only [PackedFloat.le_refl]

@[grind =]
theorem isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero {pf : PackedFloat e s} (h : ¬ pf.isNaN) (h2 : ¬ pf.isInfinite) (h3 : ¬ pf.isZero) :
    pf.isNormOrNonzeroSubnorm := by
  simp [PackedFloat.isNormOrNonzeroSubnorm]
  simp [PackedFloat.isNaN] at h
  simp [PackedFloat.isInfinite] at h2
  simp [PackedFloat.isZero] at h3
  grind

theorem eq_of_toExtRat'_eq (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero)
    (h : x.toExtRat' = y.toExtRat') : x = y := by
  simp [PackedFloat.toExtRat'] at h
  have hExtRateq := h
  simp [hx, hy] at h
  by_cases hxinf : x.isInfinite
  · simp [hxinf] at h
    by_cases hyinf : y.isInfinite
    · simp [hyinf] at h
      grind only [PackedFloat.eq_getInfinity_iff_isInfinity, → eq_mkInfinity_of_isInfinite,
        !isInfinite_getInfinity, #5505cb0d9cd21b53]
    · by_cases hyinf : y.isInfinite
      · simp [hyinf] at h
        grind only
      · simp [hyinf] at h
  · simp [hxinf] at h
    by_cases hyinf : y.isInfinite
    · simp [hyinf] at h
    · simp [hyinf] at h
      have :=
        PackedFloat.sig_eq_and_ex_eq_of_toRat_eq (x := x) (y := y)
        (by grind only [= isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero])
        (by grind only [= isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero])
        (by grind)
      apply PackedFloat.ext <;> grind only


/--
info: 'PackedFloat.eq_of_toExtRat'_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_of_toExtRat'_eq


@[grind ., grind =]
theorem isNaN_iff_toExtRat'_eq_NaN (x : PackedFloat e s) (hs : 0 < s) :
    x.isNaN ↔ x.toExtRat' = .NaN := by
  constructor
  · intros h
    simp [h]
  · intros hx
    induction x using PackedFloat.classification <;> grind

@[simp]
theorem PackedFloat.zero_le_toExtRat'_iff (x : PackedFloat e s) :
    ExtRat.Number 0 ≤ x.toExtRat' ↔ (¬ x.isNaN ∧ (x.isZero ∨ x.sign = false)) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp
      · simp; grind only [→ PackedFloat.not_isZero_of_isInfinite]
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind

@[simp]
theorem PackedFloat.le_zero_toExtRat'_iff (x : PackedFloat e s) :
    x.toExtRat' ≤ .Number 0 ↔ (¬ x.isNaN ∧ (x.isZero ∨ x.sign = true)) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp
        grind only [→ not_isZero_of_isInfinite]
      · simp
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind


@[simp]
theorem PackedFloat.lt_zero_toExtRat'_iff (x : PackedFloat e s) :
    x.toExtRat' < .Number 0 ↔ (¬ x.isNaN ∧ ¬ x.isZero ∧ x.sign = true) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp
      · simp; grind only [→ not_isZero_of_isInfinite]
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind

@[simp]
theorem PackedFloat.zero_lt_toExtRat'_iff (x : PackedFloat e s) :
    .Number 0 < x.toExtRat' ↔ (¬ x.isNaN ∧ ¬ x.isZero ∧ x.sign = false) := by
  simp [PackedFloat.toExtRat']
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
  · simp [hxNaN]
    by_cases hxInf : x.isInfinite
    · simp [hxInf]
      -- | TODO: this should be 'grind' able, I need to lint grind.
      rcases x.sign
      · simp; grind only [→ not_isZero_of_isInfinite]
      · simp;
    · simp [hxInf]
      by_cases hxZero : x.isZero
      · simp [hxZero]
      · simp [hxZero]
        grind

@[simp]
theorem eq_getInfinity_iff_toExtRat'_eq_Infinity (x : PackedFloat e s)
    (sign : Bool)
    (hs : 0 < s := by solve | simp | grind) :
    x.toExtRat' = ExtRat.Infinity sign ↔ x  = PackedFloat.getInfinity e s sign := by
  grind only [= toExtRat'_eq_Infinity_of_isInfinite, = toExtRat'_eq_NaN_of_isNaN,
    = toExtRat'_eq_zero_of_isZero, = toExtRat'_eq_toRat_of,
    !toExtRat'_getInfinity, !isInfinite_getInfinity, eq_getInfinity_iff_isInfinity,
    = isNaN_iff_toExtRat'_eq_NaN, = isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero, #8ef6]

@[simp]
theorem isNorm_maxNormalNumber_eq_decide
    (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).isNorm =
    decide (2 < exWidth) := by
  simp [PackedFloat.maxNormalNumber, isNorm]
  rcases exWidth with rfl | rfl | rfl | exWidth
  · simp; grind only
  · simp; grind only
  · simp [BitVec.intMax, BitVec.twoPow]
  · simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, decide_true, Bool.and_eq_true,
    bne_iff_ne, ne_eq]
    constructor
    · intros hcontra
      have := BitVec.toInt_inj.mpr hcontra
      simp only [BitVec.toInt_sub, BitVec.toInt_intMax, Nat.add_one_sub_one,
        Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, BitVec.toInt_one_of_lt, BitVec.toInt_allOnes,
        ↓reduceIte, Int.reduceNeg] at this
      rw [Int.bmod_eq_of_le] at this
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · grind only
    · intros hcontra
      have := BitVec.toInt_inj.mpr hcontra
      simp only [BitVec.toInt_sub, BitVec.toInt_intMax, Nat.add_one_sub_one,
        Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, BitVec.toInt_one_of_lt,
        BitVec.toInt_zero] at this
      rw [Int.bmod_eq_of_le] at this
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · have : 4 ≤ 2 ^ (exWidth + 2) := by grind only
        grind only
      · grind only

@[simp]
theorem isNorm_minNormalNumber (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.minNormalNumber e s sign).isNorm = true := by
  simp [PackedFloat.minNormalNumber, isNorm]
  constructor
  · apply BitVec.toNat_ne_iff_ne.mp
    simp
    rw [Nat.mod_eq_of_lt (by grind)]
    have : 2^2 ≤ 2 ^ e := by
      exact Fp.Nat.two_pow_le_two_pow_of_le he
    grind only
  · grind only

@[simp]
theorem toRatSig_minNormalNumber (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.minNormalNumber e s sign).toRatSig = 1 := by
  rw [toRatSig]
  simp [isNorm_minNormalNumber, he]
  grind only

@[simp]
theorem toRatExp_minNormalNumber (e s : Nat) (he : 1 < e) (sign : Bool) :
    (PackedFloat.minNormalNumber e s sign).toRatExp = minNormalExp e := by
  rw [toRatExp]
  simp [isNorm_minNormalNumber, he]
  norm_cast
  rw [Nat.mod_eq_of_lt (by grind)]
  rw [minNormalExp]
  have : 0 < bias e := by exact bias_pos_of_one_lt e he
  grind only


@[simp]
theorem toRatSig_maxNormalNumber (e s : Nat) (he : 2 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).toRatSig = 2 - 2 ^ (- (s : Int)) := by
  rw [toRatSig]
  simp [isNorm_maxNormalNumber_eq_decide, he]
  have : 0 < 2 ^ s := by grind only [!Nat.two_pow_pos]
  rw [Rat.natCast_sub_of_le (by grind only)]
  simp
  rw [Rat.sub_div_eq_div_sub_div]
  rw [Rat.div_self_eq_one_of_ne_zero (by grind only [Rat.two_pow_nat_ne_zero])]
  rw [Rat.one_div_zpow_natCast_eq_zpow_neg]
  grind only

@[simp]
theorem BitVec.ofInt_eq_zero_iff_of_width_1 :
    BitVec.ofInt 1 i = 0#1 ↔ i % 2 = 0 := by
  constructor
  · intros h
    have := BitVec.toInt_inj.mpr h
    simp only [BitVec.toInt_ofInt, BitVec.toInt_zero] at this
    simp at this
    grind only [#8803]
  · intros h
    apply BitVec.eq_of_toInt_eq
    simp
    grind only [#8803]

@[simp]
theorem isNonzeroSubnorm_minSubnormalNumber_eq_of_lt
    (exWidth sigWidth : Nat) (sign : Bool)
    (he : 1 < exWidth) (hs : 0 < sigWidth) :
    (PackedFloat.minSubnormalNumber exWidth sigWidth sign).isNonzeroSubnorm =
    true := by
  simp [PackedFloat.minSubnormalNumber, isNonzeroSubnorm]
  simp [show ¬ sigWidth = 0 by grind only]
  simp [show ¬ exWidth = 0 by grind only]

theorem isNonzeroSubnorm_maxSubnormalNumber_eq_of_lt
    (exWidth sigWidth : Nat) (sign : Bool)
    (he : 1 < exWidth) (hs : 0 < sigWidth) :
    (PackedFloat.maxSubnormalNumber exWidth sigWidth sign).isNonzeroSubnorm =
    true := by
  simp [PackedFloat.maxSubnormalNumber, isNonzeroSubnorm]
  simp [show ¬ sigWidth = 0 by grind only]
  simp [show ¬ exWidth = 0 by grind only]


-- TODO: show that
--    PackedFloat.minSubnormalNumber.toRat =
--    UnpackedFloat.minSubnormalNumber.toRat
-- TODO: show that
--    PackedFloat.maxNormalNumber.toRat =
--    UnpackedFloat.maxNormalNumber.toRat
end PackedFloat

namespace UnpackedFloat


theorem two_zpow_mul_two_zpow_neg_eq_one (z : Int) :
  (2 : Rat) ^ z * (2 : Rat) ^ (-z) = 1 := by
  rw [← Rat.zpow_add (by decide)]
  rw [show z + (-z) = 0 by grind]
  simp

/-
Use this to simplify exponentiation in Q,
since grind knows the field axioms,
and can correctly deduce from this
that these are multiplicative inverses.
-/
theorem two_pow_mul_two_pow_neg_intCast_eq_one (z : Nat) :
  (2 : Rat) ^ z * (2 : Rat) ^ (-( z : Int)) = 1 := by
  have := two_zpow_mul_two_zpow_neg_eq_one (z := z)
  simp at this ⊢
  grind only

-- TODO: find a more natural phrasing that
-- this does not overflow.
-- TODO: this is also in Fp/Theorems/Packing.lean, called 'toRat_normalize_eq_toRat'.
-- Find a way to remove this duplication.
theorem UnpackedFloat.toRat_normalize_eq {uf : UnpackedFloat e s}
  (hex : -(↑(2 ^ e) / 2) ≤ uf.ex.toInt - ↑uf.sig.clz.toNat) :
  uf.normalize.toRat = uf.toRat := by
  simp only [UnpackedFloat.toRat_eq_toRat']
  simp only [toRat', sign_normalize, beq_iff_eq, ite_self]
  rw [UnpackedFloat.normalize]
  by_cases hsig : uf.sig = 0#s
  · simp [hsig]
  · simp only [show ¬uf.sig == 0#s by grind, BitVec.shiftLeft_eq', cond_false]
    simp only [toNat_toSigNat_eq]
    rw [toNat_shiftLeft_clz_eq_toNat]
    simp only [toExpInt, BitVec.toInt_sub, BitVec.toInt_setWidth,
      Int.sub_bmod_bmod]

    have : uf.ex.toInt.bmod (2^e) = uf.ex.toInt := by
      rw [BitVec.toInt_eq_toNat_bmod]
      simp
    have hbmod : (uf.ex.toInt - uf.sig.clz.toNat).bmod (2^e) = uf.ex.toInt - uf.sig.clz.toNat := by
      rw [Int.bmod_eq_of_le]
      · grind
      · grind only [usr BitVec.two_mul_toInt_lt]
    rw [hbmod]
    have := BitVec.toNat_lt_two_pow_sub_clz (x := uf.sig) (w := s)
    rw [Nat.shiftLeft_eq]
    simp
    push_cast
    simp only [Int.neg_sub]
    simp only [Rat.zpow_sub_eq_zpow_mul_zpow (b := 2) (hb := by decide)]
    grind only [two_pow_mul_two_pow_neg_intCast_eq_one]

end UnpackedFloat

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
