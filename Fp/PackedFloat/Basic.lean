import Fp.Utils
import Fp.Utils.Dyadic
import Fp.Utils.Rat
import Fp.Grind
import Fp.Constants.Basic
import Fp.Sign.Basic
import Fp.EFixedPoint
import Fp.ExtDyadic.Basic
import Fp.ExtRat

/-!
## Packed Floating Point Numbers
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
  ex := BitVec.allOnes exWidth - 1#_
  sig := BitVec.allOnes sigWidth

@[simp]
theorem sign_maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).sig = BitVec.allOnes sigWidth := rfl

@[simp]
theorem ex_maxNormalNumber (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.maxNormalNumber exWidth sigWidth sign).ex =
    BitVec.allOnes exWidth - 1#exWidth := rfl

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

@[bv_normalize]
def isInfinite (pf : PackedFloat e s) : Bool :=
  -- Prioritize `Infinity` over `0`. This is somewhat arbitrary.
  pf.ex == .allOnes e && (s != 0 && pf.sig == .zero s)

-- TODO: delete the 'e=0' case, since a lot of the basic theory
-- just breaks down.
@[bv_normalize]
def isZero (pf : PackedFloat e s) : Bool :=
  -- Prioritize `0` over `Subnormals`.
  e != 0 && pf.ex == .zero e && pf.sig == .zero s

@[bv_normalize]
def isNonzeroSubnorm (pf : PackedFloat e s) : Bool :=
  e != 0 && pf.ex == .zero e && pf.sig != .zero s

-- See that this means that it is a number.
-- We need a different one to say that it is nonzero.
-- | does this also need a 'e != 0' condition?
@[bv_normalize]
def isNorm {e s} (pf : PackedFloat e s) : Bool :=
  pf.ex != .allOnes e && pf.ex != .zero e

@[simp, bv_normalize]
def isNormOrNonzeroSubnorm (pf : PackedFloat e s) : Bool :=
  pf.ex != .allOnes e && (pf.ex != .zero e || pf.sig != .zero s)
  -- e != 0 && pf.ex != BitVec.allOnes e

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

-- TODO: there's EquivUptoNaN, and 'smtLibEq'.
-- I should probably switch to 'EquivUptoNaN' in 'Rel',
-- and then show that this is equivalent to 'smtLibEq' or whatever
def EquivUptoNaN {e s : Nat} (x y : PackedFloat e s) : Prop :=
  x = y ∨ (x.isNaN ∧ y.isNaN)

theorem EquivUptoNaN.of_isNaN_isNaN (x y : PackedFloat e s) (hx : x.isNaN) (hy : y.isNaN) : EquivUptoNaN x y :=
  by simp [EquivUptoNaN, hx, hy]

theorem EquivUptoNaN.of_eq (x y : PackedFloat e s) (h : x = y) : EquivUptoNaN x y := by simp [EquivUptoNaN, h]

theorem EquivUptoNaN_symm (x y : PackedFloat e s) : EquivUptoNaN x y ↔ EquivUptoNaN y x := by
  simp [EquivUptoNaN]
  grind

theorem EquivUptoNaN.refl (x : PackedFloat e s) : EquivUptoNaN x x :=
  EquivUptoNaN.of_eq x x rfl

theorem EquivUptoNaN.symm {x y : PackedFloat e s} (h : EquivUptoNaN x y) : EquivUptoNaN y x :=
  (EquivUptoNaN_symm x y).mp h

theorem EquivUptoNaN.trans {x y z : PackedFloat e s}
    (hxy : EquivUptoNaN x y) (hyz : EquivUptoNaN y z) : EquivUptoNaN x z := by
  unfold EquivUptoNaN at *
  grind

/--
`EquivUptoNaN` is an equivalence relation, so it induces a `Setoid` on
`PackedFloat`. This is the relation we quotient by to obtain `SmtLibPackedFloat`
(see `Fp/SmtLibPackedFloat.lean`).
-/
instance instSetoidEquivUptoNaN (e s : Nat) : Setoid (PackedFloat e s) where
  r := EquivUptoNaN
  iseqv := ⟨EquivUptoNaN.refl, EquivUptoNaN.symm, EquivUptoNaN.trans⟩

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

@[simp, bv_normalize]
def equal_denotation (a b : PackedFloat e s) : Bool :=
  (a.sign == b.sign && a.ex == b.ex && a.sig == b.sig) ||
  (a.isNaN && b.isNaN)

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
  simp only [neg_def, neg, Bool.not_not]

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
  simp [abs, neg_def, neg]

/--
Get the next packed float away from zero, i.e.
the smallest packed float that is greater than `x` if `x` is positive,
and the largest packed float that is smaller than `x` if `x` is negative.
-/
def successorAwayFromZero (x : PackedFloat e s) : PackedFloat e s :=
  if x.isNaN
  then x
  else if x.isInfinite
  then PackedFloat.getInfinity e s x.sign
  else
    let sig := x.sig
    if sig ≠ BitVec.allOnes s
    then sigSucc
    else exSucc
  where
    sigSucc : PackedFloat e s := ⟨x.sign, x.ex, x.sig + 1#s⟩
    exSucc : PackedFloat e s := ⟨x.sign, x.ex + 1#e, 0#s⟩

end PackedFloat

-- Constants

/-- E5M2 floating point representation of 1.0 -/
@[bv_normalize]
def oneE5M2       := PackedFloat.ofBits 5 2 0b00111100#8
/-- E5M2 floating point representation of 2.0 -/
@[bv_normalize]
def twoE5M2       := PackedFloat.ofBits 5 2 0b01000000#8
/-- E3M4 floating point representation of 1.0 -/
@[bv_normalize]
def oneE3M4       := PackedFloat.ofBits 3 4 0b00110000#8
/-- E3M4 floating point representation of 2.0 -/
@[bv_normalize]
def twoE3M4       := PackedFloat.ofBits 3 4 0b01000000#8
/-- Smallest (positive) normal number in E5M2 floating point. -/
@[bv_normalize]
def minNormE5M2   := PackedFloat.ofBits 5 2 0b00000100#8
/-- Smallest (positive) subnormal number in E5M2 floating point. -/
@[bv_normalize]
def minSubnormE5M2 := PackedFloat.ofBits 5 2 0b00000001#8

namespace PackedFloat

@[simp, grind =]
theorem zero_eq_allOnes_eq_decide (e : Nat) :
    (0#e = BitVec.allOnes e) = decide (e = 0) := by
  by_cases he : 0 = e
  · subst he
    simp
  · simp [show ¬ e = 0 by omega]

@[simp, grind =]
theorem allOnes_eq_zero_eq_decide (e : Nat) :
    (BitVec.allOnes e = 0#e) = decide (e = 0) := by
  have := zero_eq_allOnes_eq_decide e
  grind

@[simp, grind =]
theorem zero_ne_allOnes_eq_decide (e : Nat) :
    (0#e ≠ BitVec.allOnes e) = decide (0 < e) := by
  grind

-- Theorems about classification

theorem classification_exhaustive (pf : PackedFloat e s) :
    pf.isNaN || pf.isInfinite || pf.isZero || pf.isNonzeroSubnorm || pf.isNorm := by
  grind [isNaN, isInfinite, isZero, isNonzeroSubnorm, isNorm]

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

theorem isNumber_of_isNormOrSubnorm (a : PackedFloat e s)
  : a.isNormOrNonzeroSubnorm → a.toEFixed.state = .Number := by
  simp_all [toEFixed, isNaN, isInfinite]

def toDyadic? (pf : PackedFloat e s) : Option Dyadic :=
  pf.toEFixed.toDyadic?

def toRat? (pf : PackedFloat e s) : Option Rat :=
  pf.toEFixed.toRat?

end PackedFloat






def ExtDyadic.toExtRat (ed : ExtDyadic) : ExtRat :=
  match ed with
  | .NaN => .NaN
  | .Infinity sign => .Infinity sign
  | .Number d => .Number d.toRat

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

instance {x y : PackedFloat e s} : Decidable (x ≤ y) := by
    simp only [← PackedFloat.le_def]
    infer_instance

instance {x y : PackedFloat e s} : Decidable (x < y) := by
  simp only [← PackedFloat.lt_def, PackedFloat.lt]
  infer_instance

def toRatSig {e s} (pf : PackedFloat e s) : Rat :=
  if pf.isNorm then
    1 + pf.sig.toNat / 2 ^ s
  else
    0 + pf.sig.toNat / 2 ^ s

/-- info: Rat.add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b -/
#guard_msgs in #check Rat.add_le_add_left

def toRatExp {e s} (pf : PackedFloat e s) : Int :=
  if pf.isNorm then
    -- ex ≠ 0
    pf.ex.toNat - bias e -- smallest: 1 - bias e
  else
    -(bias e - 1 : Nat) -- (1 - bias e)

-- TODO: Give this definition a better name; It exists
-- to be a nicer version of 'toRat'.
def toRat {e s} (pf : PackedFloat e s) : Rat :=
    pf.sign.toSign * pf.toRatSig * 2 ^ (pf.toRatExp)


def toExtRat' (pf : PackedFloat e s) : ExtRat :=
  bif pf.isNaN then
    .NaN
  else bif pf.isInfinite then
    .Infinity pf.sign
  else .Number pf.toRat


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

/-- Universal quantifiers over packed floats are decidable. -/
instance {P : PackedFloat e s → Prop} [∀ (pf : PackedFloat e s), Decidable (P pf)] : Decidable (∀ (x : PackedFloat e s), P x) := by
  rcases decideProp (fun sign e s => P (PackedFloat.mk sign e s))
  case isFalse h => exact isFalse (by
    grind
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
    · grind
    · grind
  )
  case isTrue h => exact isTrue (by
    obtain ⟨sign, e, s, h⟩ := h
    exists (PackedFloat.mk sign e s)
  )
  where
  decideProp (P : Bool → BitVec e → BitVec s → Prop) [∀ (b : Bool) (e : BitVec e) (s : BitVec s), Decidable (P b e s)] : Decidable (∃ (sign : Bool) (ex : BitVec e) (sig : BitVec s), P sign ex sig) := by
    infer_instance

end PackedFloat


namespace PackedFloat

end PackedFloat


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
