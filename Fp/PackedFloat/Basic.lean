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

end PackedFloat
