import Fp.Utils
import Fp.ForLean.Dyadic
import Fp.Grind

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

theorem BitVec.allOnes_ne_zero {e : Nat} :
    e = 0 ∨ BitVec.allOnes e ≠ BitVec.zero e := by
  match e with
  | 0     => left; rfl
  | e + 1 =>
    right
    simp only [BitVec.allOnes, BitVec.zero, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNatLT]
    grind [Nat.two_pow_pos]

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

/--
Returns the maximum (magnitude) value for the given sign.
-/
@[bv_normalize]
def getMax (exWidth sigWidth : Nat) (sign : Bool)
  : PackedFloat exWidth sigWidth where
  sign
  ex := BitVec.allOnes exWidth - 1
  sig := BitVec.allOnes sigWidth

@[simp]
theorem sign_getMax (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getMax exWidth sigWidth sign).sign = sign := rfl

@[simp]
theorem sig_getMax (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getMax exWidth sigWidth sign).sig = BitVec.allOnes sigWidth := rfl

@[simp]
theorem ex_getMax (exWidth sigWidth : Nat) (sign : Bool) :
    (PackedFloat.getMax exWidth sigWidth sign).ex = BitVec.allOnes exWidth - 1 := rfl

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
    pf.isZero →  ∃ (sign : Bool), pf = PackedFloat.getZero e s sign := by
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

@[grind →]
theorem isZeroOrSubnorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → pf.isZeroOrSubnorm := by
  grind [isZero, isZeroOrSubnorm]

@[grind →]
theorem isZeroOrSubnorm_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → pf.isZeroOrSubnorm := by
  grind [isNonzeroSubnorm, isZeroOrSubnorm]



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
  : a.isNormOrNonzeroSubnorm → a.toEFixed.state = .Number := by
  simp_all [toEFixed, isNaN, isInfinite]

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
  deriving Inhabited, Repr

attribute [bv_normalize] UnpackedFloat.ext_iff


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

theorem ExtRat.zero_def : ExtRat.Number 0 = (0 : ExtRat) := rfl

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

instance : Sub ExtRat where
  sub a b := sub a b

@[simp]
theorem sub_def {a b : ExtRat} : a.sub b = a - b := rfl

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

def lt (x y : ExtRat) : Bool :=
  x.le y && !(x.eq y)

instance : LT ExtRat where
  lt a b := lt a b

@[simp]
theorem lt_def {a b : ExtRat} : a.lt b = (a < b) := rfl

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


def isNaN (r : ExtRat) : Bool :=
  r = .NaN

@[simp] theorem isNaN_NaN : isNaN ExtRat.NaN = true := rfl
@[simp] theorem isNaN_infinity (s : Bool) : isNaN (.Infinity s) = false := rfl
@[simp] theorem isNaN_number (r : Rat) : isNaN (.Number r) = false := rfl

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

@[bv_normalize]
def bias (e : Nat) : Nat :=
  2 ^ (e - 1) - 1

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
    (x.isNaN ∧ y.isNaN ∧ x = y) ∨
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

@[simp, grind =]
theorem minus_zero_le_plus_zero {e s} :
    (PackedFloat.getZero e s true ≤ PackedFloat.getZero e s false) =
    (e = 0 → s ≠ 0) := by
  simp [getZero, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.isNaN]

@[simp, grind .]
theorem plus_zero_not_le_minus_zero :
    ¬ (PackedFloat.getZero e s false ≤ PackedFloat.getZero e s true) := by
  simp [getZero, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.isNaN]


instance {x y : PackedFloat e s} : Decidable (x ≤ y) := by
    simp only [← PackedFloat.le_def]
    infer_instance

def toNumberRatSig {e s} (pf : PackedFloat e s) : Rat :=
  if pf.isNorm then
    1 + pf.sig.toNat / 2 ^ s
  else
    0 + pf.sig.toNat / 2 ^ s


theorem toRatNumberSig_eq_of_isNorm {e s} {pf : PackedFloat e s} (hnorm : pf.isNorm) :
  pf.toNumberRatSig = 1 + pf.sig.toNat / 2 ^ s := by
  simp [toNumberRatSig, hnorm]

theorem toRatNumberSig_eq_of_not_isNorm {e s} {pf : PackedFloat e s} (hnorm : ¬ pf.isNorm) :
  pf.toNumberRatSig = pf.sig.toNat / 2 ^ s := by
  simp [toNumberRatSig, hnorm]

theorem toNumberRatSig_lt_one_of_not_isNorm {e s} (pf : PackedFloat e s) (hnorm : ¬ pf.isNorm) :
  pf.toNumberRatSig < 1 := by
  simp [toNumberRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : pf.sig.toNat < 2^s := by grind
  apply Rat.div_lt_iff .. |>.mpr
  · simp
    norm_cast
  · grind => instantiate only [Rat.pow_pos]

theorem toNumberRatSig_lt_two_of_not_isNorm {e s} (pf : PackedFloat e s) (hnorm : pf.isNorm):
  pf.toNumberRatSig < 2 := by
  simp [toNumberRatSig, hnorm]
  have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
  have : pf.sig.toNat < 2^s := by grind
  suffices (pf.sig.toNat : Rat) / (2 : Rat) ^ s < 1 from by
    grind
  apply Rat.div_lt_iff .. |>.mpr
  · simp
    norm_cast
  · grind => instantiate only [Rat.pow_pos]

@[grind! .]
theorem toNumberRatSig_lt_ite {e s} (pf : PackedFloat e s) :
  pf.toNumberRatSig < 1 + pf.isNorm.toNat := by
  by_cases hnorm : pf.isNorm
  · simp [hnorm]; grind [toNumberRatSig_lt_two_of_not_isNorm pf hnorm]
  · simp [hnorm]; grind [toNumberRatSig_lt_one_of_not_isNorm pf hnorm]

@[grind .]
theorem toNumberRatSig_lt_two {e s} (pf : PackedFloat e s) :
  pf.toNumberRatSig < 2 := by
  have := toNumberRatSig_lt_ite pf
  by_cases hnorm : pf.isNorm
  · grind [toNumberRatSig_lt_two_of_not_isNorm pf hnorm]
  · grind [toNumberRatSig_lt_one_of_not_isNorm pf hnorm]

def toNumberRatExp {e s} (pf : PackedFloat e s) : Int :=
  if pf.isNorm then
    pf.ex.toNat - bias e
  else
    -(bias e - 1 : Nat)

theorem toNumberRatExp_eq_of_not_isNorm {e s} {pf : PackedFloat e s} (hnorm : ¬ pf.isNorm) :
  pf.toNumberRatExp = -(bias e - 1 : Nat) := by
  simp [toNumberRatExp, hnorm]

theorem toNumberRatExp_eq_of_isNorm {e s} {pf : PackedFloat e s} (hnorm : pf.isNorm) :
  pf.toNumberRatExp = pf.ex.toNat - bias e := by
  simp [toNumberRatExp, hnorm]

def toNumberRat {e s} (pf : PackedFloat e s) : Rat :=
    pf.sign.toSign * pf.toNumberRatSig * 2 ^ (pf.toNumberRatExp)


@[simp]
theorem toNumberRatSig_eq_zero_of_isZero {e s} (pf : PackedFloat e s) (hzero : pf.isZero := by grind) :
  pf.toNumberRatSig = 0 := by
  simp [toNumberRatSig]
  have hnorm : ¬ pf.isNorm := by grind
  simp [hnorm]
  have : pf.sig = 0#s := by grind
  simp only [this, BitVec.toNat_ofNat, Nat.zero_mod, Rat.natCast_ofNat]
  grind

@[simp, grind .]
theorem zero_le_toNumberRatSig {e s} (pf : PackedFloat e s) :
  0 ≤ pf.toNumberRatSig  := by
  simp [toNumberRatSig]
  by_cases hnorm : pf.isNorm
  · simp [hnorm]
    have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind only [Fp.Rat.div_nonneg,
      Rat.pow_nonneg]
    have : (1 + pf.sig.toNat / 2^s) ≥ 0 := by grind
    grind
  · simp [hnorm]
    have : (pf.sig.toNat : Rat) / (2 : Rat) ^ s ≥ 0 := by grind
    have : (0 + pf.sig.toNat / 2^s) ≥ 0 := by grind
    grind

@[grind . ]
theorem sig_ne_zero_of_isNormOrNonzeroSubnorm_of_not_isNorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) (hnorm : ¬ pf.isNorm) :
    pf.sig ≠ 0#s := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at h
  grind

attribute [grind .] Rat.natCast_eq_zero_iff

@[simp, grind .]
theorem toNumberRatSig_ne_zero_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
  pf.toNumberRatSig ≠ 0 := by
  simp [toNumberRatSig]
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
theorem toNumberRat_eq_Zero_of_isZero {e s} (pf : PackedFloat e s) (hp : pf.isZero) :
    pf.toNumberRat = 0 := by
  rw [toNumberRat]
  have : pf.toNumberRatSig = 0 := by exact toNumberRatSig_eq_zero_of_isZero pf hp
  grind

@[simp]
theorem Rat.natCast_ne_zero_iff {n : Nat} : ((n : Rat) ≠ 0) ↔ n ≠ 0 := by
  grind

theorem toNumberRat_ne_zero {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
    pf.toNumberRat ≠ 0 := by
  simp [toNumberRat]
  have : pf.sign.toSign ≠ 0 := by grind only [Bool.toSign, #26b7]
  have : pf.toNumberRatSig ≠ 0 := by exact toNumberRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : (2 : Rat) ^ (pf.toNumberRatExp) > 0 := by grind only [Fp.Rat.two_pow_pos]
  rw [Rat.mul_ne_zero_iff]
  simp only [ne_eq]
  rw [Rat.mul_ne_zero_iff]
  constructor
  · constructor
    · simp
    · grind only
  · grind only

@[simp, grind →, grind =]
theorem sign_iff_toNumberRat_neg {pf : PackedFloat e s} (h : pf.isNormOrNonzeroSubnorm) :
    pf.sign = decide (pf.toNumberRat < 0) := by
  rw  [toNumberRat]
  have : pf.toNumberRatSig ≠ 0 := by
    exact toNumberRatSig_ne_zero_of_isNormOrNonzeroSubnorm h
  have : 0 ≤ pf.toNumberRatSig := by exact zero_le_toNumberRatSig pf
  have : (2 : Rat) ^ pf.toNumberRatExp > 0 := by grind only [Fp.Rat.two_pow_pos]
  by_cases hsign : pf.sign <;> simp [hsign] <;> grind


def toExtRat' (pf : PackedFloat e s) : ExtRat :=
  bif pf.isNaN then
    .NaN
  else bif pf.isInfinite then
    .Infinity pf.sign
  else .Number pf.toNumberRat


@[simp]
theorem toExtRat'_eq_Number_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} (hp : pf.isNormOrNonzeroSubnorm := by grind) :
    pf.toExtRat' =
        .Number pf.toNumberRat := by
  have hnan : pf.isNaN = false := by
    grind [isNaN, isNormOrNonzeroSubnorm]
  have hinf : pf.isInfinite = false := by
    grind [isInfinite, isNormOrNonzeroSubnorm]
  have hzero : pf.isZero = false := by
    grind [isZero, isNormOrNonzeroSubnorm]
  simp [toExtRat', hnan, hinf, toNumberRat]


@[simp]
theorem toExtRat'_eq_zero_of_isZero (pf : PackedFloat e s) (hp : pf.isZero) :
    pf.toExtRat' = .Number 0 := by
  have hnan : pf.isNaN = false := by
    grind [isNaN, isZero]
  have hinf : pf.isInfinite = false := by
    grind [isInfinite, isZero]
  simp only [toExtRat', hnan, hinf, cond_false, ExtRat.Number.injEq]
  grind

@[simp]
theorem toExtRat'_eq_NaN_of_isNaN (pf : PackedFloat e s) (hp : pf.isNaN) :
    pf.toExtRat' = .NaN := by
  simp [toExtRat', hp]

@[simp]
theorem toExtRat'_eq_Infinity_of_isInfinite (pf : PackedFloat e s) (hp : pf.isInfinite) :
    pf.toExtRat' = .Infinity pf.sign := by
  rw [toExtRat', hp]
  grind [not_isNaN_of_isInfinite]


@[simp, grind! .]
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
theorem toExtRat'_getZero (sign : Bool) (he : 0 < e := by grind) (hs : 0 < s := by grind) :
    (PackedFloat.getZero e s sign).toExtRat' = .Number 0 := by
  rw [toExtRat']
  simp [show ¬ s = 0 by grind]
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
theorem PackedFloat.le_refl (x : PackedFloat e s) : x ≤ x := by simp [← PackedFloat.le_def, PackedFloat.le]

@[simp, grind .]
theorem PackedFloat.le_NaN (x : PackedFloat e s) :
    x ≤ PackedFloat.getNaN e s ↔ x = PackedFloat.getNaN e s := by
  by_cases hx : x.isNaN
  · simp only [← PackedFloat.le_def, PackedFloat.le, hx]
    simp only [isNaN_mkNaN, and_self, not_true_eq_false, false_and]
    grind
  · simp only [← PackedFloat.le_def, PackedFloat.le]
    simp [hx]
    grind

@[simp, grind .]
theorem PackedFloat.NaN_le (x : PackedFloat e s)
    : PackedFloat.getNaN e s ≤ x ↔ x = PackedFloat.getNaN e s := by
  simp only [← PackedFloat.le_def, PackedFloat.le]
  simp only [isNaN_getNaN]
  by_cases hx : x.isNaN
  · simp [hx]
    grind
  · simp [hx]
    grind

@[simp, grind .]
theorem PackedFloat.le_iff_eq_of_isNaN (x y : PackedFloat e s)
  (hx : x.isNaN) : x ≤ y ↔ x = y := by
  simp only [← PackedFloat.le_def, PackedFloat.le, hx]
  simp only [not_true_eq_false, false_and]
  grind

@[simp, grind .]
theorem PackedFloat.le_iff_eq_of_isNaN' (x y : PackedFloat e s)
  (hy : y.isNaN) : x ≤ y ↔ x = y := by
  simp only [← PackedFloat.le_def, PackedFloat.le, hy]
  simp only [not_true_eq_false]
  grind

/--
x is infinite iff it is equal to the infinity value with the same sign.
-/
@[grind .]
theorem PackedFloat.eq_getInfinity_iff_isInfinity (hs : 0 < s)
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

attribute [grind .] BitVec.toNat_inj
attribute [grind .] BitVec.toInt_inj

@[grind .]
theorem PackedFloat.le_antisymm_of_ne_NaN
  {x y : PackedFloat e s}
  (hxy : x ≤ y) (hyx : y ≤ x) (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) :
    x = y := by
  simp only [← PackedFloat.le_def] at hxy hyx
  simp only [PackedFloat.le] at hxy hyx
  simp [hx] at hxy hyx
  simp [hy] at hxy hyx
  grind [PackedFloat]

theorem PackedFloat.le_antisymm_iff {x y : PackedFloat e s}
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

theorem PackedFloat.le_trans
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

/-
If the numbers are notNaN, then 'x ≤ y' if the x is negative and y is positive.
-/
@[simp]
theorem le_of_sign_eq_true_sign_eq_false {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN) (hxsign : x.sign = true) (hysign : y.sign = false) :
    (x ≤ y) := by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only

/-
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
  grind only [BitVec.toNat_inj, #0bf13ef81725cfb4]

@[simp, grind .]
theorem le_eq_of_sign_eq_true_of_sign_eq_true {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN := by solve | simp | grind)
    (hynan : ¬ y.isNaN := by solve | simp | grind)
    (hxsign : x.sign = true := by solve | simp | grind)
    (hysign : y.sign = true := by solve | simp | grind) :
    (x ≤ y) = ((y.ex.toNat < x.ex.toNat) ∨ (x.ex.toNat = y.ex.toNat ∧  y.sig.toNat ≤ x.sig.toNat)):= by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only [BitVec.toNat_inj, #1f279ccc014b26d2]

/--
Every number is less than +∞
-/
@[grind =>]
theorem PackedFloat.le_getInfinity_false_of_not_isNaN (hs : 0 < s) (y : PackedFloat e s) :
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
theorem PackedFloat.eq_getInfinity_of_getInfinity_le (hs : 0 < s) (y : PackedFloat e s)
  (hle : PackedFloat.getInfinity e s false ≤ y) :
  y = .getInfinity e s false := by
  have : (getInfinity e s false).sign = false := by grind
  by_cases hysign : y.sign
  · have : ¬ ((getInfinity e s false) ≤ y) := by grind only [le_iff_eq_of_isNaN,
    not_le_of_sign_eq_false_of_sign_eq_true]
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


@[grind =>]
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
theorem PackedFloat.sign_eq_of_toNumberRat_eq {x y : PackedFloat e s}
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (heq : x.toNumberRat = y.toNumberRat) : x.sign = y.sign := by
  by_cases hxsign : x.sign <;> grind only [→ sign_iff_toNumberRat_neg]

@[simp, grind .]
theorem Rat.div_cancel {p q d : Rat} (hd : d ≠ 0) :
    (p / d = q / d) <-> p = q := by
  rw [Rat.div_def, Rat.div_def]
  rw [Rat.mul_cancel_right]
  · grind

@[grind .]
theorem Rat.twoPowNeZero (n : Int) : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  grind only [Fp.Rat.two_pow_pos]

-- when subnormal, note that the exponent is zero, so it follows trivially that the
-- bases are zero.
-- When normal, the bases are in [1, 2), so we can use the fact that the function 'base * 2^pow' is injective on this domain.
theorem mul_two_pow_inj (base0 base1 : Rat)
    (pow0 pow1 : Int) (h : base0 * (2 : Rat) ^ pow0 = base1 * (2 : Rat) ^ pow1)
    (hLtBase0 : 1 ≤ base0)
    (hLtBase1 : 1 ≤ base1)
    (hBase0Lt : base0 < 2)
    (hBase1Lt : base1 < 2) :
  base0 = base1 ∧ pow0 = pow1 := by
  sorry


attribute [grind .] Rat.pow_pos

@[grind .]
theorem Rat.two_pow_int_ne_zero {n : Int} : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  apply Rat.zpow_pos
  grind only

@[grind .]
theorem Rat.two_pow_nat_ne_zero {n : Nat} : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  exact Nat.two_pow_pos n


/--
Show that the exponents are equal
if their interpretation as Rats are equal.
-/
theorem exp_eq_of_toNumberRatExp_eq
  (x y : PackedFloat e s)
  (h : x.toNumberRatExp = y.toNumberRatExp)
  (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
  (hnorm : x.isNorm = y.isNorm) : x.ex = y.ex := by
simp [toNumberRatExp] at h
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
theorem sig_eq_of_toNumberRatSig_eq_toNumberRatSig
  {x y : PackedFloat e s}
  (h : x.toNumberRatSig = y.toNumberRatSig)
  (hnorm : x.isNorm = y.isNorm) : x.sig = y.sig := by
simp [toNumberRatSig] at h
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

@[simp, grind .]
theorem PackedFloat.sig_eq_and_ex_eq_of_toNumberRat_eq {x y : PackedFloat e s}
    (hx : x.isNormOrNonzeroSubnorm) (hy : y.isNormOrNonzeroSubnorm)
    (hnormState : x.isNorm ↔ y.isNorm)
    (heq : x.toNumberRat = y.toNumberRat) :
    x.sign = y.sign ∧ x.sig = y.sig ∧ x.ex = y.ex := by
  have hSignEq : x.sign = y.sign := by
    apply PackedFloat.sign_eq_of_toNumberRat_eq hx hy heq
  simp [PackedFloat.toNumberRat] at heq
  rw [hSignEq] at heq
  simp [hSignEq]
  have : x.toNumberRatSig  * 2 ^ x.toNumberRatExp = y.toNumberRatSig * 2 ^ y.toNumberRatExp := by
    rw [← Rat.mul_cancel_left (x := x.sign.toSign)]
    · grind
    · simp
  have xsigNeZero : x.toNumberRatSig ≠ 0 := by grind only [toNumberRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
  have ySigNeZero : y.toNumberRatSig ≠ 0 := by grind only [toNumberRatSig_ne_zero_of_isNormOrNonzeroSubnorm]
  by_cases hxnorm : x.isNorm
  · have := mul_two_pow_inj
      x.toNumberRatSig
      y.toNumberRatSig
      x.toNumberRatExp
      y.toNumberRatExp
      (by grind)
      (by sorry)
      sorry
      sorry
      sorry
    -- now I need to know that 'toNumberRatSig', 'toNumberRatExp' are equal.
    have hSigEq := sig_eq_of_toNumberRatSig_eq_toNumberRatSig
       (x := x) (y := y) (by grind) (by grind)
    simp [hSigEq]
    have hExpEq := exp_eq_of_toNumberRatExp_eq
      (x := x) (y := y) (by grind) (by grind) (by grind) (by grind)
    simp [hExpEq]
  · have xSubnorm : x.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    have ySubnorm : y.isNonzeroSubnorm := by grind only [isNormOrSubnorm_eq_isNorm_or_isSubnorm]
    have expEq : x.toNumberRatExp = y.toNumberRatExp := by
      simp [x.toNumberRatExp_eq_of_not_isNorm (by grind only)]
      simp [y.toNumberRatExp_eq_of_not_isNorm (by grind only)]
    have sigEq : x.toNumberRatSig = y.toNumberRatSig := by
      rw [← Rat.mul_cancel_right (x := 2 ^ x.toNumberRatExp)]
      · rw [expEq]
        grind only
      · grind?
    have : x.sig = y.sig := by
      rw [x.toRatNumberSig_eq_of_not_isNorm (by grind only)] at sigEq
      rw [y.toRatNumberSig_eq_of_not_isNorm (by grind only)] at sigEq
      have hTwoPowNeZero : (2 : Rat) ^ s ≠ 0 := by norm_cast; grind only [usr Nat.pow_pos]
      rw [Rat.div_cancel hTwoPowNeZero] at sigEq
      simp at sigEq
      apply BitVec.eq_of_toNat_eq
      assumption
    simp [this]
    rw [exp_eq_of_isNonzeroSubnorm (by grind only)]
    rw [exp_eq_of_isNonzeroSubnorm (by grind only)]

#exit


@[simp, grind =>]
theorem PackedFloat.le_getInfinity_true_iff_eq (hs : 0 < s)
    (y : PackedFloat e s) :
    y ≤ PackedFloat.getInfinity e s true ↔ y = .getInfinity e s true := by
  constructor
  · intros h
    grind only [le_iff_eq_of_isNaN, le_iff_eq_of_isNaN', le_antisymm_of_ne_NaN,
      => getInfinity_true_le_of_not_isNaN]
  · intros h
    subst h
    grind only [le_refl]

@[grind =]
theorem isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero {pf : PackedFloat e s} (h : ¬ pf.isNaN) (h2 : ¬ pf.isInfinite) (h3 : ¬ pf.isZero) :
    pf.isNormOrNonzeroSubnorm := by
  simp [isNormOrNonzeroSubnorm]
  simp [isNaN] at h
  simp [isInfinite] at h2
  simp [isZero] at h3
  grind

@[grind ., simp]
theorem Rat.two_pow_ne_zero (n : Int) : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  grind

theorem Rat.lt_of_lt_mul_of_one_lt {left right large: Rat} (hr : 1 < large) (h : left < right)
    : left < right * large := by
  sorry


/-- a lower bound on the division of two numbers. -/
theorem lt_div {num den lnum uden : Rat}
    (huden : 0 < den)
    (hnum : lnum < num) (hden : den < uden) :
    lnum / uden < num / den := by
  rw [Rat.div_lt_iff]
  · rw [Rat.div_def]
    have : 1 < den⁻¹ * uden := by
      rw [Rat.mul_comm]
      rw [← Rat.div_def]
      rw [Rat.lt_div_iff]
      · simp; grind
      · grind
    · rw [Rat.mul_assoc]
      apply Rat.lt_of_lt_mul_of_one_lt this
      grind
  · grind only


-- when subnormal, note that the exponent is zero, so it follows trivially that the
-- bases are zero.
-- When normal, the bases are in [1, 2), so we can use the fact that the function 'base * 2^pow' is injective on this domain.
theorem technical_lemma_when_normal (base0 base1 : Rat)
    (pow0 pow1 : Int) (h : base0 * (2 : Rat) ^ pow0 = base1 * (2 : Rat) ^ pow1)
    (hLtBase0 : 1 ≤ base0)
    (hLtBase1 : 1 ≤ base1)
    (hBase0Lt : base0 < 2)
    (hBase1Lt : base1 < 2) :
  base0 = base1 ∧ pow0 = pow1 := by
  sorry

theorem eq_of_toExtRat'_eq (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero)
    (h : x.toExtRat' = y.toExtRat') : x = y := by
  simp [toExtRat'] at h
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
      rw [PackedFloat.toNumberRat, PackedFloat.toNumberRat] at h
      apply PackedFloat.ext
      · apply PackedFloat.sign_eq_of_toNumberRat_eq
        · grind
        · grind
        · grind
      · sorry

      -- 1. signs are equal if toNumberRat is equal.
      -- 2. Then, sig * exp are equal. However, because these have different 'ranges', it must be that sig and exp are separately equal?
      --   How to make this formal? Is this true?
      sorry

      -- simp [hxzero] at h
      -- simp [hyzero] at h
      -- by_cases hx : x.isNorm
      -- · simp [hx] at h
      --   by_cases hy : y.isNorm
      --   · simp [hy] at h
      --     sorry
      --   · simp [hy] at h
      --     sorry
      -- · simp [hx] at h
      --   by_cases hy : y.isNorm
      --   · simp [hy] at h
      --     sorry
      --   · simp [hy] at h
      --     sorry

@[simp]
theorem le_iff_toExtRat'_le_toExtRat'_of_not_isZero (he : 0 < e) (hs : 0 < s)
    (x y : PackedFloat e s)
    (hxzero : ¬ x.isZero) (hyzero : ¬ y.isZero) (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN) :
    x ≤ y ↔ x.toExtRat' ≤ y.toExtRat' := by
  constructor
  · intros h
    sorry
  · intros h
    sorry

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
theorem zero_le_iff_sign_eq_false {x : PackedFloat e s} (he : 0 < e):
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

@[bv_normalize]
def toEUnpackedFloat (uf : UnpackedFloat e s) : EUnpackedFloat e s :=
  .mk .Number uf

def toDyadic (uf : UnpackedFloat e s) : Dyadic :=
  let sig : BitVec (s + 1) := uf.sig.setWidth' (Nat.le.step Nat.le.refl)
  let sig := bif uf.sign then -sig else sig
  .ofIntWithPrec sig.toInt ((s - 1 : Nat) - uf.ex.toInt)

def toRat (uf : UnpackedFloat e s) : Rat :=
  uf.toDyadic.toRat


end UnpackedFloat

namespace EUnpackedFloat

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
theorem toExtRat_mkNumber (num : UnpackedFloat e s) : toExtRat (mkNumber num : EUnpackedFloat e s) = .Number num.toRat := by
  simp [toExtRat]
end EUnpackedFloat

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
