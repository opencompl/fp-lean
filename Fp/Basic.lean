import Fp.Utils
import Fp.Utils.Dyadic
import Fp.Grind
import Fp.Utils.Rat
import Fp.Constants.Basic
import Fp.Sign.Basic
import Fp.PackedFloat.Basic
import Fp.EFixedPoint.Basic
import Fp.UnpackedFloat.Basic
import Fp.EUnpackedFloat.Basic
import Fp.ExtDyadic.Basic
import Fp.ExtRat.Basic

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
negate the number in an EUnpackedFloat.
-/
def EUnpackedFloat.neg (x : EUnpackedFloat e s) : EUnpackedFloat e s :=
  { x with num := - x.num }

instance : Neg (EUnpackedFloat e s) where
  neg := .neg

@[simp]
theorem EUnpackedFloat.neg_def (x : EUnpackedFloat e s) : EUnpackedFloat.neg x  = -x := rfl

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

theorem lt_of_not_le {a b : ExtRat} (ha : a ≠ .NaN) (hb : b ≠ .NaN)
  (h : ¬ (a ≤ b)) : (b < a) := by
  rcases a with rfl | sign | r
  · simp at ha
  · simp at ha
    rcases sign with rfl | rfl
    · simp at h
      simp
      grind only
    · simp at h
      grind only
  · simp at ha
    rcases b with rfl | sign' | r'
    · simp at hb
    · simp at hb
      rcases sign' with rfl | rfl
      · simp at h
      · simp at h
        simp
    · simp at hb
      simp at h
      simp
      grind only


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

@[simp, grind =]
theorem le_NaN (x : ExtRat) : ExtRat.NaN ≤ x ↔ x = ExtRat.NaN := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

@[simp, grind =]
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

@[simp]
theorem isNaN_iff (r : ExtRat) : isNaN r = decide (r = .NaN) := by
  simp [isNaN]
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


theorem Rat.add_div_eq_add_div' (a b d : Rat)(hd : d ≠ 0) :
  a + b / d = (a * d + b) / d := by
  grind

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


attribute [grind .] Rat.natCast_eq_zero_iff

@[simp]
theorem Rat.natCast_ne_zero_iff {n : Nat} : ((n : Rat) ≠ 0) ↔ n ≠ 0 := by
  grind

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

attribute [grind .] BitVec.toNat_inj
attribute [grind .] BitVec.toInt_inj

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
  -- | We don't need the exponent to be `intMin`, as the unpacked float
  -- value is zero iff the significand it zero.
  uf.sig == 0#s

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


/--
Normalize is idempotent when the most significant bit is one,
as such a number is already normalized.
-/
theorem normalize_eq_self_of_msb_eq_true (uf : UnpackedFloat e s)
    (hmsb : uf.sig.msb = true) :
    normalize uf zsign = uf := by
  rw [normalize_eq_self_iff]
  · simp [hmsb]
  · grind only [= BitVec.msb_eq_getMsbD_zero, = BitVec.getMsbD_zero]

/--
info: 'UnpackedFloat.normalize_eq_self_of_msb_eq_true' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms normalize_eq_self_of_msb_eq_true


@[bv_normalize]
def toEUnpackedFloat (uf : UnpackedFloat e s) : EUnpackedFloat e s :=
  .mk .Number uf

@[simp]
theorem state_toEUnpackedFloat (uf : UnpackedFloat e s) : uf.toEUnpackedFloat = .mk .Number uf := rfl

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
  uf.sig.toNat

@[simp]
theorem toNat_toSigNat_eq (uf : UnpackedFloat e s) :
    toSigNat uf = uf.sig.toNat := rfl

@[simp]
theorem toSigNat_of_sig_eq_zero (uf : UnpackedFloat e s)  (h : uf.sig = 0#s) :
    uf.toSigNat = 0 := by
  simp [toSigNat, h]

def toExpInt {e s} (uf : UnpackedFloat e s) (prec : Nat := s - 1): Int :=
  - ((prec) - uf.ex.toInt)

@[simp]
theorem toExpInt_neg (uf : UnpackedFloat e s) :
  (- uf).toExpInt prec = uf.toExpInt prec := by
  simp [toExpInt]

/--
Evaluate the value of the UnpackedFloat at a given precicsion, which by default
is `s - 1`.
-/
def toRat' (uf : UnpackedFloat e s) (prec : Nat := s - 1): Rat :=
  uf.sign.toSign * uf.toSigNat * (2 : Rat) ^ uf.toExpInt prec

@[simp]
theorem toRat'_mkZero (sign : Bool) : (mkZero sign : UnpackedFloat e s).toRat' prec = 0 := by
  simp [mkZero, toRat']

@[simp, grind =>]
theorem toRat'_eq_zero_iff_isZero (uf : UnpackedFloat e s) (prec : Nat) :
    uf.isZero ↔ uf.toRat' prec = 0 := by
  simp [toRat']
  simp [UnpackedFloat.isZero]
  grind only [= BitVec.toNat_zero, = BitVec.ofNat_toNat, = BitVec.getElem_zero,
    = BitVec.getElem_setWidth, = BitVec.getLsbD_eq_getElem, #b51e, #2e5b]

@[simp, grind =>]
theorem toRat'_ne_zero_iff_not_isZero (uf : UnpackedFloat e s) :
    ¬ uf.isZero ↔ ¬ uf.toRat' prec = 0 := by
  have := uf.toRat'_eq_zero_iff_isZero  prec
  grind

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

@[grind =>, simp]
theorem toRat'_eq_zero_of_isZero (uf : UnpackedFloat e s) (hz : uf.isZero) :
    uf.toRat' prec = 0 := by
  simp [toRat']
  simp [UnpackedFloat.isZero] at hz
  simp [hz]

@[simp]
theorem toRat'_neg (uf : UnpackedFloat e s) :
    (- uf).toRat' prec = - uf.toRat' prec := by
  simp [toRat']
  grind only

@[bv_normalize]
def maxNormal (eout sout : Nat) (e s : Nat) (sign : Bool) :
    UnpackedFloat eout sout :=
  {
    sign := sign
    ex := BitVec.ofInt eout (maxNormalExp e)
    sig := (BitVec.allOnes (s + 1)).zeroExtend sout
  }

@[bv_normalize]
def minSubnormalForPackedFloat (eout sout : Nat)
  (etarget starget : Nat) (sign : Bool) :
    UnpackedFloat eout sout :=
  {
    sign := sign
    ex := BitVec.ofInt eout (minSubnormalExp etarget starget)
    -- | recall that 'startget' is in PackedFloat format, and therefore
    -- the leading one is implicit. so we need to add one to the significand to get the correct exponent.
    sig := (BitVec.leadingOne (starget + 1)).zeroExtend sout
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


@[simp, grind =]
theorem isNaN_eq_decide (x : EUnpackedFloat e s) : isNaN x = decide (x.state = .NaN) := by
  simp [isNaN]
  grind only

@[simp]
theorem isNaN_neg_eq_isNaN (x : EUnpackedFloat e s) : isNaN (- x) = isNaN x := by
  rw [← EUnpackedFloat.neg_def]
  simp [isNaN, neg]

@[bv_normalize]
def isInfinite (x : EUnpackedFloat e s) : Bool :=
  x.state == .Infinity

@[simp, grind =]
theorem isInfinite_eq_decide (x : EUnpackedFloat e s) : isInfinite x = decide (x.state = .Infinity) := by
  simp [isInfinite]
  grind only

@[simp, grind =]
theorem isInfinite_neg_eq_isInfinite (x : EUnpackedFloat e s) : isInfinite (- x) = isInfinite x := by
  rw [← EUnpackedFloat.neg_def]
  simp [isInfinite, neg]

@[bv_normalize]
def isNumber (x : EUnpackedFloat e s) : Bool :=
  x.state == .Number

@[simp, grind =]
theorem isNumber_eq_decide (x : EUnpackedFloat e s) : isNumber x = decide (x.state = .Number) := by
  simp [isNumber]
  grind only

@[bv_normalize]
def isZero (x : EUnpackedFloat e s) : Bool :=
  x.isNumber && x.num.isZero

@[simp, grind .]
theorem state_eq_number_of_isZero (x : EUnpackedFloat e s) (h : x.isZero) : x.state = .Number := by
  simp [isZero] at h ⊢
  grind only

@[bv_normalize]
def sign (x : EUnpackedFloat e s) : Bool :=
  x.num.sign

@[simp]
theorem neg_sign (x : EUnpackedFloat e s) : (-x).sign = !x.sign := by
  rw [← EUnpackedFloat.neg_def]
  simp [sign, neg]

@[simp]
theorem neg_state (uf : EUnpackedFloat e s) : (-uf).state = uf.state := by
  rw [← EUnpackedFloat.neg_def]
  simp [neg]

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

@[simp]
theorem state_mkNaN : (mkNaN : EUnpackedFloat e s).state = .NaN := rfl

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

@[simp]
theorem state_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).state = .Infinity := rfl

@[simp]
theorem sign_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).sign = sign := rfl

@[simp]
theorem sign_num_mkInfinity (sign : Bool) : (mkInfinity sign : EUnpackedFloat e s).num.sign = sign := rfl

@[simp, grind =]
theorem eq_of_mkInfinity_eq_mkInfinity {e s} (sign1 sign2 : Bool) :
    (mkInfinity sign1 : EUnpackedFloat e s) = mkInfinity sign2 ↔ sign1 = sign2 := by
  simp [mkInfinity]

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
theorem num_mkZero {e s} (sign : Bool) :
    (mkZero sign : EUnpackedFloat e s).num = UnpackedFloat.mkZero sign := rfl

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
def normalize (euf : EUnpackedFloat e s) : EUnpackedFloat e s :=
  bif euf.isNumber then
    euf.num.normalize.toEUnpackedFloat
  else
    euf

@[simp]
theorem state_normalize (euf : EUnpackedFloat e s) : (normalize euf).state = euf.state := by
  simp [normalize]
  by_cases hs : euf.state = .Number
  · simp [hs]
  · simp [hs]

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

@[simp]
theorem Nat.four_le_two_pow_of_lt {n : Nat} (hn : 1 < n) : 4 ≤ 2 ^ n := by
  have : 2 ^ 2 ≤ 2 ^ n := by apply Fp.Nat.two_pow_le_two_pow_of_le; grind only
  simp at this
  assumption

@[simp]
theorem BitVec.allOnes_eq_one_iff (e : Nat) : BitVec.allOnes e = 1#e ↔ e ≤ 1 := by
  constructor
  · intros h
    have := BitVec.toNat_inj.mpr h
    simp at this
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    rw [Nat.mod_eq_of_lt] at this
    · have : 4 ≤ 2^e := by simp [hcontra]
      grind only
    · have : 4 ≤ 2^e := by simp [hcontra]
      grind only
  · intros h
    rcases e with rfl | rfl | e
    · grind only
    · grind only
    · grind only

/--
The only way we can get 'x = x+1` is if the width is zero.
-/
theorem BitVec.add_one_eq_self_iff (x : BitVec w) : x = x + 1#w ↔ w = 0 := by
  constructor
  · intros h
    have hcontra := BitVec.toNat_inj.mpr h
    simp [BitVec.toNat_add] at hcontra
    have : x.toNat < 2^w := by grind
    by_cases hxlt : x.toNat + 1 < 2^w
    · rw [Nat.mod_eq_of_lt] at hcontra
      · grind only
      · grind only
    · have hx : x.toNat = 2^w - 1 := by grind
      rw [hx] at hcontra
      rw [show 2^w - 1 + 1 = 2^w by grind] at hcontra
      simp at hcontra
      rcases w with rfl | w
      · simp
      · simp [Nat.pow_succ] at hcontra
        have : 0 < 2^w := by grind only
        grind only
  · intros h
    simp [h]

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
