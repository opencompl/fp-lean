import Fp.Utils
import Fp.Utils.Rat
import Fp.Grind

inductive ExtRat where
  | NaN : ExtRat
  | Infinity : Bool → ExtRat
  | Number : Rat → ExtRat
deriving DecidableEq, Repr

namespace ExtRat

instance : Zero ExtRat where
  zero := .Number 0

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

def neg (x : ExtRat) : ExtRat :=
  match x with
  | .NaN => .NaN
  | .Infinity s => .Infinity (!s)
  | .Number r => .Number (-r)

def sub (x y : ExtRat) : ExtRat :=
  x.add (y.neg)


instance : Neg ExtRat where
  neg a := neg a

instance : Sub ExtRat where
  sub a b := sub a b

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

instance : Max ExtRat where
  max a b := if a ≤ b then b else a

def isNaN (r : ExtRat) : Bool :=
  r = .NaN

/-- Absolute value of an extended rational number. -/
def abs (r : ExtRat) : ExtRat :=
  match r with
  | .NaN => .NaN
  | .Infinity _sign => .Infinity false
  | .Number n => .Number (n.abs)

end ExtRat
