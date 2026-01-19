import Fp.Basic
import Fp.Rounding
import Lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-!
We build the theory of SMT-LIB's definition of floating point semantics,
including, crucially, rounding and the semantics of the basic operations
(+, -, *, / sqrt).

We follow the development from
[An Automatable Formal Semantics for IEEE-754 Floating Point Arithmetic](https://ieeexplore.ieee.org/abstract/document/7203811/) by Brain et. al.
-/


open Lean


/-- Extended real numbers, including +∞, -∞ and NaN -/
@[grind]
inductive ExtReal
| Finite (r : Real) : ExtReal
| Infinity (neg : Bool) : ExtReal
| NaN : ExtReal

namespace ExtReal

@[match_pattern, simp]
def plusInfty : ExtReal := .Infinity false

@[match_pattern, simp]
def minusInfty : ExtReal := .Infinity true

def le (a b : ExtReal) : Prop :=
  match a, b with
  | .NaN, b => b = .NaN
  | a, .NaN => a = .NaN
  | .Infinity a, .Infinity b =>
      -- either LHS is -∞ or RHS is +∞, or they are equal
      (a = true) ∨ (a = b)
   | .minusInfty, .Finite _ => true -- everything is >= -∞
   | .plusInfty, .Finite _ => false -- +∞ is not <= anything finite
   | .Finite _, .minusInfty => false -- finite is not <= -∞
   | .Finite _, .plusInfty => true -- everything is <= +∞
   | .Finite r1, .Finite r2 => r1 ≤ r2


instance : LE ExtReal where
   le := ExtReal.le

def add (a b : ExtReal) : ExtReal :=
   match a, b with
   | .NaN, _ => .NaN
   | _, .NaN => .NaN
   | .Finite r1, .Finite r2 => .Finite (r1 + r2)
   | .Infinity signA, .Infinity signB =>
      if signA = signB then .Infinity signA else .NaN
   | .Finite _, .Infinity signB => .Infinity signB
   | .Infinity signA, .Finite _ => .Infinity signA

def neg (a : ExtReal) : ExtReal :=
   match a with
   | .NaN => .NaN
   | .Finite r => .Finite (-r)
   | .Infinity sign => .Infinity (!sign)


def sub (a b : ExtReal) : ExtReal := a.add b.neg

noncomputable def mul (a b : ExtReal) : ExtReal :=
   match a, b with
   | .NaN, _ => .NaN
   | _, .NaN => .NaN
   | .Finite r1, .Finite r2 => .Finite (r1 * r2)
   | .Infinity signA, .Infinity signB =>
      .Infinity (signA != signB)
   | .Finite r, .Infinity signB =>
      if r = 0 then .NaN else .Infinity (if r < 0 then !signB else signB)
   | .Infinity signA, .Finite r =>
      if r = 0 then .NaN else .Infinity (if r < 0 then !signA else signA)

instance : Sub ExtReal where
   sub := ExtReal.sub

noncomputable def inv (a : ExtReal) : ExtReal :=
   match a with
   | .NaN => .NaN
   | .Finite r =>
      -- Note carefully, that 1/0 = +∞ in SMT-LIB.
      if r = 0 then .plusInfty
      else .Finite (1 / r)
   | .Infinity sign =>
      if sign then .Finite 0 else .Finite 0


noncomputable def div (a b : ExtReal) : ExtReal := a.mul b.inv

/--
Square root function for extended reals.
Returns NaN for negative inputs and +∞ for +∞.
-/
noncomputable def sqrt (a : ExtReal) : ExtReal :=
   match a with
   | .NaN => .NaN
   | .Finite r =>
      if r < 0 then .NaN else .Finite (Real.sqrt r)
   | .Infinity sign =>
      if sign then .NaN else .Infinity false

def lt (a b : ExtReal) : Prop := a ≤ b ∧ a ≠ b

instance : LT ExtReal where
   lt := ExtReal.lt

end ExtReal

/--
Typeclass for types that have a sign function, which mimics the sign bit
in floating point representations.
-/
class IsFpKind (X : Type) [SupSet X] [InfSet X] where
   /-- return True if negative. Sign is meant to be thought of as '-1^(sign x)'. -/
   sign : X → Bool


namespace IsFpKind

variable {X : Type} [SupSet X] [InfSet X]

/-- The lower approximant of 'v'. Returns the largest 'x : X' such that 'v x ≤ r'. -/
def lower {X : Type} [SupSet X] (v : X → ExtReal) (r : ExtReal) : X :=
   sSup (fun (x : X) => v x ≤ r)

/-- The upper approximant of 'v'.
Returns the smallest 'x : X' such that 'r ≤ v x'. -/
def upper {X : Type} [InfSet X] (v : X → ExtReal) (r : ExtReal ) : X :=
   sInf (fun (x : X) => r ≤ v x)

/-- Lower half, return 'true' iff we are strictly in the lower half. -/
def lh {X : Type} [InfSet X] [SupSet X] (r : ExtReal) (v : X → ExtReal) : Prop :=
   r - v (lower v r) < v (upper v r) - r

/-- Tiebreak, return 'true' iff we are exactly in the middle of the lower and upper approximants. -/
def tb {X : Type} [InfSet X] [SupSet X] (r : ExtReal) (v : X → ExtReal) : Prop :=
   r - v (lower v r) = v (upper v r) - r

/-- Upper half, return 'true' iff we are strictly in the upper half. -/
def uh {X : Type} [InfSet X] [SupSet X] (r : ExtReal) (v : X → ExtReal) : Prop :=
   r - v (lower v r) > v (upper v r) - r

/-- Check if 'X' is even. -/
def ev {X : Type} (x : X) (v : X → ExtReal) : Prop :=
  ∃ (z : Int), v x = .Finite (2 * z)

/-- Round signed zero. Picks between the lower and upper approximant,
based on the sign
function. -/
def rsz {X : Type} [SupSet X] [InfSet X] (sign : Bool) (v : X → ExtReal) : ExtReal → X :=
  fun r =>
    if sign then upper v r else lower v r


open Classical in
noncomputable def roundSmtLib {X : Type} [SupSet X] [InfSet X]
      (rm : RoundingMode) (sign : Bool) (r : ExtReal) (v : X → ExtReal) : ExtReal → X :=
  match rm with
  | .RNE =>
      if _hz : r = .Finite 0 then rsz sign v
      else
        if _hlh : lh r v
        then lower v
        else
         if _htb : tb r v
         then
            if _heven : ev (lower v r) v
            then lower v
            else upper v
         else
            -- not tie break, not lower, so we are in upper half.
            -- have : uh r v := by
            --    have := trichotomy_lh_tb_uh r v
            --    grind
            upper v
  | .RNA =>
      if _hnan : r = .NaN then lower v
      else
         if _hz : r = .Finite 0 then rsz sign v
         else
            if _rgt0 : r > .Finite 0
            then
              if _hlh : lh r v then lower v else upper v
            else
               -- r < 0 := by sorry
              if _hlh : lh r v ∨ tb r v
              then lower v
              else upper v
   | .RTP =>
      if _h0 : r = .Finite 0 then rsz sign v
      else upper v
   | .RTN =>
      if _h0 : r = .Finite 0 then rsz sign v
      else lower v
   | .RTZ =>
      if _h0 : r = .Finite 0 then rsz sign v
      else
         if _rgt0 : r > .Finite 0 then lower v else upper v


noncomputable def fpUnaryOp {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal)
      (f : ExtReal → ExtReal) :
      X → X :=
   fun x =>
      let sign : Bool := IsFpKind.sign x
      let y := f (v x)
      roundSmtLib rm sign y v <| y

noncomputable def fpBinaryOp {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal)
      (f : ExtReal → ExtReal → ExtReal) :
      X → X → X :=
   fun x y =>
      let z := f (v x) (v y)
      let sign : Bool := IsFpKind.sign x
      roundSmtLib rm sign z v <| z

noncomputable def fpAdd {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal) :
      X → X → X :=
   fpBinaryOp rm v ExtReal.add

noncomputable def fpSub {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal) :
      X → X → X :=
   fpBinaryOp rm v ExtReal.sub

noncomputable def fpMul {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal) :
      X → X → X :=
   fpBinaryOp rm v ExtReal.mul

noncomputable def fpInv {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal) :
      X → X :=
   fpUnaryOp rm v ExtReal.inv

noncomputable def fpNeg {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal) :
      X → X :=
   fpUnaryOp rm v ExtReal.neg

noncomputable def fpDiv {X : Type} [SupSet X] [InfSet X] [IsFpKind X]
      (rm : RoundingMode)
      (v : X → ExtReal) :
      X → X → X :=
   fpBinaryOp rm v ExtReal.div

end IsFpKind
