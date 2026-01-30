import Fp.Basic
import Fp.Rounding
import Lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Fp.SmtLibSemantics

/-!
We build the theory of SMT-LIB's definition of floating point semantics,
including, crucially, rounding and the semantics of the basic operations
(+, -, *, / sqrt).

We follow the development from
"An Automatable Formal Semantics for IEEE-754 Floating-Point Arithmetic" [1]
by Brain et. al.

[1]: https://smt-lib.org/papers/BTRW15.pdf
-/


open Lean

namespace Fp

namespace SmtLibSemantics


/-- Extended real numbers, including +∞, -∞ and NaN -/
@[grind]
inductive ExtReal
| Number (r : Real) : ExtReal
| Infinity (neg : Bool) : ExtReal
| NaN : ExtReal

namespace ExtReal

instance : Zero ExtReal where
  zero := .Number 0

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
   | .minusInfty, Number _ => true -- everything is >= -∞
   | .plusInfty, Number _ => false -- +∞ is not <= anything finite
   | Number _, .minusInfty => false -- finite is not <= -∞
   | Number _, .plusInfty => true -- everything is <= +∞
   | Number r1, Number r2 => r1 ≤ r2


noncomputable def eq (a b : ExtReal) : Bool :=
   match a, b with
   | .NaN, .NaN => true
   | .NaN, _ => false
   | _, .NaN => false
   | .Infinity signA, .Infinity signB => signA = signB
   | .Infinity _, _ => false
   | _, .Infinity _ => false
   | Number r1, Number r2 => r1 = r2

instance : LE ExtReal where
   le := ExtReal.le

def add (a b : ExtReal) : ExtReal :=
   match a, b with
   | .NaN, _ => .NaN
   | _, .NaN => .NaN
   | Number r1, Number r2 => Number (r1 + r2)
   | .Infinity signA, .Infinity signB =>
      if signA = signB then .Infinity signA else .NaN
   | Number _, .Infinity signB => .Infinity signB
   | .Infinity signA, Number _ => .Infinity signA

instance : Add ExtReal where
   add := ExtReal.add

def neg (a : ExtReal) : ExtReal :=
   match a with
   | .NaN => .NaN
   | Number r => Number (-r)
   | .Infinity sign => .Infinity (!sign)

instance : Neg ExtReal where
   neg := ExtReal.neg

def sub (a b : ExtReal) : ExtReal := a.add b.neg

instance : Sub ExtReal where
   sub := ExtReal.sub

noncomputable def mul (a b : ExtReal) : ExtReal :=
   match a, b with
   | .NaN, _ => .NaN
   | _, .NaN => .NaN
   | Number r1, Number r2 => Number (r1 * r2)
   | .Infinity signA, .Infinity signB =>
      .Infinity (signA != signB)
   | Number r, .Infinity signB =>
      if r = 0 then .NaN else .Infinity (if r < 0 then !signB else signB)
   | .Infinity signA, Number r =>
      if r = 0 then .NaN else .Infinity (if r < 0 then !signA else signA)

noncomputable instance : Mul ExtReal where
   mul := ExtReal.mul


noncomputable def inv (a : ExtReal) : ExtReal :=
   match a with
   | .NaN => .NaN
   | Number r =>
      -- Note carefully, that 1/0 = +∞ in SMT-LIB.
      if r = 0 then .plusInfty
      else Number (1 / r)
   | .Infinity sign =>
      if sign then Number 0 else Number 0


noncomputable def div (a b : ExtReal) : ExtReal := a.mul b.inv

noncomputable instance : Div ExtReal where
   div := ExtReal.div

/--
Square root function for extended reals.
Returns NaN for negative inputs and +∞ for +∞.
-/
noncomputable def sqrt (a : ExtReal) : ExtReal :=
   match a with
   | .NaN => .NaN
   | Number r =>
      if r < 0 then .NaN else Number (Real.sqrt r)
   | .Infinity sign =>
      if sign then .NaN else .Infinity false

def lt (a b : ExtReal) : Prop := a ≤ b ∧ a ≠ b

instance : LT ExtReal where
   lt := ExtReal.lt

/-- ExtReal is like ExtReal, but with more elements. -/
noncomputable instance : ExtendedNumber ExtReal where
   isNaN r := r = .NaN
   extendedEq r1 r2 := r1.eq r2

instance : RoundableEmbed (PackedFloat e s) ExtReal where
   embed := fun pf =>
      match pf.toExtRat with
      | .NaN => .NaN
      | .Infinity sign => .Infinity sign
      | .Number r => .Number r

end ExtReal

noncomputable def smtLibRealRounder : RoundMethod (PackedFloat e s) ExtReal :=
   SmtLibRoundMethod.smtLibRoundMethod e s
      SmtLibRoundMethod.smtLibV
      SmtLibRoundMethod.smtLibV

namespace RealSemantics
open Classical


noncomputable def add  (rm : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
   SmtLibSemantics.SmtLibFunctions.add (roundMethod := smtLibRealRounder) rm x y

noncomputable def sub (rm : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
   SmtLibSemantics.SmtLibFunctions.sub (roundMethod := smtLibRealRounder) rm x y

noncomputable def mul (rm : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
   SmtLibSemantics.SmtLibFunctions.mul (roundMethod := smtLibRealRounder) rm x y

noncomputable def div (rm : RoundingMode) (x y : PackedFloat e s) : PackedFloat e s :=
   SmtLibSemantics.SmtLibFunctions.div (roundMethod := smtLibRealRounder) rm x y

end RealSemantics
end SmtLibSemantics
end Fp
