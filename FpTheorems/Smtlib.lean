import Fp.Basic
import Fp.Rounding
import Lean
import Mathlib.Data.Real.Basic

/-!
We build the theory of SMT-LIB's definition of floating point semantics,
including, crucially, rounding and the semantics of the basic operations
(+, -, *, / sqrt).

We follow the development from
[An Automatable Formal Semantics for IEEE-754 Floating Point Arithmetic](https://ieeexplore.ieee.org/abstract/document/7203811/) by Brain et. al.
-/


open Lean

/-- Extended real numbers, including +∞, -∞ and NaN -/
inductive ExtReal
| Finite (r : Real) : ExtReal
| Infinity (neg : Bool) : ExtReal
| NaN : ExtReal

instance : LE ExtReal := sorry
instance : Sub ExtReal := sorry
instance : LT ExtReal := sorry

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

/-- Trichotomy of lh, tb, uh -/
theorem trichotomy_lh_tb_uh {X : Type} [InfSet X] [SupSet X] (r : ExtReal) (v : X → ExtReal) :
  lh r v ∨ tb r v ∨ uh r v :=
  by simp [lh, tb, uh]; sorry

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
      if hz : r = .Finite 0 then rsz sign v
      else
        if hlh : lh r v
        then lower v
        else
         if htb : tb r v
         then
            if heven : ev (lower v r) v
            then lower v
            else upper v
         else
            -- not tie break, not lower, so we are in upper half.
            have : uh r v := by
               have := trichotomy_lh_tb_uh r v
               grind
            upper v
  | _ => sorry
