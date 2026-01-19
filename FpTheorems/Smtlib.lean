import Fp.Basic
import Lean
import Mathlib.Data.Real.Basic

open Lean

/-- Extended real numbers, including +∞, -∞ and NaN -/
inductive ExtReal 
| Finite (r : Real) : ExtReal
| Infinity (neg : Bool) : ExtReal
| NaN : ExtReal


def lower {X : Type} (v : X → ExtReal) : (r : ExtReal ) : X :=
   sInf (fun (y : X) => v y ≤ r)

def upper {X : Type} (v : X → ExtReal) : (r : ExtReal ) : X :=
   sInf (fun (y : X) => v y ≤ r)

/-- Lower half, return True iff we are strictly in the lower half. -/
def lh {X : Type} (r : ExtReal) (v : X → ExtReal) : Prop := 
   r - v (lower v r) < v (upper v r) - r

/-- Tiebreaker function -/
def tb {X : Type} (sign : Bool) (v : X → ExtReal) : Prop :=
   r - v (lower v r) = v (upper v r) - r 

def uh {X : Type} (r : ExtReal) (v : X → ExtReal) : Prop := 
   r - v (lower v r) > v (upper v r) - r

/-- Trichotomy of lh, tb, uh -/
theorem trichotomy_lh_tb_uh {X : Type} (r : ExtReal) (v : X → ExtReal) : 
  lh r v ∨ tb sign v ∨ uh r v := 
  by simp [lh, tb, uh]; grind

/-- Check if 'X' is even. -/
def ev {X : Type} (x : X) : Prop :=
  ∃ (z : Int), x = 2 * z


/-!
We build the theory of SMT-LIB's definition of floating point semantics,
including, crucially, rounding and the semantics of the basic operations
(+, -, *, / sqrt).

We follow the development from 
[An Automatable Formal Semantics for IEEE-754 Floating Point Arithmetic](https://ieeexplore.ieee.org/abstract/document/7203811/) by Brain et. al.
-/

def round {X : Type} (rm : RoundingMode) (sign : Bool) (r : ExtReal) (v : X → ExtReal) : ExtReal → X :=
  match rm with 
  | .RNE =>
      if hz : r = .Finite 0 then rsz sign v
      else 
        if hlh : lh r v 
        then sorry
        else sorry
  | _ => sorry
    






