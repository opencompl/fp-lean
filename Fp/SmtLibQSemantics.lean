import Fp.Basic
import Fp.Rounding
import Lean
open Lean

namespace QSemantics

/-
We define the semantics of floating-point operations following the SMT-LIB
style of semantics here. In particular, close attention is paid to being
as close to the SMT-LIB definitions as possible.
-/


/-- The lower approximant of 'v'. Returns the largest 'x : X' such that 'v x ≤ r'. -/
def lower (r : ExtRat) : UnpackedFloat e s :=
  let us : Array UnpackedFloat e s := UnpackedFloat.enumerate
  let ers := us.map (fun u => u.toExtRat)
  let filtered := ers.filter (fun x => x ≤ er)
  let sorted := filtered.qsort (fun a b => a < b)
  match sorted.back? with
  | some x => UnpackedFloat.fromExtRat x
  | none => UnpackedFloat.mkInf true -- lower bound is -∞
  

/-- The upper approximant of 'v'.
Returns the smallest 'x : X' such that 'r ≤ v x'. -/
def upper (r : ExtRat) : UnpackedFloat e s :=
  let er := ExtRat.Number r
  let us : Array UnpackedFloat e s := UnpackedFloat.enumerate
  let ers := us.map (fun u => u.toExtRat)
  let filtered := ers.filter (fun x => x ≤ er)
  let sorted := filtered.qsort (fun a b => a < b)
  match sorted.back? with
  | some x => UnpackedFloat.fromExtRat x
  | none => UnpackedFloat.mkInf true -- lower bound is -∞

/-- Lower half, return 'true' iff we are strictly in the lower half. -/
def lh (r : ExtRat)  : Prop :=
   r - (lower r).toERat < (upper r).toERat - r

/-- Tiebreak, return 'true' iff we are exactly in the middle of the lower and upper approximants. -/
def tb (r : ExtRat) : Prop :=
   r - (lower r).toERat = (upper r).toERat - r

/-- Upper half, return 'true' iff we are strictly in the upper half. -/
def uh (r : ExtRat) : Prop :=
   r - (lower r).toERat > (upper r).toERat - r

/-- Check if 'X' is even. -/
def ev (x : UnpackedFloat e s) : Prop :=
  ∃ (z : Int), x.toERat = .Number (2 * z)

/-- Round signed zero. Picks between the lower and upper approximant,
based on the sign
function. -/
def rsz {X : Type} (sign : Bool) (r : ExtRat) : X :=
  -- | TODO: should this be flipped?
  fun r => if sign then upper r else lower r


open Classical in
noncomputable def roundSmtLib 
      (rm : RoundingMode) (sign : Bool) (r : ExtRat) : ExtRat → UnpackedFloat e m :=
  match rm with
  | .RNE =>
      if _hz : r = .Number 0 then rsz sign
      else
        if _hlh : lh r
        then lower 
        else
         if _htb : tb r
         then
            if _heven : ev (lower r)
            then lower
            else upper
         else
            -- not tie break, not lower, so we are in upper half.
            -- have : uh r v := by
            --    have := trichotomy_lh_tb_uh r v
            --    grind
            upper
  | .RNA =>
      if _hnan : r = .NaN then lower
      else
         if _hz : r = .Number 0 then rsz sign
         else
            if _rgt0 : (ExtRat.Number 0).lt r
            then
              if _hlh : lh r then lower else upper
            else
               -- r < 0 := by sorry
              if _hlh : lh r ∨ tb r
              then lower
              else upper 
   | .RTP =>
      if _h0 : r = .Number 0 then rsz sign
      else upper
   | .RTN =>
      if _h0 : r = .Number 0 then rsz sign
      else lower
   | .RTZ =>
      if _h0 : r = .Finite 0 then rsz sign v
      else
         if _rgt0 : r > .Finite 0 then lower v else upper v


end QSemantics
