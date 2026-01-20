import Fp.Basic
import Fp.Rounding
import Lean
open Lean

/--
Return the minimum of a list 'l' on the function 'f',
with a default value if the list is empty.
-/
def List.minOn {α β : Type} (f : α → β) (le : β → β → Bool) (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | x :: xs =>
      let restMin : α := minOn f le xs default
      if le (f x) (f restMin) then x else restMin

def List.maxOn {α β : Type} (f : α → β) (le : β → β → Bool) (l : List α) (default : α) : α :=
   List.minOn f (fun a b => le b a) l default
namespace QSemantics

/-
We define the semantics of floating-point operations following the SMT-LIB
style of semantics here. In particular, close attention is paid to being
as close to the SMT-LIB definitions as possible.
-/

/-- The lower approximant of 'v'. Returns the largest 'x : X' such that 'v x ≤ r'. -/
def lower (e s : Nat) (r : ExtRat) : PackedFloat e s :=
  let us : List (PackedFloat e s) := PackedFloat.enumerate e s
  let filtered := us.filter (fun x => decide (x.toExtRat ≤ r))
  let min := filtered.minOn
   (fun x => x.toExtRat)
   (fun a b => a ≤ b) (.getInfinity e s true)
  min

/-- The upper approximant of 'v'.
Returns the smallest 'x : X' such that 'r ≤ v x'. -/
def upper (e s : Nat) (r : ExtRat) : PackedFloat e s :=
   let us : List (PackedFloat e s) := PackedFloat.enumerate e s
   let filtered := us.filter (fun x => decide (r ≤ x.toExtRat))
   let max := filtered.maxOn
    (fun x => x.toExtRat)
    (fun a b => a ≤ b) (.getInfinity e s false)
   max


/-- Lower half, return 'true' iff we are strictly in the lower half. -/
def lh (e s : Nat) (r : ExtRat)  : Prop :=
   (r - (lower e s r).toExtRat) < (upper e s r).toExtRat - r

/-- Tiebreak, return 'true' iff we are exactly in the middle of the lower and upper approximants. -/
def tb (e s : Nat) (r : ExtRat) : Prop :=
   r - (lower e s r).toExtRat = (upper e s r).toExtRat - r
/-- Upper half, return 'true' iff we are strictly in the upper half. -/
def uh (e s : Nat) (r : ExtRat) : Prop :=
   (r - (lower e s r).toExtRat) > (upper e s r).toExtRat - r

/-- Check if 'X' is even. -/
def ev (e s : Nat) (x : PackedFloat e s) : Prop :=
  ∃ (z : Int), x.toExtRat = .Number (2 * z)

/-- Round signed zero. Picks between the lower and upper approximant,
based on the sign
function. -/
def rsz (e s : Nat) (sign : Bool) (r : ExtRat) : PackedFloat e s :=
  -- | TODO: should this be flipped?
  if sign then upper e s r else lower e s r


open Classical in
noncomputable def roundSmtLib (e s : Nat)
      (rm : RoundingMode) (sign : Bool) (r : ExtRat) : ExtRat → PackedFloat e s :=
  match rm with
  | .RNE =>
      if _hz : r = .Number 0 then rsz e s sign
      else
        if _hlh : lh e s r
        then lower e s
        else
         if _htb : tb e s r
         then
            if _heven : ev e s (lower e s r)
            then lower e s
            else upper e s
         else
            -- not tie break, not lower, so we are in upper half.
            -- have : uh r v := by
            --    have := trichotomy_lh_tb_uh r v
            --    grind
            upper e s
  | .RNA =>
      if _hnan : r = .NaN then lower e s
      else
         if _hz : r = .Number 0 then rsz e s sign
         else
            if _rgt0 : (ExtRat.Number 0).lt r
            then
              if _hlh : lh e s r then lower e s else upper e s
            else
               -- r < 0 := by sorry
              if _hlh : lh e s r ∨ tb e s r
              then lower e s
              else upper e s
   | .RTP =>
      if _h0 : r = .Number 0 then rsz e s sign
      else upper e s
   | .RTN =>
      if _h0 : r = .Number 0 then rsz e s sign
      else lower e s
   | .RTZ =>
      if _h0 : r = .Number 0 then rsz e s sign
      else
         if _rgt0 : r > .Number 0 then lower e s else upper e s


end QSemantics
