import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound
import Fp.Utils
import Lean
open Lean


namespace Fp
namespace SmtLibSemantics

/-
We follow the development from
"An Automatable Formal Semantics for IEEE-754 Floating-Point Arithmetic" [1]
by Brain et. al.

[1]: https://smt-lib.org/papers/BTRW15.pdf
-/

/--
An extended number system to be instantiated with extended rationals, reals, or ints.
-/
class ExtendedNumber (R : Type) extends Add R, Sub R, LT R, LE R, Neg R, Zero R where
  /-- Check if number is a NaN -/
  isNaN : R → Prop
  /-- Check if two numbers are equal, with extended semantics for inf and NaN -/
  extendedEq : R → R → Prop

def ExtendedNumber.isZero {R : Type} [ExtendedNumber R] (r : R) : Prop :=
  ExtendedNumber.extendedEq r (Zero.zero)

def ExtendedNumber.ltZero {R : Type} [ExtendedNumber R] (r : R) : Prop :=
  r < (Zero.zero)

def ExtendedNumber.gtZero {R : Type} [ExtendedNumber R] (r : R) : Prop :=
  (Zero.zero) < r

instance [hEx : ExtendedNumber R] [DecidableRel ((· < ·) : R → R → Prop)] :
    DecidablePred (hEx.ltZero : R → Prop) := by
  unfold ExtendedNumber.ltZero
  infer_instance
instance [hEx : ExtendedNumber R] [DecidableRel ((· < ·) : R → R → Prop)] :
    DecidablePred (hEx.gtZero : R → Prop) := by
  unfold ExtendedNumber.gtZero
  infer_instance

instance [hEx : ExtendedNumber R] [DecidableRel hEx.extendedEq] :
    DecidablePred hEx.isZero := by
  unfold ExtendedNumber.isZero
  infer_instance


instance instExtendedRat : ExtendedNumber ExtRat where
  isNaN r := r.isNaN
  extendedEq r1 r2 := r1.eq r2

instance : Decidable (instExtendedRat.isZero r) := by
  simp [ExtendedNumber.isZero, ExtendedNumber.extendedEq]
  infer_instance

instance : Decidable (instExtendedRat.isNaN r) := by
  simp [ExtendedNumber.isNaN]
  infer_instance

instance : DecidableRel instExtendedRat.extendedEq := by
  simp [ExtendedNumber.extendedEq]
  infer_instance

/-- Embed the type `X` into the extended rationals. -/
class RoundableEmbed (X : Type) (R : Type) where
  embed : X → R

/--
Compute the upper approximant, which is the closest `x` such that `r ≤ embed x`.
Abstractly, this obeys the adjunction law: `r ≤ embed x ↔ upper r ≤ x`.
-/
structure RoundableUpper (X : Type) (R : Type) where
  upper : R → X

/-- Compute the lower approximant, which is the closest `x` such that `embed x ≤ r`.
Abstractly, this obeys the adjunction law: `embed x ≤ r ↔ x ≤ lower r`.
-/
structure RoundableLower (X : Type) (R : Type) where
  lower : R → X

/-- The default embedding of packed floats into the extended rationals. -/
instance  : RoundableEmbed (PackedFloat e s) ExtRat where
  embed (x : PackedFloat e s) : ExtRat := x.toExtRat


/-- A rounding adjunction is a triple (lower, embed, upper), where
`lower` and `upper` compute the lower and upper approximants of `embed`. -/
structure RoundableAdjunction (X : Type) (R : Type) extends
  RoundableEmbed X R,
  RoundableLower X R,
  RoundableUpper X R
  where

/-- Check if the given rational `r` is *strictly in* the lower half
of the interval `(embed (lower r), embed (upper r))`. -/
structure RoundableLowerHalf (X : Type) (R : Type) where
  lowerHalf : R → Prop

/-- Check if the given rational `r` is exactly in between
the two closest representable values `embed (lower r)` and `embed (upper r)`. -/
structure RoundableTieBreak (X : Type) (R : Type) where
  tieBreak : R → Prop

/--
Check if the number `X` is even when written in scientific notation with a power of two.
This assumes that `X` has a representation where we can check the least significant bit of the significand.
-/
structure RoundableIsEven (X : Type) where
  isEven : X → Bool

/-- Check that a packed float is even by checking the least significant bit of the significand. -/
def roundableIsEven_of_packedFloat
    : RoundableIsEven (PackedFloat e s) where
  isEven (x : PackedFloat e s) : Bool :=
    x.sig.toNat % 2 == 0

/-- Roundable predicates allow us to determine if a rational is in the lower half, tie break,
and also let us check if a value X represents an even number (for RNE). -/
structure RoundablePredicates (X : Type) (R : Type) extends
  RoundableLowerHalf X R,
  RoundableTieBreak X R,
  RoundableIsEven X
  where

structure RoundMethod (X : Type) (R : Type) extends
  RoundableAdjunction X R,
  RoundablePredicates X R

def RoundMethod.rounderForSign {X : Type}
    (roundMethod : RoundMethod X R)
    (sign : Bool) (r : R) : X :=
  if sign then roundMethod.upper r else roundMethod.lower r

open  ExtendedNumber in
/-- define the rounding function for a given choice of 'RoundMethod'. -/
def RoundMethod.round {e s R} (roundMethod : RoundMethod (PackedFloat e s) R) [inst : ExtendedNumber R]
    [DecidablePred inst.isZero]
    [DecidablePred inst.isNaN]
    [DecidablePred roundMethod.lowerHalf]
    [DecidablePred roundMethod.tieBreak]
    [DecidablePred inst.gtZero]
    [DecidablePred inst.ltZero]
    (rm : RoundingMode) (sign : Bool) (r : R) : PackedFloat e s :=
  match rm with
  | .RNE =>
      if isNaN r then roundMethod.lower r
      else if isZero r then roundMethod.rounderForSign sign r
      else if ¬ (isZero r) ∧ roundMethod.lowerHalf r then roundMethod.lower r
      else if ¬ (isZero r) ∧ roundMethod.tieBreak r ∧ roundMethod.isEven (roundMethod.lower r) then roundMethod.lower r
      else if ¬ (isZero r) ∧ roundMethod.tieBreak r ∧ roundMethod.isEven (roundMethod.upper r) then roundMethod.upper r
      else if ¬ (isZero r) ∧ !roundMethod.lowerHalf r ∧ !roundMethod.tieBreak r then roundMethod.upper r
      else .mkNaN -- does not occur.
  | .RNA =>
      if gtZero r ∧ ¬ (roundMethod.lowerHalf r) then roundMethod.upper r
      else if gtZero r ∧ (roundMethod.lowerHalf r) then roundMethod.lower r
      else if isZero r then roundMethod.rounderForSign sign r
      else if isNaN r then roundMethod.lower r
      else if ltZero r ∧ ¬ (roundMethod.lowerHalf r) ∧ ¬ (roundMethod.tieBreak r) then roundMethod.upper r
      else if ltZero r ∧ ((roundMethod.lowerHalf r) ∨ (roundMethod.tieBreak r)) then roundMethod.lower r
      else .mkNaN -- does not occur.
   | .RTP =>
      if isZero r then roundMethod.rounderForSign sign r
      else roundMethod.upper r
   | .RTN =>
      if isZero r then roundMethod.rounderForSign sign r
      else roundMethod.lower r
   | .RTZ =>
      if gtZero r then roundMethod.lower r
      else if isZero r then roundMethod.rounderForSign sign r
      else roundMethod.upper r

namespace SmtLibRoundMethod

/-- 'lower' is a valid greatest lower bound for 'r'. -/
def IsLawfulLower [ExtendedNumber R] [RE : RoundableEmbed X R] (r : R) (lower : X) : Prop :=
  RE.embed lower ≤ r ∧ (∀ (lower' : X), RE.embed lower' ≤ r → RE.embed lower' ≤ RE.embed lower)

open Classical in
noncomputable def smtLibLower [Inhabited X] [ExtendedNumber R] [RoundableEmbed X R] : RoundableLower X R where
  lower (r : R) : X :=
    if hp : ∃ (x : X), IsLawfulLower r x then
      Classical.choose hp
    else
      default

/-- 'upper' is a valid least upper bound for 'r'. -/
def IsLawfulUpper [ExtendedNumber R] [RE : RoundableEmbed X R] (r : R) (upper : X) : Prop :=
  r ≤ RE.embed upper ∧ (∀ (upper' : X), r ≤ RE.embed upper' → RE.embed upper ≤ RE.embed upper')

open Classical in
noncomputable def smtLibUpper {X R} [Inhabited X] [ExtendedNumber R] [RoundableEmbed X R] : RoundableUpper X R where
  upper (r : R) : X :=
    if hp : ∃ (x : X), IsLawfulUpper r x then
      /- Use hilbert epsilon to pick -/
      Classical.choose hp
    else
      default

/--
The default SMT-Lib adjunction of packed floats into rationals, written `v_ε,σ(f)`,
where `vlower` and `vupper` is defined via exhaustive enumeration
for better computational properties.

We will show later that the `vlower` and `vupper` defined this way agree
with the galois adjunction expected.
-/
noncomputable def smtLibV [Inhabited X] [ExtendedNumber R] [RoundableEmbed X R] :
    RoundableAdjunction X R where
  embed := RoundableEmbed.embed
  lower := smtLibLower.lower
  upper := smtLibUpper.upper

/--
The SMT-Lib definition of the rounding methods for any choice of rounding adjunction 'v'.
-/
def smtLibRoundMethod (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  RoundMethod (PackedFloat e s) R where
  embed := v.embed
  lower := v.lower
  upper := v.upper
  lowerHalf r := ExtendedNumber.extendedEq (v.embed (v.lower r))  (ves.embed (ves.lower r))
  /-
  The SMT-LIb specification would have one write:
  ```lean
  (v.embed (v.lower r) < ves.embed (ves.lower r)) =
  (ves.embed (ves.upper r) < (ves.embed (v.upper r)))
  ```
  however, this does not type check at `ves.embed (v.upper r)`,
  since `v.upper r` has type `PackedFloat e s`, while `ves.embed`
  expects an argument of type `PackedFloat e (s + 1)`.

  We correct this mistake, and use `v.embed` instead,
  since the purpose of this definition is to compare the
  ExtRat values of the embeddings.
  -/
  tieBreak r :=
    (v.embed (v.lower r) < ves.embed (ves.lower r)) =
    (ves.embed (ves.upper r) < (v.embed (v.upper r)))
  isEven := roundableIsEven_of_packedFloat.isEven

instance [hExtended : ExtendedNumber R]
    [DecidableRel hExtended.extendedEq]
    {v : RoundableAdjunction (PackedFloat e s) R}
    {ves : RoundableAdjunction (PackedFloat e (s + 1)) R} :
    DecidablePred ((smtLibRoundMethod e s v ves).lowerHalf) := by
  simp [smtLibRoundMethod]
  infer_instance

set_option trace.Meta.synthInstance true in
instance [hExtended : ExtendedNumber R]
    [hdec : ((r s : R) → Decidable (r < s))]
    {v : RoundableAdjunction (PackedFloat e s) R}
    {ves : RoundableAdjunction (PackedFloat e (s + 1)) R} :
    DecidablePred ((smtLibRoundMethod e s v ves).tieBreak) := by
  simp [smtLibRoundMethod]
  infer_instance

  -- infer_instance

end SmtLibRoundMethod

namespace SmtLibFunctions


def neg (x : PackedFloat e s) : PackedFloat e s :=
  if x.isNaN then x else { x with sign := !x.sign }

def abs (x : PackedFloat e s) : PackedFloat e s :=
  if x.isNaN then x else { x with sign := false }

def addSign (rm : RoundingMode) (f g : PackedFloat e s) : Bool :=
  if rm = .RTN then f.sign || g.sign else f.sign && g.sign

def subSign (rm : RoundingMode) (f g : PackedFloat e s) : Bool :=
  addSign rm f (neg g)

def xorSign (f g : PackedFloat e s) : Bool :=
  f.sign != g.sign

section Operations

variable {e s : Nat} {R : Type} [inst : ExtendedNumber R] (roundMethod : RoundMethod (PackedFloat e s) R)
      [DecidablePred roundMethod.lowerHalf]
      [DecidablePred roundMethod.tieBreak]
      [DecidablePred inst.isNaN]
      [DecidablePred inst.isZero]
      [DecidablePred inst.gtZero]
      [DecidablePred inst.ltZero]
      (rm : RoundingMode)

def add (x y : PackedFloat e s) : PackedFloat e s :=
      let z :=  ((roundMethod.embed x) + (roundMethod.embed y))
      let sign : Bool := addSign rm x y
      roundMethod.round rm sign z

def sub (x y : PackedFloat e s) : PackedFloat e s :=
      let z :=  ((roundMethod.embed x) - (roundMethod.embed y))
      let sign : Bool := subSign rm x (neg y)
      roundMethod.round rm sign z

def mul [Mul R] (x y : PackedFloat e s) : PackedFloat e s :=
      let z :=  ((roundMethod.embed x) * (roundMethod.embed y))
      let sign : Bool := xorSign x y
      roundMethod.round rm sign z

def div [Div R] (x y : PackedFloat e s) : PackedFloat e s :=
      let z :=  ((roundMethod.embed x) / (roundMethod.embed y))
      if xorSign x y then
        neg (roundMethod.round rm true  (-z))
      else
        roundMethod.round rm false z

end Operations


end SmtLibFunctions
end SmtLibSemantics
end Fp
