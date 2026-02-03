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

instance [hExtended : ExtendedNumber R]
    [hdec : ((r s : R) → Decidable (r < s))]
    {v : RoundableAdjunction (PackedFloat e s) R}
    {ves : RoundableAdjunction (PackedFloat e (s + 1)) R} :
    DecidablePred ((smtLibRoundMethod e s v ves).tieBreak) := by
  simp [smtLibRoundMethod]
  infer_instance

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

/-!
## Binary Relations (Section from BTRW15)

Following the BTRW15 paper, we define binary relations for comparing floating-point
numbers. These are defined in terms of the embedding `v : X → R` into the extended
number system R (e.g., extended rationals or reals).

These relations are different from the equality and ordering relations on `X`
(i.e., structural equality) and those on `R` (i.e., `=` and `≤`). Despite their
names, they are not actually equality or ordering relations as they do not
contain `(NaN, NaN)`, and `eq`, `leq`, `geq` contain both `(+0, -0)` and `(-0, +0)`.

```
eq_{ε,σ}  = {(f,g) ∈ F_{ε,σ} × F_{ε,σ} | v(f) = v(g)}
leq_{ε,σ} = {(f,g) ∈ F_{ε,σ} × F_{ε,σ} | v(f) ≤ v(g)}
lt_{ε,σ}  = {(f,g) ∈ F_{ε,σ} × F_{ε,σ} | v(f) < v(g)}
geq_{ε,σ} = {(f,g) ∈ F_{ε,σ} × F_{ε,σ} | v(f) ≥ v(g)}
gt_{ε,σ}  = {(f,g) ∈ F_{ε,σ} × F_{ε,σ} | v(f) > v(g)}
```
-/
section BinaryRelations

variable {X R : Type} [inst : ExtendedNumber R] (v : RoundableEmbed X R)

/-- `FpEqRel v f g` holds iff `v(f) = v(g)` in the extended number system.
Note: This returns false for `(NaN, NaN)` since `extendedEq` on NaN is false. -/
def FpEqRel (f g : X) : Prop :=
  inst.extendedEq (v.embed f) (v.embed g)

/-- `FpLeqRel v f g` holds iff `v(f) ≤ v(g)` in the extended number system. -/
def FpLeqRel (f g : X) : Prop :=
  v.embed f ≤ v.embed g

/-- `FpLtRel v f g` holds iff `v(f) < v(g)` in the extended number system. -/
def FpLtRel (f g : X) : Prop :=
  v.embed f < v.embed g

/-- `FpGeqRel v f g` holds iff `v(f) ≥ v(g)` in the extended number system. -/
def FpGeqRel (f g : X) : Prop :=
  v.embed g ≤ v.embed f

/-- `FpGtRel v f g` holds iff `v(f) > v(g)` in the extended number system. -/
def FpGtRel (f g : X) : Prop :=
  v.embed g < v.embed f

/-- `FpIsNaN v f` holds iff `v(f)` is NaN in the extended number system. -/
def FpIsNaN (f : X) : Prop :=
  inst.isNaN (v.embed f)

/-- `FpSemanticEq v f g` holds iff `f` and `g` are semantically equal:
either they have equal embeddings, or both are NaN.
This is needed because NaN bit patterns may differ but are semantically equivalent. -/
def FpSemanticEq (f g : X) : Prop :=
  inst.extendedEq (v.embed f) (v.embed g) ∨ (FpIsNaN v f ∧ FpIsNaN v g)

end BinaryRelations

section BinaryRelationsDecidable

variable {X R : Type} [inst : ExtendedNumber R] (v : RoundableEmbed X R)

instance [DecidableRel inst.extendedEq] : Decidable (FpEqRel v f g) := by
  unfold FpEqRel; infer_instance

instance [DecidableRel ((· ≤ ·) : R → R → Prop)] : Decidable (FpLeqRel v f g) := by
  unfold FpLeqRel; infer_instance

instance [DecidableRel ((· < ·) : R → R → Prop)] : Decidable (FpLtRel v f g) := by
  unfold FpLtRel; infer_instance

instance [DecidableRel ((· ≤ ·) : R → R → Prop)] : Decidable (FpGeqRel v f g) := by
  unfold FpGeqRel; infer_instance

instance [DecidableRel ((· < ·) : R → R → Prop)] : Decidable (FpGtRel v f g) := by
  unfold FpGtRel; infer_instance

instance [DecidablePred inst.isNaN] : Decidable (FpIsNaN v f) := by
  unfold FpIsNaN; infer_instance

instance [DecidableRel inst.extendedEq] [DecidablePred inst.isNaN] :
    Decidable (FpSemanticEq v f g) := by
  unfold FpSemanticEq FpIsNaN; infer_instance

end BinaryRelationsDecidable

/-!
## Min/Max Relations

Following the BTRW15 paper specification, min and max are defined as relations
rather than functions because when one input is -0 and the other is +0,
the result is underspecified. IEEE-754 allows either value to be returned,
and compliant implementations vary (e.g., x87 vs SSE units may differ).

```
max_{ε,σ}(f,g) = f   if gt_{ε,σ}(f,g) or g = NaN
              = g   if gt_{ε,σ}(g,f) or f = NaN
              = h   where h ∈ {f,g}, if eq_{ε,σ}(f,g)

min_{ε,σ}(f,g) = f   if lt_{ε,σ}(f,g) or g = NaN
              = g   if lt_{ε,σ}(g,f) or f = NaN
              = h   where h ∈ {f,g}, if eq_{ε,σ}(f,g)
```

Note: The underspecification is an issue only when one input is -0 and the other
is +0. We consider as acceptable any model that satisfies these specifications,
regardless of whether it returns -0 or +0 for (-0, +0) and (+0, -0).
-/
section MinMaxRelations

variable {X R : Type} [inst : ExtendedNumber R] (v : RoundableEmbed X R)

/--
`FpMaxRel v f g h` holds when `h` is a valid result of `max(f, g)` according to
the BTRW15 SMT-LIB floating point semantics, parameterized by embedding `v`.

Note: We use `FpSemanticEq` instead of structural equality because implementations
may normalize NaN values to a canonical form, so the returned NaN may have a different
bit pattern than the input NaN while being semantically equivalent.
-/
def FpMaxRel (f g h : X) : Prop :=
  -- Case 1: f if gt(f,g) or g is NaN
  (FpGtRel v f g ∨ FpIsNaN v g) ∧ FpSemanticEq v h f
  ∨
  -- Case 2: g if gt(g,f) or f is NaN
  (FpGtRel v g f ∨ FpIsNaN v f) ∧ FpSemanticEq v h g
  ∨
  -- Case 3: h ∈ {f, g} if eq(f,g) (underspecified for ±0 case)
  (FpEqRel v f g ∧ (FpSemanticEq v h f ∨ FpSemanticEq v h g))

/--
`FpMinRel v f g h` holds when `h` is a valid result of `min(f, g)` according to
the BTRW15 SMT-LIB floating point semantics, parameterized by embedding `v`.

Note: We use `FpSemanticEq` instead of structural equality because implementations
may normalize NaN values to a canonical form, so the returned NaN may have a different
bit pattern than the input NaN while being semantically equivalent.
-/
def FpMinRel (f g h : X) : Prop :=
  -- Case 1: f if lt(f,g) or g is NaN
  (FpLtRel v f g ∨ FpIsNaN v g) ∧ FpSemanticEq v h f
  ∨
  -- Case 2: g if lt(g,f) or f is NaN
  (FpLtRel v g f ∨ FpIsNaN v f) ∧ FpSemanticEq v h g
  ∨
  -- Case 3: h ∈ {f, g} if eq(f,g) (underspecified for ±0 case)
  (FpEqRel v f g ∧ (FpSemanticEq v h f ∨ FpSemanticEq v h g))

end MinMaxRelations

section MinMaxRelationsDecidable

variable {X R : Type} [inst : ExtendedNumber R] (v : RoundableEmbed X R)

instance [DecidableRel ((· < ·) : R → R → Prop)]
    [DecidablePred inst.isNaN] [DecidableRel inst.extendedEq] :
    Decidable (FpMaxRel v f g h) := by
  unfold FpMaxRel FpGtRel FpIsNaN FpEqRel FpSemanticEq; infer_instance

instance [DecidableRel ((· < ·) : R → R → Prop)]
    [DecidablePred inst.isNaN] [DecidableRel inst.extendedEq] :
    Decidable (FpMinRel v f g h) := by
  unfold FpMinRel FpLtRel FpIsNaN FpEqRel FpSemanticEq; infer_instance

end MinMaxRelationsDecidable

end SmtLibSemantics
end Fp
