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

The two equality notions differ in their treatment of NaN:
- `smtLibEq`: NaN = NaN (SMT-LIB semantics, structural equality)
- `ieeeEq`: NaN ≠ NaN (IEEE 754 semantics, behavioral equality)

SMT-LIB uses NaN = NaN because there is a single NaN element in the carrier set.
IEEE 754 uses NaN ≠ NaN because NaN represents "not a number" and comparing
undefined values should return false.
-/
class ExtendedNumber (R : Type) extends Add R, Sub R, LT R, LE R, Neg R, Zero R where
  /-- Check if number is a NaN -/
  isNaN : R → Prop
  /-- SMT-LIB equality: NaN = NaN (structural equality on the carrier set) -/
  smtLibEq : R → R → Prop

/-- IEEE equality: NaN ≠ NaN (behavioral equality following IEEE 754) -/
def ExtendedNumber.ieeeEq {R : Type} [inst : ExtendedNumber R] (r1 r2 : R) : Prop :=
  ¬inst.isNaN r1 ∧ ¬inst.isNaN r2 ∧ inst.smtLibEq r1 r2

def ExtendedNumber.isZero {R : Type} [ExtendedNumber R] (r : R) : Prop :=
  ExtendedNumber.smtLibEq r (Zero.zero)

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

instance [hEx : ExtendedNumber R] [DecidableRel hEx.smtLibEq] :
    DecidablePred hEx.isZero := by
  unfold ExtendedNumber.isZero
  infer_instance

instance instExtendedRat : ExtendedNumber ExtRat where
  isNaN r := r.isNaN
  smtLibEq r1 r2 := r1.eq r2

instance : Decidable (instExtendedRat.isZero r) := by
  simp [ExtendedNumber.isZero, ExtendedNumber.smtLibEq]
  infer_instance

instance : Decidable (instExtendedRat.isNaN r) := by
  simp [ExtendedNumber.isNaN]
  infer_instance

instance : DecidableRel instExtendedRat.smtLibEq := by
  simp [ExtendedNumber.smtLibEq]
  infer_instance

instance [hEx : ExtendedNumber R] [DecidablePred hEx.isNaN] [DecidableRel hEx.smtLibEq] :
    DecidableRel hEx.ieeeEq := by
  unfold ExtendedNumber.ieeeEq
  infer_instance


@[simp]
theorem instExtendedRat.isNaN_eq (r1 : ExtRat) :
  instExtendedRat.isNaN r1 = ExtRat.isNaN r1 := rfl

@[simp]
theorem instExtendedRat.smtLibEq (r s : ExtRat) :
    instExtendedRat.smtLibEq r s = (r = s) := by
  simp [ExtendedNumber.smtLibEq]

@[simp]
theorem instExtendedRat.isZero (r : ExtRat) :
    instExtendedRat.isZero r = (r = 0) := by
  simp [ExtendedNumber.isZero]

@[simp]
theorem instExtendedRat.ltZero (r : ExtRat) :
    instExtendedRat.ltZero r = (r < 0) := by
  simp [ExtendedNumber.ltZero]

@[simp]
theorem instExtendedRat.gtZero (r : ExtRat) :
    instExtendedRat.gtZero r = (0 < r) := by
  simp [ExtendedNumber.gtZero]

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

@[simp]
theorem isEven_roundableIsEven_of_packedFloat (x : PackedFloat e s) :
  roundableIsEven_of_packedFloat.isEven x = (x.sig.toNat % 2 == 0) := rfl

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

@[simp]
theorem rounderForSign_true_eq_upper {X : Type} (roundMethod : RoundMethod X R) (r : R) :
  roundMethod.rounderForSign true r = roundMethod.upper r := rfl

@[simp]
theorem rounderForSign_false_eq_lower {X : Type} (roundMethod : RoundMethod X R) (r : R) :
  roundMethod.rounderForSign false r = roundMethod.lower r := rfl

section Round

variable
    {e s R} (roundMethod : RoundMethod (PackedFloat e s) R) [inst : ExtendedNumber R]
    [DecidablePred inst.isZero]
    [DecidablePred inst.isNaN]
    [DecidablePred roundMethod.lowerHalf]
    [DecidablePred roundMethod.tieBreak]
    [DecidablePred inst.gtZero]
    [DecidablePred inst.ltZero]
    (rm : RoundingMode) (sign : Bool) (r : R)

open ExtendedNumber

def RoundMethod.roundRNE : PackedFloat e s :=
      if isNaN r then roundMethod.lower r
      else if ¬ (isZero r) ∧ !roundMethod.lowerHalf r ∧ !roundMethod.tieBreak r then roundMethod.upper r
      else if ¬ (isZero r) ∧ roundMethod.tieBreak r ∧ roundMethod.isEven (roundMethod.upper r) then roundMethod.upper r
      else if ¬ (isZero r) ∧ roundMethod.tieBreak r ∧ roundMethod.isEven (roundMethod.lower r) then roundMethod.lower r
      else if ¬ (isZero r) ∧ roundMethod.lowerHalf r then roundMethod.lower r
      else if isZero r then roundMethod.rounderForSign sign r
      else .getNaN e s -- does not occur.

def RoundMethod.roundRNA : PackedFloat e s :=
      if isNaN r then roundMethod.lower r
      else if gtZero r ∧ ¬ roundMethod.lowerHalf r then roundMethod.upper r
      else if gtZero r ∧ roundMethod.lowerHalf r then roundMethod.lower r
      else if isZero r then roundMethod.rounderForSign sign r
      else if ltZero r ∧ ¬ roundMethod.lowerHalf r ∧ ¬ roundMethod.tieBreak r then roundMethod.upper r
      else if ltZero r ∧ (roundMethod.lowerHalf r ∨ roundMethod.tieBreak r) then roundMethod.lower r
      else .getNaN e s -- does not occur.

def RoundMethod.roundRTP : PackedFloat e s :=
  if isZero r then roundMethod.rounderForSign sign r
  else  roundMethod.upper r


def RoundMethod.roundRTN : PackedFloat e s :=
  if isZero r then roundMethod.rounderForSign sign r
  else roundMethod.lower r

def RoundMethod.roundRTZ : PackedFloat e s :=
  if isZero r then roundMethod.rounderForSign sign r
  else if gtZero r then roundMethod.lower r
  else if ltZero r then roundMethod.upper r
  else .getNaN e s -- does not occur.


/-- define the rounding function for a given choice of 'RoundMethod'. -/
def RoundMethod.round : PackedFloat e s :=
  match rm with
  | .RNE => roundMethod.roundRNE sign r
  | .RNA => roundMethod.roundRNA sign r
  | .RTP => roundMethod.roundRTP sign r
  | .RTN => roundMethod.roundRTN sign r
  | .RTZ => roundMethod.roundRTZ sign r

@[simp]
theorem RoundMethod.round_RNE_eq : roundMethod.round .RNE sign r = roundMethod.roundRNE sign r := by
  simp [RoundMethod.round]

@[simp]
theorem RoundMethod.round_RNA_eq : roundMethod.round .RNA sign r = roundMethod.roundRNA sign r := by
  simp [RoundMethod.round]

@[simp]
theorem RoundMethod.round_RTP_eq : roundMethod.round .RTP sign r = roundMethod.roundRTP sign r := by
  simp [RoundMethod.round]

@[simp]
theorem RoundMethod.round_RTN_eq : roundMethod.round .RTN sign r = roundMethod.roundRTN sign r := by
  simp [RoundMethod.round]

@[simp]
theorem RoundMethod.round_RTZ_eq : roundMethod.round .RTZ sign r = roundMethod.roundRTZ sign r := by
  simp [RoundMethod.round]

end Round

-- namespace SmtLibRoundMethod

/-- 'lower' is a valid greatest lower bound for 'r'. -/
def IsLawfulLower [ExtendedNumber R] [RE : RoundableEmbed X R] [LE X] (r : R) (lower : X) : Prop :=
  RE.embed lower ≤ r ∧ (∀ (lower' : X), RE.embed lower' ≤ r → lower' ≤ lower)

open Classical in
noncomputable def smtLibLower [Inhabited X] [ExtendedNumber R] [RoundableEmbed X R] [LE X] : RoundableLower X R where
  lower (r : R) : X := epsilon (fun x => IsLawfulLower r x)

/--
'upper' is a valid least upper bound for 'r'.
TODO: need to use RoundableLe to say that `upper ≤ upper'`
to get the correct ordering.
This definition is too loose.
-/
def IsLawfulUpper [ExtendedNumber R] [RE : RoundableEmbed X R] [LE X] (r : R) (upper : X) : Prop :=
  r ≤ RE.embed upper ∧ (∀ (upper' : X), r ≤ RE.embed upper' → upper ≤ upper')

open Classical in
noncomputable def smtLibUpper {X R} [Inhabited X] [ExtendedNumber R] [RoundableEmbed X R] [LE X] : RoundableUpper X R where
  upper (r : R) : X := epsilon (fun x => IsLawfulUpper r x)

/--
The default SMT-Lib adjunction of packed floats into rationals, written `v_ε,σ(f)`,
where `vlower` and `vupper` is defined via exhaustive enumeration
for better computational properties.

We will show later that the `vlower` and `vupper` defined this way agree
with the galois adjunction expected.
-/
noncomputable def smtLibV [Inhabited X] [ExtendedNumber R] [RoundableEmbed X R] [LE X] :
    RoundableAdjunction X R where
  embed := RoundableEmbed.embed
  lower := smtLibLower.lower
  upper := smtLibUpper.upper

@[simp]
theorem smtLibV_embed_eq [Inhabited X]
  [ExtendedNumber R] [RoundableEmbed X R] [LE X]
    : (smtLibV (X := X) (R := R)).embed = RoundableEmbed.embed := rfl

@[simp]
theorem smtLibV_lower_eq [Inhabited X]
  [ExtendedNumber R] [RoundableEmbed X R] [LE X]
    : (smtLibV (X := X) (R := R)).lower = smtLibLower.lower := rfl

@[simp]
theorem smtLibV_upper_eq [Inhabited X]
  [ExtendedNumber R] [RoundableEmbed X R] [LE X]
    : (smtLibV (X := X) (R := R)).upper = smtLibUpper.upper := rfl

/--
The SMT-Lib definition of the rounding methods for any choice of rounding adjunction 'v'.
-/
def smtLibRoundMethod {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  RoundMethod (PackedFloat e s) R where
  embed := v.embed
  lower := v.lower
  upper := v.upper
  lowerHalf r := ExtendedNumber.smtLibEq (v.embed (v.lower r))  (ves.embed (ves.lower r))
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


@[simp]
theorem smtLibRoundMethod.lower_eq {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  (smtLibRoundMethod e s v ves).lower = v.lower := rfl

@[simp]
theorem smtLibRoundMethod.upper_eq {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  (smtLibRoundMethod e s v ves).upper = v.upper := rfl

@[simp]
theorem smtLibRoundMethod.embed_eq {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  (smtLibRoundMethod e s v ves).embed = v.embed := rfl

-- @[simp]
theorem smtLibRoundMethod.lowerHalf_eq {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  (smtLibRoundMethod e s v ves).lowerHalf = (fun r => ExtendedNumber.smtLibEq (v.embed (v.lower r))  (ves.embed (ves.lower r))) := rfl

-- @[simp]
theorem smtLibRoundMethod.tieBreak_eq {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  (smtLibRoundMethod e s v ves).tieBreak = (fun r =>
    (v.embed (v.lower r) < ves.embed (ves.lower r)) =
    (ves.embed (ves.upper r) < (v.embed (v.upper r)))) := rfl

theorem smtLibRoundMethod.roundForSign_eq {R : Type} (e s : Nat)
    (v : RoundableAdjunction (PackedFloat e s) R)
    (ves : RoundableAdjunction (PackedFloat e (s + 1)) R)
    [ExtendedNumber R] :
  (smtLibRoundMethod e s v ves).rounderForSign = fun sign r =>
    if sign then v.upper r else v.lower r := by
  rfl


instance [hExtended : ExtendedNumber R]
    [DecidableRel hExtended.smtLibEq]
    {v : RoundableAdjunction (PackedFloat e s) R}
    {ves : RoundableAdjunction (PackedFloat e (s + 1)) R} :
    DecidablePred ((smtLibRoundMethod e s v ves).lowerHalf) := by
  rw [smtLibRoundMethod]
  infer_instance

instance [hExtended : ExtendedNumber R]
    [hdec : ((r s : R) → Decidable (r < s))]
    {v : RoundableAdjunction (PackedFloat e s) R}
    {ves : RoundableAdjunction (PackedFloat e (s + 1)) R} :
    DecidablePred ((smtLibRoundMethod e s v ves).tieBreak) := by
  rw [smtLibRoundMethod]
  infer_instance

-- end SmtLibRoundMethod

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

/--
Division. The result sign is the xor of the operand signs, passed to `round` so
that zero results carry the IEEE-754 sign (the embedding `v` collapses `±0`, so
the sign of a zero *result* cannot be recovered from `z` itself).

The divideByZero case (`y = ±0`, `x` finite nonzero) must be special-cased for the
same reason: `v(y) = 0` forgets the divisor's sign, so the sign of the resulting
infinity — which IEEE-754 §7.3 defines as the xor of the operand signs — is not a
function of `z`. (An earlier transcription computed
`if xorSign then neg (round rm true (-z)) else round rm false z`; that is the
identity on the sign of `z` for both zero and infinite `z`, and therefore produced
`+0` where IEEE-754 requires `-0` and `∞ / -0 = +∞` where IEEE-754 requires `-∞`.
The present definition agrees with the implementation — itself validated bit-for-bit
against symfpu — on all inputs of small formats; see `Fp/Theorems/Division.lean`.)
-/
def div [Div R] (x y : PackedFloat e s) : PackedFloat e s :=
      let z :=  ((roundMethod.embed x) / (roundMethod.embed y))
      let sign : Bool := xorSign x y
      if ExtendedNumber.isZero (roundMethod.embed y)
          ∧ ¬ ExtendedNumber.isZero (roundMethod.embed x)
          ∧ ¬ ExtendedNumber.isNaN (roundMethod.embed x) then
        PackedFloat.getInfinity e s sign
      else
        roundMethod.round rm sign z

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

/-- `FpSmtLibEqRel v f g` holds iff `v(f) = v(g)` using SMT-LIB equality.
This uses SMT-LIB semantics where NaN = NaN (since there's a single NaN in the carrier set).
Note: All NaN bit patterns map to the same `ExtRat.NaN`, so different NaN representations are equal. -/
def FpSmtLibEqRel (f g : X) : Prop :=
  inst.smtLibEq (v.embed f) (v.embed g)

/-- `FpIeeeEqRel v f g` holds iff `v(f) = v(g)` using IEEE equality.
This uses IEEE 754 semantics where NaN ≠ NaN.
This matches the paper's `eq_{ε,σ}` which "does not contain (NaN, NaN)". -/
def FpIeeeEqRel (f g : X) : Prop :=
  inst.ieeeEq (v.embed f) (v.embed g)

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

end BinaryRelations

section BinaryRelationsDecidable

variable {X R : Type} [inst : ExtendedNumber R] (v : RoundableEmbed X R)

instance [DecidableRel inst.smtLibEq] : Decidable (FpSmtLibEqRel v f g) := by
  unfold FpSmtLibEqRel; infer_instance

instance [DecidablePred inst.isNaN] [DecidableRel inst.smtLibEq] :
    Decidable (FpIeeeEqRel v f g) := by
  unfold FpIeeeEqRel ExtendedNumber.ieeeEq; infer_instance

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

We use `FpSmtLibEqRel` (SMT-LIB equality where NaN = NaN) rather than structural equality
because implementations may normalize NaN values to a canonical form. Since all NaN bit
patterns embed to the same value, they are equal under `FpSmtLibEqRel`.
-/
def FpMaxRel (f g h : X) : Prop :=
  -- Case 1: f if gt(f,g) or g is NaN
  (FpGtRel v f g ∨ FpIsNaN v g) ∧ FpSmtLibEqRel v h f
  ∨
  -- Case 2: g if gt(g,f) or f is NaN
  (FpGtRel v g f ∨ FpIsNaN v f) ∧ FpSmtLibEqRel v h g
  ∨
  -- Case 3: h ∈ {f, g} if eq(f,g) (underspecified for ±0 case)
  (FpSmtLibEqRel v f g ∧ (FpSmtLibEqRel v h f ∨ FpSmtLibEqRel v h g))

/--
`FpMinRel v f g h` holds when `h` is a valid result of `min(f, g)` according to
the BTRW15 SMT-LIB floating point semantics, parameterized by embedding `v`.

We use `FpSmtLibEqRel` (SMT-LIB equality where NaN = NaN) rather than structural equality
because implementations may normalize NaN values to a canonical form. Since all NaN bit
patterns embed to the same value, they are equal under `FpSmtLibEqRel`.
-/
def FpMinRel (f g h : X) : Prop :=
  -- Case 1: f if lt(f,g) or g is NaN
  (FpLtRel v f g ∨ FpIsNaN v g) ∧ FpSmtLibEqRel v h f
  ∨
  -- Case 2: g if lt(g,f) or f is NaN
  (FpLtRel v g f ∨ FpIsNaN v f) ∧ FpSmtLibEqRel v h g
  ∨
  -- Case 3: h ∈ {f, g} if eq(f,g) (underspecified for ±0 case)
  (FpSmtLibEqRel v f g ∧ (FpSmtLibEqRel v h f ∨ FpSmtLibEqRel v h g))

end MinMaxRelations

section MinMaxRelationsDecidable

variable {X R : Type} [inst : ExtendedNumber R] (v : RoundableEmbed X R)

instance [DecidableRel ((· < ·) : R → R → Prop)]
    [DecidablePred inst.isNaN] [DecidableRel inst.smtLibEq] :
    Decidable (FpMaxRel v f g h) := by
  unfold FpMaxRel FpGtRel FpIsNaN FpSmtLibEqRel; infer_instance

instance [DecidableRel ((· < ·) : R → R → Prop)]
    [DecidablePred inst.isNaN] [DecidableRel inst.smtLibEq] :
    Decidable (FpMinRel v f g h) := by
  unfold FpMinRel FpLtRel FpIsNaN FpSmtLibEqRel; infer_instance

end MinMaxRelationsDecidable

end SmtLibSemantics
end Fp
