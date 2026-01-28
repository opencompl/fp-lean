import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound
import Fp.Utils
import Lean
open Lean

-- Reference paper: https://smt-lib.org/papers/BTRW15.pdf

class ExtendedRatLike (R : Type) extends Add R, Sub R, LT R, LE R where
  /-- Check if number is a NaN-/
  isNaN : R → Prop
  /-- Check if two numbers are equal, with extended semantics for inf and NaN -/
  extendedEq : R → R → Prop
  /-- make a rational. -/
  ofExtRat : ExtRat → R

def ExtendedRatLike.isZero {R : Type} [ExtendedRatLike R] (r : R) : Prop :=
  ExtendedRatLike.extendedEq r (ExtendedRatLike.ofExtRat (ExtRat.Number 0))

def ExtendedRatLike.ltZero {R : Type} [ExtendedRatLike R] (r : R) : Prop :=
  r < (ExtendedRatLike.ofExtRat (ExtRat.Number 0))

def ExtendedRatLike.gtZero {R : Type} [ExtendedRatLike R] (r : R) : Prop :=
  (ExtendedRatLike.ofExtRat (ExtRat.Number 0)) < r

instance : ExtendedRatLike ExtRat where
  isNaN r := r.isNaN
  extendedEq r1 r2 := r1.eq r2
  ofExtRat r := r

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
instance roundableEmbedPackedFloatRatLike [ExtendedRatLike R] : RoundableEmbed (PackedFloat e s) R where
  embed (x : PackedFloat e s) : R := ExtendedRatLike.ofExtRat x.toExtRat


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

open ExtendedRatLike in
/--
The lower half predicate return `True` if the rational `r` is strictly
between the lower approximant `l` and upper approximant `u`.

Recall that this is used to check if the number needs to be rounded up.
- If `l < u`, then we check that `r` is closer to `l` than to `u`.
- If `l = u`, then we return `True`, since the number is perfectly representable,
  and thus does not need to be rounded up.
-/
def roundableLowerHalf_of_roundableLower_roundableUpper_roundableEmbed (X R : Type)
    [ExtendedRatLike R]
    (lower : RoundableLower X R)
    (upper : RoundableUpper X R)
    (embed : RoundableEmbed X R) : RoundableLowerHalf X R where
  lowerHalf (r : R) : Prop :=
    let l := lower.lower r
    let u := upper.upper r
    let l_ext := embed.embed l
    let u_ext := embed.embed u
    extendedEq l_ext r ∨ -- either the number is perfectly representable.
    -- if it is not, then in the interval, check that we are
    -- strictly in the lower half.
    (r - l_ext) < (u_ext - r)


/-- Check if the given rational `r` is exactly in between
the two closest representable values `embed (lower r)` and `embed (upper r)`. -/
structure RoundableTieBreak (X : Type) (R : Type) where
  tieBreak : R → Prop

/--
Recall that tie break is used to determine if we are exactly in the middle
between the lower and upper approximants.

In the implementation, this corresponds to the guard bit being 1 and
the  sticky bit being zero.

If we are representable, then the lower and upper approximants overlap.
In this case, the guard bit is 0, and thus we return false.

-/
def roundableTieBreak_of_roundableLower_roundableUpper_roundableEmbed (X : Type) (R : Type) [ExtendedRatLike R]
    (lower : RoundableLower X R)
    (upper : RoundableUpper X R)
    (embed : RoundableEmbed X R) : RoundableTieBreak X R where
  tieBreak (r : R) : Prop :=
    let l := lower.lower r
    let u := upper.upper r
    let l_ext := embed.embed l
    let u_ext := embed.embed u
    (ExtendedRatLike.extendedEq l_ext u_ext) ∨ ExtendedRatLike.extendedEq (r - l_ext) (u_ext - r)


/--
Check if the number `X` is even when written in scientific notation with a power of two.
This assumes that `X` has a representation where we can check the least significant bit of the significand.
(@bollu question: Why is this a generic structure according to SMT-LIB?)
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

def RoundMethod.rounderForSign {X : Type} (roundMethod : RoundMethod X R) (sign : Bool) (r : R) : X :=
  if sign then roundMethod.upper r else roundMethod.lower r

open Classical ExtendedRatLike in
/-- define the rounding function for a given choice of 'RoundMethod'. -/
noncomputable def RoundMethod.roundAux (roundMethod : RoundMethod (PackedFloat e s) R) [ExtendedRatLike R]
    (rm : RoundingMode) (sign : Bool) (r : R) : PackedFloat e s :=
  match rm with
  | .RNE =>
      if isNaN r then roundMethod.lower r
      else if isZero r then roundMethod.rounderForSign sign r
      else if ! (isZero r) && roundMethod.lowerHalf r then roundMethod.lower r
      else if ! (isZero r) && roundMethod.tieBreak r && roundMethod.isEven (roundMethod.lower r) then roundMethod.lower r
      else if ! (isZero r) && roundMethod.tieBreak r && roundMethod.isEven (roundMethod.upper r) then roundMethod.upper r
      else if ! (isZero r) && !roundMethod.lowerHalf r && !roundMethod.tieBreak r then roundMethod.upper r
      else .mkNaN
  | .RNA =>
      if _hnan : isNaN r then roundMethod.lower r
      else
         if _hz : isZero r then roundMethod.rounderForSign sign r
         else
            if _rgt0 : ExtendedRatLike.gtZero r
            then
              if _hlh : roundMethod.lowerHalf r then roundMethod.lower r else roundMethod.upper r
            else
               -- r < 0 := by sorry
              if _hlh : roundMethod.lowerHalf r ∨ roundMethod.tieBreak r
              then roundMethod.lower r
              else roundMethod.upper r
   | .RTP =>
      if _h0 : isZero r then roundMethod.rounderForSign sign r
      else roundMethod.upper r
   | .RTN =>
      if _h0 : isZero r then roundMethod.rounderForSign sign r
      else roundMethod.lower r
   | .RTZ =>
      if _h0 : isZero r then roundMethod.rounderForSign sign r
      else
         if _rgt0 : ExtendedRatLike.gtZero r  then roundMethod.lower r else roundMethod.upper r

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

def roundableLowerByEnumeration [ExtendedRatLike R]
  [DecidableRel (fun (a b : R) => a < b)]
  [DecidableRel (fun (a b : R) => a ≤ b)]
  (embed : RoundableEmbed X R)
  (smallest : X) (univ : List X)  : RoundableLower X R where
  -- | smallest element
  lower (r : R) : X :=
    let filtered := univ.filter (fun x => decide (embed.embed x ≤ r))
    let min := filtered.maxOn
     (fun x => embed.embed x)
     (fun a b => a < b) smallest
    min

  def roundableUpperByEnumeration [ExtendedRatLike R] [DecidableRel (fun (a b : R) => a < b)]
    [DecidableRel (fun (a b : R) => a ≤ b)]
    (embed : RoundableEmbed X R) (univ : List X) (largest : X) : RoundableUpper X R where
  upper (r : R) : X :=
     let filtered := univ.filter (fun x => decide (r < embed.embed x))
     let max := filtered.minOn
      (fun x => embed.embed x)
      (fun a b => a < b) largest
    max


/--
Given an embedding and an enumeration of the type 'X', along with smallest and largest elements,
create a 'RoundableAdjunction' instance for 'X' by using the enumeration to brute-force
the lower and upper rounding functions.
-/
def RoundableAdjunction.ofEmbedByEnumeration (embed : RoundableEmbed X R)
    [ExtendedRatLike R] [DecidableRel (fun (a b : R) => a < b)] [DecidableRel (fun (a b : R) => a ≤ b)]
    (smallest : X) (univ : List X) (largest : X) : RoundableAdjunction X R where
  embed := embed.embed
  lower := (roundableLowerByEnumeration embed smallest univ).lower
  upper := (roundableUpperByEnumeration embed univ largest).upper

namespace SlowComputableRound

def roundByEnumeration (e s : Nat) :
  RoundMethod (PackedFloat e s) ExtRat where
  embed := roundableEmbedPackedFloatRatLike.embed
  lower := lower |>.lower
  upper := upper |>.upper
  lowerHalf := (roundableLowerHalf_of_roundableLower_roundableUpper_roundableEmbed (PackedFloat e s) ExtRat
    lower upper roundableEmbedPackedFloatRatLike).lowerHalf
  tieBreak :=
    (roundableTieBreak_of_roundableLower_roundableUpper_roundableEmbed (PackedFloat e s) ExtRat
      lower upper roundableEmbedPackedFloatRatLike).tieBreak
  isEven := roundableIsEven_of_packedFloat.isEven
  where
    smallest := PackedFloat.getInfinity e s true
    largest := PackedFloat.getInfinity e s false
    lower := roundableLowerByEnumeration roundableEmbedPackedFloatRatLike smallest (PackedFloat.enumerateAllList e s)
    upper := roundableUpperByEnumeration roundableEmbedPackedFloatRatLike (PackedFloat.enumerateAllList e s) largest
end SlowComputableRound

namespace SmtLibRoundMethod

def IsLawfulLower [ExtendedRatLike R] [RE : RoundableEmbed X R] (r : R) (lower : X) : Prop :=
  RE.embed lower ≤ r ∧ (∀ (lower' : X), RE.embed lower' ≤ r → RE.embed lower' ≤ RE.embed lower)

open Classical in
noncomputable def smtLibLower [Inhabited X] [ExtendedRatLike R] [RoundableEmbed X R] : RoundableLower X R where
  lower (r : R) : X :=
    if hp : ∃ (x : X), IsLawfulLower r x then
      /- Use hilbert epsilon to pick -/
      Classical.choose hp
    else
      default

def IsLawfulUpper [ExtendedRatLike R] [RE : RoundableEmbed X R] (r : R) (upper : X) : Prop :=
  r ≤ RE.embed upper ∧ (∀ (upper' : X), r ≤ RE.embed upper' → RE.embed upper ≤ RE.embed upper')

open Classical in
noncomputable def smtLibUpper [Inhabited X] [ExtendedRatLike R] [RoundableEmbed X R] : RoundableUpper X R where
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
noncomputable def smtLibV [Inhabited X] [ExtendedRatLike R] [RoundableEmbed X R] :
    RoundableAdjunction X R where
  embed := RoundableEmbed.embed
  lower := smtLibLower.lower
  upper := smtLibUpper.upper

/--
The SMT-Lib definition of the rounding methods for any choice of rounding adjunction 'v'.
The lower and upper half are defined according to 'v'.
-/
noncomputable def smtLibRoundMethod (e s : Nat) (v : RoundableAdjunction (PackedFloat e s) R) [ExtendedRatLike R] :
  RoundMethod (PackedFloat e s) R where
  embed := v.embed
  lower := v.lower
  upper := v.upper
  lowerHalf r := v.embed (v.lower r) = ves.embed (ves.lower r)
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
  where
    ves : RoundableAdjunction (PackedFloat e (s + 1)) R := smtLibV

end SmtLibRoundMethod

namespace QSemanticsRef

namespace ExhaustiveEnumerationTesting

def EUnpackedFloat.round {E S : Nat} (e s : Nat)
  (rm : RoundingMode) (euf : EUnpackedFloat E S)  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  if euf.isNaN then
    EUnpackedFloat.mkNaN
  else if euf.isInfinite then
    EUnpackedFloat.mkInfinity euf.sign
  else
    let uf : UnpackedFloat E S := euf.num
    let roundedPf : PackedFloat e s := uf.round rm |>.pack
    roundedPf.unpack

/-
def roundMethodsEqual? (E : Nat := 4) (S : Nat := 4) (e : Nat := 4) (s : Nat := 2)
  (r1 r2 : RoundMethod (PackedFloat e s) ExtRat)
  [DecidablePred r1.tieBreak]
  [DecidablePred r2.tieBreak]
  [DecidablePred r1.lowerHalf]
  [DecidablePred r2.lowerHalf]
  : IO Bool := do
  let success : Bool := true
  -- success := success || (← lowerHalfEqual?) -- good
  let success := success || (← lowerEqual?) -- good
  let success := success || (← higherEqual?) -- good
  let success := success || (← tieBreakEqual?) -- good
  return success

  -- isEvenEqual? -- good
  where
    lowerEqual? : IO Bool := do
      for pf in PackedFloat.enumerateAllList E S do
        let r := pf.toExtRat
        let l1 := r1.lower r
        let l2 := r2.lower r
        if l1 != l2 then
          IO.println s!"Discrepancy in lower for {repr pf} (ExtRat: {repr r})"
          IO.println s!"{repr l1} vs {repr l2}"
          return false
      return true
    higherEqual? : IO Bool := do
      for pf in PackedFloat.enumerateAllList E S do
        let r := pf.toExtRat
        let u1 := r1.upper r
        let u2 := r2.upper r
        if u1 != u2 then
          IO.println s!"Discrepancy in upper for {repr pf} (ExtRat: {repr r})"
          IO.println s!"{repr u1} vs {repr u2}"
          return false
      return true
    tieBreakEqual? : IO Bool := do
      for pf in PackedFloat.enumerateAllList E S do
        let r := pf.toExtRat
        let tb1 := decide (r1.tieBreak r)
        let tb2 := decide (r2.tieBreak r)
        let out1 := r1.roundAux .RNE pf.sign r
        let out2 := r2.roundAux .RNE pf.sign r
        if tb1 != tb2 then
          IO.println s!"Discrepancy in tieBreak for {repr pf} (ExtRat: {repr r})"
          IO.println s!"tiebreak1:{repr tb1} ~ rounded1:{repr out1.toExtRat}"
          IO.println s!"tiebreak2:{repr tb2} ~ rounded2:{repr out2.toExtRat}"
          IO.println s!"l:{repr (r1.lower r).toExtRat} <= {repr r} <= {repr (r1.upper r).toExtRat}"
        return false
      return true
    lowerHalfEqual? : IO Bool := do
      for pf in PackedFloat.enumerateAllList E S do
        let r := pf.toExtRat
        let lh1 := r1.lowerHalf r
        let lh2 := r2.lowerHalf r
        if lh1 != lh2 then
          IO.println s!"Discrepancy in lowerHalf for {repr pf} (ExtRat: {repr r})"
          IO.println s!"{repr lh1} vs {repr lh2}"
          return false
      return true
    isEvenEqual? : IO Bool := do
      for pf in PackedFloat.enumerateAllList e s do
        let r := pf.toExtRat
        let lh1 := r1.isEven pf
        let lh2 := r2.isEven pf
        if lh1 != lh2 then
          IO.println s!"Discrepancy in lowerHalf for {repr pf} (ExtRat: {repr r})"
          IO.println s!"{repr lh1} vs {repr lh2}"
          return false
      return true


/-- info: true -/
#guard_msgs in #eval roundMethodsEqual? 2 4 2 3
  (SmtLibRoundMethod.smtLibRoundMethod _ _ (SmtLibRoundMethod.smtLibV _ _))
  (SlowComputableRound.roundByEnumeration _ _)
-/


-- #exit

/-- test that 'lower' agrees with reference implementation -/
def compareRoundingFunctions
  (E S : Nat) (e s : Nat) (rm : RoundingMode)
  (rounderGolden rounderUnderTest : RoundingMode → (sign  : Bool) → PackedFloat E S → PackedFloat e s)
  : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerateNumberList E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r := pf.toExtRat
    let sign := pf.sign
    let golden := rounderGolden rm sign pf
    let test : PackedFloat e s := rounderUnderTest rm sign pf
    let res := golden.equal_denotation test
    if !res then
      nfailure := nfailure + 1
      if nfailure > 10 then
        continue
      IO.println s!"---"
      let rgolden := golden.toExtRat
      let rtest := test.toExtRat
      let distGolden := (r - rgolden).abs
      let distTest :=  (r - rtest).abs
      let correct := distGolden ≤ distTest
      IO.println s!"Discrepancy for (Q: {repr r}) (RM: {repr rm}) (Sign: {sign}) {repr pf}"
      IO.println s!"  Golden: (Q: {repr golden.toExtRat}) (UF: {repr golden.unpack}) (PF: {repr golden})"
      IO.println s!"  Tested: (Q: {repr test.toExtRat}) (UF: {repr test.unpack}) (PF: {repr test})"
      IO.println s!"  Distance: {if correct then "✅" else "❌"}"
      IO.println s!"    distGolden : {repr distGolden}"
      IO.println s!"    distTest : {repr distTest})"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0


/--
error: Unknown constant `PackedFloat.enumerate`
---
error: Unknown identifier `SlowComputableRound.roundBySlowEnumeration`
-/
#guard_msgs in #eval compareRoundingFunctions 5 4 5 2 .RNE
  (rounderGolden := fun rm sign pf =>
      let v := (RoundableAdjunction.ofEmbedByEnumeration (X := PackedFloat _ _)
          (roundableEmbedPackedFloatRatLike)
          (PackedFloat.getInfinity _ _ true )
          (PackedFloat.enumerate _ _)
          (PackedFloat.getInfinity _ _ false))
      (SmtLibRoundMethod.smtLibRoundMethod _ _ v).roundAux rm sign pf.toExtRat)
  (rounderUnderTest := fun rm sign pf => (SlowComputableRound.roundBySlowEnumeration _ _).roundAux rm sign pf.toExtRat)


/-
/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'RoundMethod.roundAux', which is 'noncomputable'
-/
#guard_msgs in #eval compareRoundingFunctions 4 4 4 2 .RNE
  (rounderGolden := fun rm sign pf =>
      let v := (RoundableAdjunction.ofEmbedByEnumeration (X := PackedFloat _ _)
          (roundableEmbedPackedFloatRatLike)
          (PackedFloat.getInfinity _ _ true )
          (PackedFloat.enumerateAllList _ _)
          (PackedFloat.getInfinity _ _ false))
      (SmtLibRoundMethod.smtLibRoundMethod _ _ v).roundAux rm sign pf.toExtRat)
  (rounderUnderTest := fun rm sign pf =>
    EUnpackedFloat.round _ _ (rm := rm) (euf := pf.unpack) |>.pack
  )
  -- (rounderUnderTest := fun rm sign pf => (SlowComputableRound.roundByEnumeration _ _).roundAux rm sign pf.toExtRat)
-/

end ExhaustiveEnumerationTesting
