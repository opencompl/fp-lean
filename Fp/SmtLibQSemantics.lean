import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound
import Lean
open Lean

-- Reference paper: https://smt-lib.org/papers/BTRW15.pdf

structure RoundableUpper (X : Type) where
  upper : ExtRat → X

structure RoundableLower (X : Type) where
  lower : ExtRat → X

structure RoundableEmbed (X : Type) where
  embed : X → ExtRat

def roundableEmbedPackedFloat : RoundableEmbed (PackedFloat e s) where
  embed (x : PackedFloat e s) : ExtRat := x.toExtRat

structure RoundableAdjunction (X : Type) extends
  RoundableEmbed X,
  RoundableLower X,
  RoundableUpper X
  where


structure RoundableLowerHalf (X : Type) where
  lowerHalf : ExtRat → Bool

def roundableLowerHalf_of_roundableLower_roundableUpper_roundableEmbed (X : Type)
    (lower : RoundableLower X)
    (upper : RoundableUpper X)
    (embed : RoundableEmbed X) : RoundableLowerHalf X where
  lowerHalf (r : ExtRat) : Bool :=
    let l := lower.lower r
    let u := upper.upper r
    let l_ext := embed.embed l
    let u_ext := embed.embed u
    (r - l_ext) < (u_ext - r)


structure RoundableTieBreak (X : Type) where
  tieBreak : ExtRat → Bool

def roundableTieBreak_of_roundableLower_roundableUpper_roundableEmbed (X : Type)
    (lower : RoundableLower X)
    (upper : RoundableUpper X)
    (embed : RoundableEmbed X) : RoundableTieBreak X where
  tieBreak (r : ExtRat) : Bool :=
    let l := lower.lower r
    let u := upper.upper r
    let l_ext := embed.embed l
    let u_ext := embed.embed u
    (r - l_ext) = (u_ext - r)


structure RoundableIsEven (X : Type) where
  isEven : X → Bool



def roundableIsEven_of_packedFloat
    : RoundableIsEven (PackedFloat e s) where
  isEven (x : PackedFloat e s) : Bool :=
    x.sig.getLsbD 0 = false


structure RoundablePredicates (X : Type) extends
  RoundableLowerHalf X,
  RoundableTieBreak X,
  RoundableIsEven X
  where


structure RoundMethod (X : Type) extends
  RoundableAdjunction X,
  RoundablePredicates X

def RoundMethod.rounderForSign {X : Type} (roundMethod : RoundMethod X) (sign : Bool) (r : ExtRat) : X :=
  if sign then roundMethod.upper r else roundMethod.lower r

def RoundMethod.roundAux (roundMethod : RoundMethod (PackedFloat e s))
    (rm : RoundingMode) (sign : Bool) (r : ExtRat) : PackedFloat e s :=
  match rm with
  | .RNE =>
      if _hz : r = .Number 0 then roundMethod.rounderForSign sign r
      else
        if _hlh : roundMethod.lowerHalf r
        then roundMethod.lower r
        else
         if _htb : roundMethod.tieBreak r
         then
            if _heven : roundMethod.isEven (roundMethod.lower r)
            then roundMethod.lower r
            else roundMethod.upper r
         else
            -- not tie break, not lower, so we are in upper half.
            -- have : uh r v := by
            --    have := trichotomy_lh_tb_uh r v
            --    grind
            roundMethod.upper r
  | .RNA =>
      if _hnan : r = .NaN then roundMethod.lower r
      else
         if _hz : r = .Number 0 then roundMethod.rounderForSign sign r
         else
            if _rgt0 : (ExtRat.Number 0).lt r
            then
              if _hlh : roundMethod.lowerHalf r then roundMethod.lower r else roundMethod.upper r
            else
               -- r < 0 := by sorry
              if _hlh : roundMethod.lowerHalf r ∨ roundMethod.tieBreak r
              then roundMethod.lower r
              else roundMethod.upper r
   | .RTP =>
      if _h0 : r = .Number 0 then roundMethod.rounderForSign sign r
      else roundMethod.upper r
   | .RTN =>
      if _h0 : r = .Number 0 then roundMethod.rounderForSign sign r
      else roundMethod.lower r
   | .RTZ =>
      if _h0 : r = .Number 0 then roundMethod.rounderForSign sign r
      else
         if _rgt0 : r > .Number 0 then roundMethod.lower r else roundMethod.upper r


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

def roundableLowerByEnumeration (embed : RoundableEmbed X) (univ : List X) (smallest : X) : RoundableLower X where
  lower (r : ExtRat) : X :=
    let filtered := univ.filter (fun x => decide (embed.embed x ≤ r))
    let min := filtered.maxOn
     (fun x => embed.embed x)
     (fun a b => a ≤ b) smallest
    min

  def roundableUpperByEnumeration
    (embed : RoundableEmbed X) (univ : List X) (largest : X) : RoundableUpper X where
  upper (r : ExtRat) : X :=
     let filtered := univ.filter (fun x => decide (r ≤ embed.embed x))
     let max := filtered.minOn
      (fun x => embed.embed x)
      (fun a b => a ≤ b) largest
    max


/--
Given an embedding and an enumeration of the type 'X', along with smallest and largest elements,
create a 'RoundableAdjunction' instance for 'X' by using the enumeration to brute-force
the lower and upper rounding functions.
-/
def RoundableAdjunction.ofEmbedByEnumeration (embed : RoundableEmbed X)
    (smallest : X) (univ : List X) (largest : X) : RoundableAdjunction X where
  embed := embed.embed
  lower := (roundableLowerByEnumeration embed univ  smallest).lower
  upper := (roundableUpperByEnumeration embed univ  largest).upper


namespace SlowEnumerationRoundMethod

def roundBySlowEnumeration : RoundMethod (PackedFloat e s) where
  embed := roundableEmbedPackedFloat.embed
  lower := lower |>.lower
  upper := upper |>.upper
  lowerHalf := (roundableLowerHalf_of_roundableLower_roundableUpper_roundableEmbed (PackedFloat e s)
    lower upper roundableEmbedPackedFloat).lowerHalf
  tieBreak :=
    (roundableTieBreak_of_roundableLower_roundableUpper_roundableEmbed (PackedFloat e s)
      lower upper roundableEmbedPackedFloat).tieBreak
  isEven := roundableIsEven_of_packedFloat.isEven
  where
    lower := roundableLowerByEnumeration roundableEmbedPackedFloat (PackedFloat.enumerate e s) (PackedFloat.getInfinity e s true)
    upper := roundableUpperByEnumeration roundableEmbedPackedFloat (PackedFloat.enumerate e s) (PackedFloat.getInfinity e s false)
end SlowEnumerationRoundMethod

namespace SmtLibRoundMethod

/--
The default SMT-Lib rounding method, written `v_ε,σ(f)`,
where `vlower` and `vupper` is defined via exhaustive enumeration
for better computational properties.

We will show later that the `vlower` and `vupper` defined this way agree
with the galois adjunction expected.
-/
def smtLibV (e s : Nat) : RoundableAdjunction (PackedFloat e s) :=
  RoundableAdjunction.ofEmbedByEnumeration
    roundableEmbedPackedFloat
    (smallest := PackedFloat.getInfinity e s true)
    (univ := PackedFloat.enumerate e s)
    (largest := PackedFloat.getInfinity e s false)


/--
The SMT-Lib definition of the rounding methods, which are based on the packed float representations.
-/
def smtLibRoundMethod (e s : Nat) (v : RoundableAdjunction (PackedFloat e s)) :
  RoundMethod (PackedFloat e s) where
  embed := v.embed
  lower := v.lower
  upper := v.upper
  lowerHalf r := v.embed (v.lower r) = ves.embed (ves.lower r)
  tieBreak r := v.embed (v.lower r) < ves.embed (ves.lower r)
  isEven := roundableIsEven_of_packedFloat.isEven
  where
    ves := smtLibV e (s - 1)

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

/-- test that 'lower' agrees with reference implementation -/
def runRoundAgreesWithUnpackedFloatRound (E S : Nat) (e s : Nat) (rm : RoundingMode)
  (roundSemantics : RoundMethod (PackedFloat e s))
  : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let sign := pf.sign
    let golden := roundSemantics.roundAux rm sign r
    let ufRounded := pf.unpack |> EUnpackedFloat.round e s rm
    let ufRoundedPacked := ufRounded.pack
    let res := golden = ufRoundedPacked
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}), RoundingMode: {repr rm}, sign: {sign}"
      IO.println s!"  Golden result:       {repr golden}  | ExtRat: {repr golden.toExtRat} | UnpackedFloat : {repr golden.unpack}"
      IO.println s!"  UnpackedFloat result: {repr ufRoundedPacked} | ExtRat: {repr ufRoundedPacked.toExtRat} | UnpackedFloat : {repr ufRounded}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

#guard_msgs in #eval runRoundAgreesWithUnpackedFloatRound 5 4 5 3 .RNE (SlowEnumerationRoundMethod.roundBySlowEnumeration)

/-
These are left unimplemented, and will be impplemented in a subequent PR
for the faster rounding.
def lowerAgreesWithRefTest (E S : Nat)
  (roundSemanticsTest : RoundMethod (PackedFloat e s))
  (roundSemanticsGolden : RoundMethod (PackedFloat e s)) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let fast := roundSemanticsTest.lower r
    let golden := roundSemanticsGolden.lower r
    let res := fast = golden
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}) in lower approximant"
      IO.println s!"  Golden result:  {repr golden}  | ExtRat: {repr golden.toExtRat} | UnpackedFloat : {repr golden.unpack}"
      IO.println s!"  Fast result: {repr fast} | ExtRat: {repr fast.toExtRat} | UnpackedFloat : {repr fast.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

def upperAgreesWithRefTest (E S : Nat)
  (roundSemanticsTest : RoundMethod (PackedFloat e s))
  (roundSemanticsGolden : RoundMethod (PackedFloat e s)) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let fast := roundSemanticsTest.upper r
    let golden := roundSemanticsGolden.upper r
    let res := fast = golden
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}) in upper approximant"
      IO.println s!"  Golden result:  {repr golden}  | ExtRat: {repr golden.toExtRat} | UnpackedFloat : {repr golden.unpack}"
      IO.println s!"  Fast result: {repr fast} | ExtRat: {repr fast.toExtRat} | UnpackedFloat : {repr fast.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0
-/

end ExhaustiveEnumerationTesting
