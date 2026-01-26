import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound
import Lean
open Lean

-- Reference paper: https://smt-lib.org/papers/BTRW15.pdf

/-- Embed the type `X` into the extended rationals. -/
structure RoundableEmbed (X : Type) where
  embed : X → ExtRat


/--
Compute the upper approximant, which is the closest `x` such that `r ≤ embed x`.
Abstractly, this obeys the adjunction law: `r ≤ embed x ↔ upper r ≤ x`.
-/
structure RoundableUpper (X : Type) where
  upper : ExtRat → X

/-- Compute the lower approximant, which is the closest `x` such that `embed x ≤ r`.
Abstractly, this obeys the adjunction law: `embed x ≤ r ↔ x ≤ lower r`.
-/
structure RoundableLower (X : Type) where
  lower : ExtRat → X


/-- The default embedding of packed floats into the extended rationals. -/
def roundableEmbedPackedFloat : RoundableEmbed (PackedFloat e s) where
  embed (x : PackedFloat e s) : ExtRat := x.toExtRat


/-- A rounding adjunction is a triple (lower, embed, upper), where
`lower` and `upper` compute the lower and upper approximants of `embed`. -/
structure RoundableAdjunction (X : Type) extends
  RoundableEmbed X,
  RoundableLower X,
  RoundableUpper X
  where


/-- Check if the given rational `r` is *strictly in* the lower half
of the interval `(embed (lower r), embed (upper r))`. -/
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


/-- Check if the given rational `r` is exactly in between
the two closest representable values `embed (lower r)` and `embed (upper r)`. -/
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
    x.sig.getLsbD 0 = false

/-- Roundable predicates allow us to determine if a rational is in the lower half, tie break,
and also let us check if a value X represents an even number (for RNE). -/
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

/-- define the rounding function for a given choice of 'RoundMethod'. -/
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

def roundableLowerByEnumeration (embed : RoundableEmbed X)
  (smallest : X) (univ : List X) : RoundableLower X where
  -- | smallest element
  lower (r : ExtRat) : X :=
    let filtered := univ.filter (fun x => decide (embed.embed x ≤ r))
    let min := filtered.maxOn
     (fun x => embed.embed x)
     (fun a b => a ≤ b) smallest
    min

  def roundableUpperByEnumeration
    (embed : RoundableEmbed X)
    (univ : List X) (largest : X) : RoundableUpper X where
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
  lower := (roundableLowerByEnumeration embed smallest univ).lower
  upper := (roundableUpperByEnumeration embed univ largest).upper


namespace SlowComputableRound

def roundBySlowEnumeration (e s : Nat) : RoundMethod (PackedFloat e s) where
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
    smallest := PackedFloat.getInfinity e s true
    largest := PackedFloat.getInfinity e s false
    lower := roundableLowerByEnumeration roundableEmbedPackedFloat smallest (PackedFloat.enumerate e s)
    upper := roundableUpperByEnumeration roundableEmbedPackedFloat (PackedFloat.enumerate e s) largest
end SlowComputableRound

namespace SmtLibRoundMethod

/--
The default SMT-Lib adjunction of packed floats into rationals, written `v_ε,σ(f)`,
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
The SMT-Lib definition of the rounding methods for any choice of rounding adjunction 'v'.
The lower and upper half are defined according to 'v'.
-/
def smtLibRoundMethod (e s : Nat) (v : RoundableAdjunction (PackedFloat e s)) :
  RoundMethod (PackedFloat e s) where
  embed := v.embed
  lower := v.lower
  upper := v.upper
  lowerHalf r := v.embed (v.lower r) = ves.embed (ves.lower r)
  tieBreak r :=
    (v.embed (v.lower r) < ves.embed (ves.lower r)) =
    (ves.embed (ves.upper r) = (ves.embed (ves.upper r)))
  isEven := roundableIsEven_of_packedFloat.isEven
  where
    ves : RoundableAdjunction (PackedFloat e (s + 1)) := smtLibV e (s + 1)

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
def compareRoundingFunctions
  (E S : Nat) (e s : Nat) (rm : RoundingMode)
  (rounderGolden rounderUnderTest : RoundingMode → (sign  : Bool) → PackedFloat E S → PackedFloat e s)
  : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r := pf.toExtRat
    let sign := pf.sign
    let golden := rounderGolden rm sign pf
    let test : PackedFloat e s := rounderUnderTest rm sign pf
    let res := golden = test
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}), RoundingMode: {repr rm}, sign: {sign}"
      IO.println s!"  Golden result:       {repr golden}  | ExtRat: {repr golden.toExtRat} | UnpackedFloat : {repr golden.unpack}"
      IO.println s!"  Tested result: {repr test} | ExtRat: {repr test.toExtRat} | UnpackedFloat : {repr test}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

/--
info: Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x33#6 } (ExtRat: ExtRat.Number 230), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number 232 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0xc#4 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number 214), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number 216 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0xa#4 } | ExtRat: ExtRat.Number 208 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x23#6 } (ExtRat: ExtRat.Number 198), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number 200 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 192 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number 182), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number 184 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0x6#4 } | ExtRat: ExtRat.Number 176 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x13#6 } (ExtRat: ExtRat.Number 166), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number 168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0x4#4 } | ExtRat: ExtRat.Number 160 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number 150), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number 152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0x2#4 } | ExtRat: ExtRat.Number 144 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0xe#4, sig := 0x03#6 } (ExtRat: ExtRat.Number 134), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number 136 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0xe#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 128 | UnpackedFloat : { sign := +, ex := 0xe#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number 126), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 120 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number 125), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xe#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 120 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x33#6 } (ExtRat: ExtRat.Number 115), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number 116 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0xc#4 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number 107), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number 108 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0xa#4 } | ExtRat: ExtRat.Number 104 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x23#6 } (ExtRat: ExtRat.Number 99), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number 100 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 96 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number 91), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number 92 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0x6#4 } | ExtRat: ExtRat.Number 88 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x13#6 } (ExtRat: ExtRat.Number 83), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number 84 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0x4#4 } | ExtRat: ExtRat.Number 80 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number 75), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number 76 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0x2#4 } | ExtRat: ExtRat.Number 72 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0xd#4, sig := 0x03#6 } (ExtRat: ExtRat.Number 67), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number 68 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0xd#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 64 | UnpackedFloat : { sign := +, ex := 0xd#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number 63), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 60 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xd#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 60 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number 58 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0xc#4 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number 54 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0xa#4 } | ExtRat: ExtRat.Number 52 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number 50 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 48 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number 46 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0x6#4 } | ExtRat: ExtRat.Number 44 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number 42 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0x4#4 } | ExtRat: ExtRat.Number 40 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number 38 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0x2#4 } | ExtRat: ExtRat.Number 36 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0xc#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number 34 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0xc#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 32 | UnpackedFloat : { sign := +, ex := 0xc#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 30 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xc#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 30 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number 29 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0xc#4 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number 27 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0xa#4 } | ExtRat: ExtRat.Number 26 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number 25 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 24 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number 23 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0x6#4 } | ExtRat: ExtRat.Number 22 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number 21 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0x4#4 } | ExtRat: ExtRat.Number 20 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number 19 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0x2#4 } | ExtRat: ExtRat.Number 18 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0xb#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number 17 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0xb#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 16 | UnpackedFloat : { sign := +, ex := 0xb#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 15 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xb#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0xe#4 } | ExtRat: ExtRat.Number 15 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0xc#4 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0xa#4 } | ExtRat: ExtRat.Number 13 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 12 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0x6#4 } | ExtRat: ExtRat.Number 11 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0x4#4 } | ExtRat: ExtRat.Number 10 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0x2#4 } | ExtRat: ExtRat.Number 9 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0xa#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0xa#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 8 | UnpackedFloat : { sign := +, ex := 0xa#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0xa#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0xc#4 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 6 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0x4#4 } | ExtRat: ExtRat.Number 5 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x9#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x9#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 4 | UnpackedFloat : { sign := +, ex := 0x9#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x9#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0x8#4 } | ExtRat: ExtRat.Number 3 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x8#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x8#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 2 | UnpackedFloat : { sign := +, ex := 0x8#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x8#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x7#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x7#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 1 | UnpackedFloat : { sign := +, ex := 0x7#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x7#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x6#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x6#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { sign := +, ex := 0x6#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x6#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x5#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x5#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { sign := +, ex := 0x5#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x5#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x4#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x4#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { sign := +, ex := 0x4#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x4#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x3#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x3#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { sign := +, ex := 0x3#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x3#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x2#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x2#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { sign := +, ex := 0x2#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (63 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (125 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x2#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (15 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (115 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (29 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x1d#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (107 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (27 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x1b#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (13 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (99 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (25 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x19#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (3 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (91 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (23 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x17#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (11 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (83 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (21 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x15#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (5 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (75 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (19 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x13#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (9 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x1#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (67 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (17 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x11#5 } }
  Tested result: { sign := +, ex := 0x1#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { sign := +, ex := 0x1#4, sig := 0x0#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number (31 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number (61 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1#4, sig := 0x0#4 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0xe#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x33#6 } (ExtRat: ExtRat.Number (51 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (13 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x19#5, sig := 0x1a#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (3 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0xc#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x2b#6 } (ExtRat: ExtRat.Number (43 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (11 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x19#5, sig := 0x16#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (5 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0xa#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x23#6 } (ExtRat: ExtRat.Number (35 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (9 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x19#5, sig := 0x12#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0x8#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x1b#6 } (ExtRat: ExtRat.Number (27 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x18#5, sig := 0x1c#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (3 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0x6#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x13#6 } (ExtRat: ExtRat.Number (19 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x18#5, sig := 0x14#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0x4#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x0b#6 } (ExtRat: ExtRat.Number (11 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x17#5, sig := 0x18#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0x2#4 }
Discrepancy found for { sign := +, ex := 0x0#4, sig := 0x03#6 } (ExtRat: ExtRat.Number (3 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x16#5, sig := 0x10#5 } }
  Tested result: { sign := +, ex := 0x0#4, sig := 0x0#4 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { sign := +, ex := 0x0#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x3e#6 } (ExtRat: ExtRat.Number -252), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xf#4, sig := 0x0#4 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { sign := -, ex := 0xf#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x3d#6 } (ExtRat: ExtRat.Number -250), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xf#4, sig := 0x0#4 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { sign := -, ex := 0xf#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x3c#6 } (ExtRat: ExtRat.Number -248), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xf#4, sig := 0x0#4 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { sign := -, ex := 0xf#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number -246), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xf#4, sig := 0x0#4 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { sign := -, ex := 0xf#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number -244), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xf#4, sig := 0x0#4 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { sign := -, ex := 0xf#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x39#6 } (ExtRat: ExtRat.Number -242), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xf#4, sig := 0x0#4 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { sign := -, ex := 0xf#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x35#6 } (ExtRat: ExtRat.Number -234), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number -232 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0xe#4 } | ExtRat: ExtRat.Number -240 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number -218), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number -216 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0xc#4 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x25#6 } (ExtRat: ExtRat.Number -202), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number -200 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0xa#4 } | ExtRat: ExtRat.Number -208 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number -186), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number -184 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -192 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x15#6 } (ExtRat: ExtRat.Number -170), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number -168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x6#4 } | ExtRat: ExtRat.Number -176 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number -154), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number -152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x4#4 } | ExtRat: ExtRat.Number -160 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0xe#4, sig := 0x05#6 } (ExtRat: ExtRat.Number -138), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xe#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number -136 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x2#4 } | ExtRat: ExtRat.Number -144 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number -123), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -120 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -128 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number -122), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -120 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -128 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x39#6 } (ExtRat: ExtRat.Number -121), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -120 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xe#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -128 | UnpackedFloat : { sign := -, ex := 0xe#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x35#6 } (ExtRat: ExtRat.Number -117), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number -116 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0xe#4 } | ExtRat: ExtRat.Number -120 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number -109), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number -108 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0xc#4 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x25#6 } (ExtRat: ExtRat.Number -101), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number -100 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0xa#4 } | ExtRat: ExtRat.Number -104 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number -93), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number -92 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -96 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x15#6 } (ExtRat: ExtRat.Number -85), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number -84 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x6#4 } | ExtRat: ExtRat.Number -88 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number -77), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number -76 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x4#4 } | ExtRat: ExtRat.Number -80 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0xd#4, sig := 0x05#6 } (ExtRat: ExtRat.Number -69), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xd#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number -68 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x2#4 } | ExtRat: ExtRat.Number -72 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -60 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -64 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number -61), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -60 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -64 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -60 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xd#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -64 | UnpackedFloat : { sign := -, ex := 0xd#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number -58 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0xe#4 } | ExtRat: ExtRat.Number -60 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number -54 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0xc#4 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number -50 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0xa#4 } | ExtRat: ExtRat.Number -52 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number -46 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -48 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number -42 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x6#4 } | ExtRat: ExtRat.Number -44 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number -38 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x4#4 } | ExtRat: ExtRat.Number -40 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0xc#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xc#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number -34 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x2#4 } | ExtRat: ExtRat.Number -36 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -30 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -32 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -30 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -32 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -30 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xc#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -32 | UnpackedFloat : { sign := -, ex := 0xc#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number -29 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0xe#4 } | ExtRat: ExtRat.Number -30 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number -27 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0xc#4 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number -25 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0xa#4 } | ExtRat: ExtRat.Number -26 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number -23 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -24 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number -21 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x6#4 } | ExtRat: ExtRat.Number -22 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number -19 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x4#4 } | ExtRat: ExtRat.Number -20 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0xb#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xb#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number -17 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x2#4 } | ExtRat: ExtRat.Number -18 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -15 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -16 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -15 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -16 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number -15 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xb#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -16 | UnpackedFloat : { sign := -, ex := 0xb#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0xe#4 } | ExtRat: ExtRat.Number -15 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0xc#4 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0xa#4 } | ExtRat: ExtRat.Number -13 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -12 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x6#4 } | ExtRat: ExtRat.Number -11 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x4#4 } | ExtRat: ExtRat.Number -10 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0xa#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0xa#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x2#4 } | ExtRat: ExtRat.Number -9 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -8 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -8 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0xa#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -8 | UnpackedFloat : { sign := -, ex := 0xa#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0xc#4 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -6 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x4#4 } | ExtRat: ExtRat.Number -5 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x9#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x9#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -4 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -4 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x9#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -4 | UnpackedFloat : { sign := -, ex := 0x9#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x8#4 } | ExtRat: ExtRat.Number -3 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x8#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x8#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -2 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -2 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x8#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -2 | UnpackedFloat : { sign := -, ex := 0x8#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x7#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x7#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -1 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -1 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x7#4, sig := 0x0#4 } | ExtRat: ExtRat.Number -1 | UnpackedFloat : { sign := -, ex := 0x7#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x6#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x6#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x6#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { sign := -, ex := 0x6#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x5#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x5#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x5#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { sign := -, ex := 0x5#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x4#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x4#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x4#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { sign := -, ex := 0x4#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x3#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x3#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x3#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { sign := -, ex := 0x3#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x2#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x2#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-123 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-61 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-121 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-15 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x1e#5 } }
  Tested result: { sign := -, ex := 0x2#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { sign := -, ex := 0x2#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-117 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-29 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x1d#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-15 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-109 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-27 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x1b#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-101 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-25 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x19#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-13 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-93 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-23 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x17#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-3 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-85 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-21 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x15#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-11 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-77 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-19 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x13#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-5 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x1#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-69 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-17 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x11#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-9 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x2#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x3b#6 } (ExtRat: ExtRat.Number (-59 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x19#5, sig := 0x1c#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x3a#6 } (ExtRat: ExtRat.Number (-29 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x19#5, sig := 0x1c#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x39#6 } (ExtRat: ExtRat.Number (-57 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0xe#4 }  | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x19#5, sig := 0x1c#5 } }
  Tested result: { sign := -, ex := 0x1#4, sig := 0x0#4 } | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { sign := -, ex := 0x1#4, sig := 0x0#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x35#6 } (ExtRat: ExtRat.Number (-53 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0xd#4 }  | ExtRat: ExtRat.Number (-13 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x19#5, sig := 0x1a#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0xe#4 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0xe#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x2d#6 } (ExtRat: ExtRat.Number (-45 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0xb#4 }  | ExtRat: ExtRat.Number (-11 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x19#5, sig := 0x16#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0xc#4 } | ExtRat: ExtRat.Number (-3 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0xc#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x25#6 } (ExtRat: ExtRat.Number (-37 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0x9#4 }  | ExtRat: ExtRat.Number (-9 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x19#5, sig := 0x12#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0xa#4 } | ExtRat: ExtRat.Number (-5 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0xa#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x1d#6 } (ExtRat: ExtRat.Number (-29 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0x7#4 }  | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x18#5, sig := 0x1c#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0x8#4 } | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0x8#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x15#6 } (ExtRat: ExtRat.Number (-21 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0x5#4 }  | ExtRat: ExtRat.Number (-5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x18#5, sig := 0x14#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0x6#4 } | ExtRat: ExtRat.Number (-3 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0x6#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x0d#6 } (ExtRat: ExtRat.Number (-13 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0x3#4 }  | ExtRat: ExtRat.Number (-3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x17#5, sig := 0x18#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0x4#4 } | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0x4#4 }
Discrepancy found for { sign := -, ex := 0x0#4, sig := 0x05#6 } (ExtRat: ExtRat.Number (-5 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0#4, sig := 0x1#4 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x16#5, sig := 0x10#5 } }
  Tested result: { sign := -, ex := 0x0#4, sig := 0x2#4 } | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { sign := -, ex := 0x0#4, sig := 0x2#4 }
Total tests run: 1890, Successes: 1604, Failures: 286 (84.867725% success rate)
---
info: false
-/
#guard_msgs in #eval compareRoundingFunctions 4 6 4 4 .RNE
  (rounderGolden := fun rm sign pf => (SlowComputableRound.roundBySlowEnumeration 4 4).roundAux rm sign pf.toExtRat)
  (rounderUnderTest := fun rm sign pf =>
      let v := (RoundableAdjunction.ofEmbedByEnumeration (X := PackedFloat _ _)
          (roundableEmbedPackedFloat)
          (PackedFloat.getInfinity _ _ true )
          (PackedFloat.enumerate _ _)
          (PackedFloat.getInfinity _ _ false))
      (SmtLibRoundMethod.smtLibRoundMethod _ _ v).roundAux rm sign pf.toExtRat)

/-
#guard_msgs in #eval runRoundAgreesWithUnpackedFloatRound 5 4 5 2 .RNE
    (SmtLibRoundMethod.smtLibRoundMethod _ _
      (RoundableAdjunction.ofEmbedByEnumeration (X := PackedFloat 5 2) (roundableEmbedPackedFloat)
      (PackedFloat.getInfinity _ _ true ) (PackedFloat.enumerate _ _) (PackedFloat.getInfinity _ _ false)))
-/


end ExhaustiveEnumerationTesting
