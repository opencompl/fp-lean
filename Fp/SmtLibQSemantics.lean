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

/--
info: Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xe#4 } (ExtRat: ExtRat.Number 61440), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1f#5, sig := 0x0#2 } | ExtRat: ExtRat.Infinity false | UnpackedFloat : { state := ∞, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 59392), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 57344 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 57344), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 57344 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 55296), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 57344 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 29696), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28672 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 28672), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 24576 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28672 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 27648), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 24576 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28672 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 14848), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14336 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 14336), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 12288 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14336 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 13824), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 12288 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14336 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 7424), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 7168), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 6144 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 6912), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 6144 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 3712), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 3584 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 3584), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 3072 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 3584 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 3456), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 3072 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 3584 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 1856), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 1792 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 1792), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 1536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 1792 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 1728), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 1536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 1792 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 928), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 896 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 896), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 896 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 864), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 896 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 464), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 448 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 448), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 448 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 432), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 448 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 232), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 224), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 216), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 116), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 112), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 96 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 108), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 96 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 58), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 56), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 48 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 54), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 48 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 29), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 28), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 24 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 27), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 24 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 14), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 12 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 12 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 7), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 6 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 6 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 3 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 3 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (13 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (3 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (11 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xe#4 } (ExtRat: ExtRat.Number -61440), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1f#5, sig := 0x0#2 } | ExtRat: ExtRat.Infinity true | UnpackedFloat : { state := ∞, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -59392), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -57344 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -57344), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -57344 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -55296), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -57344 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -29696), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28672 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -28672), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28672 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -27648), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -24576 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28672 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -14848), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14336 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -14336), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14336 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -13824), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -12288 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14336 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -7424), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -7168), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -6912), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -6144 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -3712), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -3584 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -3584), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -3584 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -3456), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -3072 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -3584 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -1856), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -1792 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -1792), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -1792 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -1728), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -1536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -1792 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -928), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -896 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -896), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -896 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -864), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -896 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -464), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -448 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -448), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -448 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -432), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -448 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -232), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -224), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -216), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -116), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -112), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -108), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -96 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -58), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -56), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -54), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -48 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -29), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -28), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -27), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -24 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -14), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -12 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -7), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -6 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -3 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-13 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-3 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-11 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x00#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x2#4 } (ExtRat: ExtRat.Number (-1 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x0#2 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x1#4 } (ExtRat: ExtRat.Number (-1 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x0#2 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x0#4 } (ExtRat: ExtRat.Number 0), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x0#2 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Total tests run: 930, Successes: 739, Failures: 191 (79.462366% success rate)
---
info: false
-/
#guard_msgs in #eval runRoundAgreesWithUnpackedFloatRound 5 4 5 2 .RNE (SlowEnumerationRoundMethod.roundBySlowEnumeration)



/--
info: Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 59392), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity false | UnpackedFloat : { state := ∞, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 57344 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 57344), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity false | UnpackedFloat : { state := ∞, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 57344 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 55296), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity false | UnpackedFloat : { state := ∞, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 57344 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 53248), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity false | UnpackedFloat : { state := ∞, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 51200), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity false | UnpackedFloat : { state := ∞, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 43008), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 49152 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 40960 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1e#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 38912), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 40960 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 29696), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28672 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 28672), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28672 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 27648), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28672 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 26624), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 24576 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 25600), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 24576 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 21504), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 24576 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 20480 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1d#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 19456), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1d#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 20480 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 14848), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14336 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 14336), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14336 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 13824), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14336 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 13312), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 12288 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 12800), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 12288 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 10752), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 12288 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 10240 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1c#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 9728), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1c#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 10240 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 7424), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 7168), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 6912), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7168 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 6656), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 6144 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 6400), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 6144 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 5376), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 6144 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 5120 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1b#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 4864), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1b#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 5120 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 3712), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 3584 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 3584), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 3584 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 3456), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 3584 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 3328), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 3072 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 3200), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 3072 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 2688), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 3072 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 2560 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x1a#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 2432), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x1a#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 2560 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 1856), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 1792 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 1792), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 1792 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 1728), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 1792 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 1664), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 1536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 1600), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 1536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 1344), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 1536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 1280 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x19#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 1216), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x19#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 1280 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 928), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 896 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 896), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 896 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 864), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 896 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 832), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 800), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 672), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 640 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x18#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 608), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x18#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 640 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 464), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 448 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 448), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 448 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 432), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 448 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 416), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 400), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 336), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 320 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x17#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 304), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x17#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 320 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 232), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 224), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 216), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 224 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 208), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 200), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 168), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 160 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x16#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 152), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x16#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 160 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 116), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 112), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 108), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 112 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 104), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 96 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 100), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 96 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 84), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 96 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 80 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x15#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 76), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x15#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 80 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 58), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 56), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 54), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 56 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 52), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 48 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 50), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 48 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 42), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 48 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 40 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x14#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 38), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x14#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 40 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xd#4 } (ExtRat: ExtRat.Number 29), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 28), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xb#4 } (ExtRat: ExtRat.Number 27), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 28 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 26), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 24 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0x9#4 } (ExtRat: ExtRat.Number 25), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 24 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0x5#4 } (ExtRat: ExtRat.Number 21), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 24 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 20 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x13#5, sig := 0x3#4 } (ExtRat: ExtRat.Number 19), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x13#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 20 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 14), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 14 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0xa#4 } (ExtRat: ExtRat.Number 13), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 12 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 12 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 12 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 10 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x12#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x12#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 10 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xc#4 } (ExtRat: ExtRat.Number 7), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number 7 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 6 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 6 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 6 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 5 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x11#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x11#5, sig := 0x1#2 } | ExtRat: ExtRat.Number 5 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/2), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 3 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x2#2 } | ExtRat: ExtRat.Number 3 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number 3 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x10#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x10#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/4), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0f#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0f#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/8), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 1 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0e#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/16), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0d#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0d#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/32), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0c#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0c#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/64), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0b#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0b#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/128), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x0a#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x0a#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/256), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x09#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x09#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/512), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x08#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x08#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/1024), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x07#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x07#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/2048), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x06#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x06#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/4096), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x05#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x05#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/8192), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x04#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x04#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/16384), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x03#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x03#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/32768), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x02#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x02#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (29 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (7 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (27 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (13 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (25 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (21 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x01#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (19 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x01#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (5 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x5#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (13 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (3 : Rat)/65536), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (11 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (5 : Rat)/131072), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x4#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (9 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x4#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0x5#4 } (ExtRat: ExtRat.Number (5 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number (1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x31#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (1 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x30#6, sig := 0x4#3 } }
Discrepancy found for { sign := +, ex := 0x00#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (3 : Rat)/262144), RoundingMode: RNE, sign: false
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := +, ex := 0x00#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (1 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x30#6, sig := 0x4#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -59392), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity true | UnpackedFloat : { state := ∞, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -57344 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -57344), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity true | UnpackedFloat : { state := ∞, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -57344 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -55296), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity true | UnpackedFloat : { state := ∞, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -57344 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -53248), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity true | UnpackedFloat : { state := ∞, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -51200), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Infinity true | UnpackedFloat : { state := ∞, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0x5#4 } (ExtRat: ExtRat.Number -43008), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x2#2 }  | ExtRat: ExtRat.Number -49152 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x6#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -40960 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x1e#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -38912), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -40960 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -29696), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28672 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -28672), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28672 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -27648), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28672 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -26624), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24576 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -25600), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24576 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -23552), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -20480 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24576 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -22528), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -20480 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24576 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1d#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -19456), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1d#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -20480 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -14848), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14336 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -14336), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14336 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -13824), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14336 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -13312), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12288 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -12800), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12288 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -11776), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -10240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12288 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -11264), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -10240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12288 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1c#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -9728), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1c#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -10240 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -7424), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -7168), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -6912), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7168 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -6656), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6144 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -6400), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6144 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -5888), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -5120 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6144 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -5632), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -5120 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6144 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1b#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -4864), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1b#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -5120 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -3712), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -3584 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -3584), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -3584 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -3456), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -3584 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -3328), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3072 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -3200), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3072 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -2944), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -2560 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3072 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -2816), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -2560 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3072 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x1a#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -2432), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x1a#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -2560 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -1856), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -1792 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -1792), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -1792 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -1728), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -1792 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -1664), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -1536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -1600), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x1a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -1536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -1472), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -1280 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -1536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -1408), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -1280 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -1536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x19#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -1216), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x19#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -1280 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -928), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -896 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -896), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -896 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -864), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -896 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -832), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -800), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x19#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x0a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -736), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -640 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -704), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -640 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x18#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -608), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x18#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -640 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -464), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -448 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -448), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -448 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -432), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -448 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -416), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -400), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x18#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x09#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -368), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -320 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -352), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -320 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x17#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -304), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x17#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -320 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -232), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -224), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -216), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -224 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -208), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -200), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x17#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x08#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -184), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -160 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -176), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -160 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x16#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -152), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x16#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -160 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -116), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -112), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -108), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -112 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -104), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -96 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -100), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x16#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x07#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -96 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -92), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -80 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -96 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -88), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -80 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -96 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x15#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -76), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x15#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -80 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -58), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -56), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -54), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -56 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -52), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -48 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -50), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x15#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x06#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -48 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -46), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -40 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -48 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -44), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -40 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -48 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x14#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -38), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x14#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -40 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xd#4 } (ExtRat: ExtRat.Number -29), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -28), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xb#4 } (ExtRat: ExtRat.Number -27), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -28 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -26), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0x9#4 } (ExtRat: ExtRat.Number -25), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x14#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x05#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0x7#4 } (ExtRat: ExtRat.Number -23), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -20 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -22), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -20 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -24 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x13#5, sig := 0x3#4 } (ExtRat: ExtRat.Number -19), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x13#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -20 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -14), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -14 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0xa#4 } (ExtRat: ExtRat.Number -13), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x13#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x04#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -10 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0x6#4 } (ExtRat: ExtRat.Number -11), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -10 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -12 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x12#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x12#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -10 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xc#4 } (ExtRat: ExtRat.Number -7), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x3#2 } | ExtRat: ExtRat.Number -7 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x12#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x03#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -5 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number -5 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -6 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x11#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x11#5, sig := 0x1#2 } | ExtRat: ExtRat.Number -5 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/2), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x11#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x02#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x2#2 } | ExtRat: ExtRat.Number -3 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x10#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x10#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/4), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x10#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x01#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0f#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0f#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/8), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0f#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number -1 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0e#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0e#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/16), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0e#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3f#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0d#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0d#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/32), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0d#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3e#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0c#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0c#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/64), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0c#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3d#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0b#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0b#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/128), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0b#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3c#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x0a#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x0a#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/256), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x0a#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/32 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3b#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x09#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x09#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/512), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x09#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/64 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x3a#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x08#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x08#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/1024), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x08#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/128 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x39#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x07#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x07#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/2048), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x07#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/256 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x38#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x06#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x06#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/4096), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x06#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/512 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x37#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x05#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x05#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/8192), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x05#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/1024 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x36#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x04#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x04#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/16384), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x04#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/2048 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x35#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x03#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x03#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/32768), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x03#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/4096 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x34#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x02#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x02#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-29 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-7 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-27 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-7 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x7#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-13 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-25 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x02#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/8192 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x33#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-23 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-11 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-5 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x5#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-3 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x01#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-19 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x01#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-5 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x5#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xd#4 } (ExtRat: ExtRat.Number (-13 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xc#4 } (ExtRat: ExtRat.Number (-3 : Rat)/65536), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xb#4 } (ExtRat: ExtRat.Number (-11 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x3#2 } | ExtRat: ExtRat.Number (-3 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x6#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0xa#4 } (ExtRat: ExtRat.Number (-5 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x4#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x9#4 } (ExtRat: ExtRat.Number (-9 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x01#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/16384 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x32#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x4#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x7#4 } (ExtRat: ExtRat.Number (-7 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x00#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x30#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x4#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x6#4 } (ExtRat: ExtRat.Number (-3 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := -, ex := 0x00#5, sig := 0x1#2 }  | ExtRat: ExtRat.Number (-1 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x30#6, sig := 0x4#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x2#2 } | ExtRat: ExtRat.Number (-1 : Rat)/32768 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x31#6, sig := 0x4#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x3#4 } (ExtRat: ExtRat.Number (-3 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x1#2 } | ExtRat: ExtRat.Number (-1 : Rat)/65536 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x30#6, sig := 0x4#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x2#4 } (ExtRat: ExtRat.Number (-1 : Rat)/131072), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x0#2 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x1#4 } (ExtRat: ExtRat.Number (-1 : Rat)/262144), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x0#2 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Discrepancy found for { sign := -, ex := 0x00#5, sig := 0x0#4 } (ExtRat: ExtRat.Number 0), RoundingMode: RNE, sign: true
  Golden result:       { sign := +, ex := 0x00#5, sig := 0x0#2 }  | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := false, ex := 0x00#6, sig := 0x0#3 } }
  UnpackedFloat result: { sign := -, ex := 0x00#5, sig := 0x0#2 } | ExtRat: ExtRat.Number 0 | UnpackedFloat : { state := num, num := { sign := true, ex := 0x00#6, sig := 0x0#3 } }
Total tests run: 930, Successes: 463, Failures: 467 (49.784946% success rate)
---
info: false
-/
#guard_msgs in #eval runRoundAgreesWithUnpackedFloatRound 5 4 5 2 .RNE
    (SmtLibRoundMethod.smtLibRoundMethod _ _
      (RoundableAdjunction.ofEmbedByEnumeration (X := PackedFloat 5 2) (roundableEmbedPackedFloat)
      (PackedFloat.getInfinity _ _ true ) (PackedFloat.enumerate _ _) (PackedFloat.getInfinity _ _ false)))

end ExhaustiveEnumerationTesting
