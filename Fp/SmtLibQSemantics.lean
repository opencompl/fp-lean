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

structure RoundableLowerHalf (X : Type) where
  lowerHalf : ExtRat → Bool

structure RoundableTieBreak (X : Type) where
  tieBreak : ExtRat → Bool

structure RoundableUpperHalf (X : Type) where
  upperHalf : ExtRat → Bool

structure RoundableIsEven (X : Type) where
  isEven : X → Bool

structure RoundableIsZero (X : Type) where
  isZero : X → Bool


structure RoundMethod (X : Type) extends
  RoundableEmbed X,
  RoundableLower X,
  RoundableUpper X,
  RoundableLowerHalf X,
  RoundableTieBreak X,
  RoundableUpperHalf X,
  RoundableIsEven X,
  RoundableIsZero X where

def RoundMethod.rounderForSign {X : Type} (roundMethod : RoundMethod X) (sign : Bool) (r : ExtRat) : X :=
  if sign then roundMethod.upper r else roundMethod.lower r

def RoundMethod.roundSmtLib (e s : Nat) (roundMethod : RoundMethod (PackedFloat e s))
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
namespace QSemanticsRef

/-
We define the semantics of floating-point operations following the SMT-LIB
style of semantics here. In particular, close attention is paid to being
as close to the SMT-LIB definitions as possible.
-/

/-- The lower approximant of 'v'. Returns the largest 'x : X' such that 'v x ≤ r'. -/
def lower (e s : Nat) (r : ExtRat) : PackedFloat e s :=
  let us : List (PackedFloat e s) := PackedFloat.enumerate e s
  let filtered := us.filter (fun x => decide (x.toExtRat ≤ r))
  let min := filtered.maxOn
   (fun x => x.toExtRat)
   (fun a b => a ≤ b) (.getInfinity e s true)
  min

/-- The upper approximant of 'v'.
Returns the smallest 'x : X' such that 'r ≤ v x'. -/
def upper (e s : Nat) (r : ExtRat) : PackedFloat e s :=
   let us : List (PackedFloat e s) := PackedFloat.enumerate e s
   let filtered := us.filter (fun x => decide (r ≤ x.toExtRat))
   let max := filtered.minOn
    (fun x => x.toExtRat)
    (fun a b => a ≤ b) (.getInfinity e s false)
   max


/-- Lower half, return 'true' iff we are strictly in the lower half. -/
def lh (e s : Nat) (r : ExtRat)  : Bool :=
   (r - (lower e s r).toExtRat) < (upper e s r).toExtRat - r

/-- Tiebreak, return 'true' iff we are exactly in the middle of the lower and upper approximants. -/
def tb (e s : Nat) (r : ExtRat) : Bool :=
   r - (lower e s r).toExtRat = (upper e s r).toExtRat - r
/-- Upper half, return 'true' iff we are strictly in the upper half. -/
def uh (e s : Nat) (r : ExtRat) : Bool :=
   (r - (lower e s r).toExtRat) > (upper e s r).toExtRat - r

/-- Check if 'X' is even. -/
def ev (e s : Nat) (x : PackedFloat e s) : Bool :=
   match x.toExtRat with
   | .Number n =>
       let den := n.den
       let num := n.num
       num = 0 ∨ (den = 1 ∧ num.natAbs % 2 = 0)
   | _ => false

/-- Round signed zero. Picks between the lower and upper approximant,
based on the sign
function. -/
def rsz (e s : Nat) (sign : Bool) (r : ExtRat) : PackedFloat e s :=
  -- | TODO: should this be flipped?
  if sign then upper e s r else lower e s r


def roundSmtLib (e s : Nat)
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


namespace ExhaustiveEnumeration

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
def runRoundAgreesWithUnpackedFloatRound (E S : Nat) (e s : Nat) (rm : RoundingMode) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let sign := pf.sign
    let ref := QSemanticsRef.roundSmtLib e s rm sign r r
    let ufRounded := pf.unpack |> EUnpackedFloat.round e s rm
    let ufRoundedPacked := ufRounded.pack
    let res := ref = ufRoundedPacked
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}), RoundingMode: {repr rm}, sign: {sign}"
      IO.println s!"  Ref result:       {repr ref}  | ExtRat: {repr ref.toExtRat} | UnpackedFloat : {repr ref.unpack}"
      IO.println s!"  UnpackedFloat result: {repr ufRoundedPacked} | ExtRat: {repr ufRoundedPacked.toExtRat} | UnpackedFloat : {repr ufRounded}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0
end ExhaustiveEnumeration

end QSemanticsRef


namespace QSemanticsFast

/-
We define the semantics of floating-point operations following the SMT-LIB
style of semantics here. In particular, close attention is paid to being
as close to the SMT-LIB definitions as possible.
-/

/-- The lower approximant of 'v'. Returns the largest 'x : X' such that 'v x ≤ r'. -/
def lower (e s : Nat) (r : ExtRat) : PackedFloat e s :=
  let _posInf := PackedFloat.getInfinity e s false
  let negInf := PackedFloat.getInfinity e s true
  let max := PackedFloat.getMax e s false
  let min := PackedFloat.getMax e s true
  match r with
  | .NaN => PackedFloat.getNaN e s
  | .Infinity false => .getInfinity e s false
  | .Infinity true => .getInfinity e s true
  | .Number r =>
     -- | lower approximant.
      if r < min.toExtRat.number then negInf
      else if r ≥ max.toExtRat.number then max
      else
         let num := r.num
         let den := r.den
         let twoPow := Nat.log2 den
         let numPow := num.natAbs.nextPowerOfTwo
         let dyadic : Dyadic := r.toDyadic e
         let roundDown : Dyadic := dyadic.roundDown (e + s + 1)
         let unpacked : UnpackedFloat (exponentWidth e s) (s + 1) :=  {
            sign := dyadic.numerator < 0,
            ex := - (roundDown.precision.getD 0),
            sig := dyadic.numerator
         }
         let eunpacked : EUnpackedFloat (exponentWidth e s) (s + 1) :=
            unpacked.toEUnpackedFloat
         eunpacked.pack

def lowerIO (e s : Nat) (r : ExtRat) : IO (PackedFloat e s) := do
  let _posInf := PackedFloat.getInfinity e s false
  let negInf := PackedFloat.getInfinity e s true
  let max := PackedFloat.getMax e s false
  let min := PackedFloat.getMax e s true
  match r with
  | .NaN => return PackedFloat.getNaN e s
  | .Infinity false => return .getInfinity e s false
  | .Infinity true => return .getInfinity e s true
  | .Number r =>
     -- | lower approximant.
      if r < min.toExtRat.number then return negInf
      else if r ≥ max.toExtRat.number then return max
      else
         let num := r.num
         let den := r.den
         IO.println s!"  lower({r}): num = {num}, den = {den}"
         let denExp := Nat.log2 den -- we assume that denominator is always power of 2.
         IO.println s!"  lower({r}): denExp:{denExp} 2^denExp:{2 ^ denExp} den:{den}"
         let numeratorBits := num.natAbs.nextPowerOfTwo
         IO.println s!"  lower({r}): numeratorBits: {numeratorBits} | num:{num.natAbs}"
         let dyadic : Dyadic := r.toDyadic e
         let roundDown : Dyadic := dyadic.roundDown (e + s + 1)
         let unpacked : UnpackedFloat (exponentWidth e s) (s + 1) :=  {
            sign := dyadic.numerator < 0,
            ex := - (roundDown.precision.getD 0),
            sig := dyadic.numerator
         }
         let eunpacked : EUnpackedFloat (exponentWidth e s) (s + 1) :=
            unpacked.toEUnpackedFloat
         return eunpacked.pack


/-- The upper approximant of 'v'.
Returns the smallest 'x : X' such that 'r ≤ v x'. -/
def upper (e s : Nat) (r : ExtRat) : PackedFloat e s :=
   (lower e s r.neg).neg

/-- Lower half, return 'true' iff we are strictly in the lower half. -/
def lh (e s : Nat) (r : ExtRat)  : Bool :=
   (r - (lower e s r).toExtRat) < (upper e s r).toExtRat - r

/-- Tiebreak, return 'true' iff we are exactly in the middle of the lower and upper approximants. -/
def tb (e s : Nat) (r : ExtRat) : Bool :=
   r - (lower e s r).toExtRat = (upper e s r).toExtRat - r
/-- Upper half, return 'true' iff we are strictly in the upper half. -/
def uh (e s : Nat) (r : ExtRat) : Bool :=
   (r - (lower e s r).toExtRat) > (upper e s r).toExtRat - r

/-- Check if 'X' is even. -/
def ev (e s : Nat) (x : PackedFloat e s) : Bool :=
  match x.toExtRat with
  | .Number n =>
      let den := n.den
      let num := n.num
      num = 0 ∨ (den = 1 ∧ num.natAbs % 2 = 0)
  | _ => false

/-- Round signed zero. Picks between the lower and upper approximant,
based on the sign
function. -/
def rsz (e s : Nat) (sign : Bool) (r : ExtRat) : PackedFloat e s :=
  -- | TODO: should this be flipped?
  if sign then upper e s r else lower e s r

def roundSmtLib (e s : Nat)
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


namespace ExhaustiveEnumeration

def lowerAgreesWithRefTest (E S : Nat) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let fast ← QSemanticsFast.lowerIO E S r
    let ref := QSemanticsRef.lower E S r
    let res := fast = ref
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}) in lower approximant"
      IO.println s!"  Ref result:  {repr ref}  | ExtRat: {repr ref.toExtRat} | UnpackedFloat : {repr ref.unpack}"
      IO.println s!"  Fast result: {repr fast} | ExtRat: {repr fast.toExtRat} | UnpackedFloat : {repr fast.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

def upperAgreesWithRefTest (E S : Nat) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let fast := QSemanticsFast.upper E S r
    let ref := QSemanticsRef.upper E S r
    let res := fast = ref
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}) in upper approximant"
      IO.println s!"  Ref result:  {repr ref}  | ExtRat: {repr ref.toExtRat} | UnpackedFloat : {repr ref.unpack}"
      IO.println s!"  Fast result: {repr fast} | ExtRat: {repr fast.toExtRat} | UnpackedFloat : {repr fast.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

def runFastIdempotent (E S : Nat) (rm : RoundingMode) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let sign := pf.sign
    let fast := QSemanticsFast.roundSmtLib E S rm sign r r
    let res := fast.toExtRat = r
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Idempotency failure for {repr r} RoundingMode: {repr rm}, sign: {sign}"
      IO.println s!"  original (PF) {repr pf} | rounded(PF) {repr fast}"
      IO.println s!"  original (Q)  {repr r} | rounded(Q) {repr fast.toExtRat}"
      IO.println s!"  original (UF) {repr pf.unpack} | rounded(UF) {repr fast.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

def runSlowIdempotent (E S : Nat) (rm : RoundingMode) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let sign := pf.sign
    let ref := QSemanticsRef.roundSmtLib E S rm sign r r
    let res := ref.toExtRat = r
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Idempotency failure for {repr r} RoundingMode: {repr rm}, sign: {sign}"
      IO.println s!"  original (PF) {repr pf} | rounded(PF) {repr ref}"
      IO.println s!"  original (Q)  {repr r} | rounded(Q) {repr ref.toExtRat}"
      IO.println s!"  original (UF) {repr pf.unpack} | rounded(UF) {repr ref.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0

-- return true on success
def runFastAgreesWithRefTest (E S : Nat) (e s : Nat) (rm : RoundingMode) : IO Bool := do
  let pfs : List (PackedFloat E S) := PackedFloat.enumerate E S
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in pfs do
    let r : ExtRat := pf.toExtRat
    let sign := pf.sign
    let fast := QSemanticsFast.roundSmtLib e s rm sign r r
    let ref := QSemanticsRef.roundSmtLib e s rm sign r r
    let res := fast = ref
    if !res then
      nfailure := nfailure + 1
      IO.println s!"Discrepancy found for {repr pf} (ExtRat: {repr r}), RoundingMode: {repr rm}, sign: {sign}"
      IO.println s!"  Ref result:  {repr ref}  | ExtRat: {repr ref.toExtRat} | UnpackedFloat : {repr ref.unpack}"
      IO.println s!"  Fast result: {repr fast} | ExtRat: {repr fast.toExtRat} | UnpackedFloat : {repr fast.unpack}"
    else
      nsuccess := nsuccess + 1
  let percentSuccess : Float :=
    if nsuccess + nfailure == 0 then 100.0
    else (nsuccess.toFloat / (nsuccess + nfailure).toFloat) * 100.0
  IO.println s!"Total tests run: {nsuccess + nfailure}, Successes: {nsuccess}, Failures: {nfailure} ({percentSuccess}% success rate)"
  return nfailure == 0


end ExhaustiveEnumeration

end QSemanticsFast
