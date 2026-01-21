import Fp.Basic
import Fp.Rounding
import Lean
open Lean


-- https://smt-lib.org/papers/BTRW15.pdf

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
      if r < min.toExtRat.number then negInf
      else if r ≥ max.toExtRat.number then max
      else
         let dyadic : Dyadic := r.toDyadic (minSubnormalExp e s + 2)
         let roundDown : Dyadic := dyadic.roundDown ((minSubnormalExp e s))
         let unpacked : UnpackedFloat (exponentWidth e s) (s + 1) :=  {
            sign := dyadic.numerator < 0,
            ex := - (roundDown.precision.getD 0),
            sig := dyadic.numerator
         }
         let eunpacked : EUnpackedFloat (exponentWidth e s) (s + 1) :=
            unpacked.toEUnpackedFloat
         eunpacked.pack


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
