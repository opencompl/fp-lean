/-
Create a computable version of the rounding function on the rationals,
that is an intermediate between the hopelessly uncomputable SMT-LIB version
and the complicated circuit version for UnpackedFloat.
-/
import Fp.Basic
import Fp.UnpackedRound

namespace Fp


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

/-
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
-/

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


namespace RoundingQNaiveComputable

structure Float2Rat (E S : Nat) where mk_ ::
  sortedNumbers : Array (PackedFloat E S × Rat)


def Float2Rat.mk (E S : Nat) : Float2Rat E S where
  sortedNumbers := PackedFloat.enumerateSortedNumberRatArray E S

def Float2Rat.minimum (r : Float2Rat E S) : PackedFloat E S × Rat :=
  r.sortedNumbers[0]!

def Float2Rat.maximum (r : Float2Rat E S) : PackedFloat E S × Rat :=
  r.sortedNumbers[r.sortedNumbers.size - 1]!


/-- Return a packed float that is the closest under approximation to 'q'.
Returns 'none' if there is no such packed float (i.e., q is less than
the smallest representable packed float).
Uses linear search, starting from the largest element, and stopping
when we find a number less than or equal to 'q'.
-/
def Float2Rat.closestLower (r : Float2Rat E S) (q : Rat) : (PackedFloat E S × Rat) := Id.run do
  let arr := r.sortedNumbers
  let mut min : PackedFloat E S × Rat := arr[arr.size - 1]!
  for i in (List.range arr.size).reverse do
    let (pf, pfVal) := arr[i]!
    if pfVal <= q then
      min := (pf, pfVal)
      break
  min

/--
Return a packed float that is the closest over approximation to 'q'.
Returns 'none' if there is no such packed float (i.e., q is greater than
the largest representable packed float).
-/
def Float2Rat.closestHigher (r : Float2Rat E S) (q : Rat) : PackedFloat E S × Rat := Id.run do
  let arr := r.sortedNumbers
  let mut max : PackedFloat E S × Rat := arr[0]!
  for i in [0: arr.size] do
    let (pf, pfVal) := arr[i]!
    if pfVal >= q then
      max := (pf, pfVal)
      break
  return max


structure Rounder (E S : Nat) where
  f2r : Float2Rat E S := Float2Rat.mk E S
  f2r' : Float2Rat E (S + 1) := Float2Rat.mk E (S + 1)

def Rounder.rnePackedFloat (rounder : Rounder E S) (q : Rat) (sign : Bool) : IO (PackedFloat E S) := do
  let lo := rounder.f2r.closestLower q
  let hi := rounder.f2r.closestHigher q
  let lowest := rounder.f2r.minimum
  let highest := rounder.f2r.maximum
  let lo' := rounder.f2r'.closestLower q
  let hi' := rounder.f2r'.closestHigher q
  let lowest' := rounder.f2r'.minimum
  let highest' := rounder.f2r'.maximum

  IO.println s!"lo':{repr lo'.2} lo:{repr lo.2} q:{q} hi:{repr hi.2} hi':{repr hi'.2}"
  if q = 0 then
    return { PackedFloat.getZero E S with sign := sign }

  if lo.2 == hi.2 then return lo.1 -- we are perfectly representable.


  if q < lowest'.2 then
    -- lower than the lowest repr. number in the *larger* system with an extra significand bit
    return PackedFloat.getInfinity E S true
  else if lowest'.2 <= q && q <= lowest.2 then
    -- lower than the lowest repr. number in the original system
    return lowest.1
  else if highest.2 <= q && q < highest'.2 then
    -- higher than the highest repr. number in the original system
    return highest.1
  else if highest'.2 <= q then
    -- higher than the highest repr. number in the *larger* system with an extra significand bit
    return PackedFloat.getInfinity E S false

  -- we now know that lo.2 < q < hi.2
  let lo2q := q - lo.2
  let q2hi := hi.2 - q

  let inLowerHalf := lo2q < q2hi
  let atMid := lo2q == q2hi

  if inLowerHalf then
    return lo.1
  else if atMid then
    -- tie, use round to even
    let sigLo := lo.1.sig
    if sigLo % 2 == 0 then
      return lo.1
    else
      return hi.1
  else
    return hi.1


namespace ExhaustiveTesting

def testAgainstUnpackedFloatRounding (EIn SIn : Nat) (EOut SOut : Nat) : IO Bool := do
  let rounder : Rounder EOut SOut := {}
  let mut nsuccess : Nat := 0
  let mut nfailure : Nat := 0
  for pf in PackedFloat.enumerateSortedNumberRatArray EIn SIn do
    IO.println s!"---"
    let circuit := UnpackedFloat.debugRound
        (targetExponentWidth := EOut)
        (targetSignificandWidth := SOut)
        (pf.1.unpack.num) .RNE
    let circuitPf := EUnpackedFloat.pack (e := EOut) (s := SOut) circuit.1
    let golden ← rounder.rnePackedFloat pf.2 pf.1.sign
    if circuitPf == golden then
      nsuccess := nsuccess + 1
    else
      if nfailure < 200 then
        IO.println s!"Mismatch on input {repr pf.1.toExtRat} | {repr pf.1.unpack}"
        IO.println s!"  Circuit: {repr circuitPf.toExtRat} | {repr circuitPf.unpack}"
        IO.println s!"  Golden : {repr golden.toExtRat} | {repr golden.unpack}"
      nfailure := nfailure + 1

  let percentSucces := (nsuccess * 100) / (nsuccess + nfailure)
  IO.println s!"nsuccess = {nsuccess}, nfailure = {nfailure}, success% = {percentSucces}%"
  return nfailure == 0


/--
info: ---
lo':-1 lo:-1 q:-1 hi:-1 hi':-1
Mismatch on input ExtRat.Number (-1 : Rat)/2 | { state := num, num := { sign := true, ex := 0x3#2, sig := 0x2#2 } }
  Circuit: ExtRat.Number 0 | { state := num, num := { sign := true, ex := 0x0#2, sig := 0x0#2 } }
  Golden : ExtRat.Number (-1 : Rat)/2 | { state := num, num := { sign := true, ex := 0x3#2, sig := 0x2#2 } }
---
lo':0 lo:0 q:0 hi:0 hi':0
---
lo':0 lo:0 q:0 hi:0 hi':0
---
lo':1 lo:1 q:1 hi:1 hi':1
Mismatch on input ExtRat.Number (1 : Rat)/2 | { state := num, num := { sign := false, ex := 0x3#2, sig := 0x2#2 } }
  Circuit: ExtRat.Number 0 | { state := num, num := { sign := false, ex := 0x0#2, sig := 0x0#2 } }
  Golden : ExtRat.Number (1 : Rat)/2 | { state := num, num := { sign := false, ex := 0x3#2, sig := 0x2#2 } }
nsuccess = 2, nfailure = 2, success% = 50%
---
info: false
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 1 1 1 1


/--
info: ---
lo':240 lo:224 q:-252 hi:-224 hi':-240
---
lo':240 lo:224 q:-248 hi:-224 hi':-240
---
lo':240 lo:224 q:-244 hi:-224 hi':-240
---
lo':-240 lo:224 q:-240 hi:-224 hi':-240
Mismatch on input ExtRat.Number -240 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x3c#6 } }
  Circuit: ExtRat.Infinity true | { state := ∞, num := { sign := true, ex := 0x00#5, sig := 0x0#3 } }
  Golden : ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
---
lo':-240 lo:224 q:-236 hi:-224 hi':-224
---
lo':-240 lo:224 q:-232 hi:-224 hi':-224
---
lo':-240 lo:224 q:-228 hi:-224 hi':-224
---
lo':-224 lo:-224 q:-224 hi:-224 hi':-224
---
lo':-224 lo:-224 q:-220 hi:-192 hi':-208
---
lo':-224 lo:-224 q:-216 hi:-192 hi':-208
---
lo':-224 lo:-224 q:-212 hi:-192 hi':-208
---
lo':-208 lo:-224 q:-208 hi:-192 hi':-208
---
lo':-208 lo:-224 q:-204 hi:-192 hi':-192
---
lo':-208 lo:-224 q:-200 hi:-192 hi':-192
---
lo':-208 lo:-224 q:-196 hi:-192 hi':-192
---
lo':-192 lo:-192 q:-192 hi:-192 hi':-192
---
lo':-192 lo:-192 q:-188 hi:-160 hi':-176
---
lo':-192 lo:-192 q:-184 hi:-160 hi':-176
---
lo':-192 lo:-192 q:-180 hi:-160 hi':-176
---
lo':-176 lo:-192 q:-176 hi:-160 hi':-176
---
lo':-176 lo:-192 q:-172 hi:-160 hi':-160
---
lo':-176 lo:-192 q:-168 hi:-160 hi':-160
---
lo':-176 lo:-192 q:-164 hi:-160 hi':-160
---
lo':-160 lo:-160 q:-160 hi:-160 hi':-160
---
lo':-160 lo:-160 q:-156 hi:-128 hi':-144
---
lo':-160 lo:-160 q:-152 hi:-128 hi':-144
---
lo':-160 lo:-160 q:-148 hi:-128 hi':-144
---
lo':-144 lo:-160 q:-144 hi:-128 hi':-144
---
lo':-144 lo:-160 q:-140 hi:-128 hi':-128
---
lo':-144 lo:-160 q:-136 hi:-128 hi':-128
---
lo':-144 lo:-160 q:-132 hi:-128 hi':-128
---
lo':-128 lo:-128 q:-128 hi:-128 hi':-128
---
lo':-128 lo:-128 q:-126 hi:-112 hi':-120
---
lo':-128 lo:-128 q:-124 hi:-112 hi':-120
---
lo':-128 lo:-128 q:-122 hi:-112 hi':-120
---
lo':-120 lo:-128 q:-120 hi:-112 hi':-120
---
lo':-120 lo:-128 q:-118 hi:-112 hi':-112
---
lo':-120 lo:-128 q:-116 hi:-112 hi':-112
---
lo':-120 lo:-128 q:-114 hi:-112 hi':-112
---
lo':-112 lo:-112 q:-112 hi:-112 hi':-112
---
lo':-112 lo:-112 q:-110 hi:-96 hi':-104
---
lo':-112 lo:-112 q:-108 hi:-96 hi':-104
---
lo':-112 lo:-112 q:-106 hi:-96 hi':-104
---
lo':-104 lo:-112 q:-104 hi:-96 hi':-104
---
lo':-104 lo:-112 q:-102 hi:-96 hi':-96
---
lo':-104 lo:-112 q:-100 hi:-96 hi':-96
---
lo':-104 lo:-112 q:-98 hi:-96 hi':-96
---
lo':-96 lo:-96 q:-96 hi:-96 hi':-96
---
lo':-96 lo:-96 q:-94 hi:-80 hi':-88
---
lo':-96 lo:-96 q:-92 hi:-80 hi':-88
---
lo':-96 lo:-96 q:-90 hi:-80 hi':-88
---
lo':-88 lo:-96 q:-88 hi:-80 hi':-88
---
lo':-88 lo:-96 q:-86 hi:-80 hi':-80
---
lo':-88 lo:-96 q:-84 hi:-80 hi':-80
---
lo':-88 lo:-96 q:-82 hi:-80 hi':-80
---
lo':-80 lo:-80 q:-80 hi:-80 hi':-80
---
lo':-80 lo:-80 q:-78 hi:-64 hi':-72
---
lo':-80 lo:-80 q:-76 hi:-64 hi':-72
---
lo':-80 lo:-80 q:-74 hi:-64 hi':-72
---
lo':-72 lo:-80 q:-72 hi:-64 hi':-72
---
lo':-72 lo:-80 q:-70 hi:-64 hi':-64
---
lo':-72 lo:-80 q:-68 hi:-64 hi':-64
---
lo':-72 lo:-80 q:-66 hi:-64 hi':-64
---
lo':-64 lo:-64 q:-64 hi:-64 hi':-64
---
lo':-64 lo:-64 q:-63 hi:-56 hi':-60
---
lo':-64 lo:-64 q:-62 hi:-56 hi':-60
---
lo':-64 lo:-64 q:-61 hi:-56 hi':-60
---
lo':-60 lo:-64 q:-60 hi:-56 hi':-60
---
lo':-60 lo:-64 q:-59 hi:-56 hi':-56
---
lo':-60 lo:-64 q:-58 hi:-56 hi':-56
---
lo':-60 lo:-64 q:-57 hi:-56 hi':-56
---
lo':-56 lo:-56 q:-56 hi:-56 hi':-56
---
lo':-56 lo:-56 q:-55 hi:-48 hi':-52
---
lo':-56 lo:-56 q:-54 hi:-48 hi':-52
---
lo':-56 lo:-56 q:-53 hi:-48 hi':-52
---
lo':-52 lo:-56 q:-52 hi:-48 hi':-52
---
lo':-52 lo:-56 q:-51 hi:-48 hi':-48
---
lo':-52 lo:-56 q:-50 hi:-48 hi':-48
---
lo':-52 lo:-56 q:-49 hi:-48 hi':-48
---
lo':-48 lo:-48 q:-48 hi:-48 hi':-48
---
lo':-48 lo:-48 q:-47 hi:-40 hi':-44
---
lo':-48 lo:-48 q:-46 hi:-40 hi':-44
---
lo':-48 lo:-48 q:-45 hi:-40 hi':-44
---
lo':-44 lo:-48 q:-44 hi:-40 hi':-44
---
lo':-44 lo:-48 q:-43 hi:-40 hi':-40
---
lo':-44 lo:-48 q:-42 hi:-40 hi':-40
---
lo':-44 lo:-48 q:-41 hi:-40 hi':-40
---
lo':-40 lo:-40 q:-40 hi:-40 hi':-40
---
lo':-40 lo:-40 q:-39 hi:-32 hi':-36
---
lo':-40 lo:-40 q:-38 hi:-32 hi':-36
---
lo':-40 lo:-40 q:-37 hi:-32 hi':-36
---
lo':-36 lo:-40 q:-36 hi:-32 hi':-36
---
lo':-36 lo:-40 q:-35 hi:-32 hi':-32
---
lo':-36 lo:-40 q:-34 hi:-32 hi':-32
---
lo':-36 lo:-40 q:-33 hi:-32 hi':-32
---
lo':-32 lo:-32 q:-32 hi:-32 hi':-32
---
lo':-32 lo:-32 q:-63/2 hi:-28 hi':-30
---
lo':-32 lo:-32 q:-31 hi:-28 hi':-30
---
lo':-32 lo:-32 q:-61/2 hi:-28 hi':-30
---
lo':-30 lo:-32 q:-30 hi:-28 hi':-30
---
lo':-30 lo:-32 q:-59/2 hi:-28 hi':-28
---
lo':-30 lo:-32 q:-29 hi:-28 hi':-28
---
lo':-30 lo:-32 q:-57/2 hi:-28 hi':-28
---
lo':-28 lo:-28 q:-28 hi:-28 hi':-28
---
lo':-28 lo:-28 q:-55/2 hi:-24 hi':-26
---
lo':-28 lo:-28 q:-27 hi:-24 hi':-26
---
lo':-28 lo:-28 q:-53/2 hi:-24 hi':-26
---
lo':-26 lo:-28 q:-26 hi:-24 hi':-26
---
lo':-26 lo:-28 q:-51/2 hi:-24 hi':-24
---
lo':-26 lo:-28 q:-25 hi:-24 hi':-24
---
lo':-26 lo:-28 q:-49/2 hi:-24 hi':-24
---
lo':-24 lo:-24 q:-24 hi:-24 hi':-24
---
lo':-24 lo:-24 q:-47/2 hi:-20 hi':-22
---
lo':-24 lo:-24 q:-23 hi:-20 hi':-22
---
lo':-24 lo:-24 q:-45/2 hi:-20 hi':-22
---
lo':-22 lo:-24 q:-22 hi:-20 hi':-22
---
lo':-22 lo:-24 q:-43/2 hi:-20 hi':-20
---
lo':-22 lo:-24 q:-21 hi:-20 hi':-20
---
lo':-22 lo:-24 q:-41/2 hi:-20 hi':-20
---
lo':-20 lo:-20 q:-20 hi:-20 hi':-20
---
lo':-20 lo:-20 q:-39/2 hi:-16 hi':-18
---
lo':-20 lo:-20 q:-19 hi:-16 hi':-18
---
lo':-20 lo:-20 q:-37/2 hi:-16 hi':-18
---
lo':-18 lo:-20 q:-18 hi:-16 hi':-18
---
lo':-18 lo:-20 q:-35/2 hi:-16 hi':-16
---
lo':-18 lo:-20 q:-17 hi:-16 hi':-16
---
lo':-18 lo:-20 q:-33/2 hi:-16 hi':-16
---
lo':-16 lo:-16 q:-16 hi:-16 hi':-16
---
lo':-16 lo:-16 q:-63/4 hi:-14 hi':-15
---
lo':-16 lo:-16 q:-31/2 hi:-14 hi':-15
---
lo':-16 lo:-16 q:-61/4 hi:-14 hi':-15
---
lo':-15 lo:-16 q:-15 hi:-14 hi':-15
---
lo':-15 lo:-16 q:-59/4 hi:-14 hi':-14
---
lo':-15 lo:-16 q:-29/2 hi:-14 hi':-14
---
lo':-15 lo:-16 q:-57/4 hi:-14 hi':-14
---
lo':-14 lo:-14 q:-14 hi:-14 hi':-14
---
lo':-14 lo:-14 q:-55/4 hi:-12 hi':-13
---
lo':-14 lo:-14 q:-27/2 hi:-12 hi':-13
---
lo':-14 lo:-14 q:-53/4 hi:-12 hi':-13
---
lo':-13 lo:-14 q:-13 hi:-12 hi':-13
---
lo':-13 lo:-14 q:-51/4 hi:-12 hi':-12
---
lo':-13 lo:-14 q:-25/2 hi:-12 hi':-12
---
lo':-13 lo:-14 q:-49/4 hi:-12 hi':-12
---
lo':-12 lo:-12 q:-12 hi:-12 hi':-12
---
lo':-12 lo:-12 q:-47/4 hi:-10 hi':-11
---
lo':-12 lo:-12 q:-23/2 hi:-10 hi':-11
---
lo':-12 lo:-12 q:-45/4 hi:-10 hi':-11
---
lo':-11 lo:-12 q:-11 hi:-10 hi':-11
---
lo':-11 lo:-12 q:-43/4 hi:-10 hi':-10
---
lo':-11 lo:-12 q:-21/2 hi:-10 hi':-10
---
lo':-11 lo:-12 q:-41/4 hi:-10 hi':-10
---
lo':-10 lo:-10 q:-10 hi:-10 hi':-10
---
lo':-10 lo:-10 q:-39/4 hi:-8 hi':-9
---
lo':-10 lo:-10 q:-19/2 hi:-8 hi':-9
---
lo':-10 lo:-10 q:-37/4 hi:-8 hi':-9
---
lo':-9 lo:-10 q:-9 hi:-8 hi':-9
---
lo':-9 lo:-10 q:-35/4 hi:-8 hi':-8
---
lo':-9 lo:-10 q:-17/2 hi:-8 hi':-8
---
lo':-9 lo:-10 q:-33/4 hi:-8 hi':-8
---
lo':-8 lo:-8 q:-8 hi:-8 hi':-8
---
lo':-8 lo:-8 q:-63/8 hi:-7 hi':(-15 : Rat)/2
---
lo':-8 lo:-8 q:-31/4 hi:-7 hi':(-15 : Rat)/2
---
lo':-8 lo:-8 q:-61/8 hi:-7 hi':(-15 : Rat)/2
---
lo':(-15 : Rat)/2 lo:-8 q:-15/2 hi:-7 hi':(-15 : Rat)/2
---
lo':(-15 : Rat)/2 lo:-8 q:-59/8 hi:-7 hi':-7
---
lo':(-15 : Rat)/2 lo:-8 q:-29/4 hi:-7 hi':-7
---
lo':(-15 : Rat)/2 lo:-8 q:-57/8 hi:-7 hi':-7
---
lo':-7 lo:-7 q:-7 hi:-7 hi':-7
---
lo':-7 lo:-7 q:-55/8 hi:-6 hi':(-13 : Rat)/2
---
lo':-7 lo:-7 q:-27/4 hi:-6 hi':(-13 : Rat)/2
---
lo':-7 lo:-7 q:-53/8 hi:-6 hi':(-13 : Rat)/2
---
lo':(-13 : Rat)/2 lo:-7 q:-13/2 hi:-6 hi':(-13 : Rat)/2
---
lo':(-13 : Rat)/2 lo:-7 q:-51/8 hi:-6 hi':-6
---
lo':(-13 : Rat)/2 lo:-7 q:-25/4 hi:-6 hi':-6
---
lo':(-13 : Rat)/2 lo:-7 q:-49/8 hi:-6 hi':-6
---
lo':-6 lo:-6 q:-6 hi:-6 hi':-6
---
lo':-6 lo:-6 q:-47/8 hi:-5 hi':(-11 : Rat)/2
---
lo':-6 lo:-6 q:-23/4 hi:-5 hi':(-11 : Rat)/2
---
lo':-6 lo:-6 q:-45/8 hi:-5 hi':(-11 : Rat)/2
---
lo':(-11 : Rat)/2 lo:-6 q:-11/2 hi:-5 hi':(-11 : Rat)/2
---
lo':(-11 : Rat)/2 lo:-6 q:-43/8 hi:-5 hi':-5
---
lo':(-11 : Rat)/2 lo:-6 q:-21/4 hi:-5 hi':-5
---
lo':(-11 : Rat)/2 lo:-6 q:-41/8 hi:-5 hi':-5
---
lo':-5 lo:-5 q:-5 hi:-5 hi':-5
---
lo':-5 lo:-5 q:-39/8 hi:-4 hi':(-9 : Rat)/2
---
lo':-5 lo:-5 q:-19/4 hi:-4 hi':(-9 : Rat)/2
---
lo':-5 lo:-5 q:-37/8 hi:-4 hi':(-9 : Rat)/2
---
lo':(-9 : Rat)/2 lo:-5 q:-9/2 hi:-4 hi':(-9 : Rat)/2
---
lo':(-9 : Rat)/2 lo:-5 q:-35/8 hi:-4 hi':-4
---
lo':(-9 : Rat)/2 lo:-5 q:-17/4 hi:-4 hi':-4
---
lo':(-9 : Rat)/2 lo:-5 q:-33/8 hi:-4 hi':-4
---
lo':-4 lo:-4 q:-4 hi:-4 hi':-4
---
lo':-4 lo:-4 q:-63/16 hi:(-7 : Rat)/2 hi':(-15 : Rat)/4
---
lo':-4 lo:-4 q:-31/8 hi:(-7 : Rat)/2 hi':(-15 : Rat)/4
---
lo':-4 lo:-4 q:-61/16 hi:(-7 : Rat)/2 hi':(-15 : Rat)/4
---
lo':(-15 : Rat)/4 lo:-4 q:-15/4 hi:(-7 : Rat)/2 hi':(-15 : Rat)/4
---
lo':(-15 : Rat)/4 lo:-4 q:-59/16 hi:(-7 : Rat)/2 hi':(-7 : Rat)/2
---
lo':(-15 : Rat)/4 lo:-4 q:-29/8 hi:(-7 : Rat)/2 hi':(-7 : Rat)/2
---
lo':(-15 : Rat)/4 lo:-4 q:-57/16 hi:(-7 : Rat)/2 hi':(-7 : Rat)/2
---
lo':(-7 : Rat)/2 lo:(-7 : Rat)/2 q:-7/2 hi:(-7 : Rat)/2 hi':(-7 : Rat)/2
---
lo':(-7 : Rat)/2 lo:(-7 : Rat)/2 q:-55/16 hi:-3 hi':(-13 : Rat)/4
---
lo':(-7 : Rat)/2 lo:(-7 : Rat)/2 q:-27/8 hi:-3 hi':(-13 : Rat)/4
---
lo':(-7 : Rat)/2 lo:(-7 : Rat)/2 q:-53/16 hi:-3 hi':(-13 : Rat)/4
---
lo':(-13 : Rat)/4 lo:(-7 : Rat)/2 q:-13/4 hi:-3 hi':(-13 : Rat)/4
---
lo':(-13 : Rat)/4 lo:(-7 : Rat)/2 q:-51/16 hi:-3 hi':-3
---
lo':(-13 : Rat)/4 lo:(-7 : Rat)/2 q:-25/8 hi:-3 hi':-3
---
lo':(-13 : Rat)/4 lo:(-7 : Rat)/2 q:-49/16 hi:-3 hi':-3
---
lo':-3 lo:-3 q:-3 hi:-3 hi':-3
---
lo':-3 lo:-3 q:-47/16 hi:(-5 : Rat)/2 hi':(-11 : Rat)/4
---
lo':-3 lo:-3 q:-23/8 hi:(-5 : Rat)/2 hi':(-11 : Rat)/4
---
lo':-3 lo:-3 q:-45/16 hi:(-5 : Rat)/2 hi':(-11 : Rat)/4
---
lo':(-11 : Rat)/4 lo:-3 q:-11/4 hi:(-5 : Rat)/2 hi':(-11 : Rat)/4
---
lo':(-11 : Rat)/4 lo:-3 q:-43/16 hi:(-5 : Rat)/2 hi':(-5 : Rat)/2
---
lo':(-11 : Rat)/4 lo:-3 q:-21/8 hi:(-5 : Rat)/2 hi':(-5 : Rat)/2
---
lo':(-11 : Rat)/4 lo:-3 q:-41/16 hi:(-5 : Rat)/2 hi':(-5 : Rat)/2
---
lo':(-5 : Rat)/2 lo:(-5 : Rat)/2 q:-5/2 hi:(-5 : Rat)/2 hi':(-5 : Rat)/2
---
lo':(-5 : Rat)/2 lo:(-5 : Rat)/2 q:-39/16 hi:-2 hi':(-9 : Rat)/4
---
lo':(-5 : Rat)/2 lo:(-5 : Rat)/2 q:-19/8 hi:-2 hi':(-9 : Rat)/4
---
lo':(-5 : Rat)/2 lo:(-5 : Rat)/2 q:-37/16 hi:-2 hi':(-9 : Rat)/4
---
lo':(-9 : Rat)/4 lo:(-5 : Rat)/2 q:-9/4 hi:-2 hi':(-9 : Rat)/4
---
lo':(-9 : Rat)/4 lo:(-5 : Rat)/2 q:-35/16 hi:-2 hi':-2
---
lo':(-9 : Rat)/4 lo:(-5 : Rat)/2 q:-17/8 hi:-2 hi':-2
---
lo':(-9 : Rat)/4 lo:(-5 : Rat)/2 q:-33/16 hi:-2 hi':-2
---
lo':-2 lo:-2 q:-2 hi:-2 hi':-2
---
lo':-2 lo:-2 q:-63/32 hi:(-7 : Rat)/4 hi':(-15 : Rat)/8
---
lo':-2 lo:-2 q:-31/16 hi:(-7 : Rat)/4 hi':(-15 : Rat)/8
---
lo':-2 lo:-2 q:-61/32 hi:(-7 : Rat)/4 hi':(-15 : Rat)/8
---
lo':(-15 : Rat)/8 lo:-2 q:-15/8 hi:(-7 : Rat)/4 hi':(-15 : Rat)/8
---
lo':(-15 : Rat)/8 lo:-2 q:-59/32 hi:(-7 : Rat)/4 hi':(-7 : Rat)/4
---
lo':(-15 : Rat)/8 lo:-2 q:-29/16 hi:(-7 : Rat)/4 hi':(-7 : Rat)/4
---
lo':(-15 : Rat)/8 lo:-2 q:-57/32 hi:(-7 : Rat)/4 hi':(-7 : Rat)/4
---
lo':(-7 : Rat)/4 lo:(-7 : Rat)/4 q:-7/4 hi:(-7 : Rat)/4 hi':(-7 : Rat)/4
---
lo':(-7 : Rat)/4 lo:(-7 : Rat)/4 q:-55/32 hi:(-3 : Rat)/2 hi':(-13 : Rat)/8
---
lo':(-7 : Rat)/4 lo:(-7 : Rat)/4 q:-27/16 hi:(-3 : Rat)/2 hi':(-13 : Rat)/8
---
lo':(-7 : Rat)/4 lo:(-7 : Rat)/4 q:-53/32 hi:(-3 : Rat)/2 hi':(-13 : Rat)/8
---
lo':(-13 : Rat)/8 lo:(-7 : Rat)/4 q:-13/8 hi:(-3 : Rat)/2 hi':(-13 : Rat)/8
---
lo':(-13 : Rat)/8 lo:(-7 : Rat)/4 q:-51/32 hi:(-3 : Rat)/2 hi':(-3 : Rat)/2
---
lo':(-13 : Rat)/8 lo:(-7 : Rat)/4 q:-25/16 hi:(-3 : Rat)/2 hi':(-3 : Rat)/2
---
lo':(-13 : Rat)/8 lo:(-7 : Rat)/4 q:-49/32 hi:(-3 : Rat)/2 hi':(-3 : Rat)/2
---
lo':(-3 : Rat)/2 lo:(-3 : Rat)/2 q:-3/2 hi:(-3 : Rat)/2 hi':(-3 : Rat)/2
---
lo':(-3 : Rat)/2 lo:(-3 : Rat)/2 q:-47/32 hi:(-5 : Rat)/4 hi':(-11 : Rat)/8
---
lo':(-3 : Rat)/2 lo:(-3 : Rat)/2 q:-23/16 hi:(-5 : Rat)/4 hi':(-11 : Rat)/8
---
lo':(-3 : Rat)/2 lo:(-3 : Rat)/2 q:-45/32 hi:(-5 : Rat)/4 hi':(-11 : Rat)/8
---
lo':(-11 : Rat)/8 lo:(-3 : Rat)/2 q:-11/8 hi:(-5 : Rat)/4 hi':(-11 : Rat)/8
---
lo':(-11 : Rat)/8 lo:(-3 : Rat)/2 q:-43/32 hi:(-5 : Rat)/4 hi':(-5 : Rat)/4
---
lo':(-11 : Rat)/8 lo:(-3 : Rat)/2 q:-21/16 hi:(-5 : Rat)/4 hi':(-5 : Rat)/4
---
lo':(-11 : Rat)/8 lo:(-3 : Rat)/2 q:-41/32 hi:(-5 : Rat)/4 hi':(-5 : Rat)/4
---
lo':(-5 : Rat)/4 lo:(-5 : Rat)/4 q:-5/4 hi:(-5 : Rat)/4 hi':(-5 : Rat)/4
---
lo':(-5 : Rat)/4 lo:(-5 : Rat)/4 q:-39/32 hi:-1 hi':(-9 : Rat)/8
---
lo':(-5 : Rat)/4 lo:(-5 : Rat)/4 q:-19/16 hi:-1 hi':(-9 : Rat)/8
---
lo':(-5 : Rat)/4 lo:(-5 : Rat)/4 q:-37/32 hi:-1 hi':(-9 : Rat)/8
---
lo':(-9 : Rat)/8 lo:(-5 : Rat)/4 q:-9/8 hi:-1 hi':(-9 : Rat)/8
---
lo':(-9 : Rat)/8 lo:(-5 : Rat)/4 q:-35/32 hi:-1 hi':-1
---
lo':(-9 : Rat)/8 lo:(-5 : Rat)/4 q:-17/16 hi:-1 hi':-1
---
lo':(-9 : Rat)/8 lo:(-5 : Rat)/4 q:-33/32 hi:-1 hi':-1
---
lo':-1 lo:-1 q:-1 hi:-1 hi':-1
---
lo':-1 lo:-1 q:-63/64 hi:(-7 : Rat)/8 hi':(-15 : Rat)/16
---
lo':-1 lo:-1 q:-31/32 hi:(-7 : Rat)/8 hi':(-15 : Rat)/16
---
lo':-1 lo:-1 q:-61/64 hi:(-7 : Rat)/8 hi':(-15 : Rat)/16
---
lo':(-15 : Rat)/16 lo:-1 q:-15/16 hi:(-7 : Rat)/8 hi':(-15 : Rat)/16
---
lo':(-15 : Rat)/16 lo:-1 q:-59/64 hi:(-7 : Rat)/8 hi':(-7 : Rat)/8
---
lo':(-15 : Rat)/16 lo:-1 q:-29/32 hi:(-7 : Rat)/8 hi':(-7 : Rat)/8
---
lo':(-15 : Rat)/16 lo:-1 q:-57/64 hi:(-7 : Rat)/8 hi':(-7 : Rat)/8
---
lo':(-7 : Rat)/8 lo:(-7 : Rat)/8 q:-7/8 hi:(-7 : Rat)/8 hi':(-7 : Rat)/8
---
lo':(-7 : Rat)/8 lo:(-7 : Rat)/8 q:-55/64 hi:(-3 : Rat)/4 hi':(-13 : Rat)/16
---
lo':(-7 : Rat)/8 lo:(-7 : Rat)/8 q:-27/32 hi:(-3 : Rat)/4 hi':(-13 : Rat)/16
---
lo':(-7 : Rat)/8 lo:(-7 : Rat)/8 q:-53/64 hi:(-3 : Rat)/4 hi':(-13 : Rat)/16
---
lo':(-13 : Rat)/16 lo:(-7 : Rat)/8 q:-13/16 hi:(-3 : Rat)/4 hi':(-13 : Rat)/16
---
lo':(-13 : Rat)/16 lo:(-7 : Rat)/8 q:-51/64 hi:(-3 : Rat)/4 hi':(-3 : Rat)/4
---
lo':(-13 : Rat)/16 lo:(-7 : Rat)/8 q:-25/32 hi:(-3 : Rat)/4 hi':(-3 : Rat)/4
---
lo':(-13 : Rat)/16 lo:(-7 : Rat)/8 q:-49/64 hi:(-3 : Rat)/4 hi':(-3 : Rat)/4
---
lo':(-3 : Rat)/4 lo:(-3 : Rat)/4 q:-3/4 hi:(-3 : Rat)/4 hi':(-3 : Rat)/4
---
lo':(-3 : Rat)/4 lo:(-3 : Rat)/4 q:-47/64 hi:(-5 : Rat)/8 hi':(-11 : Rat)/16
---
lo':(-3 : Rat)/4 lo:(-3 : Rat)/4 q:-23/32 hi:(-5 : Rat)/8 hi':(-11 : Rat)/16
---
lo':(-3 : Rat)/4 lo:(-3 : Rat)/4 q:-45/64 hi:(-5 : Rat)/8 hi':(-11 : Rat)/16
---
lo':(-11 : Rat)/16 lo:(-3 : Rat)/4 q:-11/16 hi:(-5 : Rat)/8 hi':(-11 : Rat)/16
---
lo':(-11 : Rat)/16 lo:(-3 : Rat)/4 q:-43/64 hi:(-5 : Rat)/8 hi':(-5 : Rat)/8
---
lo':(-11 : Rat)/16 lo:(-3 : Rat)/4 q:-21/32 hi:(-5 : Rat)/8 hi':(-5 : Rat)/8
---
lo':(-11 : Rat)/16 lo:(-3 : Rat)/4 q:-41/64 hi:(-5 : Rat)/8 hi':(-5 : Rat)/8
---
lo':(-5 : Rat)/8 lo:(-5 : Rat)/8 q:-5/8 hi:(-5 : Rat)/8 hi':(-5 : Rat)/8
---
lo':(-5 : Rat)/8 lo:(-5 : Rat)/8 q:-39/64 hi:(-1 : Rat)/2 hi':(-9 : Rat)/16
---
lo':(-5 : Rat)/8 lo:(-5 : Rat)/8 q:-19/32 hi:(-1 : Rat)/2 hi':(-9 : Rat)/16
---
lo':(-5 : Rat)/8 lo:(-5 : Rat)/8 q:-37/64 hi:(-1 : Rat)/2 hi':(-9 : Rat)/16
---
lo':(-9 : Rat)/16 lo:(-5 : Rat)/8 q:-9/16 hi:(-1 : Rat)/2 hi':(-9 : Rat)/16
---
lo':(-9 : Rat)/16 lo:(-5 : Rat)/8 q:-35/64 hi:(-1 : Rat)/2 hi':(-1 : Rat)/2
---
lo':(-9 : Rat)/16 lo:(-5 : Rat)/8 q:-17/32 hi:(-1 : Rat)/2 hi':(-1 : Rat)/2
---
lo':(-9 : Rat)/16 lo:(-5 : Rat)/8 q:-33/64 hi:(-1 : Rat)/2 hi':(-1 : Rat)/2
---
lo':(-1 : Rat)/2 lo:(-1 : Rat)/2 q:-1/2 hi:(-1 : Rat)/2 hi':(-1 : Rat)/2
---
lo':(-1 : Rat)/2 lo:(-1 : Rat)/2 q:-63/128 hi:(-7 : Rat)/16 hi':(-15 : Rat)/32
---
lo':(-1 : Rat)/2 lo:(-1 : Rat)/2 q:-31/64 hi:(-7 : Rat)/16 hi':(-15 : Rat)/32
---
lo':(-1 : Rat)/2 lo:(-1 : Rat)/2 q:-61/128 hi:(-7 : Rat)/16 hi':(-15 : Rat)/32
---
lo':(-15 : Rat)/32 lo:(-1 : Rat)/2 q:-15/32 hi:(-7 : Rat)/16 hi':(-15 : Rat)/32
---
lo':(-15 : Rat)/32 lo:(-1 : Rat)/2 q:-59/128 hi:(-7 : Rat)/16 hi':(-7 : Rat)/16
---
lo':(-15 : Rat)/32 lo:(-1 : Rat)/2 q:-29/64 hi:(-7 : Rat)/16 hi':(-7 : Rat)/16
---
lo':(-15 : Rat)/32 lo:(-1 : Rat)/2 q:-57/128 hi:(-7 : Rat)/16 hi':(-7 : Rat)/16
---
lo':(-7 : Rat)/16 lo:(-7 : Rat)/16 q:-7/16 hi:(-7 : Rat)/16 hi':(-7 : Rat)/16
---
lo':(-7 : Rat)/16 lo:(-7 : Rat)/16 q:-55/128 hi:(-3 : Rat)/8 hi':(-13 : Rat)/32
---
lo':(-7 : Rat)/16 lo:(-7 : Rat)/16 q:-27/64 hi:(-3 : Rat)/8 hi':(-13 : Rat)/32
---
lo':(-7 : Rat)/16 lo:(-7 : Rat)/16 q:-53/128 hi:(-3 : Rat)/8 hi':(-13 : Rat)/32
---
lo':(-13 : Rat)/32 lo:(-7 : Rat)/16 q:-13/32 hi:(-3 : Rat)/8 hi':(-13 : Rat)/32
---
lo':(-13 : Rat)/32 lo:(-7 : Rat)/16 q:-51/128 hi:(-3 : Rat)/8 hi':(-3 : Rat)/8
---
lo':(-13 : Rat)/32 lo:(-7 : Rat)/16 q:-25/64 hi:(-3 : Rat)/8 hi':(-3 : Rat)/8
---
lo':(-13 : Rat)/32 lo:(-7 : Rat)/16 q:-49/128 hi:(-3 : Rat)/8 hi':(-3 : Rat)/8
---
lo':(-3 : Rat)/8 lo:(-3 : Rat)/8 q:-3/8 hi:(-3 : Rat)/8 hi':(-3 : Rat)/8
---
lo':(-3 : Rat)/8 lo:(-3 : Rat)/8 q:-47/128 hi:(-5 : Rat)/16 hi':(-11 : Rat)/32
---
lo':(-3 : Rat)/8 lo:(-3 : Rat)/8 q:-23/64 hi:(-5 : Rat)/16 hi':(-11 : Rat)/32
---
lo':(-3 : Rat)/8 lo:(-3 : Rat)/8 q:-45/128 hi:(-5 : Rat)/16 hi':(-11 : Rat)/32
---
lo':(-11 : Rat)/32 lo:(-3 : Rat)/8 q:-11/32 hi:(-5 : Rat)/16 hi':(-11 : Rat)/32
---
lo':(-11 : Rat)/32 lo:(-3 : Rat)/8 q:-43/128 hi:(-5 : Rat)/16 hi':(-5 : Rat)/16
---
lo':(-11 : Rat)/32 lo:(-3 : Rat)/8 q:-21/64 hi:(-5 : Rat)/16 hi':(-5 : Rat)/16
---
lo':(-11 : Rat)/32 lo:(-3 : Rat)/8 q:-41/128 hi:(-5 : Rat)/16 hi':(-5 : Rat)/16
---
lo':(-5 : Rat)/16 lo:(-5 : Rat)/16 q:-5/16 hi:(-5 : Rat)/16 hi':(-5 : Rat)/16
---
lo':(-5 : Rat)/16 lo:(-5 : Rat)/16 q:-39/128 hi:(-1 : Rat)/4 hi':(-9 : Rat)/32
---
lo':(-5 : Rat)/16 lo:(-5 : Rat)/16 q:-19/64 hi:(-1 : Rat)/4 hi':(-9 : Rat)/32
---
lo':(-5 : Rat)/16 lo:(-5 : Rat)/16 q:-37/128 hi:(-1 : Rat)/4 hi':(-9 : Rat)/32
---
lo':(-9 : Rat)/32 lo:(-5 : Rat)/16 q:-9/32 hi:(-1 : Rat)/4 hi':(-9 : Rat)/32
---
lo':(-9 : Rat)/32 lo:(-5 : Rat)/16 q:-35/128 hi:(-1 : Rat)/4 hi':(-1 : Rat)/4
---
lo':(-9 : Rat)/32 lo:(-5 : Rat)/16 q:-17/64 hi:(-1 : Rat)/4 hi':(-1 : Rat)/4
---
lo':(-9 : Rat)/32 lo:(-5 : Rat)/16 q:-33/128 hi:(-1 : Rat)/4 hi':(-1 : Rat)/4
---
lo':(-1 : Rat)/4 lo:(-1 : Rat)/4 q:-1/4 hi:(-1 : Rat)/4 hi':(-1 : Rat)/4
---
lo':(-1 : Rat)/4 lo:(-1 : Rat)/4 q:-63/256 hi:(-7 : Rat)/32 hi':(-15 : Rat)/64
---
lo':(-1 : Rat)/4 lo:(-1 : Rat)/4 q:-31/128 hi:(-7 : Rat)/32 hi':(-15 : Rat)/64
---
lo':(-1 : Rat)/4 lo:(-1 : Rat)/4 q:-61/256 hi:(-7 : Rat)/32 hi':(-15 : Rat)/64
---
lo':(-15 : Rat)/64 lo:(-1 : Rat)/4 q:-15/64 hi:(-7 : Rat)/32 hi':(-15 : Rat)/64
---
lo':(-15 : Rat)/64 lo:(-1 : Rat)/4 q:-59/256 hi:(-7 : Rat)/32 hi':(-7 : Rat)/32
---
lo':(-15 : Rat)/64 lo:(-1 : Rat)/4 q:-29/128 hi:(-7 : Rat)/32 hi':(-7 : Rat)/32
---
lo':(-15 : Rat)/64 lo:(-1 : Rat)/4 q:-57/256 hi:(-7 : Rat)/32 hi':(-7 : Rat)/32
---
lo':(-7 : Rat)/32 lo:(-7 : Rat)/32 q:-7/32 hi:(-7 : Rat)/32 hi':(-7 : Rat)/32
---
lo':(-7 : Rat)/32 lo:(-7 : Rat)/32 q:-55/256 hi:(-3 : Rat)/16 hi':(-13 : Rat)/64
---
lo':(-7 : Rat)/32 lo:(-7 : Rat)/32 q:-27/128 hi:(-3 : Rat)/16 hi':(-13 : Rat)/64
---
lo':(-7 : Rat)/32 lo:(-7 : Rat)/32 q:-53/256 hi:(-3 : Rat)/16 hi':(-13 : Rat)/64
---
lo':(-13 : Rat)/64 lo:(-7 : Rat)/32 q:-13/64 hi:(-3 : Rat)/16 hi':(-13 : Rat)/64
---
lo':(-13 : Rat)/64 lo:(-7 : Rat)/32 q:-51/256 hi:(-3 : Rat)/16 hi':(-3 : Rat)/16
---
lo':(-13 : Rat)/64 lo:(-7 : Rat)/32 q:-25/128 hi:(-3 : Rat)/16 hi':(-3 : Rat)/16
---
lo':(-13 : Rat)/64 lo:(-7 : Rat)/32 q:-49/256 hi:(-3 : Rat)/16 hi':(-3 : Rat)/16
---
lo':(-3 : Rat)/16 lo:(-3 : Rat)/16 q:-3/16 hi:(-3 : Rat)/16 hi':(-3 : Rat)/16
---
lo':(-3 : Rat)/16 lo:(-3 : Rat)/16 q:-47/256 hi:(-5 : Rat)/32 hi':(-11 : Rat)/64
---
lo':(-3 : Rat)/16 lo:(-3 : Rat)/16 q:-23/128 hi:(-5 : Rat)/32 hi':(-11 : Rat)/64
---
lo':(-3 : Rat)/16 lo:(-3 : Rat)/16 q:-45/256 hi:(-5 : Rat)/32 hi':(-11 : Rat)/64
---
lo':(-11 : Rat)/64 lo:(-3 : Rat)/16 q:-11/64 hi:(-5 : Rat)/32 hi':(-11 : Rat)/64
---
lo':(-11 : Rat)/64 lo:(-3 : Rat)/16 q:-43/256 hi:(-5 : Rat)/32 hi':(-5 : Rat)/32
---
lo':(-11 : Rat)/64 lo:(-3 : Rat)/16 q:-21/128 hi:(-5 : Rat)/32 hi':(-5 : Rat)/32
---
lo':(-11 : Rat)/64 lo:(-3 : Rat)/16 q:-41/256 hi:(-5 : Rat)/32 hi':(-5 : Rat)/32
---
lo':(-5 : Rat)/32 lo:(-5 : Rat)/32 q:-5/32 hi:(-5 : Rat)/32 hi':(-5 : Rat)/32
---
lo':(-5 : Rat)/32 lo:(-5 : Rat)/32 q:-39/256 hi:(-1 : Rat)/8 hi':(-9 : Rat)/64
---
lo':(-5 : Rat)/32 lo:(-5 : Rat)/32 q:-19/128 hi:(-1 : Rat)/8 hi':(-9 : Rat)/64
---
lo':(-5 : Rat)/32 lo:(-5 : Rat)/32 q:-37/256 hi:(-1 : Rat)/8 hi':(-9 : Rat)/64
---
lo':(-9 : Rat)/64 lo:(-5 : Rat)/32 q:-9/64 hi:(-1 : Rat)/8 hi':(-9 : Rat)/64
---
lo':(-9 : Rat)/64 lo:(-5 : Rat)/32 q:-35/256 hi:(-1 : Rat)/8 hi':(-1 : Rat)/8
---
lo':(-9 : Rat)/64 lo:(-5 : Rat)/32 q:-17/128 hi:(-1 : Rat)/8 hi':(-1 : Rat)/8
---
lo':(-9 : Rat)/64 lo:(-5 : Rat)/32 q:-33/256 hi:(-1 : Rat)/8 hi':(-1 : Rat)/8
---
lo':(-1 : Rat)/8 lo:(-1 : Rat)/8 q:-1/8 hi:(-1 : Rat)/8 hi':(-1 : Rat)/8
---
lo':(-1 : Rat)/8 lo:(-1 : Rat)/8 q:-63/512 hi:(-7 : Rat)/64 hi':(-15 : Rat)/128
---
lo':(-1 : Rat)/8 lo:(-1 : Rat)/8 q:-31/256 hi:(-7 : Rat)/64 hi':(-15 : Rat)/128
---
lo':(-1 : Rat)/8 lo:(-1 : Rat)/8 q:-61/512 hi:(-7 : Rat)/64 hi':(-15 : Rat)/128
---
lo':(-15 : Rat)/128 lo:(-1 : Rat)/8 q:-15/128 hi:(-7 : Rat)/64 hi':(-15 : Rat)/128
---
lo':(-15 : Rat)/128 lo:(-1 : Rat)/8 q:-59/512 hi:(-7 : Rat)/64 hi':(-7 : Rat)/64
---
lo':(-15 : Rat)/128 lo:(-1 : Rat)/8 q:-29/256 hi:(-7 : Rat)/64 hi':(-7 : Rat)/64
---
lo':(-15 : Rat)/128 lo:(-1 : Rat)/8 q:-57/512 hi:(-7 : Rat)/64 hi':(-7 : Rat)/64
---
lo':(-7 : Rat)/64 lo:(-7 : Rat)/64 q:-7/64 hi:(-7 : Rat)/64 hi':(-7 : Rat)/64
---
lo':(-7 : Rat)/64 lo:(-7 : Rat)/64 q:-55/512 hi:(-3 : Rat)/32 hi':(-13 : Rat)/128
---
lo':(-7 : Rat)/64 lo:(-7 : Rat)/64 q:-27/256 hi:(-3 : Rat)/32 hi':(-13 : Rat)/128
---
lo':(-7 : Rat)/64 lo:(-7 : Rat)/64 q:-53/512 hi:(-3 : Rat)/32 hi':(-13 : Rat)/128
---
lo':(-13 : Rat)/128 lo:(-7 : Rat)/64 q:-13/128 hi:(-3 : Rat)/32 hi':(-13 : Rat)/128
---
lo':(-13 : Rat)/128 lo:(-7 : Rat)/64 q:-51/512 hi:(-3 : Rat)/32 hi':(-3 : Rat)/32
---
lo':(-13 : Rat)/128 lo:(-7 : Rat)/64 q:-25/256 hi:(-3 : Rat)/32 hi':(-3 : Rat)/32
---
lo':(-13 : Rat)/128 lo:(-7 : Rat)/64 q:-49/512 hi:(-3 : Rat)/32 hi':(-3 : Rat)/32
---
lo':(-3 : Rat)/32 lo:(-3 : Rat)/32 q:-3/32 hi:(-3 : Rat)/32 hi':(-3 : Rat)/32
---
lo':(-3 : Rat)/32 lo:(-3 : Rat)/32 q:-47/512 hi:(-5 : Rat)/64 hi':(-11 : Rat)/128
---
lo':(-3 : Rat)/32 lo:(-3 : Rat)/32 q:-23/256 hi:(-5 : Rat)/64 hi':(-11 : Rat)/128
---
lo':(-3 : Rat)/32 lo:(-3 : Rat)/32 q:-45/512 hi:(-5 : Rat)/64 hi':(-11 : Rat)/128
---
lo':(-11 : Rat)/128 lo:(-3 : Rat)/32 q:-11/128 hi:(-5 : Rat)/64 hi':(-11 : Rat)/128
---
lo':(-11 : Rat)/128 lo:(-3 : Rat)/32 q:-43/512 hi:(-5 : Rat)/64 hi':(-5 : Rat)/64
---
lo':(-11 : Rat)/128 lo:(-3 : Rat)/32 q:-21/256 hi:(-5 : Rat)/64 hi':(-5 : Rat)/64
---
lo':(-11 : Rat)/128 lo:(-3 : Rat)/32 q:-41/512 hi:(-5 : Rat)/64 hi':(-5 : Rat)/64
---
lo':(-5 : Rat)/64 lo:(-5 : Rat)/64 q:-5/64 hi:(-5 : Rat)/64 hi':(-5 : Rat)/64
---
lo':(-5 : Rat)/64 lo:(-5 : Rat)/64 q:-39/512 hi:(-1 : Rat)/16 hi':(-9 : Rat)/128
---
lo':(-5 : Rat)/64 lo:(-5 : Rat)/64 q:-19/256 hi:(-1 : Rat)/16 hi':(-9 : Rat)/128
---
lo':(-5 : Rat)/64 lo:(-5 : Rat)/64 q:-37/512 hi:(-1 : Rat)/16 hi':(-9 : Rat)/128
---
lo':(-9 : Rat)/128 lo:(-5 : Rat)/64 q:-9/128 hi:(-1 : Rat)/16 hi':(-9 : Rat)/128
---
lo':(-9 : Rat)/128 lo:(-5 : Rat)/64 q:-35/512 hi:(-1 : Rat)/16 hi':(-1 : Rat)/16
---
lo':(-9 : Rat)/128 lo:(-5 : Rat)/64 q:-17/256 hi:(-1 : Rat)/16 hi':(-1 : Rat)/16
---
lo':(-9 : Rat)/128 lo:(-5 : Rat)/64 q:-33/512 hi:(-1 : Rat)/16 hi':(-1 : Rat)/16
---
lo':(-1 : Rat)/16 lo:(-1 : Rat)/16 q:-1/16 hi:(-1 : Rat)/16 hi':(-1 : Rat)/16
---
lo':(-1 : Rat)/16 lo:(-1 : Rat)/16 q:-63/1024 hi:(-7 : Rat)/128 hi':(-15 : Rat)/256
---
lo':(-1 : Rat)/16 lo:(-1 : Rat)/16 q:-31/512 hi:(-7 : Rat)/128 hi':(-15 : Rat)/256
---
lo':(-1 : Rat)/16 lo:(-1 : Rat)/16 q:-61/1024 hi:(-7 : Rat)/128 hi':(-15 : Rat)/256
---
lo':(-15 : Rat)/256 lo:(-1 : Rat)/16 q:-15/256 hi:(-7 : Rat)/128 hi':(-15 : Rat)/256
---
lo':(-15 : Rat)/256 lo:(-1 : Rat)/16 q:-59/1024 hi:(-7 : Rat)/128 hi':(-7 : Rat)/128
---
lo':(-15 : Rat)/256 lo:(-1 : Rat)/16 q:-29/512 hi:(-7 : Rat)/128 hi':(-7 : Rat)/128
---
lo':(-15 : Rat)/256 lo:(-1 : Rat)/16 q:-57/1024 hi:(-7 : Rat)/128 hi':(-7 : Rat)/128
---
lo':(-7 : Rat)/128 lo:(-7 : Rat)/128 q:-7/128 hi:(-7 : Rat)/128 hi':(-7 : Rat)/128
---
lo':(-7 : Rat)/128 lo:(-7 : Rat)/128 q:-55/1024 hi:(-3 : Rat)/64 hi':(-13 : Rat)/256
---
lo':(-7 : Rat)/128 lo:(-7 : Rat)/128 q:-27/512 hi:(-3 : Rat)/64 hi':(-13 : Rat)/256
---
lo':(-7 : Rat)/128 lo:(-7 : Rat)/128 q:-53/1024 hi:(-3 : Rat)/64 hi':(-13 : Rat)/256
---
lo':(-13 : Rat)/256 lo:(-7 : Rat)/128 q:-13/256 hi:(-3 : Rat)/64 hi':(-13 : Rat)/256
---
lo':(-13 : Rat)/256 lo:(-7 : Rat)/128 q:-51/1024 hi:(-3 : Rat)/64 hi':(-3 : Rat)/64
---
lo':(-13 : Rat)/256 lo:(-7 : Rat)/128 q:-25/512 hi:(-3 : Rat)/64 hi':(-3 : Rat)/64
---
lo':(-13 : Rat)/256 lo:(-7 : Rat)/128 q:-49/1024 hi:(-3 : Rat)/64 hi':(-3 : Rat)/64
---
lo':(-3 : Rat)/64 lo:(-3 : Rat)/64 q:-3/64 hi:(-3 : Rat)/64 hi':(-3 : Rat)/64
---
lo':(-3 : Rat)/64 lo:(-3 : Rat)/64 q:-47/1024 hi:(-5 : Rat)/128 hi':(-11 : Rat)/256
---
lo':(-3 : Rat)/64 lo:(-3 : Rat)/64 q:-23/512 hi:(-5 : Rat)/128 hi':(-11 : Rat)/256
---
lo':(-3 : Rat)/64 lo:(-3 : Rat)/64 q:-45/1024 hi:(-5 : Rat)/128 hi':(-11 : Rat)/256
---
lo':(-11 : Rat)/256 lo:(-3 : Rat)/64 q:-11/256 hi:(-5 : Rat)/128 hi':(-11 : Rat)/256
---
lo':(-11 : Rat)/256 lo:(-3 : Rat)/64 q:-43/1024 hi:(-5 : Rat)/128 hi':(-5 : Rat)/128
---
lo':(-11 : Rat)/256 lo:(-3 : Rat)/64 q:-21/512 hi:(-5 : Rat)/128 hi':(-5 : Rat)/128
---
lo':(-11 : Rat)/256 lo:(-3 : Rat)/64 q:-41/1024 hi:(-5 : Rat)/128 hi':(-5 : Rat)/128
---
lo':(-5 : Rat)/128 lo:(-5 : Rat)/128 q:-5/128 hi:(-5 : Rat)/128 hi':(-5 : Rat)/128
---
lo':(-5 : Rat)/128 lo:(-5 : Rat)/128 q:-39/1024 hi:(-1 : Rat)/32 hi':(-9 : Rat)/256
---
lo':(-5 : Rat)/128 lo:(-5 : Rat)/128 q:-19/512 hi:(-1 : Rat)/32 hi':(-9 : Rat)/256
---
lo':(-5 : Rat)/128 lo:(-5 : Rat)/128 q:-37/1024 hi:(-1 : Rat)/32 hi':(-9 : Rat)/256
---
lo':(-9 : Rat)/256 lo:(-5 : Rat)/128 q:-9/256 hi:(-1 : Rat)/32 hi':(-9 : Rat)/256
---
lo':(-9 : Rat)/256 lo:(-5 : Rat)/128 q:-35/1024 hi:(-1 : Rat)/32 hi':(-1 : Rat)/32
---
lo':(-9 : Rat)/256 lo:(-5 : Rat)/128 q:-17/512 hi:(-1 : Rat)/32 hi':(-1 : Rat)/32
---
lo':(-9 : Rat)/256 lo:(-5 : Rat)/128 q:-33/1024 hi:(-1 : Rat)/32 hi':(-1 : Rat)/32
---
lo':(-1 : Rat)/32 lo:(-1 : Rat)/32 q:-1/32 hi:(-1 : Rat)/32 hi':(-1 : Rat)/32
---
lo':(-1 : Rat)/32 lo:(-1 : Rat)/32 q:-63/2048 hi:(-7 : Rat)/256 hi':(-15 : Rat)/512
---
lo':(-1 : Rat)/32 lo:(-1 : Rat)/32 q:-31/1024 hi:(-7 : Rat)/256 hi':(-15 : Rat)/512
---
lo':(-1 : Rat)/32 lo:(-1 : Rat)/32 q:-61/2048 hi:(-7 : Rat)/256 hi':(-15 : Rat)/512
---
lo':(-15 : Rat)/512 lo:(-1 : Rat)/32 q:-15/512 hi:(-7 : Rat)/256 hi':(-15 : Rat)/512
---
lo':(-15 : Rat)/512 lo:(-1 : Rat)/32 q:-59/2048 hi:(-7 : Rat)/256 hi':(-7 : Rat)/256
---
lo':(-15 : Rat)/512 lo:(-1 : Rat)/32 q:-29/1024 hi:(-7 : Rat)/256 hi':(-7 : Rat)/256
---
lo':(-15 : Rat)/512 lo:(-1 : Rat)/32 q:-57/2048 hi:(-7 : Rat)/256 hi':(-7 : Rat)/256
---
lo':(-7 : Rat)/256 lo:(-7 : Rat)/256 q:-7/256 hi:(-7 : Rat)/256 hi':(-7 : Rat)/256
---
lo':(-7 : Rat)/256 lo:(-7 : Rat)/256 q:-55/2048 hi:(-3 : Rat)/128 hi':(-13 : Rat)/512
---
lo':(-7 : Rat)/256 lo:(-7 : Rat)/256 q:-27/1024 hi:(-3 : Rat)/128 hi':(-13 : Rat)/512
---
lo':(-7 : Rat)/256 lo:(-7 : Rat)/256 q:-53/2048 hi:(-3 : Rat)/128 hi':(-13 : Rat)/512
---
lo':(-13 : Rat)/512 lo:(-7 : Rat)/256 q:-13/512 hi:(-3 : Rat)/128 hi':(-13 : Rat)/512
---
lo':(-13 : Rat)/512 lo:(-7 : Rat)/256 q:-51/2048 hi:(-3 : Rat)/128 hi':(-3 : Rat)/128
---
lo':(-13 : Rat)/512 lo:(-7 : Rat)/256 q:-25/1024 hi:(-3 : Rat)/128 hi':(-3 : Rat)/128
---
lo':(-13 : Rat)/512 lo:(-7 : Rat)/256 q:-49/2048 hi:(-3 : Rat)/128 hi':(-3 : Rat)/128
---
lo':(-3 : Rat)/128 lo:(-3 : Rat)/128 q:-3/128 hi:(-3 : Rat)/128 hi':(-3 : Rat)/128
---
lo':(-3 : Rat)/128 lo:(-3 : Rat)/128 q:-47/2048 hi:(-5 : Rat)/256 hi':(-11 : Rat)/512
---
lo':(-3 : Rat)/128 lo:(-3 : Rat)/128 q:-23/1024 hi:(-5 : Rat)/256 hi':(-11 : Rat)/512
---
lo':(-3 : Rat)/128 lo:(-3 : Rat)/128 q:-45/2048 hi:(-5 : Rat)/256 hi':(-11 : Rat)/512
---
lo':(-11 : Rat)/512 lo:(-3 : Rat)/128 q:-11/512 hi:(-5 : Rat)/256 hi':(-11 : Rat)/512
---
lo':(-11 : Rat)/512 lo:(-3 : Rat)/128 q:-43/2048 hi:(-5 : Rat)/256 hi':(-5 : Rat)/256
---
lo':(-11 : Rat)/512 lo:(-3 : Rat)/128 q:-21/1024 hi:(-5 : Rat)/256 hi':(-5 : Rat)/256
---
lo':(-11 : Rat)/512 lo:(-3 : Rat)/128 q:-41/2048 hi:(-5 : Rat)/256 hi':(-5 : Rat)/256
---
lo':(-5 : Rat)/256 lo:(-5 : Rat)/256 q:-5/256 hi:(-5 : Rat)/256 hi':(-5 : Rat)/256
---
lo':(-5 : Rat)/256 lo:(-5 : Rat)/256 q:-39/2048 hi:(-1 : Rat)/64 hi':(-9 : Rat)/512
---
lo':(-5 : Rat)/256 lo:(-5 : Rat)/256 q:-19/1024 hi:(-1 : Rat)/64 hi':(-9 : Rat)/512
---
lo':(-5 : Rat)/256 lo:(-5 : Rat)/256 q:-37/2048 hi:(-1 : Rat)/64 hi':(-9 : Rat)/512
---
lo':(-9 : Rat)/512 lo:(-5 : Rat)/256 q:-9/512 hi:(-1 : Rat)/64 hi':(-9 : Rat)/512
---
lo':(-9 : Rat)/512 lo:(-5 : Rat)/256 q:-35/2048 hi:(-1 : Rat)/64 hi':(-1 : Rat)/64
---
lo':(-9 : Rat)/512 lo:(-5 : Rat)/256 q:-17/1024 hi:(-1 : Rat)/64 hi':(-1 : Rat)/64
---
lo':(-9 : Rat)/512 lo:(-5 : Rat)/256 q:-33/2048 hi:(-1 : Rat)/64 hi':(-1 : Rat)/64
---
lo':(-1 : Rat)/64 lo:(-1 : Rat)/64 q:-1/64 hi:(-1 : Rat)/64 hi':(-1 : Rat)/64
---
lo':(-1 : Rat)/64 lo:(-1 : Rat)/64 q:-31/2048 hi:(-3 : Rat)/256 hi':(-7 : Rat)/512
---
lo':(-1 : Rat)/64 lo:(-1 : Rat)/64 q:-15/1024 hi:(-3 : Rat)/256 hi':(-7 : Rat)/512
---
lo':(-1 : Rat)/64 lo:(-1 : Rat)/64 q:-29/2048 hi:(-3 : Rat)/256 hi':(-7 : Rat)/512
---
lo':(-7 : Rat)/512 lo:(-1 : Rat)/64 q:-7/512 hi:(-3 : Rat)/256 hi':(-7 : Rat)/512
---
lo':(-7 : Rat)/512 lo:(-1 : Rat)/64 q:-27/2048 hi:(-3 : Rat)/256 hi':(-3 : Rat)/256
---
lo':(-7 : Rat)/512 lo:(-1 : Rat)/64 q:-13/1024 hi:(-3 : Rat)/256 hi':(-3 : Rat)/256
---
lo':(-7 : Rat)/512 lo:(-1 : Rat)/64 q:-25/2048 hi:(-3 : Rat)/256 hi':(-3 : Rat)/256
---
lo':(-3 : Rat)/256 lo:(-3 : Rat)/256 q:-3/256 hi:(-3 : Rat)/256 hi':(-3 : Rat)/256
---
lo':(-3 : Rat)/256 lo:(-3 : Rat)/256 q:-23/2048 hi:(-1 : Rat)/128 hi':(-5 : Rat)/512
---
lo':(-3 : Rat)/256 lo:(-3 : Rat)/256 q:-11/1024 hi:(-1 : Rat)/128 hi':(-5 : Rat)/512
---
lo':(-3 : Rat)/256 lo:(-3 : Rat)/256 q:-21/2048 hi:(-1 : Rat)/128 hi':(-5 : Rat)/512
---
lo':(-5 : Rat)/512 lo:(-3 : Rat)/256 q:-5/512 hi:(-1 : Rat)/128 hi':(-5 : Rat)/512
---
lo':(-5 : Rat)/512 lo:(-3 : Rat)/256 q:-19/2048 hi:(-1 : Rat)/128 hi':(-1 : Rat)/128
---
lo':(-5 : Rat)/512 lo:(-3 : Rat)/256 q:-9/1024 hi:(-1 : Rat)/128 hi':(-1 : Rat)/128
---
lo':(-5 : Rat)/512 lo:(-3 : Rat)/256 q:-17/2048 hi:(-1 : Rat)/128 hi':(-1 : Rat)/128
---
lo':(-1 : Rat)/128 lo:(-1 : Rat)/128 q:-1/128 hi:(-1 : Rat)/128 hi':(-1 : Rat)/128
---
lo':(-1 : Rat)/128 lo:(-1 : Rat)/128 q:-15/2048 hi:(-1 : Rat)/256 hi':(-3 : Rat)/512
---
lo':(-1 : Rat)/128 lo:(-1 : Rat)/128 q:-7/1024 hi:(-1 : Rat)/256 hi':(-3 : Rat)/512
---
lo':(-1 : Rat)/128 lo:(-1 : Rat)/128 q:-13/2048 hi:(-1 : Rat)/256 hi':(-3 : Rat)/512
---
lo':(-3 : Rat)/512 lo:(-1 : Rat)/128 q:-3/512 hi:(-1 : Rat)/256 hi':(-3 : Rat)/512
---
lo':(-3 : Rat)/512 lo:(-1 : Rat)/128 q:-11/2048 hi:(-1 : Rat)/256 hi':(-1 : Rat)/256
---
lo':(-3 : Rat)/512 lo:(-1 : Rat)/128 q:-5/1024 hi:(-1 : Rat)/256 hi':(-1 : Rat)/256
---
lo':(-3 : Rat)/512 lo:(-1 : Rat)/128 q:-9/2048 hi:(-1 : Rat)/256 hi':(-1 : Rat)/256
---
lo':(-1 : Rat)/256 lo:(-1 : Rat)/256 q:-1/256 hi:(-1 : Rat)/256 hi':(-1 : Rat)/256
---
lo':(-1 : Rat)/256 lo:(-1 : Rat)/256 q:-7/2048 hi:0 hi':(-1 : Rat)/512
---
lo':(-1 : Rat)/256 lo:(-1 : Rat)/256 q:-3/1024 hi:0 hi':(-1 : Rat)/512
---
lo':(-1 : Rat)/256 lo:(-1 : Rat)/256 q:-5/2048 hi:0 hi':(-1 : Rat)/512
---
lo':(-1 : Rat)/512 lo:(-1 : Rat)/256 q:-1/512 hi:0 hi':(-1 : Rat)/512
---
lo':(-1 : Rat)/512 lo:(-1 : Rat)/256 q:-3/2048 hi:0 hi':0
---
lo':(-1 : Rat)/512 lo:(-1 : Rat)/256 q:-1/1024 hi:0 hi':0
---
lo':(-1 : Rat)/512 lo:(-1 : Rat)/256 q:-1/2048 hi:0 hi':0
---
lo':0 lo:0 q:0 hi:0 hi':0
---
lo':0 lo:0 q:0 hi:0 hi':0
---
lo':0 lo:0 q:1/2048 hi:(1 : Rat)/256 hi':(1 : Rat)/512
---
lo':0 lo:0 q:1/1024 hi:(1 : Rat)/256 hi':(1 : Rat)/512
---
lo':0 lo:0 q:3/2048 hi:(1 : Rat)/256 hi':(1 : Rat)/512
---
lo':(1 : Rat)/512 lo:0 q:1/512 hi:(1 : Rat)/256 hi':(1 : Rat)/512
---
lo':(1 : Rat)/512 lo:0 q:5/2048 hi:(1 : Rat)/256 hi':(1 : Rat)/256
---
lo':(1 : Rat)/512 lo:0 q:3/1024 hi:(1 : Rat)/256 hi':(1 : Rat)/256
---
lo':(1 : Rat)/512 lo:0 q:7/2048 hi:(1 : Rat)/256 hi':(1 : Rat)/256
---
lo':(1 : Rat)/256 lo:(1 : Rat)/256 q:1/256 hi:(1 : Rat)/256 hi':(1 : Rat)/256
---
lo':(1 : Rat)/256 lo:(1 : Rat)/256 q:9/2048 hi:(1 : Rat)/128 hi':(3 : Rat)/512
---
lo':(1 : Rat)/256 lo:(1 : Rat)/256 q:5/1024 hi:(1 : Rat)/128 hi':(3 : Rat)/512
---
lo':(1 : Rat)/256 lo:(1 : Rat)/256 q:11/2048 hi:(1 : Rat)/128 hi':(3 : Rat)/512
---
lo':(3 : Rat)/512 lo:(1 : Rat)/256 q:3/512 hi:(1 : Rat)/128 hi':(3 : Rat)/512
---
lo':(3 : Rat)/512 lo:(1 : Rat)/256 q:13/2048 hi:(1 : Rat)/128 hi':(1 : Rat)/128
---
lo':(3 : Rat)/512 lo:(1 : Rat)/256 q:7/1024 hi:(1 : Rat)/128 hi':(1 : Rat)/128
---
lo':(3 : Rat)/512 lo:(1 : Rat)/256 q:15/2048 hi:(1 : Rat)/128 hi':(1 : Rat)/128
---
lo':(1 : Rat)/128 lo:(1 : Rat)/128 q:1/128 hi:(1 : Rat)/128 hi':(1 : Rat)/128
---
lo':(1 : Rat)/128 lo:(1 : Rat)/128 q:17/2048 hi:(3 : Rat)/256 hi':(5 : Rat)/512
---
lo':(1 : Rat)/128 lo:(1 : Rat)/128 q:9/1024 hi:(3 : Rat)/256 hi':(5 : Rat)/512
---
lo':(1 : Rat)/128 lo:(1 : Rat)/128 q:19/2048 hi:(3 : Rat)/256 hi':(5 : Rat)/512
---
lo':(5 : Rat)/512 lo:(1 : Rat)/128 q:5/512 hi:(3 : Rat)/256 hi':(5 : Rat)/512
---
lo':(5 : Rat)/512 lo:(1 : Rat)/128 q:21/2048 hi:(3 : Rat)/256 hi':(3 : Rat)/256
---
lo':(5 : Rat)/512 lo:(1 : Rat)/128 q:11/1024 hi:(3 : Rat)/256 hi':(3 : Rat)/256
---
lo':(5 : Rat)/512 lo:(1 : Rat)/128 q:23/2048 hi:(3 : Rat)/256 hi':(3 : Rat)/256
---
lo':(3 : Rat)/256 lo:(3 : Rat)/256 q:3/256 hi:(3 : Rat)/256 hi':(3 : Rat)/256
---
lo':(3 : Rat)/256 lo:(3 : Rat)/256 q:25/2048 hi:(1 : Rat)/64 hi':(7 : Rat)/512
---
lo':(3 : Rat)/256 lo:(3 : Rat)/256 q:13/1024 hi:(1 : Rat)/64 hi':(7 : Rat)/512
---
lo':(3 : Rat)/256 lo:(3 : Rat)/256 q:27/2048 hi:(1 : Rat)/64 hi':(7 : Rat)/512
---
lo':(7 : Rat)/512 lo:(3 : Rat)/256 q:7/512 hi:(1 : Rat)/64 hi':(7 : Rat)/512
---
lo':(7 : Rat)/512 lo:(3 : Rat)/256 q:29/2048 hi:(1 : Rat)/64 hi':(1 : Rat)/64
---
lo':(7 : Rat)/512 lo:(3 : Rat)/256 q:15/1024 hi:(1 : Rat)/64 hi':(1 : Rat)/64
---
lo':(7 : Rat)/512 lo:(3 : Rat)/256 q:31/2048 hi:(1 : Rat)/64 hi':(1 : Rat)/64
---
lo':(1 : Rat)/64 lo:(1 : Rat)/64 q:1/64 hi:(1 : Rat)/64 hi':(1 : Rat)/64
---
lo':(1 : Rat)/64 lo:(1 : Rat)/64 q:33/2048 hi:(5 : Rat)/256 hi':(9 : Rat)/512
---
lo':(1 : Rat)/64 lo:(1 : Rat)/64 q:17/1024 hi:(5 : Rat)/256 hi':(9 : Rat)/512
---
lo':(1 : Rat)/64 lo:(1 : Rat)/64 q:35/2048 hi:(5 : Rat)/256 hi':(9 : Rat)/512
---
lo':(9 : Rat)/512 lo:(1 : Rat)/64 q:9/512 hi:(5 : Rat)/256 hi':(9 : Rat)/512
---
lo':(9 : Rat)/512 lo:(1 : Rat)/64 q:37/2048 hi:(5 : Rat)/256 hi':(5 : Rat)/256
---
lo':(9 : Rat)/512 lo:(1 : Rat)/64 q:19/1024 hi:(5 : Rat)/256 hi':(5 : Rat)/256
---
lo':(9 : Rat)/512 lo:(1 : Rat)/64 q:39/2048 hi:(5 : Rat)/256 hi':(5 : Rat)/256
---
lo':(5 : Rat)/256 lo:(5 : Rat)/256 q:5/256 hi:(5 : Rat)/256 hi':(5 : Rat)/256
---
lo':(5 : Rat)/256 lo:(5 : Rat)/256 q:41/2048 hi:(3 : Rat)/128 hi':(11 : Rat)/512
---
lo':(5 : Rat)/256 lo:(5 : Rat)/256 q:21/1024 hi:(3 : Rat)/128 hi':(11 : Rat)/512
---
lo':(5 : Rat)/256 lo:(5 : Rat)/256 q:43/2048 hi:(3 : Rat)/128 hi':(11 : Rat)/512
---
lo':(11 : Rat)/512 lo:(5 : Rat)/256 q:11/512 hi:(3 : Rat)/128 hi':(11 : Rat)/512
---
lo':(11 : Rat)/512 lo:(5 : Rat)/256 q:45/2048 hi:(3 : Rat)/128 hi':(3 : Rat)/128
---
lo':(11 : Rat)/512 lo:(5 : Rat)/256 q:23/1024 hi:(3 : Rat)/128 hi':(3 : Rat)/128
---
lo':(11 : Rat)/512 lo:(5 : Rat)/256 q:47/2048 hi:(3 : Rat)/128 hi':(3 : Rat)/128
---
lo':(3 : Rat)/128 lo:(3 : Rat)/128 q:3/128 hi:(3 : Rat)/128 hi':(3 : Rat)/128
---
lo':(3 : Rat)/128 lo:(3 : Rat)/128 q:49/2048 hi:(7 : Rat)/256 hi':(13 : Rat)/512
---
lo':(3 : Rat)/128 lo:(3 : Rat)/128 q:25/1024 hi:(7 : Rat)/256 hi':(13 : Rat)/512
---
lo':(3 : Rat)/128 lo:(3 : Rat)/128 q:51/2048 hi:(7 : Rat)/256 hi':(13 : Rat)/512
---
lo':(13 : Rat)/512 lo:(3 : Rat)/128 q:13/512 hi:(7 : Rat)/256 hi':(13 : Rat)/512
---
lo':(13 : Rat)/512 lo:(3 : Rat)/128 q:53/2048 hi:(7 : Rat)/256 hi':(7 : Rat)/256
---
lo':(13 : Rat)/512 lo:(3 : Rat)/128 q:27/1024 hi:(7 : Rat)/256 hi':(7 : Rat)/256
---
lo':(13 : Rat)/512 lo:(3 : Rat)/128 q:55/2048 hi:(7 : Rat)/256 hi':(7 : Rat)/256
---
lo':(7 : Rat)/256 lo:(7 : Rat)/256 q:7/256 hi:(7 : Rat)/256 hi':(7 : Rat)/256
---
lo':(7 : Rat)/256 lo:(7 : Rat)/256 q:57/2048 hi:(1 : Rat)/32 hi':(15 : Rat)/512
---
lo':(7 : Rat)/256 lo:(7 : Rat)/256 q:29/1024 hi:(1 : Rat)/32 hi':(15 : Rat)/512
---
lo':(7 : Rat)/256 lo:(7 : Rat)/256 q:59/2048 hi:(1 : Rat)/32 hi':(15 : Rat)/512
---
lo':(15 : Rat)/512 lo:(7 : Rat)/256 q:15/512 hi:(1 : Rat)/32 hi':(15 : Rat)/512
---
lo':(15 : Rat)/512 lo:(7 : Rat)/256 q:61/2048 hi:(1 : Rat)/32 hi':(1 : Rat)/32
---
lo':(15 : Rat)/512 lo:(7 : Rat)/256 q:31/1024 hi:(1 : Rat)/32 hi':(1 : Rat)/32
---
lo':(15 : Rat)/512 lo:(7 : Rat)/256 q:63/2048 hi:(1 : Rat)/32 hi':(1 : Rat)/32
---
lo':(1 : Rat)/32 lo:(1 : Rat)/32 q:1/32 hi:(1 : Rat)/32 hi':(1 : Rat)/32
---
lo':(1 : Rat)/32 lo:(1 : Rat)/32 q:33/1024 hi:(5 : Rat)/128 hi':(9 : Rat)/256
---
lo':(1 : Rat)/32 lo:(1 : Rat)/32 q:17/512 hi:(5 : Rat)/128 hi':(9 : Rat)/256
---
lo':(1 : Rat)/32 lo:(1 : Rat)/32 q:35/1024 hi:(5 : Rat)/128 hi':(9 : Rat)/256
---
lo':(9 : Rat)/256 lo:(1 : Rat)/32 q:9/256 hi:(5 : Rat)/128 hi':(9 : Rat)/256
---
lo':(9 : Rat)/256 lo:(1 : Rat)/32 q:37/1024 hi:(5 : Rat)/128 hi':(5 : Rat)/128
---
lo':(9 : Rat)/256 lo:(1 : Rat)/32 q:19/512 hi:(5 : Rat)/128 hi':(5 : Rat)/128
---
lo':(9 : Rat)/256 lo:(1 : Rat)/32 q:39/1024 hi:(5 : Rat)/128 hi':(5 : Rat)/128
---
lo':(5 : Rat)/128 lo:(5 : Rat)/128 q:5/128 hi:(5 : Rat)/128 hi':(5 : Rat)/128
---
lo':(5 : Rat)/128 lo:(5 : Rat)/128 q:41/1024 hi:(3 : Rat)/64 hi':(11 : Rat)/256
---
lo':(5 : Rat)/128 lo:(5 : Rat)/128 q:21/512 hi:(3 : Rat)/64 hi':(11 : Rat)/256
---
lo':(5 : Rat)/128 lo:(5 : Rat)/128 q:43/1024 hi:(3 : Rat)/64 hi':(11 : Rat)/256
---
lo':(11 : Rat)/256 lo:(5 : Rat)/128 q:11/256 hi:(3 : Rat)/64 hi':(11 : Rat)/256
---
lo':(11 : Rat)/256 lo:(5 : Rat)/128 q:45/1024 hi:(3 : Rat)/64 hi':(3 : Rat)/64
---
lo':(11 : Rat)/256 lo:(5 : Rat)/128 q:23/512 hi:(3 : Rat)/64 hi':(3 : Rat)/64
---
lo':(11 : Rat)/256 lo:(5 : Rat)/128 q:47/1024 hi:(3 : Rat)/64 hi':(3 : Rat)/64
---
lo':(3 : Rat)/64 lo:(3 : Rat)/64 q:3/64 hi:(3 : Rat)/64 hi':(3 : Rat)/64
---
lo':(3 : Rat)/64 lo:(3 : Rat)/64 q:49/1024 hi:(7 : Rat)/128 hi':(13 : Rat)/256
---
lo':(3 : Rat)/64 lo:(3 : Rat)/64 q:25/512 hi:(7 : Rat)/128 hi':(13 : Rat)/256
---
lo':(3 : Rat)/64 lo:(3 : Rat)/64 q:51/1024 hi:(7 : Rat)/128 hi':(13 : Rat)/256
---
lo':(13 : Rat)/256 lo:(3 : Rat)/64 q:13/256 hi:(7 : Rat)/128 hi':(13 : Rat)/256
---
lo':(13 : Rat)/256 lo:(3 : Rat)/64 q:53/1024 hi:(7 : Rat)/128 hi':(7 : Rat)/128
---
lo':(13 : Rat)/256 lo:(3 : Rat)/64 q:27/512 hi:(7 : Rat)/128 hi':(7 : Rat)/128
---
lo':(13 : Rat)/256 lo:(3 : Rat)/64 q:55/1024 hi:(7 : Rat)/128 hi':(7 : Rat)/128
---
lo':(7 : Rat)/128 lo:(7 : Rat)/128 q:7/128 hi:(7 : Rat)/128 hi':(7 : Rat)/128
---
lo':(7 : Rat)/128 lo:(7 : Rat)/128 q:57/1024 hi:(1 : Rat)/16 hi':(15 : Rat)/256
---
lo':(7 : Rat)/128 lo:(7 : Rat)/128 q:29/512 hi:(1 : Rat)/16 hi':(15 : Rat)/256
---
lo':(7 : Rat)/128 lo:(7 : Rat)/128 q:59/1024 hi:(1 : Rat)/16 hi':(15 : Rat)/256
---
lo':(15 : Rat)/256 lo:(7 : Rat)/128 q:15/256 hi:(1 : Rat)/16 hi':(15 : Rat)/256
---
lo':(15 : Rat)/256 lo:(7 : Rat)/128 q:61/1024 hi:(1 : Rat)/16 hi':(1 : Rat)/16
---
lo':(15 : Rat)/256 lo:(7 : Rat)/128 q:31/512 hi:(1 : Rat)/16 hi':(1 : Rat)/16
---
lo':(15 : Rat)/256 lo:(7 : Rat)/128 q:63/1024 hi:(1 : Rat)/16 hi':(1 : Rat)/16
---
lo':(1 : Rat)/16 lo:(1 : Rat)/16 q:1/16 hi:(1 : Rat)/16 hi':(1 : Rat)/16
---
lo':(1 : Rat)/16 lo:(1 : Rat)/16 q:33/512 hi:(5 : Rat)/64 hi':(9 : Rat)/128
---
lo':(1 : Rat)/16 lo:(1 : Rat)/16 q:17/256 hi:(5 : Rat)/64 hi':(9 : Rat)/128
---
lo':(1 : Rat)/16 lo:(1 : Rat)/16 q:35/512 hi:(5 : Rat)/64 hi':(9 : Rat)/128
---
lo':(9 : Rat)/128 lo:(1 : Rat)/16 q:9/128 hi:(5 : Rat)/64 hi':(9 : Rat)/128
---
lo':(9 : Rat)/128 lo:(1 : Rat)/16 q:37/512 hi:(5 : Rat)/64 hi':(5 : Rat)/64
---
lo':(9 : Rat)/128 lo:(1 : Rat)/16 q:19/256 hi:(5 : Rat)/64 hi':(5 : Rat)/64
---
lo':(9 : Rat)/128 lo:(1 : Rat)/16 q:39/512 hi:(5 : Rat)/64 hi':(5 : Rat)/64
---
lo':(5 : Rat)/64 lo:(5 : Rat)/64 q:5/64 hi:(5 : Rat)/64 hi':(5 : Rat)/64
---
lo':(5 : Rat)/64 lo:(5 : Rat)/64 q:41/512 hi:(3 : Rat)/32 hi':(11 : Rat)/128
---
lo':(5 : Rat)/64 lo:(5 : Rat)/64 q:21/256 hi:(3 : Rat)/32 hi':(11 : Rat)/128
---
lo':(5 : Rat)/64 lo:(5 : Rat)/64 q:43/512 hi:(3 : Rat)/32 hi':(11 : Rat)/128
---
lo':(11 : Rat)/128 lo:(5 : Rat)/64 q:11/128 hi:(3 : Rat)/32 hi':(11 : Rat)/128
---
lo':(11 : Rat)/128 lo:(5 : Rat)/64 q:45/512 hi:(3 : Rat)/32 hi':(3 : Rat)/32
---
lo':(11 : Rat)/128 lo:(5 : Rat)/64 q:23/256 hi:(3 : Rat)/32 hi':(3 : Rat)/32
---
lo':(11 : Rat)/128 lo:(5 : Rat)/64 q:47/512 hi:(3 : Rat)/32 hi':(3 : Rat)/32
---
lo':(3 : Rat)/32 lo:(3 : Rat)/32 q:3/32 hi:(3 : Rat)/32 hi':(3 : Rat)/32
---
lo':(3 : Rat)/32 lo:(3 : Rat)/32 q:49/512 hi:(7 : Rat)/64 hi':(13 : Rat)/128
---
lo':(3 : Rat)/32 lo:(3 : Rat)/32 q:25/256 hi:(7 : Rat)/64 hi':(13 : Rat)/128
---
lo':(3 : Rat)/32 lo:(3 : Rat)/32 q:51/512 hi:(7 : Rat)/64 hi':(13 : Rat)/128
---
lo':(13 : Rat)/128 lo:(3 : Rat)/32 q:13/128 hi:(7 : Rat)/64 hi':(13 : Rat)/128
---
lo':(13 : Rat)/128 lo:(3 : Rat)/32 q:53/512 hi:(7 : Rat)/64 hi':(7 : Rat)/64
---
lo':(13 : Rat)/128 lo:(3 : Rat)/32 q:27/256 hi:(7 : Rat)/64 hi':(7 : Rat)/64
---
lo':(13 : Rat)/128 lo:(3 : Rat)/32 q:55/512 hi:(7 : Rat)/64 hi':(7 : Rat)/64
---
lo':(7 : Rat)/64 lo:(7 : Rat)/64 q:7/64 hi:(7 : Rat)/64 hi':(7 : Rat)/64
---
lo':(7 : Rat)/64 lo:(7 : Rat)/64 q:57/512 hi:(1 : Rat)/8 hi':(15 : Rat)/128
---
lo':(7 : Rat)/64 lo:(7 : Rat)/64 q:29/256 hi:(1 : Rat)/8 hi':(15 : Rat)/128
---
lo':(7 : Rat)/64 lo:(7 : Rat)/64 q:59/512 hi:(1 : Rat)/8 hi':(15 : Rat)/128
---
lo':(15 : Rat)/128 lo:(7 : Rat)/64 q:15/128 hi:(1 : Rat)/8 hi':(15 : Rat)/128
---
lo':(15 : Rat)/128 lo:(7 : Rat)/64 q:61/512 hi:(1 : Rat)/8 hi':(1 : Rat)/8
---
lo':(15 : Rat)/128 lo:(7 : Rat)/64 q:31/256 hi:(1 : Rat)/8 hi':(1 : Rat)/8
---
lo':(15 : Rat)/128 lo:(7 : Rat)/64 q:63/512 hi:(1 : Rat)/8 hi':(1 : Rat)/8
---
lo':(1 : Rat)/8 lo:(1 : Rat)/8 q:1/8 hi:(1 : Rat)/8 hi':(1 : Rat)/8
---
lo':(1 : Rat)/8 lo:(1 : Rat)/8 q:33/256 hi:(5 : Rat)/32 hi':(9 : Rat)/64
---
lo':(1 : Rat)/8 lo:(1 : Rat)/8 q:17/128 hi:(5 : Rat)/32 hi':(9 : Rat)/64
---
lo':(1 : Rat)/8 lo:(1 : Rat)/8 q:35/256 hi:(5 : Rat)/32 hi':(9 : Rat)/64
---
lo':(9 : Rat)/64 lo:(1 : Rat)/8 q:9/64 hi:(5 : Rat)/32 hi':(9 : Rat)/64
---
lo':(9 : Rat)/64 lo:(1 : Rat)/8 q:37/256 hi:(5 : Rat)/32 hi':(5 : Rat)/32
---
lo':(9 : Rat)/64 lo:(1 : Rat)/8 q:19/128 hi:(5 : Rat)/32 hi':(5 : Rat)/32
---
lo':(9 : Rat)/64 lo:(1 : Rat)/8 q:39/256 hi:(5 : Rat)/32 hi':(5 : Rat)/32
---
lo':(5 : Rat)/32 lo:(5 : Rat)/32 q:5/32 hi:(5 : Rat)/32 hi':(5 : Rat)/32
---
lo':(5 : Rat)/32 lo:(5 : Rat)/32 q:41/256 hi:(3 : Rat)/16 hi':(11 : Rat)/64
---
lo':(5 : Rat)/32 lo:(5 : Rat)/32 q:21/128 hi:(3 : Rat)/16 hi':(11 : Rat)/64
---
lo':(5 : Rat)/32 lo:(5 : Rat)/32 q:43/256 hi:(3 : Rat)/16 hi':(11 : Rat)/64
---
lo':(11 : Rat)/64 lo:(5 : Rat)/32 q:11/64 hi:(3 : Rat)/16 hi':(11 : Rat)/64
---
lo':(11 : Rat)/64 lo:(5 : Rat)/32 q:45/256 hi:(3 : Rat)/16 hi':(3 : Rat)/16
---
lo':(11 : Rat)/64 lo:(5 : Rat)/32 q:23/128 hi:(3 : Rat)/16 hi':(3 : Rat)/16
---
lo':(11 : Rat)/64 lo:(5 : Rat)/32 q:47/256 hi:(3 : Rat)/16 hi':(3 : Rat)/16
---
lo':(3 : Rat)/16 lo:(3 : Rat)/16 q:3/16 hi:(3 : Rat)/16 hi':(3 : Rat)/16
---
lo':(3 : Rat)/16 lo:(3 : Rat)/16 q:49/256 hi:(7 : Rat)/32 hi':(13 : Rat)/64
---
lo':(3 : Rat)/16 lo:(3 : Rat)/16 q:25/128 hi:(7 : Rat)/32 hi':(13 : Rat)/64
---
lo':(3 : Rat)/16 lo:(3 : Rat)/16 q:51/256 hi:(7 : Rat)/32 hi':(13 : Rat)/64
---
lo':(13 : Rat)/64 lo:(3 : Rat)/16 q:13/64 hi:(7 : Rat)/32 hi':(13 : Rat)/64
---
lo':(13 : Rat)/64 lo:(3 : Rat)/16 q:53/256 hi:(7 : Rat)/32 hi':(7 : Rat)/32
---
lo':(13 : Rat)/64 lo:(3 : Rat)/16 q:27/128 hi:(7 : Rat)/32 hi':(7 : Rat)/32
---
lo':(13 : Rat)/64 lo:(3 : Rat)/16 q:55/256 hi:(7 : Rat)/32 hi':(7 : Rat)/32
---
lo':(7 : Rat)/32 lo:(7 : Rat)/32 q:7/32 hi:(7 : Rat)/32 hi':(7 : Rat)/32
---
lo':(7 : Rat)/32 lo:(7 : Rat)/32 q:57/256 hi:(1 : Rat)/4 hi':(15 : Rat)/64
---
lo':(7 : Rat)/32 lo:(7 : Rat)/32 q:29/128 hi:(1 : Rat)/4 hi':(15 : Rat)/64
---
lo':(7 : Rat)/32 lo:(7 : Rat)/32 q:59/256 hi:(1 : Rat)/4 hi':(15 : Rat)/64
---
lo':(15 : Rat)/64 lo:(7 : Rat)/32 q:15/64 hi:(1 : Rat)/4 hi':(15 : Rat)/64
---
lo':(15 : Rat)/64 lo:(7 : Rat)/32 q:61/256 hi:(1 : Rat)/4 hi':(1 : Rat)/4
---
lo':(15 : Rat)/64 lo:(7 : Rat)/32 q:31/128 hi:(1 : Rat)/4 hi':(1 : Rat)/4
---
lo':(15 : Rat)/64 lo:(7 : Rat)/32 q:63/256 hi:(1 : Rat)/4 hi':(1 : Rat)/4
---
lo':(1 : Rat)/4 lo:(1 : Rat)/4 q:1/4 hi:(1 : Rat)/4 hi':(1 : Rat)/4
---
lo':(1 : Rat)/4 lo:(1 : Rat)/4 q:33/128 hi:(5 : Rat)/16 hi':(9 : Rat)/32
---
lo':(1 : Rat)/4 lo:(1 : Rat)/4 q:17/64 hi:(5 : Rat)/16 hi':(9 : Rat)/32
---
lo':(1 : Rat)/4 lo:(1 : Rat)/4 q:35/128 hi:(5 : Rat)/16 hi':(9 : Rat)/32
---
lo':(9 : Rat)/32 lo:(1 : Rat)/4 q:9/32 hi:(5 : Rat)/16 hi':(9 : Rat)/32
---
lo':(9 : Rat)/32 lo:(1 : Rat)/4 q:37/128 hi:(5 : Rat)/16 hi':(5 : Rat)/16
---
lo':(9 : Rat)/32 lo:(1 : Rat)/4 q:19/64 hi:(5 : Rat)/16 hi':(5 : Rat)/16
---
lo':(9 : Rat)/32 lo:(1 : Rat)/4 q:39/128 hi:(5 : Rat)/16 hi':(5 : Rat)/16
---
lo':(5 : Rat)/16 lo:(5 : Rat)/16 q:5/16 hi:(5 : Rat)/16 hi':(5 : Rat)/16
---
lo':(5 : Rat)/16 lo:(5 : Rat)/16 q:41/128 hi:(3 : Rat)/8 hi':(11 : Rat)/32
---
lo':(5 : Rat)/16 lo:(5 : Rat)/16 q:21/64 hi:(3 : Rat)/8 hi':(11 : Rat)/32
---
lo':(5 : Rat)/16 lo:(5 : Rat)/16 q:43/128 hi:(3 : Rat)/8 hi':(11 : Rat)/32
---
lo':(11 : Rat)/32 lo:(5 : Rat)/16 q:11/32 hi:(3 : Rat)/8 hi':(11 : Rat)/32
---
lo':(11 : Rat)/32 lo:(5 : Rat)/16 q:45/128 hi:(3 : Rat)/8 hi':(3 : Rat)/8
---
lo':(11 : Rat)/32 lo:(5 : Rat)/16 q:23/64 hi:(3 : Rat)/8 hi':(3 : Rat)/8
---
lo':(11 : Rat)/32 lo:(5 : Rat)/16 q:47/128 hi:(3 : Rat)/8 hi':(3 : Rat)/8
---
lo':(3 : Rat)/8 lo:(3 : Rat)/8 q:3/8 hi:(3 : Rat)/8 hi':(3 : Rat)/8
---
lo':(3 : Rat)/8 lo:(3 : Rat)/8 q:49/128 hi:(7 : Rat)/16 hi':(13 : Rat)/32
---
lo':(3 : Rat)/8 lo:(3 : Rat)/8 q:25/64 hi:(7 : Rat)/16 hi':(13 : Rat)/32
---
lo':(3 : Rat)/8 lo:(3 : Rat)/8 q:51/128 hi:(7 : Rat)/16 hi':(13 : Rat)/32
---
lo':(13 : Rat)/32 lo:(3 : Rat)/8 q:13/32 hi:(7 : Rat)/16 hi':(13 : Rat)/32
---
lo':(13 : Rat)/32 lo:(3 : Rat)/8 q:53/128 hi:(7 : Rat)/16 hi':(7 : Rat)/16
---
lo':(13 : Rat)/32 lo:(3 : Rat)/8 q:27/64 hi:(7 : Rat)/16 hi':(7 : Rat)/16
---
lo':(13 : Rat)/32 lo:(3 : Rat)/8 q:55/128 hi:(7 : Rat)/16 hi':(7 : Rat)/16
---
lo':(7 : Rat)/16 lo:(7 : Rat)/16 q:7/16 hi:(7 : Rat)/16 hi':(7 : Rat)/16
---
lo':(7 : Rat)/16 lo:(7 : Rat)/16 q:57/128 hi:(1 : Rat)/2 hi':(15 : Rat)/32
---
lo':(7 : Rat)/16 lo:(7 : Rat)/16 q:29/64 hi:(1 : Rat)/2 hi':(15 : Rat)/32
---
lo':(7 : Rat)/16 lo:(7 : Rat)/16 q:59/128 hi:(1 : Rat)/2 hi':(15 : Rat)/32
---
lo':(15 : Rat)/32 lo:(7 : Rat)/16 q:15/32 hi:(1 : Rat)/2 hi':(15 : Rat)/32
---
lo':(15 : Rat)/32 lo:(7 : Rat)/16 q:61/128 hi:(1 : Rat)/2 hi':(1 : Rat)/2
---
lo':(15 : Rat)/32 lo:(7 : Rat)/16 q:31/64 hi:(1 : Rat)/2 hi':(1 : Rat)/2
---
lo':(15 : Rat)/32 lo:(7 : Rat)/16 q:63/128 hi:(1 : Rat)/2 hi':(1 : Rat)/2
---
lo':(1 : Rat)/2 lo:(1 : Rat)/2 q:1/2 hi:(1 : Rat)/2 hi':(1 : Rat)/2
---
lo':(1 : Rat)/2 lo:(1 : Rat)/2 q:33/64 hi:(5 : Rat)/8 hi':(9 : Rat)/16
---
lo':(1 : Rat)/2 lo:(1 : Rat)/2 q:17/32 hi:(5 : Rat)/8 hi':(9 : Rat)/16
---
lo':(1 : Rat)/2 lo:(1 : Rat)/2 q:35/64 hi:(5 : Rat)/8 hi':(9 : Rat)/16
---
lo':(9 : Rat)/16 lo:(1 : Rat)/2 q:9/16 hi:(5 : Rat)/8 hi':(9 : Rat)/16
---
lo':(9 : Rat)/16 lo:(1 : Rat)/2 q:37/64 hi:(5 : Rat)/8 hi':(5 : Rat)/8
---
lo':(9 : Rat)/16 lo:(1 : Rat)/2 q:19/32 hi:(5 : Rat)/8 hi':(5 : Rat)/8
---
lo':(9 : Rat)/16 lo:(1 : Rat)/2 q:39/64 hi:(5 : Rat)/8 hi':(5 : Rat)/8
---
lo':(5 : Rat)/8 lo:(5 : Rat)/8 q:5/8 hi:(5 : Rat)/8 hi':(5 : Rat)/8
---
lo':(5 : Rat)/8 lo:(5 : Rat)/8 q:41/64 hi:(3 : Rat)/4 hi':(11 : Rat)/16
---
lo':(5 : Rat)/8 lo:(5 : Rat)/8 q:21/32 hi:(3 : Rat)/4 hi':(11 : Rat)/16
---
lo':(5 : Rat)/8 lo:(5 : Rat)/8 q:43/64 hi:(3 : Rat)/4 hi':(11 : Rat)/16
---
lo':(11 : Rat)/16 lo:(5 : Rat)/8 q:11/16 hi:(3 : Rat)/4 hi':(11 : Rat)/16
---
lo':(11 : Rat)/16 lo:(5 : Rat)/8 q:45/64 hi:(3 : Rat)/4 hi':(3 : Rat)/4
---
lo':(11 : Rat)/16 lo:(5 : Rat)/8 q:23/32 hi:(3 : Rat)/4 hi':(3 : Rat)/4
---
lo':(11 : Rat)/16 lo:(5 : Rat)/8 q:47/64 hi:(3 : Rat)/4 hi':(3 : Rat)/4
---
lo':(3 : Rat)/4 lo:(3 : Rat)/4 q:3/4 hi:(3 : Rat)/4 hi':(3 : Rat)/4
---
lo':(3 : Rat)/4 lo:(3 : Rat)/4 q:49/64 hi:(7 : Rat)/8 hi':(13 : Rat)/16
---
lo':(3 : Rat)/4 lo:(3 : Rat)/4 q:25/32 hi:(7 : Rat)/8 hi':(13 : Rat)/16
---
lo':(3 : Rat)/4 lo:(3 : Rat)/4 q:51/64 hi:(7 : Rat)/8 hi':(13 : Rat)/16
---
lo':(13 : Rat)/16 lo:(3 : Rat)/4 q:13/16 hi:(7 : Rat)/8 hi':(13 : Rat)/16
---
lo':(13 : Rat)/16 lo:(3 : Rat)/4 q:53/64 hi:(7 : Rat)/8 hi':(7 : Rat)/8
---
lo':(13 : Rat)/16 lo:(3 : Rat)/4 q:27/32 hi:(7 : Rat)/8 hi':(7 : Rat)/8
---
lo':(13 : Rat)/16 lo:(3 : Rat)/4 q:55/64 hi:(7 : Rat)/8 hi':(7 : Rat)/8
---
lo':(7 : Rat)/8 lo:(7 : Rat)/8 q:7/8 hi:(7 : Rat)/8 hi':(7 : Rat)/8
---
lo':(7 : Rat)/8 lo:(7 : Rat)/8 q:57/64 hi:1 hi':(15 : Rat)/16
---
lo':(7 : Rat)/8 lo:(7 : Rat)/8 q:29/32 hi:1 hi':(15 : Rat)/16
---
lo':(7 : Rat)/8 lo:(7 : Rat)/8 q:59/64 hi:1 hi':(15 : Rat)/16
---
lo':(15 : Rat)/16 lo:(7 : Rat)/8 q:15/16 hi:1 hi':(15 : Rat)/16
---
lo':(15 : Rat)/16 lo:(7 : Rat)/8 q:61/64 hi:1 hi':1
---
lo':(15 : Rat)/16 lo:(7 : Rat)/8 q:31/32 hi:1 hi':1
---
lo':(15 : Rat)/16 lo:(7 : Rat)/8 q:63/64 hi:1 hi':1
---
lo':1 lo:1 q:1 hi:1 hi':1
---
lo':1 lo:1 q:33/32 hi:(5 : Rat)/4 hi':(9 : Rat)/8
---
lo':1 lo:1 q:17/16 hi:(5 : Rat)/4 hi':(9 : Rat)/8
---
lo':1 lo:1 q:35/32 hi:(5 : Rat)/4 hi':(9 : Rat)/8
---
lo':(9 : Rat)/8 lo:1 q:9/8 hi:(5 : Rat)/4 hi':(9 : Rat)/8
---
lo':(9 : Rat)/8 lo:1 q:37/32 hi:(5 : Rat)/4 hi':(5 : Rat)/4
---
lo':(9 : Rat)/8 lo:1 q:19/16 hi:(5 : Rat)/4 hi':(5 : Rat)/4
---
lo':(9 : Rat)/8 lo:1 q:39/32 hi:(5 : Rat)/4 hi':(5 : Rat)/4
---
lo':(5 : Rat)/4 lo:(5 : Rat)/4 q:5/4 hi:(5 : Rat)/4 hi':(5 : Rat)/4
---
lo':(5 : Rat)/4 lo:(5 : Rat)/4 q:41/32 hi:(3 : Rat)/2 hi':(11 : Rat)/8
---
lo':(5 : Rat)/4 lo:(5 : Rat)/4 q:21/16 hi:(3 : Rat)/2 hi':(11 : Rat)/8
---
lo':(5 : Rat)/4 lo:(5 : Rat)/4 q:43/32 hi:(3 : Rat)/2 hi':(11 : Rat)/8
---
lo':(11 : Rat)/8 lo:(5 : Rat)/4 q:11/8 hi:(3 : Rat)/2 hi':(11 : Rat)/8
---
lo':(11 : Rat)/8 lo:(5 : Rat)/4 q:45/32 hi:(3 : Rat)/2 hi':(3 : Rat)/2
---
lo':(11 : Rat)/8 lo:(5 : Rat)/4 q:23/16 hi:(3 : Rat)/2 hi':(3 : Rat)/2
---
lo':(11 : Rat)/8 lo:(5 : Rat)/4 q:47/32 hi:(3 : Rat)/2 hi':(3 : Rat)/2
---
lo':(3 : Rat)/2 lo:(3 : Rat)/2 q:3/2 hi:(3 : Rat)/2 hi':(3 : Rat)/2
---
lo':(3 : Rat)/2 lo:(3 : Rat)/2 q:49/32 hi:(7 : Rat)/4 hi':(13 : Rat)/8
---
lo':(3 : Rat)/2 lo:(3 : Rat)/2 q:25/16 hi:(7 : Rat)/4 hi':(13 : Rat)/8
---
lo':(3 : Rat)/2 lo:(3 : Rat)/2 q:51/32 hi:(7 : Rat)/4 hi':(13 : Rat)/8
---
lo':(13 : Rat)/8 lo:(3 : Rat)/2 q:13/8 hi:(7 : Rat)/4 hi':(13 : Rat)/8
---
lo':(13 : Rat)/8 lo:(3 : Rat)/2 q:53/32 hi:(7 : Rat)/4 hi':(7 : Rat)/4
---
lo':(13 : Rat)/8 lo:(3 : Rat)/2 q:27/16 hi:(7 : Rat)/4 hi':(7 : Rat)/4
---
lo':(13 : Rat)/8 lo:(3 : Rat)/2 q:55/32 hi:(7 : Rat)/4 hi':(7 : Rat)/4
---
lo':(7 : Rat)/4 lo:(7 : Rat)/4 q:7/4 hi:(7 : Rat)/4 hi':(7 : Rat)/4
---
lo':(7 : Rat)/4 lo:(7 : Rat)/4 q:57/32 hi:2 hi':(15 : Rat)/8
---
lo':(7 : Rat)/4 lo:(7 : Rat)/4 q:29/16 hi:2 hi':(15 : Rat)/8
---
lo':(7 : Rat)/4 lo:(7 : Rat)/4 q:59/32 hi:2 hi':(15 : Rat)/8
---
lo':(15 : Rat)/8 lo:(7 : Rat)/4 q:15/8 hi:2 hi':(15 : Rat)/8
---
lo':(15 : Rat)/8 lo:(7 : Rat)/4 q:61/32 hi:2 hi':2
---
lo':(15 : Rat)/8 lo:(7 : Rat)/4 q:31/16 hi:2 hi':2
---
lo':(15 : Rat)/8 lo:(7 : Rat)/4 q:63/32 hi:2 hi':2
---
lo':2 lo:2 q:2 hi:2 hi':2
---
lo':2 lo:2 q:33/16 hi:(5 : Rat)/2 hi':(9 : Rat)/4
---
lo':2 lo:2 q:17/8 hi:(5 : Rat)/2 hi':(9 : Rat)/4
---
lo':2 lo:2 q:35/16 hi:(5 : Rat)/2 hi':(9 : Rat)/4
---
lo':(9 : Rat)/4 lo:2 q:9/4 hi:(5 : Rat)/2 hi':(9 : Rat)/4
---
lo':(9 : Rat)/4 lo:2 q:37/16 hi:(5 : Rat)/2 hi':(5 : Rat)/2
---
lo':(9 : Rat)/4 lo:2 q:19/8 hi:(5 : Rat)/2 hi':(5 : Rat)/2
---
lo':(9 : Rat)/4 lo:2 q:39/16 hi:(5 : Rat)/2 hi':(5 : Rat)/2
---
lo':(5 : Rat)/2 lo:(5 : Rat)/2 q:5/2 hi:(5 : Rat)/2 hi':(5 : Rat)/2
---
lo':(5 : Rat)/2 lo:(5 : Rat)/2 q:41/16 hi:3 hi':(11 : Rat)/4
---
lo':(5 : Rat)/2 lo:(5 : Rat)/2 q:21/8 hi:3 hi':(11 : Rat)/4
---
lo':(5 : Rat)/2 lo:(5 : Rat)/2 q:43/16 hi:3 hi':(11 : Rat)/4
---
lo':(11 : Rat)/4 lo:(5 : Rat)/2 q:11/4 hi:3 hi':(11 : Rat)/4
---
lo':(11 : Rat)/4 lo:(5 : Rat)/2 q:45/16 hi:3 hi':3
---
lo':(11 : Rat)/4 lo:(5 : Rat)/2 q:23/8 hi:3 hi':3
---
lo':(11 : Rat)/4 lo:(5 : Rat)/2 q:47/16 hi:3 hi':3
---
lo':3 lo:3 q:3 hi:3 hi':3
---
lo':3 lo:3 q:49/16 hi:(7 : Rat)/2 hi':(13 : Rat)/4
---
lo':3 lo:3 q:25/8 hi:(7 : Rat)/2 hi':(13 : Rat)/4
---
lo':3 lo:3 q:51/16 hi:(7 : Rat)/2 hi':(13 : Rat)/4
---
lo':(13 : Rat)/4 lo:3 q:13/4 hi:(7 : Rat)/2 hi':(13 : Rat)/4
---
lo':(13 : Rat)/4 lo:3 q:53/16 hi:(7 : Rat)/2 hi':(7 : Rat)/2
---
lo':(13 : Rat)/4 lo:3 q:27/8 hi:(7 : Rat)/2 hi':(7 : Rat)/2
---
lo':(13 : Rat)/4 lo:3 q:55/16 hi:(7 : Rat)/2 hi':(7 : Rat)/2
---
lo':(7 : Rat)/2 lo:(7 : Rat)/2 q:7/2 hi:(7 : Rat)/2 hi':(7 : Rat)/2
---
lo':(7 : Rat)/2 lo:(7 : Rat)/2 q:57/16 hi:4 hi':(15 : Rat)/4
---
lo':(7 : Rat)/2 lo:(7 : Rat)/2 q:29/8 hi:4 hi':(15 : Rat)/4
---
lo':(7 : Rat)/2 lo:(7 : Rat)/2 q:59/16 hi:4 hi':(15 : Rat)/4
---
lo':(15 : Rat)/4 lo:(7 : Rat)/2 q:15/4 hi:4 hi':(15 : Rat)/4
---
lo':(15 : Rat)/4 lo:(7 : Rat)/2 q:61/16 hi:4 hi':4
---
lo':(15 : Rat)/4 lo:(7 : Rat)/2 q:31/8 hi:4 hi':4
---
lo':(15 : Rat)/4 lo:(7 : Rat)/2 q:63/16 hi:4 hi':4
---
lo':4 lo:4 q:4 hi:4 hi':4
---
lo':4 lo:4 q:33/8 hi:5 hi':(9 : Rat)/2
---
lo':4 lo:4 q:17/4 hi:5 hi':(9 : Rat)/2
---
lo':4 lo:4 q:35/8 hi:5 hi':(9 : Rat)/2
---
lo':(9 : Rat)/2 lo:4 q:9/2 hi:5 hi':(9 : Rat)/2
---
lo':(9 : Rat)/2 lo:4 q:37/8 hi:5 hi':5
---
lo':(9 : Rat)/2 lo:4 q:19/4 hi:5 hi':5
---
lo':(9 : Rat)/2 lo:4 q:39/8 hi:5 hi':5
---
lo':5 lo:5 q:5 hi:5 hi':5
---
lo':5 lo:5 q:41/8 hi:6 hi':(11 : Rat)/2
---
lo':5 lo:5 q:21/4 hi:6 hi':(11 : Rat)/2
---
lo':5 lo:5 q:43/8 hi:6 hi':(11 : Rat)/2
---
lo':(11 : Rat)/2 lo:5 q:11/2 hi:6 hi':(11 : Rat)/2
---
lo':(11 : Rat)/2 lo:5 q:45/8 hi:6 hi':6
---
lo':(11 : Rat)/2 lo:5 q:23/4 hi:6 hi':6
---
lo':(11 : Rat)/2 lo:5 q:47/8 hi:6 hi':6
---
lo':6 lo:6 q:6 hi:6 hi':6
---
lo':6 lo:6 q:49/8 hi:7 hi':(13 : Rat)/2
---
lo':6 lo:6 q:25/4 hi:7 hi':(13 : Rat)/2
---
lo':6 lo:6 q:51/8 hi:7 hi':(13 : Rat)/2
---
lo':(13 : Rat)/2 lo:6 q:13/2 hi:7 hi':(13 : Rat)/2
---
lo':(13 : Rat)/2 lo:6 q:53/8 hi:7 hi':7
---
lo':(13 : Rat)/2 lo:6 q:27/4 hi:7 hi':7
---
lo':(13 : Rat)/2 lo:6 q:55/8 hi:7 hi':7
---
lo':7 lo:7 q:7 hi:7 hi':7
---
lo':7 lo:7 q:57/8 hi:8 hi':(15 : Rat)/2
---
lo':7 lo:7 q:29/4 hi:8 hi':(15 : Rat)/2
---
lo':7 lo:7 q:59/8 hi:8 hi':(15 : Rat)/2
---
lo':(15 : Rat)/2 lo:7 q:15/2 hi:8 hi':(15 : Rat)/2
---
lo':(15 : Rat)/2 lo:7 q:61/8 hi:8 hi':8
---
lo':(15 : Rat)/2 lo:7 q:31/4 hi:8 hi':8
---
lo':(15 : Rat)/2 lo:7 q:63/8 hi:8 hi':8
---
lo':8 lo:8 q:8 hi:8 hi':8
---
lo':8 lo:8 q:33/4 hi:10 hi':9
---
lo':8 lo:8 q:17/2 hi:10 hi':9
---
lo':8 lo:8 q:35/4 hi:10 hi':9
---
lo':9 lo:8 q:9 hi:10 hi':9
---
lo':9 lo:8 q:37/4 hi:10 hi':10
---
lo':9 lo:8 q:19/2 hi:10 hi':10
---
lo':9 lo:8 q:39/4 hi:10 hi':10
---
lo':10 lo:10 q:10 hi:10 hi':10
---
lo':10 lo:10 q:41/4 hi:12 hi':11
---
lo':10 lo:10 q:21/2 hi:12 hi':11
---
lo':10 lo:10 q:43/4 hi:12 hi':11
---
lo':11 lo:10 q:11 hi:12 hi':11
---
lo':11 lo:10 q:45/4 hi:12 hi':12
---
lo':11 lo:10 q:23/2 hi:12 hi':12
---
lo':11 lo:10 q:47/4 hi:12 hi':12
---
lo':12 lo:12 q:12 hi:12 hi':12
---
lo':12 lo:12 q:49/4 hi:14 hi':13
---
lo':12 lo:12 q:25/2 hi:14 hi':13
---
lo':12 lo:12 q:51/4 hi:14 hi':13
---
lo':13 lo:12 q:13 hi:14 hi':13
---
lo':13 lo:12 q:53/4 hi:14 hi':14
---
lo':13 lo:12 q:27/2 hi:14 hi':14
---
lo':13 lo:12 q:55/4 hi:14 hi':14
---
lo':14 lo:14 q:14 hi:14 hi':14
---
lo':14 lo:14 q:57/4 hi:16 hi':15
---
lo':14 lo:14 q:29/2 hi:16 hi':15
---
lo':14 lo:14 q:59/4 hi:16 hi':15
---
lo':15 lo:14 q:15 hi:16 hi':15
---
lo':15 lo:14 q:61/4 hi:16 hi':16
---
lo':15 lo:14 q:31/2 hi:16 hi':16
---
lo':15 lo:14 q:63/4 hi:16 hi':16
---
lo':16 lo:16 q:16 hi:16 hi':16
---
lo':16 lo:16 q:33/2 hi:20 hi':18
---
lo':16 lo:16 q:17 hi:20 hi':18
---
lo':16 lo:16 q:35/2 hi:20 hi':18
---
lo':18 lo:16 q:18 hi:20 hi':18
---
lo':18 lo:16 q:37/2 hi:20 hi':20
---
lo':18 lo:16 q:19 hi:20 hi':20
---
lo':18 lo:16 q:39/2 hi:20 hi':20
---
lo':20 lo:20 q:20 hi:20 hi':20
---
lo':20 lo:20 q:41/2 hi:24 hi':22
---
lo':20 lo:20 q:21 hi:24 hi':22
---
lo':20 lo:20 q:43/2 hi:24 hi':22
---
lo':22 lo:20 q:22 hi:24 hi':22
---
lo':22 lo:20 q:45/2 hi:24 hi':24
---
lo':22 lo:20 q:23 hi:24 hi':24
---
lo':22 lo:20 q:47/2 hi:24 hi':24
---
lo':24 lo:24 q:24 hi:24 hi':24
---
lo':24 lo:24 q:49/2 hi:28 hi':26
---
lo':24 lo:24 q:25 hi:28 hi':26
---
lo':24 lo:24 q:51/2 hi:28 hi':26
---
lo':26 lo:24 q:26 hi:28 hi':26
---
lo':26 lo:24 q:53/2 hi:28 hi':28
---
lo':26 lo:24 q:27 hi:28 hi':28
---
lo':26 lo:24 q:55/2 hi:28 hi':28
---
lo':28 lo:28 q:28 hi:28 hi':28
---
lo':28 lo:28 q:57/2 hi:32 hi':30
---
lo':28 lo:28 q:29 hi:32 hi':30
---
lo':28 lo:28 q:59/2 hi:32 hi':30
---
lo':30 lo:28 q:30 hi:32 hi':30
---
lo':30 lo:28 q:61/2 hi:32 hi':32
---
lo':30 lo:28 q:31 hi:32 hi':32
---
lo':30 lo:28 q:63/2 hi:32 hi':32
---
lo':32 lo:32 q:32 hi:32 hi':32
---
lo':32 lo:32 q:33 hi:40 hi':36
---
lo':32 lo:32 q:34 hi:40 hi':36
---
lo':32 lo:32 q:35 hi:40 hi':36
---
lo':36 lo:32 q:36 hi:40 hi':36
---
lo':36 lo:32 q:37 hi:40 hi':40
---
lo':36 lo:32 q:38 hi:40 hi':40
---
lo':36 lo:32 q:39 hi:40 hi':40
---
lo':40 lo:40 q:40 hi:40 hi':40
---
lo':40 lo:40 q:41 hi:48 hi':44
---
lo':40 lo:40 q:42 hi:48 hi':44
---
lo':40 lo:40 q:43 hi:48 hi':44
---
lo':44 lo:40 q:44 hi:48 hi':44
---
lo':44 lo:40 q:45 hi:48 hi':48
---
lo':44 lo:40 q:46 hi:48 hi':48
---
lo':44 lo:40 q:47 hi:48 hi':48
---
lo':48 lo:48 q:48 hi:48 hi':48
---
lo':48 lo:48 q:49 hi:56 hi':52
---
lo':48 lo:48 q:50 hi:56 hi':52
---
lo':48 lo:48 q:51 hi:56 hi':52
---
lo':52 lo:48 q:52 hi:56 hi':52
---
lo':52 lo:48 q:53 hi:56 hi':56
---
lo':52 lo:48 q:54 hi:56 hi':56
---
lo':52 lo:48 q:55 hi:56 hi':56
---
lo':56 lo:56 q:56 hi:56 hi':56
---
lo':56 lo:56 q:57 hi:64 hi':60
---
lo':56 lo:56 q:58 hi:64 hi':60
---
lo':56 lo:56 q:59 hi:64 hi':60
---
lo':60 lo:56 q:60 hi:64 hi':60
---
lo':60 lo:56 q:61 hi:64 hi':64
---
lo':60 lo:56 q:62 hi:64 hi':64
---
lo':60 lo:56 q:63 hi:64 hi':64
---
lo':64 lo:64 q:64 hi:64 hi':64
---
lo':64 lo:64 q:66 hi:80 hi':72
---
lo':64 lo:64 q:68 hi:80 hi':72
---
lo':64 lo:64 q:70 hi:80 hi':72
---
lo':72 lo:64 q:72 hi:80 hi':72
---
lo':72 lo:64 q:74 hi:80 hi':80
---
lo':72 lo:64 q:76 hi:80 hi':80
---
lo':72 lo:64 q:78 hi:80 hi':80
---
lo':80 lo:80 q:80 hi:80 hi':80
---
lo':80 lo:80 q:82 hi:96 hi':88
---
lo':80 lo:80 q:84 hi:96 hi':88
---
lo':80 lo:80 q:86 hi:96 hi':88
---
lo':88 lo:80 q:88 hi:96 hi':88
---
lo':88 lo:80 q:90 hi:96 hi':96
---
lo':88 lo:80 q:92 hi:96 hi':96
---
lo':88 lo:80 q:94 hi:96 hi':96
---
lo':96 lo:96 q:96 hi:96 hi':96
---
lo':96 lo:96 q:98 hi:112 hi':104
---
lo':96 lo:96 q:100 hi:112 hi':104
---
lo':96 lo:96 q:102 hi:112 hi':104
---
lo':104 lo:96 q:104 hi:112 hi':104
---
lo':104 lo:96 q:106 hi:112 hi':112
---
lo':104 lo:96 q:108 hi:112 hi':112
---
lo':104 lo:96 q:110 hi:112 hi':112
---
lo':112 lo:112 q:112 hi:112 hi':112
---
lo':112 lo:112 q:114 hi:128 hi':120
---
lo':112 lo:112 q:116 hi:128 hi':120
---
lo':112 lo:112 q:118 hi:128 hi':120
---
lo':120 lo:112 q:120 hi:128 hi':120
---
lo':120 lo:112 q:122 hi:128 hi':128
---
lo':120 lo:112 q:124 hi:128 hi':128
---
lo':120 lo:112 q:126 hi:128 hi':128
---
lo':128 lo:128 q:128 hi:128 hi':128
---
lo':128 lo:128 q:132 hi:160 hi':144
---
lo':128 lo:128 q:136 hi:160 hi':144
---
lo':128 lo:128 q:140 hi:160 hi':144
---
lo':144 lo:128 q:144 hi:160 hi':144
---
lo':144 lo:128 q:148 hi:160 hi':160
---
lo':144 lo:128 q:152 hi:160 hi':160
---
lo':144 lo:128 q:156 hi:160 hi':160
---
lo':160 lo:160 q:160 hi:160 hi':160
---
lo':160 lo:160 q:164 hi:192 hi':176
---
lo':160 lo:160 q:168 hi:192 hi':176
---
lo':160 lo:160 q:172 hi:192 hi':176
---
lo':176 lo:160 q:176 hi:192 hi':176
---
lo':176 lo:160 q:180 hi:192 hi':192
---
lo':176 lo:160 q:184 hi:192 hi':192
---
lo':176 lo:160 q:188 hi:192 hi':192
---
lo':192 lo:192 q:192 hi:192 hi':192
---
lo':192 lo:192 q:196 hi:224 hi':208
---
lo':192 lo:192 q:200 hi:224 hi':208
---
lo':192 lo:192 q:204 hi:224 hi':208
---
lo':208 lo:192 q:208 hi:224 hi':208
---
lo':208 lo:192 q:212 hi:224 hi':224
---
lo':208 lo:192 q:216 hi:224 hi':224
---
lo':208 lo:192 q:220 hi:224 hi':224
---
lo':224 lo:224 q:224 hi:224 hi':224
---
lo':224 lo:224 q:228 hi:-224 hi':240
---
lo':224 lo:224 q:232 hi:-224 hi':240
---
lo':224 lo:224 q:236 hi:-224 hi':240
---
lo':240 lo:224 q:240 hi:-224 hi':240
---
lo':240 lo:224 q:244 hi:-224 hi':-240
---
lo':240 lo:224 q:248 hi:-224 hi':-240
---
lo':240 lo:224 q:252 hi:-224 hi':-240
nsuccess = 959, nfailure = 1, success% = 99%
---
info: false
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 4 5 4 2

/--
info: ---
lo':(7 : Rat)/2 lo:3 q:-15/4 hi:-3 hi':(-7 : Rat)/2
---
lo':(-7 : Rat)/2 lo:3 q:-7/2 hi:-3 hi':(-7 : Rat)/2
Mismatch on input ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x1#4, sig := 0xe#4 } }
  Circuit: ExtRat.Infinity true | { state := ∞, num := { sign := true, ex := 0x0#3, sig := 0x0#2 } }
  Golden : ExtRat.Number -3 | { state := num, num := { sign := true, ex := 0x1#3, sig := 0x3#2 } }
---
lo':(-7 : Rat)/2 lo:3 q:-13/4 hi:-3 hi':-3
---
lo':-3 lo:-3 q:-3 hi:-3 hi':-3
---
lo':-3 lo:-3 q:-11/4 hi:-2 hi':(-5 : Rat)/2
---
lo':(-5 : Rat)/2 lo:-3 q:-5/2 hi:-2 hi':(-5 : Rat)/2
---
lo':(-5 : Rat)/2 lo:-3 q:-9/4 hi:-2 hi':-2
---
lo':-2 lo:-2 q:-2 hi:-2 hi':-2
---
lo':-2 lo:-2 q:-15/8 hi:(-3 : Rat)/2 hi':(-7 : Rat)/4
---
lo':(-7 : Rat)/4 lo:-2 q:-7/4 hi:(-3 : Rat)/2 hi':(-7 : Rat)/4
---
lo':(-7 : Rat)/4 lo:-2 q:-13/8 hi:(-3 : Rat)/2 hi':(-3 : Rat)/2
---
lo':(-3 : Rat)/2 lo:(-3 : Rat)/2 q:-3/2 hi:(-3 : Rat)/2 hi':(-3 : Rat)/2
---
lo':(-3 : Rat)/2 lo:(-3 : Rat)/2 q:-11/8 hi:-1 hi':(-5 : Rat)/4
---
lo':(-5 : Rat)/4 lo:(-3 : Rat)/2 q:-5/4 hi:-1 hi':(-5 : Rat)/4
---
lo':(-5 : Rat)/4 lo:(-3 : Rat)/2 q:-9/8 hi:-1 hi':-1
---
lo':-1 lo:-1 q:-1 hi:-1 hi':-1
---
lo':-1 lo:-1 q:-7/8 hi:(-1 : Rat)/2 hi':(-3 : Rat)/4
---
lo':(-3 : Rat)/4 lo:-1 q:-3/4 hi:(-1 : Rat)/2 hi':(-3 : Rat)/4
---
lo':(-3 : Rat)/4 lo:-1 q:-5/8 hi:(-1 : Rat)/2 hi':(-1 : Rat)/2
---
lo':(-1 : Rat)/2 lo:(-1 : Rat)/2 q:-1/2 hi:(-1 : Rat)/2 hi':(-1 : Rat)/2
---
lo':(-1 : Rat)/2 lo:(-1 : Rat)/2 q:-3/8 hi:0 hi':(-1 : Rat)/4
---
lo':(-1 : Rat)/4 lo:(-1 : Rat)/2 q:-1/4 hi:0 hi':(-1 : Rat)/4
---
lo':(-1 : Rat)/4 lo:(-1 : Rat)/2 q:-1/8 hi:0 hi':0
---
lo':0 lo:0 q:0 hi:0 hi':0
---
lo':0 lo:0 q:0 hi:0 hi':0
---
lo':0 lo:0 q:1/8 hi:(1 : Rat)/2 hi':(1 : Rat)/4
---
lo':(1 : Rat)/4 lo:0 q:1/4 hi:(1 : Rat)/2 hi':(1 : Rat)/4
---
lo':(1 : Rat)/4 lo:0 q:3/8 hi:(1 : Rat)/2 hi':(1 : Rat)/2
---
lo':(1 : Rat)/2 lo:(1 : Rat)/2 q:1/2 hi:(1 : Rat)/2 hi':(1 : Rat)/2
---
lo':(1 : Rat)/2 lo:(1 : Rat)/2 q:5/8 hi:1 hi':(3 : Rat)/4
---
lo':(3 : Rat)/4 lo:(1 : Rat)/2 q:3/4 hi:1 hi':(3 : Rat)/4
---
lo':(3 : Rat)/4 lo:(1 : Rat)/2 q:7/8 hi:1 hi':1
---
lo':1 lo:1 q:1 hi:1 hi':1
---
lo':1 lo:1 q:9/8 hi:(3 : Rat)/2 hi':(5 : Rat)/4
---
lo':(5 : Rat)/4 lo:1 q:5/4 hi:(3 : Rat)/2 hi':(5 : Rat)/4
---
lo':(5 : Rat)/4 lo:1 q:11/8 hi:(3 : Rat)/2 hi':(3 : Rat)/2
---
lo':(3 : Rat)/2 lo:(3 : Rat)/2 q:3/2 hi:(3 : Rat)/2 hi':(3 : Rat)/2
---
lo':(3 : Rat)/2 lo:(3 : Rat)/2 q:13/8 hi:2 hi':(7 : Rat)/4
---
lo':(7 : Rat)/4 lo:(3 : Rat)/2 q:7/4 hi:2 hi':(7 : Rat)/4
---
lo':(7 : Rat)/4 lo:(3 : Rat)/2 q:15/8 hi:2 hi':2
---
lo':2 lo:2 q:2 hi:2 hi':2
---
lo':2 lo:2 q:9/4 hi:3 hi':(5 : Rat)/2
---
lo':(5 : Rat)/2 lo:2 q:5/2 hi:3 hi':(5 : Rat)/2
---
lo':(5 : Rat)/2 lo:2 q:11/4 hi:3 hi':3
---
lo':3 lo:3 q:3 hi:3 hi':3
---
lo':3 lo:3 q:13/4 hi:-3 hi':(7 : Rat)/2
---
lo':(7 : Rat)/2 lo:3 q:7/2 hi:-3 hi':(7 : Rat)/2
---
lo':(7 : Rat)/2 lo:3 q:15/4 hi:-3 hi':(-7 : Rat)/2
nsuccess = 47, nfailure = 1, success% = 97%
---
info: false
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 2 3 2 1


end ExhaustiveTesting

end RoundingQNaiveComputable
end Fp
