/-
Create a computable version of the rounding function on the rationals,
that is an intermediate between the hopelessly uncomputable SMT-LIB version
and the complicated circuit version for UnpackedFloat.
-/
import Fp.Basic
import Fp.UnpackedRound

namespace Fp
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

def Rounder.rnePackedFloat (rounder : Rounder E S) (q : Rat) (sign : Bool) : PackedFloat E S := Id.run do
  let lo := rounder.f2r.closestLower q
  let hi := rounder.f2r.closestHigher q
  let lowest := rounder.f2r.minimum
  let highest := rounder.f2r.maximum
  let lo' := rounder.f2r'.closestLower q
  let hi' := rounder.f2r'.closestHigher q
  let lowest' := rounder.f2r'.minimum
  let highest' := rounder.f2r'.maximum

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
    let circuit := UnpackedFloat.debugRound
        (targetExponentWidth := EOut)
        (targetSignificandWidth := SOut)
        (pf.1.unpack.num) .RNE
    let circuitPf := EUnpackedFloat.pack (e := EOut) (s := SOut) circuit.1
    let golden := rounder.rnePackedFloat pf.2 pf.1.sign
    if circuitPf == golden then
      nsuccess := nsuccess + 1
    else
      if nfailure < 200 then
        IO.println s!"---"
        IO.println s!"Mismatch on input {repr pf.1.toExtRat} | {repr pf.1.unpack}"
        IO.println s!"  Circuit: {repr circuitPf.toExtRat} | {repr circuitPf.unpack}"
        IO.println s!"  Golden : {repr golden.toExtRat} | {repr golden.unpack}"
      nfailure := nfailure + 1

  let percentSucces := (nsuccess * 100) / (nsuccess + nfailure)
  IO.println s!"nsuccess = {nsuccess}, nfailure = {nfailure}, success% = {percentSucces}%"
  return nfailure == 0


/--
info: nsuccess = 2, nfailure = 0, success% = 100%
---
info: true
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 1 1 1 1


/--
info: ---
Mismatch on input ExtRat.Number -236 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Infinity true | { state := ∞, num := { sign := true, ex := 0x00#5, sig := 0x0#3 } }
---
Mismatch on input ExtRat.Number -232 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Infinity true | { state := ∞, num := { sign := true, ex := 0x00#5, sig := 0x0#3 } }
---
Mismatch on input ExtRat.Number -228 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Infinity true | { state := ∞, num := { sign := true, ex := 0x00#5, sig := 0x0#3 } }
---
Mismatch on input ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -192 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -220 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -192 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -216 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -192 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -212 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number -224 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -192 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -118 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -128 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -116 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -128 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -114 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -128 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -128 | { state := num, num := { sign := true, ex := 0x07#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -110 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -96 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -108 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -96 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -106 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number -112 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -96 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -59 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -64 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -58 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -64 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -57 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -64 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -64 | { state := num, num := { sign := true, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -55 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -48 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -54 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -48 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -53 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number -56 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -48 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/2 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -32 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -29 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -32 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/2 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -32 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -32 | { state := num, num := { sign := true, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/2 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -24 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number -27 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -24 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/2 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number -28 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -24 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/4 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -16 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/2 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -16 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/4 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -16 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -16 | { state := num, num := { sign := true, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/4 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -12 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/2 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -12 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/4 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number -14 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -12 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/8 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -8 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/4 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -8 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/8 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -8 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -8 | { state := num, num := { sign := true, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/8 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -6 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/4 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -6 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/8 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number -7 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -6 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/16 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -4 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/8 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -4 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/16 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -4 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -4 | { state := num, num := { sign := true, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/16 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -3 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/8 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -3 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/16 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -3 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/32 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/16 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/32 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -2 | { state := num, num := { sign := true, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/32 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/2 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/16 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/2 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/32 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/4 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/2 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -1 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -1 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -1 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number -1 | { state := num, num := { sign := true, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/2 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/2 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/2 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/2 | { state := num, num := { sign := true, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/4 | { state := num, num := { sign := true, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/512 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/512 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/8 | { state := num, num := { sign := true, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/512 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/512 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/512 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/16 | { state := num, num := { sign := true, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/512 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-59 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-29 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-57 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-1 : Rat)/32 | { state := num, num := { sign := true, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-55 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-53 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (-7 : Rat)/256 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (-3 : Rat)/128 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (-27 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-13 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x34#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-25 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x32#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x30#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/64 | { state := num, num := { sign := true, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-23 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x2e#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/128 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-11 : Rat)/1024 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x2c#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/128 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (-21 : Rat)/2048 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x2a#6 } }
  Circuit: ExtRat.Number (-3 : Rat)/256 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (-1 : Rat)/128 | { state := num, num := { sign := true, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (21 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x2a#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/128 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (11 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x2c#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/128 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (23 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x2e#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/128 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x30#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/128 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (25 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x32#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (13 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x34#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (3 : Rat)/256 | { state := num, num := { sign := false, ex := 0x19#5, sig := 0x6#3 } }
  Golden : ExtRat.Number (1 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/2048 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1a#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/512 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/512 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/1024 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1b#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/512 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/512 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/512 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/512 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1c#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/256 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1d#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/2 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/2 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/128 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/16 | { state := num, num := { sign := false, ex := 0x1e#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (1 : Rat)/2 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/4 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 1 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/32 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 1 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/64 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/8 | { state := num, num := { sign := false, ex := 0x1f#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 1 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/32 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/2 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/16 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/2 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/32 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/2 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number (3 : Rat)/2 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/32 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/16 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/32 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/4 | { state := num, num := { sign := false, ex := 0x00#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/16 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 3 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/8 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 3 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/16 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 3 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 3 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/16 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 4 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/8 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 4 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/16 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number (7 : Rat)/2 | { state := num, num := { sign := false, ex := 0x01#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 4 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/8 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 6 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/4 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 6 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/8 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 6 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 6 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/8 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 8 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/4 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 8 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/8 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number 7 | { state := num, num := { sign := false, ex := 0x02#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 8 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/4 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 12 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (27 : Rat)/2 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 12 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/4 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 12 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 12 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/4 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 16 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (29 : Rat)/2 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 16 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/4 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number 14 | { state := num, num := { sign := false, ex := 0x03#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 16 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (53 : Rat)/2 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 24 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 27 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 24 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (55 : Rat)/2 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 24 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 24 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number (57 : Rat)/2 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 32 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number 29 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 32 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number (59 : Rat)/2 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number 28 | { state := num, num := { sign := false, ex := 0x04#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 32 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number 53 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 48 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 54 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 48 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 55 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 48 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 48 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 57 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x39#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 64 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number 58 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x3a#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 64 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number 59 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x3b#6 } }
  Circuit: ExtRat.Number 56 | { state := num, num := { sign := false, ex := 0x05#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 64 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x4#3 } }
---
Mismatch on input ExtRat.Number 106 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x35#6 } }
  Circuit: ExtRat.Number 112 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 96 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 108 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x36#6 } }
  Circuit: ExtRat.Number 112 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 96 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 110 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x37#6 } }
  Circuit: ExtRat.Number 112 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 96 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x6#3 } }
---
Mismatch on input ExtRat.Number 112 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x38#6 } }
  Circuit: ExtRat.Number 112 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x7#3 } }
  Golden : ExtRat.Number 96 | { state := num, num := { sign := false, ex := 0x06#5, sig := 0x6#3 } }
nsuccess = 720, nfailure = 210, success% = 77%
---
info: false
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 4 5 4 2

/--
info: nsuccess = 6, nfailure = 0, success% = 100%
---
info: true
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 2 1 2 1


end ExhaustiveTesting

end RoundingQNaiveComputable
end Fp
