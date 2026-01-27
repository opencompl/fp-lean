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

def Rounder.rnePackedFloat (rounder : Rounder E S) (q : Rat) : PackedFloat E S := Id.run do
  let lo := rounder.f2r.closestLower q
  let hi := rounder.f2r.closestHigher q
  let lowest := rounder.f2r.minimum
  let highest := rounder.f2r.maximum
  let lo' := rounder.f2r'.closestLower q
  let hi' := rounder.f2r'.closestHigher q
  let lowest' := rounder.f2r'.minimum
  let highest' := rounder.f2r'.maximum

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
    let golden := rounder.rnePackedFloat pf.2
    if circuitPf == golden then
      nsuccess := nsuccess + 1
    else
      if nfailure < 2 then
        IO.println s!"---"
        IO.println s!"Mismatch on input {repr pf.1.toExtRat}"
        IO.println s!"  Circuit: {repr circuitPf.toExtRat}"
        IO.println s!"  Golden : {repr golden.toExtRat}"
      nfailure := nfailure + 1

  let percentSucces := (nsuccess * 100) / (nsuccess + nfailure)
  IO.println s!"nsuccess = {nsuccess}, nfailure = {nfailure}, success% = {percentSucces}%"
  return nfailure == 0


/--
info: ---
Mismatch on input ExtRat.Number 0
  Circuit: ExtRat.Number 0
  Golden : ExtRat.Number 0
nsuccess = 5, nfailure = 1, success% = 83%
---
info: false
-/
#guard_msgs in #eval testAgainstUnpackedFloatRounding 2 1 2 1

end ExhaustiveTesting

end RoundingQNaiveComputable
end Fp
