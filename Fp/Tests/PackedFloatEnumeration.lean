import Fp.Rounding
import Fp.SmtLibSemantics
import Fp.Theorems.Basic
import Fp.Theorems.Packing
import Fp.Theorems.Packing
import Fp.Theorems.Ordering
import Fp.Theorems.UnpackedRound

namespace Fp
open SmtLibSemantics


structure PackedFloatEnumeration (e : Nat) (s : Nat) where ofEnumeration ::
  -- | Sorted array of packed float with its rational value. Only numbers,
  -- no infinities and NaNs.
  enumeration : Array (PackedFloat e s)


def PackedFloatEnumeration.mk (e s : Nat) : PackedFloatEnumeration e s where
  enumeration := Id.run do
    let mut arr : Array (PackedFloat e s) := #[]
    for sign in [true, false] do
      for exp in [:2^e] do
        for sig in [:2^s] do
          let pf : PackedFloat e s := PackedFloat.mk sign exp sig
          let er := pf.toExtRat
          let ExtRat.Number r := er
            | continue
          arr := arr.push pf
    arr.qsort (fun a b => a ≤ b)

def PackedFloatEnumeration.minNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  let num := enum.enumeration[0]!
  (num, num.toRat)

def PackedFloatEnumeration.maxNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  let num := enum.enumeration[enum.enumeration.size - 1]!
  (num, num.toRat)

def PackedFloatEnumeration.greatestLowerBound (enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut glb? := none
  for hi : i in [:arr.size] do
    let curPf := arr[i]
    let curRat := curPf.toRat
    if curRat <= r then
        -- is a lower bound
        glb? :=
          match glb? with
          | none => some (curPf, curRat)
          | some (_, glbRat) =>
            -- is larger than the current lower bound.
            if curRat > glbRat then
              some (curPf, curRat)
            else
              glb?
  glb?

def PackedFloatEnumeration.leastUpperBound (
    enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut lub? := none
  for hi : i in [0:arr.size] do
    let curPf := arr[i]
    let curRat := curPf.toRat
    if curRat >= r then
        -- is an upper bound
        lub? :=
          match lub? with
          | none => some (curPf, curRat)
          | some (_, lubRat) =>
            -- is smaller than the current upper bound.
            if curRat < lubRat then
              some (curPf, curRat)
            else
              lub?
  lub?

end Fp
