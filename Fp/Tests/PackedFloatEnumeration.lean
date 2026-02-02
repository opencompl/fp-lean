import Fp.Rounding
import Fp.SmtLibSemantics

namespace Fp
open SmtLibSemantics

structure PackedFloatEnumeration (e : Nat) (s : Nat) where ofEnumeration ::
  -- | Sorted array of packed float with its rational value. Only numbers,
  -- no infinities and NaNs.
  enumeration : Array (PackedFloat e s × Rat)

def PackedFloatEnumeration.mk (e s : Nat) : PackedFloatEnumeration e s where
  enumeration := Id.run do
    let mut arr : Array (PackedFloat e s × Rat) := #[]
    for sign in [true, false] do
      for exp in [:2^e] do
        for sig in [:2^s] do
          let pf : PackedFloat e s := PackedFloat.mk sign exp sig
          let er := pf.toExtRat
          let ExtRat.Number r := er
            | continue
          arr := arr.push (pf, r)
    arr.qsort (fun (_, r1) (_, r2) => r1 < r2)

def PackedFloatEnumeration.minNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  enum.enumeration[0]!

def PackedFloatEnumeration.maxNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  enum.enumeration[enum.enumeration.size - 1]!

def PackedFloatEnumeration.greatestLowerBound (enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut glb? := none
  for hi : i in [:arr.size] do
    let (curPf, curRat) := arr[i]
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
    let (curPf, curRat) := arr[i]
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
