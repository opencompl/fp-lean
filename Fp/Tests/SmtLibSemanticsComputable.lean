import Fp.Rounding
import Fp.SmtLibSemantics

namespace Fp
open SmtLibSemantics

namespace SmtLibSemanticsComputable

structure PackedFloatEnumeration (e : Nat) (s : Nat) where ofEnumeration ::
  -- | Sorted array of packed float with its rational value. Only numbers,
  -- no infinities and NaNs.
  enumeration : Array (PackedFloat e s × Rat)


def PackedFloatEnumeration.mk (e s : Nat) : PackedFloatEnumeration e s where
  enumeration := Id.run do
    let mut arr : Array (PackedFloat e s × Rat) := #[]
    for sign in [true, false] do
      for exp in [0:2^e] do
        for sig in [0:2^s] do
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
  let mut glb := none
  for hi : i in [0:arr.size] do
    let (pf, rpf) := arr[i]
    if rpf <= r then
      glb := some (pf, rpf)
  glb

def PackedFloatEnumeration.leastUpperBound (
    enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut lub := none
  for i in [0:arr.size] do
    -- index from the back.
    let (pf, rpf) := arr[arr.size - 1 - i]!
    if rpf >= r then
      lub := some (pf, rpf)
      break
  lub


/-
This file defines a computable version of the SMT-LIB semantics,
which is used for comparing results from SMT solvers with those from Lean's floating-point library.
-/

def lowerFromEmbedByEnumeration {e s}
    (enum : PackedFloatEnumeration e s) :
    RoundableLower (PackedFloat e s) ExtRat where
  lower := fun (r : ExtRat) =>
    match r with
    | .NaN => .mkNaN
    | .Infinity x => .getInfinity e s x -- infinity is representable.
    | .Number r =>
      -- for a number, if it is below the min number, return -inf
      match enum.greatestLowerBound r with
      | some (pf, _) => pf
      | none => PackedFloat.getInfinity _ _ true

def upperFromEmbedByEnumeration {e s}
    (enum : PackedFloatEnumeration e s) :
    RoundableUpper (PackedFloat e s) ExtRat where
  upper := fun (r : ExtRat) =>
    match r with
    | .NaN => .mkNaN
    | .Infinity x => .getInfinity e s x -- infinity is representable.
    | .Number r =>
      -- for a number, if it is above the max number, return +inf
      match enum.leastUpperBound r with
      | some (pf, _) => pf
      | none => PackedFloat.getInfinity _ _ false

def computableV : RoundableAdjunction (PackedFloat e s) ExtRat where
  lower := lowerFromEmbedByEnumeration (PackedFloatEnumeration.mk e s) |>.lower
  upper := upperFromEmbedByEnumeration (PackedFloatEnumeration.mk e s) |>.upper
  embed := PackedFloat.toExtRat

#check SmtLibSemantics.SmtLibRoundMethod.smtLibRoundMethod

abbrev computableSmtLibRoundMethod (e s : Nat) :
    RoundMethod (PackedFloat e s) ExtRat :=
  SmtLibRoundMethod.smtLibRoundMethod e s
    (computableV)
    (computableV)

instance : DecidablePred ((computableSmtLibRoundMethod e s).lowerHalf) := by
  simp [computableSmtLibRoundMethod]
  infer_instance

instance : DecidablePred ((computableSmtLibRoundMethod e s).tieBreak) := by
  simp [computableSmtLibRoundMethod]
  infer_instance


/-- A computable version of the SMT-LIB rounder functions. -/
def computableSmtLibRound {e s : Nat}
  (rm : RoundingMode) (sign : Bool)
  (r : ExtRat) : PackedFloat e s :=
  (computableSmtLibRoundMethod e s).round rm sign r

end SmtLibSemanticsComputable

end Fp
