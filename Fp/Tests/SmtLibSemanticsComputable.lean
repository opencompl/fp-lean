import Fp.Rounding
import Fp.SmtLibSemantics
import Fp.Tests.PackedFloatEnumeration

namespace Fp
open SmtLibSemantics

namespace SmtLibSemanticsComputable

def mkZero (sign : Bool) (e s : Nat) : PackedFloat e s :=
  EUnpackedFloat.mkNumber (UnpackedFloat.mkZero sign) |>.pack


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
      | some (pf, rpf) =>
        if rpf = 0
        then mkZero false e s -- lower bound is +0 (footnote 5)
        else pf
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
      | some (pf, rpf) =>
          if rpf = 0
          then mkZero true e s -- upper bound is -0 (footnote 5)
          else pf
      | none => PackedFloat.getInfinity _ _ false

def computableV : RoundableAdjunction (PackedFloat e s) ExtRat where
  lower := lowerFromEmbedByEnumeration (PackedFloatEnumeration.mk e s) |>.lower
  upper := upperFromEmbedByEnumeration (PackedFloatEnumeration.mk e s) |>.upper
  embed := PackedFloat.toExtRat

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
