import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Multiplication

namespace Fp

theorem roundQ_eq_round_of_UnpackedFloat (inf : UnpackedFloat ein sin) (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ ein sin eout sout rm (EUnpackedFloat.mkNumber inf) =
      (UnpackedFloat.round inf rm).pack := by sorry

theorem roundQ_eq_round_of_NaN (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ 0 0 eout sout rm (EUnpackedFloat.mkNaN) = PackedFloat.mkNaN := by sorry

theorem roundQ_eq_round_of_Infinity (sign : Bool) (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ 0 0 eout sout rm (EUnpackedFloat.mkInfinity sign) =
      PackedFloat.getInfinity eout sout sign := by sorry

/--
Example theorem we will prove, using our proof strategy of proving against the SMT-Lib semantics.
-/
theorem mul_eq_mul (eout sout : Nat) (rm : RoundingMode) (a b : PackedFloat ein sin) :
  Fp.SmtLibSemantics.SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin)
    rm a b = PackedFloat.mul rm a b
     := by sorry
end Fp
