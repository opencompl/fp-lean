import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ

namespace Fp

theorem round_correct (inf : UnpackedFloat ein sin) (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemantics.SmtLibRoundMethod.smtLibRoundMethod inf eout sout rm =
      (UnpackedFloat.round inf rm).toExtRat := by sorry

end Fp
