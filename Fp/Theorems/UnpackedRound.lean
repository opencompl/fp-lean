import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ

namespace Fp

theorem round_correct (inf : UnpackedFloat ein sin) (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ ein sin eout sout rm (EUnpackedFloat.mkNumber inf) =
      (UnpackedFloat.round inf rm).pack := by sorry

end Fp
