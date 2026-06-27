import Fp.Theorems.UnpackedFloat.Round.IsLowerHalfTieBreak
import Fp.Theorems.UnpackedFloat.Round.IsEvenLowerCore

namespace Fp


/-# blastIsEvenUpper, blastIsEvenLower

The bitblasted even predicates agree with the SMT-LIB `isEven` of the upper/lower approximants, for a
nonnegative-or-negative, in-range, normalized input. (Strong hypotheses are required because `isEven`
reads the *stored significand* of the approximant, which the value-level `Rel` cannot pin down; the
RNE call site applies these to the already-clamped `x.truncateFittingExponent`.) -/

theorem blastIsEvenUpper_iff_smtLibIsEven_upper
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
  x.blastIsEvenUpper ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat')) = true := by
  have heq : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
        (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat')) = x.blastIsEvenUpper ep sp :=
    isEven_smtLibUpper_eq_blastIsEvenUpper he hs heu hsu x hxnorm hnotunder hnotover
  rw [heq]

theorem blastIsEvenUpper_eq
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
  x.blastIsEvenUpper ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat'))) := by
  have := blastIsEvenUpper_iff_smtLibIsEven_upper he hs heu hsu x hxnorm hnotunder hnotover
  grind

theorem blastIsEvenLower_iff_smtLibIsEven_lower
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
  x.blastIsEvenLower ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')) = true := by
  have heq : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
        (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')) = x.blastIsEvenLower ep sp :=
    isEven_smtLibLower_eq_blastIsEvenLower he hs heu hsu x hxnorm hnotunder hnotover
  rw [heq]

theorem blastIsEvenLower_eq
    (he : 2 < ep) (hs : 0 < sp) (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false) :
  x.blastIsEvenLower ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat'))) := by
  have := blastIsEvenLower_iff_smtLibIsEven_lower he hs heu hsu x hxnorm hnotunder hnotover
  grind

end Fp
