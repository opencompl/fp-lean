import Fp.Theorems.UnpackedFloat.Round.IsLowerHalfTieBreak

namespace Fp


/-# blastIsEvenUpper, blastIsEvenLower -/

theorem blastIsEvenUpper_iff_smtLibIsEven_upper (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenUpper ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat')) = true := by
  simp [UnpackedFloat.blastIsEvenUpper]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

theorem blastIsEvenUpper_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenUpper ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat'))) := by
  have := blastIsEvenUpper_iff_smtLibIsEven_upper he hs x
  grind

theorem blastIsEvenLower_iff_smtLibIsEven_lower (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenLower ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')) = true := by
  simp [UnpackedFloat.blastIsEvenLower]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

theorem blastIsEvenLower_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenLower ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat'))) := by
  have := blastIsEvenLower_iff_smtLibIsEven_lower he hs x
  grind

end Fp
