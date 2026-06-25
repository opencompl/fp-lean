import Fp.Theorems.UnpackedFloat.Round.RounderForSign

namespace Fp


/-# blastIsLowerHalf -/

@[simp]
theorem blastIsLowerHalf_iff_smtLibLowerHalf  (he : 1 < ep) (hs : 0 < sp)  (x : UnpackedFloat e s)  :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
    := by
  simp [UnpackedFloat.blastIsLowerHalf]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem blastIsLowerHalf_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsLowerHalf ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')) := by
  have := blastIsLowerHalf_iff_smtLibLowerHalf he hs x
  grind


@[simp]
theorem blastTieBreak_iff_smtLibTieBreak (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') := by
  simp [UnpackedFloat.blastIsTieBreak]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem blastIsTieBreak_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat')) := by
  have := blastTieBreak_iff_smtLibTieBreak he hs x
  grind

end Fp
