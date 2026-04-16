import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing
import Fp.Theorems.Negation
import Fp.Theorems.Ordering

namespace Fp
namespace PackedFloat

/--
successorAwayFromZero of NaN is NaN
-/
@[simp, grind .]
theorem successorAwayFromZero_eq_of_isNaN (pf : PackedFloat e s) (hNaN : pf.isNaN) :
    pf.successorAwayFromZero = pf := by
  simp  [PackedFloat.successorAwayFromZero, hNaN]

/--
successorAwayFromZero of ∞ is ∞
-/
@[simp, grind .]
theorem successorAwayFromZero_eq_of_isInfinite (pf : PackedFloat e s)
    (hInf : pf.isInfinite) :
    pf.successorAwayFromZero = pf := by
  simp  [PackedFloat.successorAwayFromZero, hInf]
  grind only [PackedFloat.eq_getInfinity_iff_isInfinity, → PackedFloat.eq_mkInfinity_of_isInfinite,
    → PackedFloat.unpack_eq_NaN_of_isNaN, !PackedFloat.unpack_getInfinity,
    !PackedFloat.isInfinite_getInfinity, !PackedFloat.isInfinite_unpack_eq_isInfinite, #532a]

/--
successorAwayFromZero of max normal number is +∞.
-/
@[simp, grind .]
theorem successorAwayFromZero_maxNormal_eq (he : 1 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).successorAwayFromZero =
    PackedFloat.getInfinity e s sign := by
  simp only [PackedFloat.successorAwayFromZero]
  have : ¬ (PackedFloat.maxNormalNumber e s sign).isNaN := by
    grind
  simp [this]
  intros hmax
  intros hsub
  apply Classical.byContradiction
  intros hcontra
  apply hcontra
  simp [PackedFloat.getInfinity]
  grind only



theorem toRat_successorAwayFromZero_eq
  (x : PackedFloat e s)
  (he : 0 < e)
  (hs : 0 < s) :
  x.successorAwayFromZero.toRat = x.toRat + x.sign.toSign * (2 : Rat) ^ (- (s : Int)) := by sorry

end PackedFloat
end Fp
