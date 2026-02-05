import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Multiplication

namespace Fp

@[simp]
theorem roundQ_eq (ein sin eout sout : Nat) (rm : RoundingMode) (euf : EUnpackedFloat ein sin):
    Fp.SmtLibSemanticsQ.roundQ ein sin eout sout rm euf =
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm euf.sign
    euf.toExtRat := by
  simp [SmtLibSemanticsQ.roundQ]

@[simp]
theorem lower_NaN_eq_PackedFloat_mkNaN :
  SmtLibSemantics.smtLibLower.lower ExtRat.NaN = (PackedFloat.mkNaN : PackedFloat e s) := sorry

@[simp]
theorem upper_NaN_eq_PackedFloat_mkNaN :
  SmtLibSemantics.smtLibUpper.upper ExtRat.NaN = (PackedFloat.mkNaN : PackedFloat e s) := sorry

@[simp]
theorem roundRNA_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
    (ExtRat.NaN) = PackedFloat.mkNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]

@[simp]
theorem roundRNE_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
    (ExtRat.NaN) = PackedFloat.mkNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRNE]

@[simp]
theorem roundRTP_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTP sign
    (ExtRat.NaN) = PackedFloat.mkNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]

@[simp]
theorem roundRTN_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN sign
    (ExtRat.NaN) = PackedFloat.mkNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  rcases sign <;> simp

@[simp]
theorem rountRTZ_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTZ sign
    (ExtRat.NaN) = PackedFloat.mkNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ]
  rcases sign <;> simp

theorem roundQ_eq_round_of_UnpackedFloat (inf : UnpackedFloat ein sin) (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ ein sin eout sout rm (EUnpackedFloat.mkNumber inf) =
      (UnpackedFloat.round inf rm).pack := by sorry

theorem roundQ_eq_round_of_NaN (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ 0 0 eout sout rm (EUnpackedFloat.mkNaN) = PackedFloat.mkNaN := by
  simp
  rcases rm
  · simp
  · simp
  · simp
  · simp
  · simp

theorem roundQ_eq_round_of_Infinity (sign : Bool) (eout sout : Nat) (rm : RoundingMode) :
    Fp.SmtLibSemanticsQ.roundQ 0 0 eout sout rm (EUnpackedFloat.mkInfinity sign) =
      PackedFloat.getInfinity eout sout sign := by sorry

/--
Case splitting on the different values a packed float
can have: it can be nan, infinity, zero, or a nonzero normal/subnormal.+
-/
@[elab_as_elim]
theorem PackedFloat.kindCasesNaNInfZeroNum {P : PackedFloat e s → Prop}
    (x : PackedFloat e s)
    (nanCase : ∀ (n : PackedFloat e s), n.isNaN → P n)
    (infCase : ∀ sign, P (PackedFloat.getInfinity e s sign))
    (zeroCase : ∀ sign, P (PackedFloat.getZero e s sign))
    (numCase : ∀ (n : PackedFloat e s), n.isNormOrNonzeroSubnorm → P n) :
    P x := by
  have := x.classification_exhaustive
  simp at this
  by_cases h1 : x.isNaN
  · grind
  · by_cases h2 : x.isInfinite
    · grind
    · by_cases h3 : x.isZero
      · grind
      · by_cases h4 : x.isNonzeroSubnorm
        · grind
        · by_cases h5 : x.isNorm
          · grind
          · grind

/--
Example theorem we will prove, using our proof strategy of proving against the SMT-Lib semantics.
-/
theorem mul_eq_mul (eout sout : Nat) (rm : RoundingMode) (a b : PackedFloat ein sin) :
  Fp.SmtLibSemantics.SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin)
    rm a b = PackedFloat.mul rm a b := by
  simp [SmtLibSemantics.SmtLibFunctions.mul]
  rw [PackedFloat.mul, EUnpackedFloat.mul]
  -- need principle to do case splitting on the different cases.
  sorry

end Fp
