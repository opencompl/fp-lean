import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Multiplication
import Fp.Theorems.Packing


namespace Fp

@[simp]
theorem roundQ_eq (eout sout : Nat) (rm : RoundingMode) (sign : Bool) (r : ExtRat):
    (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ eout sout).round rm sign r =
    (SmtLibSemantics.smtLibRoundMethod eout sout
      SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
    r := rfl

set_option warn.sorry false in
@[simp]
theorem lower_NaN_eq_PackedFloat_mkNaN :
  SmtLibSemantics.smtLibLower.lower ExtRat.NaN = (PackedFloat.getNaN e s : PackedFloat e s) := sorry

set_option warn.sorry false in
@[simp]
theorem upper_NaN_eq_PackedFloat_mkNaN :
  SmtLibSemantics.smtLibUpper.upper ExtRat.NaN = (PackedFloat.getNaN e s : PackedFloat e s) := sorry

@[simp]
theorem roundRNA_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]

@[simp]
theorem roundRNE_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRNE]

@[simp]
theorem roundRTP_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTP sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]

@[simp]
theorem roundRTN_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  rcases sign <;> simp

@[simp]
theorem rountRTZ_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTZ sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ]
  rcases sign <;> simp


@[simp]
theorem round_eq_mkNaN_of_NaN {sign} {eout sout : Nat} {rm : RoundingMode} :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
        rm sign ExtRat.NaN = PackedFloat.getNaN eout sout := by
  rcases rm
  · simp
  · simp
  · simp
  · simp
  · simp

set_option warn.sorry false in
@[simp]
theorem round_eq_mkZero_of_mkZero {zeroSign : Bool} {eout sout : Nat} {rm : RoundingMode} :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
        rm zeroSign (ExtRat.Number 0) = PackedFloat.getZero eout sout zeroSign := by
  rcases rm <;> sorry

set_option warn.sorry false in
theorem roundQ_Number_eq_round (er : ExtRat) (uf : UnpackedFloat ein sin)
    (hruf : ExtRat.Number uf.toRat = er) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
      er =
      (UnpackedFloat.round uf rm).pack := by sorry


-- theorem roundQ_Number_eq_round (r : Rat) (uf : UnpackedFloat ein sin)
--     (hruf : uf.toRat = r) :
--     (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
--       (.Number r : ExtRat) =
--       (UnpackedFloat.round uf rm).pack := by sorry


-- theorem roundQ_eq_round_of_toExtRat_mkNumber :
--     (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
--       (EUnpackedFloat.mkNumber inf).toExtRat =
--       (UnpackedFloat.round inf rm).pack := by sorry

@[simp]
theorem roundQ_eq_round_of_Infinity {zeroSign infSign : Bool} {e s : Nat} {rm : RoundingMode} :
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm zeroSign
      (ExtRat.Infinity infSign) =
      PackedFloat.getInfinity e s infSign := by sorry

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

@[grind <=]
theorem PackedFloat.eq_of_unpack_eq_unpack_of_isInfinity {x y : PackedFloat e s}
    (hs : 0 < s) (he : 0 < e)
    (hx : x.isInfinite) (hy : y.isInfinite) (h : x.unpack = y.unpack) :
    x = y := by
  cases x using PackedFloat.kindCasesNaNInfZeroNum <;> try grind

set_option warn.sorry false in
/--
Example theorem we will prove, using our proof strategy of proving against the SMT-Lib semantics.
-/
theorem mul_eq_mul {ein sin : Nat} (hsin : 0 < sin) (he : 0 < ein)
    (eout sout : Nat) (rm : RoundingMode) (a b : PackedFloat ein sin) :
    Fp.SmtLibSemantics.SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin)
    rm a b = PackedFloat.mul rm a b := by
  simp [SmtLibSemantics.SmtLibFunctions.mul]
  rw [PackedFloat.mul, EUnpackedFloat.mul]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    simp [hnan]
    rw [round_eq_mkNaN_of_NaN]
  case infCase signa =>
    simp [hsin]
    rw [← ExtRat.mul_def]
    unfold ExtRat.mul
    simp
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
      -- | why does this not apply automatically?
      rw [round_eq_mkNaN_of_NaN]
    case infCase signb =>
      simp [hsin]
      rw [roundQ_eq_round_of_Infinity] -- TODO: this should just 'simp'
    case zeroCase signb =>
      simp [he]
      rw [round_eq_mkNaN_of_NaN] -- TODO: this probably suffers due to TC instantiation :(
    case numCase hb =>
      -- TODO: prove a theorem that says that 'isNumber -> ∃ r such that b.toExtRat' = Number r'.
      -- Use that to simplify the value.
      -- simp [he, hsin]
      -- | I want this to automatically apply with simp?
      -- rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      -- rw [<- PackedFloat.toExtRat_eq_toExtRat']
      -- rw [← PackedFloat.toExtRat_unpack_eq_toExtRat]
      rw [b.toExtRat'_eq_Number_of_isNormOrNonzeroSubnorm hb]
      simp [b.toNumberRat_ne_zero hb]
      simp [show ¬ b.isNaN by grind]
      simp [show ¬ b.isZero by grind]
      rw [roundQ_eq_round_of_Infinity]
      congr
      rw [b.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      simp only [EUnpackedFloat.num_mkNumber, PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign]
      -- ⊢ decide (b.toNumberRat < 0) = b.unpack.num.sign
      sorry
  case zeroCase sign =>
    simp [he]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
      rw [round_eq_mkNaN_of_NaN]
    case infCase signb =>
      simp [hsin]
      rw [round_eq_mkNaN_of_NaN] -- TODO: this probably suffers due to TC instantiation :(
    case zeroCase signb =>
      simp [he]
      rw [round_eq_mkZero_of_mkZero]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign]
      simp [show decide (ein = 0) = false by grind]
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      simp
      rw [PackedFloat.toExtRat'_eq_Number_of_isNormOrNonzeroSubnorm hb]
      simp
      rw [round_eq_mkZero_of_mkZero]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign]
      simp [show ¬ b.isNaN by grind]
      simp [show ¬ b.isInfinite by grind]
      -- TODO: prove a theorem that says that 'isNumber -> ∃ r such that b.toExtRat' = Number r'.
      -- Use that to simplify the value.
  case numCase ha =>
    rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha]
    rw [PackedFloat.toExtRat'_eq_Number_of_isNormOrNonzeroSubnorm ha]
    -- interesting case, when a is a number.
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
      rw [round_eq_mkNaN_of_NaN]
    case infCase signb =>
      simp [hsin]
      have : ¬ a.isZero := by grind
      simp [this]
      rw [← ExtRat.mul_def, ExtRat.mul]
      simp only [SmtLibSemantics.instExtendedRat, SmtLibSemantics.instExtendedRat.eq_1, roundQ_eq]
      simp [show a.toNumberRat < 0 ↔ a.sign = true by sorry]
      simp [show a.toNumberRat = 0 ↔ a.isZero by sorry]
      simp [show ¬ a.isZero by grind]
      rw [roundQ_eq_round_of_Infinity]
      grind
    case zeroCase signb =>
      simp [he]
      rw [round_eq_mkZero_of_mkZero]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign]
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      simp
      have : ¬ a.isZero := by grind
      simp [this]
      have : ¬ b.isZero := by grind
      simp [this]
      rw [roundQ_Number_eq_round]
      rw [PackedFloat.toExtRat'_eq_Number_of_isNormOrNonzeroSubnorm hb]
      simp only [ExtRat.number_mul_number_eq, ExtRat.Number.injEq]
      -- Purely arithmetic statement.
      -- ⊢ (a.unpackNormOrNonzeroSubnorm.mul b.unpackNormOrNonzeroSubnorm).toRat = a.toNumberRat * b.toNumberRat
      sorry
end Fp
