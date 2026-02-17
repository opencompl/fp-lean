import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Multiplication
import Fp.Theorems.Packing


namespace Fp
open SmtLibSemantics

@[simp]
theorem roundQ_eq (eout sout : Nat) (rm : RoundingMode) (sign : Bool) (r : ExtRat):
    (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ eout sout).round rm sign r =
    (SmtLibSemantics.smtLibRoundMethod eout sout
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).round rm sign
    r := rfl

set_option warn.sorry false in
@[simp]
theorem lower_NaN_eq_PackedFloat_getNaN :
  SmtLibSemantics.smtLibLower.lower ExtRat.NaN = (PackedFloat.getNaN e s) := sorry

set_option warn.sorry false in
@[simp]
theorem upper_NaN_eq_PackedFloat_getNaN :
  SmtLibSemantics.smtLibUpper.upper ExtRat.NaN = (PackedFloat.getNaN e s) := sorry

@[simp]
theorem roundRNA_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).roundRNA sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]

@[simp]
theorem roundRNE_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).roundRNE sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRNE]

@[simp]
theorem roundRTP_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).roundRTP sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]

@[simp]
theorem roundRTN_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).roundRTN sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  rcases sign <;> simp

@[simp]
theorem rountRTZ_mkNaN (eout sout : Nat) (sign : Bool) :
  (SmtLibSemantics.smtLibRoundMethod eout sout
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
    (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).roundRTZ sign
    (ExtRat.NaN) = PackedFloat.getNaN eout sout := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ]
  rcases sign <;> simp


@[simp]
theorem round_eq_mkNaN_of_NaN {sign} {eout sout : Nat} {rm : RoundingMode} :
    (SmtLibSemantics.smtLibRoundMethod eout sout
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))).round
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
    (SmtLibSemantics.smtLibRoundMethod eout sout
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))
    ).round
        rm zeroSign (ExtRat.Number 0) = PackedFloat.getZero eout sout zeroSign := by
  rcases rm <;> sorry

/--
'uf' approximtes 'r' upto rounding.
-/
structure ApproximatesUptoRounding (uf : UnpackedFloat ein sin) (er : ExtRat) (eout sout : Nat) : Prop where
  /-- we have at least 2 bits more, of guard and sticky. -/
  hSigGe : sin + 2 ≥ sout
  /-- we have at least as much exponent range. -/
  hExpGe : ein ≥ eout -- we have at least as much exponent range
  /-- rational values have (sout + 1) bits of precision. -/
  hApproxUptoGuard : ∀ (r : Rat), .Number r = er → (uf.toRat - r).abs < (2 : Rat) ^ (-(sout + 1 : Int))
  /-- the sticky bit is zero iff the number truncated upto the guard bit equals -/
  hStickyBitCorrect : ∀ (r : Rat), .Number r = er → ((uf.sig.extractMsb' (sout + 1) (sin - (sout + 1)) ≠ 0) = decide (r = uf.toRat))

set_option warn.sorry false in
theorem roundQ_Number_eq_round
    (er : ExtRat) (uf : UnpackedFloat ein sin)
    (hruf : ApproximatesUptoRounding uf er eout sout) (rm : RoundingMode) (sign : Bool) :
    (SmtLibSemantics.smtLibRoundMethod eout sout
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout sout))
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat eout (sout + 1)))
    ).round rm sign
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
    (SmtLibSemantics.smtLibRoundMethod e s
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat e s))
      (SmtLibSemantics.smtLibV (SmtLibSemantics.embedPackedFloatExtRat e (s + 1)))
    ).round rm zeroSign
      (ExtRat.Infinity infSign) =
      PackedFloat.getInfinity e s infSign := by sorry


@[grind <=]
theorem PackedFloat.eq_of_unpack_eq_unpack_of_isInfinity {x y : PackedFloat e s}
    (hs : 0 < s) (he : 0 < e)
    (hx : x.isInfinite) (hy : y.isInfinite) (h : x.unpack = y.unpack) :
    x = y := by
  cases x using PackedFloat.classification <;> try grind

/--
Purely arithmetic fact that needs to be proven,
which should just be to show that the fixed point computation equals the
rational multiplication.
Actually, this is too strong, the theorem statemtnt should be able to state
something weaker, that only upto (s+1) bits agree,
and that the sticky bit is computed correctly.
-/
theorem ApproximatesUptoRounding_mul_mul
  (a b : PackedFloat ein sin)
  (ha : a.isNormOrNonzeroSubnorm = true)
  (hb : b.isNormOrNonzeroSubnorm = true) :
  ApproximatesUptoRounding (a.unpackNormOrNonzeroSubnorm.mul b.unpackNormOrNonzeroSubnorm)
  (ExtRat.Number a.toNumberRat * ExtRat.Number b.toNumberRat) ein sin := sorry

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
  cases a using PackedFloat.classification
  case nanCase hnan =>
    simp [hnan]
    rw [round_eq_mkNaN_of_NaN]
  case infCase signa =>
    simp [hsin]
    rw [← ExtRat.mul_def]
    unfold ExtRat.mul
    simp
    cases b using PackedFloat.classification
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
    cases b using PackedFloat.classification
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
    cases b using PackedFloat.classification
    case nanCase hb =>
      simp [hb]
      rw [round_eq_mkNaN_of_NaN]
    case infCase signb =>
      simp [hsin]
      have : ¬ a.isZero := by grind
      simp [this]
      rw [← ExtRat.mul_def, ExtRat.mul]
      simp only [SmtLibSemantics.instExtendedRat, SmtLibSemantics.instExtendedRat.eq_1, roundQ_eq]
      simp [show a.toNumberRat < 0 ↔ a.sign = true by grind only [→
          PackedFloat.sign_iff_toNumberRat_neg,
        #34bd]]
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
      rw [PackedFloat.toExtRat'_eq_Number_of_isNormOrNonzeroSubnorm hb]
      apply roundQ_Number_eq_round
      apply ApproximatesUptoRounding_mul_mul <;> assumption
end Fp
