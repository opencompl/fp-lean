import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Multiplication
import Fp.Theorems.Packing


namespace Fp

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


@[simp]
theorem roundQ_eq (eout sout : Nat) (rm : RoundingMode) (sign : Bool) (r : ExtRat):
    (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ eout sout).round rm sign r =
    (SmtLibSemantics.smtLibRoundMethod eout sout
      SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
    r := rfl

@[simp]
theorem isNaN_of_isLawfulLower (x : PackedFloat e s)
   (hlower : SmtLibSemantics.IsLawfulLower ExtRat.NaN x) :
    x.isNaN := by
  simp [SmtLibSemantics.IsLawfulLower] at hlower
  simp [hlower]

@[simp]
theorem isLawfulLower_of_isNaN :
  (SmtLibSemantics.IsLawfulLower ExtRat.NaN (PackedFloat.getNaN e s)) := by
  simp only [SmtLibSemantics.IsLawfulLower]
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    PackedFloat.isNaN_getNaN, PackedFloat.toExtRat'_eq_NaN_of_isNaN, ExtRat.ge_eq_le_symm,
    ExtRat.ExtRat.le_NaN_iff, decide_true, PackedFloat.toExtRat'_eq_NaN_iff_isNaN,
    Bool.decide_eq_true, PackedFloat.le_iff_eq_of_isNaN', imp_self, implies_true, and_self]

@[simp]
theorem isLawfulLower_NaN_iff_isNaN (x : PackedFloat e s) :
   SmtLibSemantics.IsLawfulLower ExtRat.NaN x ↔ x.isNaN := by
  simp only [SmtLibSemantics.IsLawfulLower, SmtLibSemantics.smtLibV_embed_eq,
    PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm, ExtRat.ExtRat.le_NaN_iff,
    PackedFloat.toExtRat'_eq_NaN_iff_isNaN, Bool.decide_eq_true, and_iff_left_iff_imp]
  intros hx
  intros lower hlower
  simp [hx, hlower]

@[elab_as_elim]
theorem Classical.epsilon_elim {α : Sort u} {p q : α → Prop} (y : α) (hy : p y)
   (hpq : ∀ x, p x → q x) :
    q (@Classical.epsilon α (Nonempty.intro y) p) := by
  apply hpq
  apply Classical.epsilon_spec_aux
  · exists y



@[simp]
theorem IsLawfulUpper_NaN_mkNaN :
   SmtLibSemantics.IsLawfulUpper ExtRat.NaN (PackedFloat.getNaN e s) := by
  simp [SmtLibSemantics.IsLawfulUpper]

@[simp]
theorem isLawfulUpper_NaN_iff_isNaN (x : PackedFloat e s) :
   SmtLibSemantics.IsLawfulUpper ExtRat.NaN x ↔ x.isNaN := by
  simp only [SmtLibSemantics.IsLawfulUpper, SmtLibSemantics.smtLibV_embed_eq,
    PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm, ExtRat.ExtRat.NaN_le_iff,
    PackedFloat.toExtRat'_eq_NaN_iff_isNaN, Bool.decide_eq_true, and_iff_left_iff_imp]
  intros hx upper
  simp [hx]

@[simp]
theorem isNaN_upper_NaN :
  (SmtLibSemantics.smtLibUpper.upper ExtRat.NaN : PackedFloat e s).isNaN := by
  simp only [SmtLibSemantics.smtLibUpper, isLawfulUpper_NaN_iff_isNaN]
  apply Classical.epsilon_elim (q := fun (x : PackedFloat e s) => x.isNaN) (y := PackedFloat.getNaN e s)
  · simp
  · simp

@[simp]
theorem isNaN_lower_NaN (e s : Nat) :
    (SmtLibSemantics.smtLibLower.lower ExtRat.NaN : PackedFloat e s).isNaN := by
  simp [SmtLibSemantics.smtLibLower]
  apply Classical.epsilon_elim (q := fun (x : PackedFloat e s) => x.isNaN) (y := PackedFloat.getNaN e s)
  · simp
  · intros x hx
    simp [hx]

@[simp]
theorem roundRNA_mkNaN (eout sout : Nat) (sign : Bool) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
    (ExtRat.NaN)).isNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]

@[simp]
theorem roundRNE_mkNaN (eout sout : Nat) (sign : Bool) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
    (ExtRat.NaN)).isNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRNE, SmtLibSemantics.ExtendedNumber.isNaN]

@[simp]
theorem roundRTP_mkNaN (eout sout : Nat) (sign : Bool) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTP sign
    (ExtRat.NaN)).isNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]



@[simp]
theorem roundRTN_mkNaN (eout sout : Nat) (sign : Bool) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN sign
    (ExtRat.NaN)).isNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  simp [SmtLibSemantics.ExtendedNumber.isZero, SmtLibSemantics.ExtendedNumber.smtLibEq]


@[simp]
theorem roundRTZ_mkNaN {eout sout : Nat} {sign : Bool} :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTZ sign
    (ExtRat.NaN)).isNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ, SmtLibSemantics.ExtendedNumber.isZero, ExtRat.eq,
    SmtLibSemantics.ExtendedNumber.gtZero, SmtLibSemantics.ExtendedNumber.smtLibEq,
    SmtLibSemantics.ExtendedNumber.ltZero]

@[simp]
theorem isNaN_round_of_nan {sign} {eout sout : Nat} {rm : RoundingMode} :
    ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
        rm sign ExtRat.NaN).isNaN := by
  rcases rm <;> simp


@[simp]
theorem IsLawfulLower_Zero_iff (x : PackedFloat e s) (he : 0 < e) :
   SmtLibSemantics.IsLawfulLower (ExtRat.Number 0) x ↔ (x = PackedFloat.getZero e s false) := by
  simp [SmtLibSemantics.IsLawfulLower]
  constructor
  · intros h
    obtain ⟨h1, h2⟩ := h
    specialize h2 (PackedFloat.getZero e s false)
    simp [PackedFloat.isZero_getZero, he, decide_true,
      Bool.not_eq_true, forall_const] at h2
    specialize (h2 (by grind))
    by_cases hzero : x.isZero
    · simp [hzero] at h1
      simp [h1] at h2
      grind only [PackedFloat.eq_mkZero_of_isZero']
    · simp [hzero] at h1
      grind only
  · intros h
    simp [h]
    simp [he]
    constructor
    · grind
    · intros lower hlower
      by_cases hzero : lower.isZero
      · simp [hzero]
        have hlower : lower = PackedFloat.getZero e s lower.sign := by
          grind only [PackedFloat.eq_mkZero_of_isZero']
        rw [hlower]
        simp [he]
      · simp [hzero]
        intros hsign
        apply PackedFloat.le_of_sign_eq_true_sign_eq_false
        · grind
        · grind
        · grind
        · grind

@[simp]
theorem lower_zero_eq {eout sout : Nat} (heout : 0 < eout)  :
  (SmtLibSemantics.smtLibLower.lower (ExtRat.Number 0) : PackedFloat eout sout) =
    PackedFloat.getZero eout sout false := by
  simp [SmtLibSemantics.smtLibLower]
  apply Classical.epsilon_elim (q := fun (x : PackedFloat eout sout) => x = PackedFloat.getZero eout sout false)
    (y := PackedFloat.getZero eout sout false)
  · rw [IsLawfulLower_Zero_iff]
    · grind
  · intros x hx
    simp [IsLawfulLower_Zero_iff, heout] at hx
    simp [hx]

-- TODO: Can we somehow unify the lower/upper proofs?
@[simp]
theorem IsLawfulUpper_Zero_iff (x : PackedFloat e s) (he : 0 < e) :
   SmtLibSemantics.IsLawfulUpper (ExtRat.Number 0) x ↔ ((x = PackedFloat.getZero e s true)):= by
  simp [SmtLibSemantics.IsLawfulUpper]
  constructor
  · intros h
    obtain ⟨h1, h2⟩ := h
    specialize h2 (PackedFloat.getZero e s true)
    simp [PackedFloat.isZero_getZero, he, decide_true,
      Bool.not_eq_true, forall_const] at h2
    specialize (h2 (by grind))
    by_cases hzero : x.isZero
    · simp [hzero] at h1
      simp [h1] at h2
      grind only [PackedFloat.eq_mkZero_of_isZero']
    · simp [hzero] at h1
      grind only
  · intros h
    simp [h]
    simp [he]
    constructor
    · grind
    · intros upper hupper
      by_cases hzero : upper.isZero
      · simp [hzero]
        have hupper : upper = PackedFloat.getZero e s upper.sign := by
          grind only [PackedFloat.eq_mkZero_of_isZero']
        rw [hupper]
        simp [he]
      · simp [hzero]
        intros hsign
        apply PackedFloat.le_of_sign_eq_true_sign_eq_false
        · grind
        · grind
        · grind
        · grind


@[simp]
theorem upper_zero_eq {eout sout : Nat} (heout : 0 < eout) :
  (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number 0) : PackedFloat eout sout) =
    PackedFloat.getZero eout sout true := by
  simp [SmtLibSemantics.smtLibUpper]
  apply Classical.epsilon_elim (q := fun (x : PackedFloat eout sout) => x = PackedFloat.getZero eout sout true)
    (y := PackedFloat.getZero eout sout true)
  · rw [IsLawfulUpper_Zero_iff]
    · grind
  · intros x hx
    simp [IsLawfulUpper_Zero_iff, heout] at hx
    simp [hx]

@[simp]
theorem roundRTZ_zero {eout sout : Nat} {zeroSign : Bool} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTZ zeroSign
    (ExtRat.Number 0)) = PackedFloat.getZero eout sout zeroSign := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  rcases zeroSign
  case false =>
    simp [lower_zero_eq, heout]
  case true =>
    simp [upper_zero_eq, heout]

@[simp]
theorem roundRNA_zero {eout sout : Nat} {zeroSign : Bool} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA zeroSign
    (ExtRat.Number 0)) = PackedFloat.getZero eout sout zeroSign := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  rcases zeroSign
  case false =>
    simp [lower_zero_eq, heout]
  case true =>
    simp [upper_zero_eq, heout]

@[simp]
theorem roundRNE_zero {eout sout : Nat} {zeroSign : Bool} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE zeroSign
    (ExtRat.Number 0)) = PackedFloat.getZero eout sout zeroSign := by
  simp [SmtLibSemantics.RoundMethod.roundRNE]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  rcases zeroSign
  case false =>
    simp [lower_zero_eq, heout]
  case true =>
    simp [upper_zero_eq, heout]

@[simp]
theorem roundRTN_zero {eout sout : Nat} {zeroSign : Bool} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN zeroSign
    (ExtRat.Number 0)) = PackedFloat.getZero eout sout zeroSign := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  simp [SmtLibSemantics.ExtendedNumber.isZero, SmtLibSemantics.ExtendedNumber.smtLibEq]
  rcases zeroSign
  case false =>
    simp [lower_zero_eq, heout]
  case true =>
    simp [upper_zero_eq, heout]

@[simp]
theorem roundRTP_zero {eout sout : Nat} {zeroSign : Bool} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTP zeroSign
    (ExtRat.Number 0)) = PackedFloat.getZero eout sout zeroSign := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]
  simp [SmtLibSemantics.ExtendedNumber.isZero, SmtLibSemantics.ExtendedNumber.smtLibEq]
  rcases zeroSign
  case false =>
    simp [lower_zero_eq, heout]
  case true =>
    simp [upper_zero_eq, heout]

@[simp]
theorem round_eq_mkZero_of_mkZero {zeroSign : Bool} {eout sout : Nat} {rm : RoundingMode}
   (heout : 0 < eout) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
        rm zeroSign (ExtRat.Number 0) = PackedFloat.getZero eout sout zeroSign := by
  rcases rm <;> simp [heout]

/-
(SmtLibSemantics.smtLibRoundMethod ein sin SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm
    (SmtLibSemantics.SmtLibFunctions.xorSign a b) (ExtRat.Number a.toRat * b.toExtRat') =
  ((a.unpackNormOrNonzeroSubnorm.mul b.unpackNormOrNonzeroSubnorm).round rm).pack
-/
-- | TODO: find the right theorem statement here,
-- we should talk about guard and sticky bits and whatnot.
set_option warn.sorry false in
theorem SmtLibSemantics_round_eq_pack_UnpackedFloat_round {rm : RoundingMode}
    {ein sin eout sout : Nat} {sign : Bool}
    (er : ExtRat) {r : Rat} (uf : UnpackedFloat ein sin)
    (hr : er = ExtRat.Number r)
    -- | round works correctly as long as our number is close enough.
    (hApprox : (uf.toRat - r).abs < ((2 : Rat) ^ (- (eout : Int)))) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign er =
    (UnpackedFloat.round uf rm).pack := by
  sorry

@[simp]
theorem IsLawfulLower_Infinity_iff (x : PackedFloat e s)
    (he : 0 < e) (hs : 0 < s) :
   SmtLibSemantics.IsLawfulLower (ExtRat.Infinity sign) x ↔ (x = PackedFloat.getInfinity e s sign) := by
  simp [SmtLibSemantics.IsLawfulLower]
  constructor
  · intros h
    obtain ⟨h1, h2⟩ := h
    induction x using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase n hnan =>
      simp [hnan] at h1
    case infCase signx =>
      simp [hs] at h1
      specialize h2 (PackedFloat.getInfinity e s sign)
      simp [hs] at h2
      grind only [Bool]
    case zeroCase signx =>
      simp [he, hs] at h1
      subst h1
      simp at h2
      specialize (h2 (PackedFloat.getInfinity e s false))
      simp [hs] at h2
      exact h2
    case numCase n hn =>
      specialize h2 (PackedFloat.getInfinity e s sign)
      simp [hs] at h2
      rw [n.toExtRat'_eq_toRat_of] at h1
      simp at h1
      subst h1
      simp [hs] at h2
      exact h2
  · intros h
    subst h
    simp [hs]
    intros lower hlower
    rcases sign
    case false =>
      simp [hs] at hlower ⊢
      grind only [=> PackedFloat.le_getInfinity_false_of_not_isNaN]
    case true =>
      simpa [he, hs] using hlower

@[simp]
theorem IsLawfulUpper_Infinity_iff (x : PackedFloat e s)
    (he : 0 < e) (hs : 0 < s) :
   SmtLibSemantics.IsLawfulUpper (ExtRat.Infinity sign) x ↔ (x = PackedFloat.getInfinity e s sign) := by
  simp [SmtLibSemantics.IsLawfulUpper]
  constructor
  · intros h
    obtain ⟨h1, h2⟩ := h
    induction x using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase n hnan =>
      simp [hnan] at h1
    case infCase signx =>
      simp [hs] at h1
      specialize h2 (PackedFloat.getInfinity e s sign)
      simp [hs] at h2
      grind only [Bool]
    case zeroCase signx =>
      simp [he, hs] at h1
      subst h1
      simp at h2
      specialize (h2 (PackedFloat.getInfinity e s true))
      simp [hs] at h2
      exact h2
    case numCase n hn =>
      specialize h2 (PackedFloat.getInfinity e s sign)
      simp [hs] at h2
      rw [n.toExtRat'_eq_toRat_of] at h1
      simp at h1
      subst h1
      simp [he, hs] at h2
      exact h2
  · intros h
    subst h
    simp [hs]
    intros upper hupper
    rcases sign
    case false =>
      simp [hs] at hupper ⊢
      grind only [=> PackedFloat.le_getInfinity_false_of_not_isNaN]
    case true =>
      simp? [he, hs] at hupper ⊢
      exact hupper

@[simp]
theorem lower_infinity_eq_getInfinity {e s} (sign : Bool) (he : 0 < e) (hs : 0 < s) :
  (SmtLibSemantics.smtLibLower.lower (ExtRat.Infinity sign) : PackedFloat e s) =
    PackedFloat.getInfinity e s sign := by
  simp [SmtLibSemantics.smtLibLower]
  apply Classical.epsilon_elim (q := fun (x : PackedFloat e s) => x = PackedFloat.getInfinity e s sign)
    (y := PackedFloat.getInfinity e s sign)
  · simp [SmtLibSemantics.IsLawfulLower, hs]
    intros lower hlower
    rcases sign
    case false =>
      simp at hlower
      simp [hs]
      simp [hlower]
    case true =>
      simp at hlower
      simp [hs] at hlower
      subst hlower
      simp
  · intros x hx
    grind only [IsLawfulLower_Infinity_iff]

@[simp]
theorem upper_infinity_eq_getInfinity {e s} (sign : Bool) (he : 0 < e) (hs : 0 < s) :
  (SmtLibSemantics.smtLibUpper.upper (ExtRat.Infinity sign) : PackedFloat e s) =
    PackedFloat.getInfinity e s sign := by
  simp [SmtLibSemantics.smtLibUpper]
  apply Classical.epsilon_elim (q := fun (x : PackedFloat e s) => x = PackedFloat.getInfinity e s sign)
    (y := PackedFloat.getInfinity e s sign)
  · simp [SmtLibSemantics.IsLawfulUpper, hs]
    intros upper hupper
    rcases sign
    case false =>
      simp [hs] at hupper ⊢
      grind only [=> PackedFloat.le_getInfinity_false_of_not_isNaN]
    case true =>
      simp? [he, hs] at hupper ⊢
      exact hupper
  · intros x hx
    grind only [IsLawfulUpper_Infinity_iff]

@[simp]
theorem roundRNA_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  simp [lower_infinity_eq_getInfinity infSign heout hsout]
  simp [lower_infinity_eq_getInfinity infSign heout (show 0 < sout + 1 by grind)]
  simp [heout, hsout]

@[simp]
theorem roundRNE_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRNE]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  simp [lower_infinity_eq_getInfinity infSign heout hsout]
  simp [lower_infinity_eq_getInfinity infSign heout (show 0 < sout + 1 by grind)]
  simp [heout, hsout]

@[simp]
theorem roundRTP_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTP sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]
  simp [SmtLibSemantics.ExtendedNumber.isNaN]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  simp [SmtLibSemantics.ExtendedNumber.gtZero, SmtLibSemantics.ExtendedNumber.ltZero]
  rcases infSign
  case false =>
    simp [upper_infinity_eq_getInfinity _ heout hsout]
  case true =>
    simp
    rcases sign
    case false =>
      simp [lower_infinity_eq_getInfinity _ heout hsout]
    case true =>
      simp [upper_infinity_eq_getInfinity _ heout hsout]

@[simp]
theorem roundRTN_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  simp [lower_infinity_eq_getInfinity infSign heout hsout]

@[simp]
theorem roundRTZ_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTZ sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ]
  simp [SmtLibSemantics.ExtendedNumber.isZero]
  simp [SmtLibSemantics.ExtendedNumber.smtLibEq]
  simp [SmtLibSemantics.ExtendedNumber.gtZero]
  simp [SmtLibSemantics.ExtendedNumber.ltZero]
  rcases infSign
  case false =>
    simp [lower_infinity_eq_getInfinity _ heout hsout]
  case true =>
    simp [upper_infinity_eq_getInfinity _ heout hsout]


@[simp]
theorem roundQ_eq_round_of_Infinity {zeroSign infSign : Bool} {e s : Nat} {rm : RoundingMode} (he : 0 < e ) (hs : 0 < s) :
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm zeroSign
      (ExtRat.Infinity infSign) =
      PackedFloat.getInfinity e s infSign := by
  cases rm
  · simp [he, hs]
  · simp [he, hs]
  · simp [he, hs]
  · simp [he, hs]
  · simp [he, hs]

@[grind <=]
theorem PackedFloat.eq_of_unpack_eq_unpack_of_isInfinity {x y : PackedFloat e s}
    (hs : 0 < s) (he : 0 < e)
    (hx : x.isInfinite) (hy : y.isInfinite) (h : x.unpack = y.unpack) :
    x = y := by
  cases x using PackedFloat.kindCasesNaNInfZeroNum <;> try grind

def EquivUptoNaN {e s : Nat} (x y : PackedFloat e s) : Prop :=
  x = y ∨ (x.isNaN ∧ y.isNaN)

theorem EquivUptoNaN.of_isNaN_isNaN (x y : PackedFloat e s) (hx : x.isNaN) (hy : y.isNaN) : EquivUptoNaN x y :=
  by simp [EquivUptoNaN, hx, hy]

theorem EquivUptoNaN.of_eq (x y : PackedFloat e s) (h : x = y) : EquivUptoNaN x y := by simp [EquivUptoNaN, h]

@[simp]
theorem EquivUptoNaN.of_mkNaN_iff (x : PackedFloat e s) : EquivUptoNaN x (PackedFloat.getNaN e s) ↔ x.isNaN := by
  simp [EquivUptoNaN]
  grind only [!PackedFloat.isNaN_mkNaN]

-- Why do we need upto (s + 2) to approximate `y` with `approx`
def CorrectlyApproximated (sout : Nat) (y : Rat) (approx : Rat) : Prop :=
  (y - approx).abs < 2 ^ (- ((sout + 1): Int)) ∧
  True -- TODO: I need to figure out what it means to have the sticky bit in a purely 'non-discrete' way

def CorrectlyApproximated.mk (sout : Nat) (y : Rat) (approx : Rat)
  (hguard : (y - approx).abs < 2 ^ (- (sout + 1 : Int))) :
  CorrectlyApproximated sout y approx := by
  simp [CorrectlyApproximated, hguard]




theorem unpackNum_mul_unpackNum_toRat_eq_mul_toRat
    {a b : PackedFloat e s}
    (ha : a.isNormOrNonzeroSubnorm)
    (hb : b.isNormOrNonzeroSubnorm) :
    ((a.unpackNum.mul b.unpackNum).toRat - a.toRat * b.toRat).abs <
  2 ^ (- (e : Int)) := by
  have ha : a.toRat = a.unpackNum.toRat := by grind
  rw [ha]
  have hb : b.toRat = b.unpackNum.toRat := by grind
  rw [hb]
  sorry


set_option warn.sorry false in
/--
Example theorem we will prove, using our proof strategy of proving against the SMT-Lib semantics.
-/
theorem mul_eq_mul {ein sin : Nat} (hsin : 0 < sin) (he : 0 < ein)
    (rm : RoundingMode) (a b : PackedFloat ein sin) :
    EquivUptoNaN
      (Fp.SmtLibSemantics.SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b)
    (PackedFloat.mul rm a b) := by
  simp [SmtLibSemantics.SmtLibFunctions.mul]
  rw [PackedFloat.mul, EUnpackedFloat.mul]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    simp [hnan]
  case infCase signa =>
    simp [hsin]
    rw [← ExtRat.mul_def]
    unfold ExtRat.mul
    simp
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
    case infCase signb =>
      simp [hsin]
      apply EquivUptoNaN.of_eq
      simp [hsin, he]
    case zeroCase signb =>
      simp [he]
    case numCase hb =>
      -- TODO: prove a theorem that says that 'isNumber -> ∃ r such that b.toExtRat' = Number r'.
      -- Use that to simplify the value.
      -- simp [he, hsin]
      -- | I want this to automatically apply with simp?
      -- rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      -- rw [<- PackedFloat.toExtRat_eq_toExtRat']
      -- rw [← PackedFloat.toExtRat_unpack_eq_toExtRat]
      rw [b.toExtRat'_eq_toRat_of hb]
      simp [b.toRat_ne_zero hb]
      simp [show ¬ b.isNaN by grind]
      simp [show ¬ b.isZero by grind]
      apply EquivUptoNaN.of_eq
      have : b.unpack.num.sign = decide (b.toRat < 0) := by
        rw [b.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
        simp only [EUnpackedFloat.num_mkNumber, PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign]
        grind only [→ PackedFloat.sign_iff_toRat_neg]
      simp [this, hsin, he]
  case zeroCase sign =>
    simp [he]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
    case infCase signb =>
      simp [hsin]
    case zeroCase signb =>
      simp [he]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign, hsin]
      simp [show decide (ein = 0) = false by grind]
      apply EquivUptoNaN.of_eq
      grind only
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      simp
      rw [b.toExtRat'_eq_toRat_of hb]
      simp only [ExtRat.number_mul_number_eq, Rat.zero_mul, round_eq_mkZero_of_mkZero, he, hsin]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign]
      simp [show ¬ b.isNaN by grind]
      simp [show ¬ b.isInfinite by grind]
      apply EquivUptoNaN.of_eq
      grind only
      -- TODO: prove a theorem that says that 'isNumber -> ∃ r such that b.toExtRat' = Number r'.
      -- Use that to simplify the value.
  case numCase ha =>
    rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha]
    rw [a.toExtRat'_eq_toRat_of ha]
    -- interesting case, when a is a number.
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
    case infCase signb =>
      simp [hsin]
      have : ¬ a.isZero := by grind
      simp [this]
      rw [← ExtRat.mul_def, ExtRat.mul]
      simp only [SmtLibSemantics.instExtendedRat, SmtLibSemantics.instExtendedRat.eq_1, roundQ_eq]
      simp [show a.toRat < 0 ↔ a.sign = true by grind]
      simp [show a.toRat = 0 ↔ a.isZero by grind]
      simp [show ¬ a.isZero by grind]
      apply EquivUptoNaN.of_eq
      simp [hsin, he]
      rw [show (signb ^^ a.sign) = (a.sign ^^ signb) by grind]
    case zeroCase signb =>
      simp [he]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign, hsin]
      apply EquivUptoNaN.of_eq
      grind only
    case numCase hb =>
      simp [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      rw [b.toExtRat'_eq_toRat_of hb]
      have : ¬ a.isZero := by grind
      simp [this]
      have : ¬ b.isZero := by grind
      simp [this]
      apply EquivUptoNaN.of_eq
      rw [SmtLibSemantics_round_eq_pack_UnpackedFloat_round (r := a.toRat * b.toRat)]
      · simp
      · apply unpackNum_mul_unpackNum_toRat_eq_mul_toRat
        · grind
        · grind
end Fp
