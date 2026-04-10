import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing
import Fp.Theorems.Negation
import Fp.Theorems.Ordering

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



@[simp]
theorem roundRTN_mkNaN (eout sout : Nat) (sign : Bool) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN sign
    (ExtRat.NaN)).isNaN := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]


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
  rcases zeroSign
  case false =>
    simp [lower_zero_eq, heout]
  case true =>
    simp [upper_zero_eq, heout]

theorem isZero_round_zero {eout sout : Nat} {zeroSign : Bool} {rm : RoundingMode} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
    rm zeroSign (ExtRat.Number 0)).isZero = true := by
  rcases rm <;> simp [heout]

/-- rounding a number never produces NaN. -/
theorem isNaN_round_number_eq_false {eout sout : Nat} {zeroSign : Bool} {rm : RoundingMode} {r : Rat} (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
    rm zeroSign (ExtRat.Number r)).isNaN = false := by
  sorry

@[simp]
theorem round_eq_mkZero_of_mkZero {zeroSign : Bool} {eout sout : Nat} {rm : RoundingMode}
   (heout : 0 < eout) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
        rm zeroSign (ExtRat.Number 0) = PackedFloat.getZero eout sout zeroSign := by
  rcases rm <;> simp [heout]

set_option warn.sorry false in
/--
Find the right theorem statement here,
we should talk about guard and sticky bits and whatnot.
-/
theorem SmtLibSemantics_round_eq_pack_UnpackedFloat_round {rm : RoundingMode}
    {ein sin eout sout : Nat} {sign : Bool}
    (er : ExtRat) {r : Rat} (uf : UnpackedFloat ein sin)
    (hnorm : uf.sig.msb = true)
    (hr : er = ExtRat.Number r)
    -- | round works correctly as long as our number is close enough.
    (hApprox : (uf.toRat = r)) :
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
      simp only [hnan, PackedFloat.toExtRat'_eq_NaN_of_isNaN, ExtRat.ExtRat.NaN_le_iff,
        decide_eq_true_eq, ExtRat.ExtRat.le_refl, ExtRat.ExtRat.eq_of_le_of_le,
        ExtRat.ExtRat.le_NaN_iff, reduceCtorEq, decide_false, Bool.false_eq_true] at h1
    case infCase signx =>
      simp only [hs, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
        ExtRat.ExtRat.infinity_le_infinity_iff, decide_implies, Bool.decide_eq_false, dite_eq_ite,
        Bool.if_true_right, Bool.not_not, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at h1
      specialize h2 (PackedFloat.getInfinity e s sign)
      simp only [hs, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
        ExtRat.ExtRat.le_refl, PackedFloat.getInfinity_le_getInfinity_iff_of_lt,
        forall_const] at h2
      grind only [Bool]
    case zeroCase signx =>
      simp only [PackedFloat.isZero_getZero, he, decide_true,
        PackedFloat.toExtRat'_eq_zero_of_isZero, ExtRat.infinity_le_number_iff] at h1
      subst h1
      simp at h2
      specialize (h2 (PackedFloat.getInfinity e s true))
      simp only [hs, PackedFloat.isNaN_getInfinity_eq_false, decide_true, Bool.not_true,
        PackedFloat.le_getInfinity_true_iff_eq, forall_const] at h2
      exact h2
    case numCase n hn =>
      specialize h2 (PackedFloat.getInfinity e s sign)
      simp only [hs, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
        ExtRat.ExtRat.le_refl, forall_const] at h2
      rw [n.toExtRat'_eq_toRat_of] at h1
      simp at h1
      subst h1
      simp [hs] at h2
      exact h2
  · intros h
    subst h
    simp [hs]
    intros upper hupper
    rcases sign
    case false =>
      simp only [ExtRat.ExtRat.inf_false_le_iff, decide_eq_true_eq, hs,
        PackedFloat.eq_getInfinity_iff_toExtRat'_eq_Infinity,
        PackedFloat.PackedFloat.getInfinity_false_le_iff_eq] at hupper ⊢
      grind only [=> PackedFloat.le_getInfinity_false_of_not_isNaN]
    case true =>
      simp only [hs, ExtRat.ExtRat.inf_true_le_iff,  ne_eq, PackedFloat.toExtRat'_eq_NaN_iff_isNaN, Bool.not_eq_true,
        Bool.decide_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true,
        PackedFloat.PackedFloat.getInfinity_true_le_of_not_isNaN] at hupper ⊢
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
      simp only [hs, ExtRat.ExtRat.inf_true_le_iff, ne_eq, PackedFloat.toExtRat'_eq_NaN_iff_isNaN, Bool.not_eq_true,
        Bool.decide_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true,
        PackedFloat.PackedFloat.getInfinity_true_le_of_not_isNaN] at hupper ⊢
      exact hupper
  · intros x hx
    grind only [IsLawfulUpper_Infinity_iff]

@[simp]
theorem roundRNA_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNA sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRNA]
  simp [lower_infinity_eq_getInfinity infSign heout hsout]
  simp [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
  simp [lower_infinity_eq_getInfinity infSign heout (show 0 < sout + 1 by grind)]
  simp [heout, hsout]
  intros ha hb
  rcases infSign
  · simp at ha
  · simp at hb

@[simp]
theorem roundRNE_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRNE]
  simp [lower_infinity_eq_getInfinity infSign heout hsout]
  simp [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
  simp [lower_infinity_eq_getInfinity infSign heout (show 0 < sout + 1 by grind)]
  simp [heout, hsout]

@[simp]
theorem roundRTP_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTP sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRTP]
  simp [heout, hsout]

@[simp]
theorem roundRTN_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTN sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRTN]
  simp [lower_infinity_eq_getInfinity infSign heout hsout]

@[simp]
theorem roundRTZ_mkInfinity (eout sout : Nat) (sign : Bool) (heout : 0 < eout) (hsout : 0 < sout) :
   ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRTZ sign
    (ExtRat.Infinity infSign)) = (PackedFloat.getInfinity eout sout infSign) := by
  simp [SmtLibSemantics.RoundMethod.roundRTZ]
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

#check SmtLibSemantics.RoundMethod.round

/--
isEven alternates between numbers.
-/
theorem isEven_lower_eq_not_isEven_upper (eout sout : Nat) (r : Rat) :
  (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r)) =
  ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)) := by
  sorry

theorem isEven_upper_eq_not_isEven_lower (eout sout : Nat) (r : Rat) :
  (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)) =
  ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r)) := by
  have := isEven_lower_eq_not_isEven_upper eout sout r
  grind only [#9ad2]

axiom embed_lower_le_self {e s : Nat} (r : ExtRat) :
    SmtLibSemantics.RoundableEmbed.embed
      (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) ≤ r -- := by
--  sorry

axiom le_lower_of_embed_le
    {e s : Nat} (r : ExtRat) (lower' : PackedFloat e s)
    (hlower' : SmtLibSemantics.RoundableEmbed.embed lower' ≤ r) :
    lower' ≤ SmtLibSemantics.smtLibLower.lower r

-- := by
--  sorry

theorem isLawfulLower_lower (e s : Nat) (r : ExtRat) :
    SmtLibSemantics.IsLawfulLower r (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) := by
  constructor
  · apply embed_lower_le_self <;> grind only
  · intros lower' hlower'
    apply le_lower_of_embed_le <;> grind only


@[simp]
theorem not_isNaN_lower_of_ne_NaN (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s).isNaN = false := by
  by_cases hnan : (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s).isNaN
  · exfalso
    have hembed := embed_lower_le_self (e := e) (s := s) r
    simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat'] at hembed
    rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN _ hnan] at hembed
    have := (ExtRat.le_NaN _).mp hembed
    exact hr this
  · simp [hnan]


@[simp]
theorem not_isNaN_lower_neg_of_ne_NaN (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower (-r) : PackedFloat e s).isNaN = false := by
  apply not_isNaN_lower_of_ne_NaN
  simp [ExtRat.neg_eq_NaN_iff, hr]

axiom self_le_embed_upper {e s : Nat} (r : ExtRat) :
    r ≤ SmtLibSemantics.RoundableEmbed.embed
      (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) -- := by
  -- sorry

axiom le_upper_of_self_le_embed
    {e s : Nat} (r : ExtRat) (upper' : PackedFloat e s)
    (hupper' : r ≤ SmtLibSemantics.RoundableEmbed.embed upper') :
    SmtLibSemantics.smtLibUpper.upper r ≤ upper' -- := by
  -- sorry


@[simp]
theorem not_isNaN_upper_of_ne_NaN (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s).isNaN = false := by
  by_cases hnan : (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s).isNaN
  · exfalso
    have hembed := self_le_embed_upper (e := e) (s := s) r
    simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat'] at hembed
    rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN _ hnan] at hembed
    simp at hembed
    grind only
  · simp [hnan]

theorem isLawfulUpper_upper (e s : Nat) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) := by
  constructor
  · apply self_le_embed_upper <;> grind only
  · intros upper' hupper'
    apply le_upper_of_self_le_embed <;> grind only

/--
two lawful uppers are equal to each other.
-/
theorem eq_of_IsLawfulUpper_of_IsLawfulUpper
    (e s : Nat) (r : ExtRat) (x y : PackedFloat e s)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hupperx : SmtLibSemantics.IsLawfulUpper r x)
    (huppery : SmtLibSemantics.IsLawfulUpper r y) :
    x = y := by
  have rlex := hupperx.1
  have rley := huppery.1
  have rlex' := hupperx.2 y rley
  have rley' := huppery.2 x rlex
  grind only [PackedFloat.le_antisymm_of_ne_NaN]


/--
two lawful lowers are equal to each other.
-/
theorem eq_of_IsLawfulLower_of_IsLawfulLower
    (e s : Nat) (r : ExtRat) (x y : PackedFloat e s)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hlowerx : SmtLibSemantics.IsLawfulLower r x)
    (hlowery : SmtLibSemantics.IsLawfulLower r y) :
    x = y := by
  have rlex := hlowerx.1
  have rley := hlowery.1
  have rlex' := hlowerx.2 y rley
  have rley' := hlowery.2 x rlex
  grind only [PackedFloat.le_antisymm_of_ne_NaN]

@[simp]
theorem embed_neg_eq_neg_embed {e s : Nat} (x : PackedFloat e s) :
    (SmtLibSemantics.RoundableEmbed.embed (-x) = - (SmtLibSemantics.RoundableEmbed.embed x : ExtRat)) := by
  simp [SmtLibSemantics.RoundableEmbed.embed]

-- lower(-x) = - upper x
@[simp]
theorem lower_neg_eq_neg_upper {e s : Nat} (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower (-r) : PackedFloat e s) = - (SmtLibSemantics.smtLibUpper.upper r) := by
  have hlower := isLawfulLower_lower e s (-r)
  have hlower1 := hlower.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower1
  have hlower2 := hlower.2
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower2

  have hupper := isLawfulUpper_upper e s r
  have hupper1 := hupper.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper1
  have hupper2 := hupper.2
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper2
  suffices SmtLibSemantics.IsLawfulLower (-r) (- (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s)) by
    apply eq_of_IsLawfulLower_of_IsLawfulLower
    · simp [hr]
    · simp [hr]
    · apply hlower
    · apply this
  constructor
  · -- TODO: need a theorem that says that 'embed_neg_eq_neg_embed'
    simp only [embed_neg_eq_neg_embed, SmtLibSemantics.smtLibV_embed_eq,
      PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm]
    grind only [= ExtRat.le_neg_iff_le_neg, = ExtRat.neg_neg]
  · intros low' hlow'
    refine PackedFloat.le_neg_iff_le_neg.mp ?_
    apply hupper2
    simp at hlow'
    apply ExtRat.le_iff_neg_le_neg.mpr
    simp
    grind only

-- upper(-x) = - lower x
@[simp]
theorem upper_neg_eq_neg_lower {e s : Nat} (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibUpper.upper (-r) : PackedFloat e s) = - (SmtLibSemantics.smtLibLower.lower r) := by
  have hupper := isLawfulUpper_upper e s (-r)
  have hupper1 := hupper.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper1
  have hupper2 := hupper.2
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper2

  have hlower := isLawfulLower_lower e s r
  have hlower1 := hlower.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower1
  have hlower2 := hlower.2
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower2
  suffices SmtLibSemantics.IsLawfulUpper (-r) (- (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s)) by
    apply eq_of_IsLawfulUpper_of_IsLawfulUpper
    · simp [ExtRat.neg_eq_NaN_iff, hr]
    · simp [hr]
    · apply hupper
    · apply this
  constructor
  · simp only [embed_neg_eq_neg_embed, SmtLibSemantics.smtLibV_embed_eq,
      PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm]
    grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]
  · intros up' hup'
    refine PackedFloat.neg_le_iff_neg_le.mp ?_
    apply hlower2
    simp at hup'
    apply ExtRat.le_iff_neg_le_neg.mpr
    simp
    grind only

/--
This tells us that `PackedFloat`s are perfectly approximated,
and that calling `lower` on a rational that represents a `PackedFloat`
gives us the same `PackedFloat` back, as long as it's not NaN.
-/
theorem lower_eq_self_of_eq_toExtRat_of_not_isNaN
  (x : PackedFloat e s) (r : ExtRat)
  (hnum : ¬ x.isNaN)
  (h : x.toExtRat = r) :
  (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) = x := by
  have hlower := isLawfulLower_lower e s r
  have hlower1 := hlower.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower1

  have hlower2 := hlower.2
  subst h
  specialize (hlower2 x)
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ExtRat.le_refl, forall_const] at hlower2
  simp only [PackedFloat.toExtRat_eq_toExtRat']
  have : SmtLibSemantics.smtLibLower.lower x.toExtRat' ≤ x := by
    apply PackedFloat.le_of_toExtRat'_le_toExtRat'
    · simp
      grind only [PackedFloat.le_iff_eq_of_isNaN']
    · simp
      grind only
    · simp only [PackedFloat.toExtRat_eq_toExtRat'] at hlower1
      grind only
  grind only [PackedFloat.le_antisymm_of_ne_NaN, PackedFloat.le_iff_eq_of_isNaN']

/--
upper perfectly approximates PackedFloats, and calling `upper` on a rational that represents a `PackedFloat`
gives us the same `PackedFloat` back, as long as it's not NaN.
-/
theorem upper_eq_self_of_eq_toExtRat_of_not_isNaN
  (x : PackedFloat e s) (r : ExtRat)
  (hnum : ¬ x.isNaN)
  (h : x.toExtRat = r) :
  (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) = x := by
  have hupper := isLawfulUpper_upper e s r
  have hupper1 := hupper.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper1
  have hupper2 := hupper.2
  subst h
  specialize (hupper2 x)
  simp only [PackedFloat.toExtRat_eq_toExtRat', SmtLibSemantics.smtLibV_embed_eq,
    ExtRat.ExtRat.le_refl, forall_const] at hupper2
  have : x ≤ SmtLibSemantics.smtLibUpper.upper x.toExtRat' := by
    apply PackedFloat.le_of_toExtRat'_le_toExtRat'
    · simp
      grind only [PackedFloat.le_iff_eq_of_isNaN']
    · simp
      grind only [PackedFloat.le_iff_eq_of_isNaN]
    · simp only [PackedFloat.toExtRat_eq_toExtRat'] at hupper1
      grind only
  simp only [PackedFloat.toExtRat_eq_toExtRat']
  grind only [PackedFloat.le_antisymm_of_ne_NaN, PackedFloat.le_iff_eq_of_isNaN']

-- /--
-- The abstract version of 'shouldRoundUp' that only depends on the rounding mode and the bits,
-- which matches the definition of `roundingDecision`.
-- -/
-- #check roundingDecision
-- def shouldRoundUp (rm : RoundingMode) (sign : Bool) (isEven : Bool) (guard : Bool) (sticky : Bool) : Bool :=


theorem round_eq_ite_roundingDecision_of_Number_of_nonneg {eout sout : Nat} (rm : RoundingMode)
    (sign : Bool)
    (isEven : Bool)
    (guard : Bool)
    (sticky : Bool)
    (_exact : Bool)
    (r : Rat)
    (hguardsticky : guard = false → sticky = false →
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout) = SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)
    )
    (hguard : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) = (guard = false))
    (htiebreak : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) = (guard = true ∧ sticky = false))
    (heven : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r)) = isEven)
    (hz : r ≠ 0)
    (hsign : sign = (r < 0))
    (hr : 0 ≤ r)
    :
    ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
    (ExtRat.Number r) : PackedFloat eout sout) =
    if roundingDecision rm sign isEven guard sticky _exact then
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper (ExtRat.Number r)
    else
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower  (ExtRat.Number r) := by
  simp [show ¬ r < 0 by grind only] at hsign
  subst hsign
  cases rm <;> simp [roundingDecision]
  case RNE =>
    simp only [SmtLibSemantics.RoundMethod.roundRNE]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · -- guard = false
      simp only [↓reduceIte, Bool.false_eq_true, false_and]
      simp at htiebreak
      simp [htiebreak]
    · -- guard = true
      simp only [Bool.true_eq_false, ↓reduceIte, true_and, ite_not]
      rcases sticky with rfl | rfl
      · -- tiebreak = false
        simp [htiebreak]
        simp [heven]
        rcases isEven with rfl | rfl
        · simp
          -- I need a theorem that says that if lower is not even then upper is.
          intros hupper
          -- isEven cannot be both true and false.
          have hcontra := isEven_upper_eq_not_isEven_lower eout sout r
          grind only
        · simp
          intros heven
          have hcontra := isEven_upper_eq_not_isEven_lower eout sout r
          grind only
      · -- tiebreak = true
        simp [htiebreak]
  case RNA =>
    -- This rounding mode is broken, I seem to have confused lower and upper!
    simp only [SmtLibSemantics.RoundMethod.roundRNA]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · -- guard = false
      simp
      intros hr
      have hrlt : r < 0 := by grind only
      grind only
    · -- guard = true
      simp
      intros hrle
      grind only
  case RTP =>
    simp only [SmtLibSemantics.RoundMethod.roundRTP]
    simp [hz]
    intros hguard hsticky
    rw [hguardsticky]
    · grind only
    · grind only
  case RTN =>
    simp only [SmtLibSemantics.RoundMethod.roundRTN]
    simp [hz]
  case RTZ =>
    simp only [SmtLibSemantics.RoundMethod.roundRTZ]
    simp [hz]
    intros hrlezero
    have hcontra : r = 0 := by grind only
    grind only

/--
When negative, the guard, stick, and isEven interpretations change.
- isEven tells us when the upper is even.
- guard bit tells us when we are in the lower half, since it is 'more negative'.
-/
theorem round_eq_ite_roundingDecision_of_Number_of_neg {eout sout : Nat} (rm : RoundingMode)
    (sign : Bool)
    (isEven : Bool)
    (guard : Bool)
    (sticky : Bool)
    (_exact : Bool)
    (r : Rat)
    (hguardsticky : guard = false → sticky = false →
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout) = SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)
    )
    -- | in the negative case, we are in the lower half when guard is true,
    -- since we are closer to lower than upp.er
    (hguard :
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) =
      (guard = true))
    (htiebreak : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) = (guard = true ∧ sticky = false))
    (heven : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)) = isEven)
    (hz : r ≠ 0)
    (hsign : sign = (r < 0))
    (hr : r < 0)
    :
    ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
    (ExtRat.Number r) : PackedFloat eout sout) =
    if roundingDecision rm sign isEven guard sticky _exact then
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower (ExtRat.Number r)
    else
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper  (ExtRat.Number r) := by
  simp [show r < 0 by grind only] at hsign
  subst hsign
  cases rm <;> simp [roundingDecision]
  case RNE =>
    simp only [SmtLibSemantics.RoundMethod.roundRNE]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · simp
      intros htiebreak'
      simp at htiebreak
      grind only
    · simp
      rcases sticky with rfl | rfl
      · -- tiebreak = false
        simp [htiebreak]
        simp at htiebreak
        simp at hguard
        simp at hguardsticky
        rcases isEven with rfl | rfl
        · simp
          intros isEven
          grind only
        · simp
          intros hevenUpper
          grind only
      · -- tiebreak = true
        simp [htiebreak]
  case RNA =>
    -- This rounding mode is broken, I seem to have confused lower and upper!
    simp only [SmtLibSemantics.RoundMethod.roundRNA]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · simp [show ¬ 0 < r by grind only]
      simp [hr]
      intros htiebreak
      simp [htiebreak]
      grind only
    · simp [show ¬ 0 < r by grind only]
      intros hr
      grind only
  case RTP =>
    simp only [SmtLibSemantics.RoundMethod.roundRTP]
    simp [hz]
  case RTN =>
    simp only [SmtLibSemantics.RoundMethod.roundRTN]
    simp [hz]
    intros hguard hsticky
    apply hguardsticky
    · grind only
    · grind only
  case RTZ =>
    simp only [SmtLibSemantics.RoundMethod.roundRTZ]
    simp [hr]
    intros hr
    grind only



/--
This proves that the `round` function is correctly implemented by `rounderSpecialCases`
in the cases when we get a special case.

TODO: how to phrase the correctness of this?
Do we just say that in the cases where the rounded result is a special case, then the `round` function returns the same result as `rounderSpecialCases`?
-/
theorem round_eq_rounderSpecialCases_of_isZero
  (heout : 0 < eout)
  (rm : RoundingMode)
  -- | We need a precondition that says that outside
  -- of the special cases, this is correctly rounded.
  (roundedResult : UnpackedFloat (exponentWidth targetExponentWidth targetSignificandWidth) (targetSignificandWidth + 1))
  (overflow : Bool)
  (underflow : Bool)
  (isZero : Bool)
  (r : Rat)
  (rounded : PackedFloat eout sout)
  (hrounded : rounded =  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign (ExtRat.Number r)))
  (hIsZero : isZero = decide (r = 0))
  (hOverflow : overflow = decide (r > (PackedFloat.maxNormalNumber eout sout (decide (r < 0))).toRat))
  (hUnderflow : underflow = decide (r < (PackedFloat.minSubnormalNumber eout sout (decide (r < 0))).toRat))
  (hrounded' : rounded.isInfinite ∨ rounded.isNaN ∨ rounded.isZero) :
  (rounded).toExtRat = (rounderSpecialCases rm roundedResult overflow underflow isZero).toExtRat := by
  rcases hrounded' with hinf | hnan | hzero
  · simp only [PackedFloat.toExtRat_eq_toExtRat', hinf,
    PackedFloat.toExtRat'_eq_Infinity_of_isInfinite]
    simp only [rounderSpecialCases]
    rcases isZero with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp at hIsZero
      sorry
    · simp only [↓reduceIte, EUnpackedFloat.toExtRat_mkZero, reduceCtorEq]
      -- contradiction, cannot have 'r' be the rounded version being infinite,
      -- as well as having 'r = 0'.
      simp only [true_eq_decide_iff] at hIsZero
      subst hIsZero
      have : rounded.isZero = true := by
        grind only [isZero_round_zero]
      grind only [→ PackedFloat.not_isZero_of_isInfinite]
  · simp only [PackedFloat.toExtRat_eq_toExtRat', hnan, PackedFloat.toExtRat'_eq_NaN_of_isNaN,
    ExtRat.ExtRat.NaN_le_iff, decide_eq_true_eq, ExtRat.ExtRat.le_refl,
    ExtRat.ExtRat.eq_of_le_of_le]
    have : rounded.isNaN = false := by
      grind only [isNaN_round_number_eq_false]
    grind only
  · simp only [PackedFloat.toExtRat_eq_toExtRat', hzero, PackedFloat.toExtRat'_eq_zero_of_isZero]
    rcases isZero with rfl | rfl
    · simp only [false_eq_decide_iff] at hIsZero
      simp only [rounderSpecialCases, Bool.false_eq_true, ↓reduceIte]
      -- this is possible upon underflow.
      rcases underflow with rfl | rfl
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rcases overflow with rfl | rfl
        · simp only [Bool.false_eq_true, ↓reduceIte, EUnpackedFloat.toExtRat_mkNumber,
          ExtRat.Number.injEq]
          simp at hOverflow
          simp at hUnderflow
          by_cases hr : r < 0
          · simp [hr] at hOverflow hUnderflow
            sorry
          · simp [hr] at hOverflow hUnderflow
            sorry
        · simp at hOverflow
          simp at hUnderflow
          -- needs relationships between maxNormalNumber and minSubnormalNumber.
          by_cases hr : r < 0
          · simp [hr] at hOverflow hUnderflow
            --   hOverflow : (PackedFloat.maxNormalNumber eout sout false).toRat < r
            --     -minSubnormalNumber ≤ r < 0
            sorry
          · simp [hr] at hOverflow hUnderflow
            simp at hr
            -- if maxNormalNumber < r,
            -- then the rounded result must be infinity?
            -- or at the very least, the rounded result cannot be zero.
            --   hOverflow : (PackedFloat.maxNormalNumber eout sout false).toRat < r
            --   hzero : rounded.isZero = true
            sorry
      · simp only [↓reduceIte]
        rcases rm with rfl | rfl | rfl | rfl | rfl
        · simp [rounderSpecialCaseUnderflow]
        · simp [rounderSpecialCaseUnderflow]
        · simp [rounderSpecialCaseUnderflow]
          by_cases hsign : roundedResult.sign
          · simp [hsign]
            sorry
          · simp [hsign]
        · simp [rounderSpecialCaseUnderflow]
          sorry
        · simp [rounderSpecialCaseUnderflow]
    · simp only [true_eq_decide_iff] at hIsZero
      subst hIsZero
      simp [rounderSpecialCases]
end Fp
