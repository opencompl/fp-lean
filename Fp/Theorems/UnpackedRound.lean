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
theorem isNaN_round_number_eq_false {eout sout : Nat} {zeroSign : Bool} {rm : RoundingMode} {r : Rat}
  (heout : 0 < eout) :
  ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
    rm zeroSign (ExtRat.Number r)).isNaN = false := by
  apply Classical.byContradiction
  intros hcontra
  simp at hcontra
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

section ComputableLowerUpper

open SmtLibSemantics

/-
### Computable Lower & Upper Bound
-/

/-- Enumerate bitvectors. -/
def enumerateBV (n : Nat) : { xs : List (BitVec n) // ∀ (x : BitVec n), x ∈ xs } :=
  let xs := List.range (2 ^ n)
  let vs := xs.map (fun x => BitVec.ofNat n x)
  ⟨vs, by
    intros x
    simp [vs, xs]
    exists x.toNat
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true]
    grind only [usr BitVec.isLt]
  ⟩

def enumerateBool : { xs : List Bool // ∀ (x : Bool), x ∈ xs } :=
  let xs := [true, false]
  ⟨xs, by
    intros x
    simp [xs]
  ⟩

def enumerateProduct {α β} (xs : { xs : List α // ∀ (a : α), a ∈ xs})
    (ys : { ys : List β // ∀ (b : β), b ∈ ys }) :
    { zs : List (α × β) // ∀ (z : α × β), z ∈ zs } :=
  let zs := xs.val.flatMap (fun x => ys.val.map (fun y => (x, y)))
  ⟨zs, by
    intros z
    obtain ⟨zx, zy⟩ := z
    simp [zs]
    grind only
  ⟩

def enumerateProduct3 {α β γ} (xs : { xs : List α // ∀ (a : α), a ∈ xs})
    (ys : { ys : List β // ∀ (b : β), b ∈ ys })
    (zs : { zs : List γ // ∀ (c : γ), c ∈ zs }) :
    { ws : List (α × β × γ) // ∀ (w : α × β × γ), w ∈ ws } :=
  let ws := xs.val.flatMap (fun x => ys.val.flatMap (fun y => zs.val.map (fun z => (x, y, z))))
  ⟨ws, by
    intros w
    obtain ⟨wx, wy, wz⟩ := w
    simp [ws]
    grind only
  ⟩

/--
enumerate all packed floats.
-/
def enumeratePackedFloatList (e s : Nat) :
    {xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs} :=
  let sign := enumerateBool
  let exp := enumerateBV e
  let sig := enumerateBV s
  let xs := enumerateProduct3 sign exp sig
  ⟨xs.val.map (fun (sign, exp, sig) => PackedFloat.mk sign exp sig), by
    intros x
    obtain ⟨sign, exp, sig⟩ := x
    simp
    rcases sign with rfl | rfl
    · simp
      grind only
    · simp
      grind only
  ⟩

/-- enumerate all packed floats as an array. -/
def enumeratePackedFloatArray (e s : Nat) :
    {xs : Array (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs} :=
  ⟨enumeratePackedFloatList e s |>.val.toArray, by
    intros x
    simp
    grind only [#968d]
  ⟩

/-- enmerate all packed floats which are not NaN.-/
def enumerateNonNanPackedFloatArray (e s : Nat) :
    {xs : Array (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ ¬ x.isNaN} :=
  let arr := enumeratePackedFloatArray e s
  let xs := arr.val.filter (fun pf => ¬ pf.isNaN)
  ⟨xs, by
    intros x
    simp [xs]
    grind only [#ca5c]
  ⟩

def enumerateNonNanPackedFloatList (e s : Nat) :
    {xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ ¬ x.isNaN} :=
  ⟨enumerateNonNanPackedFloatArray e s |>.val.toList, by
    intros x
    simp [Array.mem_toList_iff]
    grind only
  ⟩


def lowerList (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) :
    { xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ (¬ x.isNaN ∧ x.toExtRat ≤ r) } :=
    let arr := enumeratePackedFloatList e s
    let out := arr.val.filter (fun pf => ¬ pf.isNaN && pf.toExtRat ≤ r)
    ⟨out, by
      intros x
      constructor
      · intros hx
        simp [out, arr] at hx
        rw [PackedFloat.toExtRat_eq_toExtRat']
        grind only
      · intros hx
        grind only [= List.mem_filter, #f38e]
    ⟩

@[simp]
theorem mem_lowerList_iff (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) (pf : PackedFloat e s) :
    pf ∈ (lowerList e s r hr).val ↔ (¬ pf.isNaN ∧ pf.toExtRat ≤ r) := by
  have := lowerList e s r hr
  grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN,
    = PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, = PackedFloat.toExtRat'_eq_NaN_iff_isNaN,
    = PackedFloat.toExtRat'_eq_zero_of_isZero, = PackedFloat.toExtRat'_eq_toRat_of,
    = PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero, #d3b2, #96bca0d4ecd67426,
    #aefe0df31a27f84b]


@[simp]
theorem infty_mem_lowerList (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) (hs : 0 < s):
    PackedFloat.getInfinity e s true ∈ (lowerList e s r hr).val := by
    simp [hs]
    grind only

/--
the lowerList is nonempty when the significand is nonzero.
-/
@[grind! .]
theorem lowerList_nonempty (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) (hs : 0 < s) :
    (lowerList e s r hr).val.length ≠ 0 := by
  have := infty_mem_lowerList e s r hr hs
  grind only [usr List.length_pos_of_mem]

/--
on a non-NaN set of packed floats, compute the 'max'.
-/
def maxPackedFloatNonNaN
    (xs : List (PackedFloat e s)) (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    { pf : PackedFloat e s //
         ¬ pf.isNaN ∧ ∀ (x : PackedFloat e s), x ∈ xs → pf ≥ x } :=
  match xs with
  | [] => ⟨PackedFloat.getInfinity e s true, by
    constructor
    · grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN, !PackedFloat.toExtRat'_getInfinity]
    · intros x hx; simp at hx⟩
  | x :: xs =>
    let candidate := maxPackedFloatNonNaN xs (by simp; grind only [= List.mem_cons, #1c8d]) he hs
    if hc : candidate.val ≥ x then
      ⟨candidate, by
        constructor
        · grind
        · intros y hy; simp at hy; cases hy with
          | inl h => simp [h]; simp at hc; exact hc
          | inr h =>
            simp at hc
            have := (candidate.property.right) y h
            exact this⟩
    else
      ⟨x, by
        constructor
        · grind only [usr Subtype.property, = List.mem_cons, #1c8d]
        · intros y hy;
          simp at hy;
          rcases hy with h | h
          · simp [h]
          · simp
            simp at hc
            have := candidate.property.right y h
            simp at this
            apply PackedFloat.le_trans
            · exact this
            · apply PackedFloat.le_of_lt
              apply PackedFloat.lt_of_not_le
              · grind only [= PackedFloat.toExtRat'_eq_NaN_iff_isNaN, = List.mem_cons, #1c8d]
              · grind only [usr Subtype.property, = PackedFloat.isNaN_iff_toExtRat'_eq_NaN]
⟩

@[simp]
theorem not_isNaN_maxPackedFloatNaN (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    ¬ (maxPackedFloatNonNaN xs hxs he hs).val.isNaN := by
  have := (maxPackedFloatNonNaN xs hxs he hs).property
  simp [this]

/--
the result of 'maxPackedFloatNonNaN' is actually in the list when the list is nonempty.
-/
theorem maxFloatNonNaN_mem (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN)
    (hxsLen : xs.length ≠ 0)
    (he : 0 < e) (hs : 0 < s) :
    (maxPackedFloatNonNaN xs hxs he hs).val ∈ xs := by
  induction xs
  case nil => simp at hxsLen
  case cons x xs ih =>
    simp only [List.mem_cons]
    simp at ih
    simp [maxPackedFloatNonNaN]
    split
    case isTrue h =>
      simp
      rcases xs with rfl | ⟨x', xs'⟩
      · simp [maxPackedFloatNonNaN, hs] at h
        simp at ih
        simp
        simp at hxs
        subst h
        simp at hxs
        simp [maxPackedFloatNonNaN]
      · right
        apply ih
        · grind
        · simp
    case isFalse h =>
      simp
/--
all values in the list are less than the max.
-/
theorem le_maxPackedFloatNonNaN (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    ∀ x ∈ xs, x ≤ (maxPackedFloatNonNaN xs hxs he hs).val := by
  intros x hx
  obtain ⟨hnan, hle⟩ := (maxPackedFloatNonNaN xs hxs he hs).property
  simp at hle
  apply hle
  grind

/--
Every element in 'xs' is less than the 'max', when interpreted in the rationals.
-/
theorem le_maxPackedFloatNaN_toExtRat' (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    ∀ x ∈ xs, x.toExtRat' ≤ (maxPackedFloatNonNaN xs hxs he hs).val.toExtRat' := by
  intros x hx
  have := le_maxPackedFloatNonNaN xs hxs he hs x hx
  apply PackedFloat.toExtRat'_le_toExtRat'_of_le
  · grind only
  · grind only
  · grind
  · grind only
  · apply le_maxPackedFloatNonNaN
    · grind only

/--
To show that a rational 'r' is greater than the max,
it suffices to show that it is greater than all the elements in the list.
-/
theorem maxPackedFloatNaN_toExtRat'_le_of_toExtRat'_le (xs : List (PackedFloat e s))
    (hxsEmpty : xs ≠ [])
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) (r : ExtRat)
    (hr : ∀ x ∈ xs, x.toExtRat' ≤ r) :
    (maxPackedFloatNonNaN xs hxs he hs).val.toExtRat' ≤ r := by
  have := maxFloatNonNaN_mem xs hxs (by simp; grind only) he hs
  grind only [#e993]

/--
info: 'Fp.le_maxPackedFloatNaN_toExtRat'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms le_maxPackedFloatNaN_toExtRat'

theorem ExtRat.not_isNaN_of_le_of_not_isNaN (r1 r2 : ExtRat)
  (hr1 : r1 ≤ r2) (hr2 : r2 ≠ .NaN) : r1 ≠ .NaN := by
  intros hcontra
  simp at hr2
  apply hr2
  simp [hcontra] at hr1
  grind only
/--
lower is computable for all arguments.
-/
def lower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) : PackedFloat e s :=
if hr : r = .NaN then
  PackedFloat.getNaN e s
else if h0 : r = .Number 0 then
  PackedFloat.getZero e s false
else
  let arr := lowerList e s r (by simp [hr])
  let max := maxPackedFloatNonNaN arr.val (by simp; grind only [#1a7c]) he hs
  max.val


/--
The result of 'lower' is NaN iff the input is NaN.
-/
theorem isNaN_lower_iff_eq_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat):
    (lower e s he hs r).isNaN ↔ r = .NaN := by
  simp [lower]
  split
  case isTrue h =>
    simp [h]
  case isFalse h =>
    simp [h]
    by_cases hr : r = ExtRat.Number 0
    · simp [hr]
      grind
    · simp [hr]



/-- info: 'Fp.isNaN_lower_iff_eq_NaN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms isNaN_lower_iff_eq_NaN

/--
the 'lower' function indeed computes a lawful lower bound for every ExtRat.
This shows that lawful lower bounds exist for all rationals.
-/
@[simp]
theorem IsLawfulLower_lower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulLower r (lower e s he hs r) := by
  simp [lower]
  split
  case isTrue h =>
    subst h
    simp
  case isFalse h =>
    by_cases hr : r = .Number 0
    · simp [hr, he, hs]
    · simp [hr]
      constructor
      · simp only [smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm]
        apply maxPackedFloatNaN_toExtRat'_le_of_toExtRat'_le
        · grind
        · intros x hx
          simp at hx
          grind only
      · intros x hx
        simp only [smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm] at hx
        apply le_maxPackedFloatNonNaN
        simp only [mem_lowerList_iff, Bool.not_eq_true, PackedFloat.toExtRat_eq_toExtRat']
        constructor
        · grind only [= PackedFloat.toExtRat'_eq_NaN_iff_isNaN, = ExtRat.le_NaN]
        · grind only

/-- info: 'Fp.IsLawfulLower_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsLawfulLower_lower


/--
We know that that we have a lawful upper iff it's a lawful lower for the negated version.
-/
@[simp ←]
theorem IsLawfulUpper_iff_IsLawfulLower_neg_neg (r : ExtRat) (x : PackedFloat e s) :
    SmtLibSemantics.IsLawfulUpper r x ↔ SmtLibSemantics.IsLawfulLower (-r) (-x) := by
  simp only [IsLawfulUpper, smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm, IsLawfulLower, PackedFloat.toExtRat'_neg]
  constructor
  · intros h
    obtain ⟨hupper, hlower⟩ := h
    constructor
    · grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]
    · intros lower hlower'
      suffices x ≤ -lower by grind only [= PackedFloat.le_neg_iff_le_neg]
      apply hlower
      simp only [PackedFloat.toExtRat'_neg]
      grind only [= ExtRat.le_neg_iff_le_neg]
  · intros h
    obtain ⟨hlower, hupper⟩ := h
    constructor
    · grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]
    · intros upper hupper'
      suffices -upper ≤ -x by grind only [= PackedFloat.neg_le_iff_neg_le, = PackedFloat.neg_neg']
      apply hupper
      simp only [PackedFloat.toExtRat'_neg]
      grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]

/--
We have a lawful lower iff it's a lawful upper for the negated version.
-/
@[simp ←]
theorem IsLawfulLower_iff_IsLawfulUpper_neg_neg (r : ExtRat) (x : PackedFloat e s) :
    SmtLibSemantics.IsLawfulLower r x ↔ SmtLibSemantics.IsLawfulUpper (-r) (-x) := by
  rw [IsLawfulUpper_iff_IsLawfulLower_neg_neg]
  simp

def upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) : PackedFloat e s :=
  - lower e s he hs (-r)

@[simp]
theorem IsLawfulUpper_upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (upper e s he hs r) := by
  simp [upper]
  apply IsLawfulUpper_iff_IsLawfulLower_neg_neg .. |>.mpr
  simp

@[simp]
theorem isNaN_upper_iff_eq_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat):
    (upper e s he hs r).isNaN ↔ r = .NaN := by
  simp [upper]
  simp [isNaN_lower_iff_eq_NaN]

/-- info: 'Fp.IsLawfulUpper_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsLawfulUpper_upper

end ComputableLowerUpper

/-# IsEven and IsOdd -/


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

/-# IsLawfulLower, smtLibLower, and computable lower

We show that `smtLibLower` can always be replaced with `lower`
-/

/-### Lower bounds -/

theorem lsLawfulLower_smtLibLower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulLower r (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) := by
  simp [SmtLibSemantics.smtLibLower]
  apply Classical.epsilon_spec
  have := IsLawfulLower_lower e s he hs r
  grind only [#de43]

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


theorem IsLawfulLower_eq_NaN_of_isNaN (e s : Nat) (r : ExtRat) (x : PackedFloat e s)
    (hlower : SmtLibSemantics.IsLawfulLower r x) :
    x.isNaN = true → r = .NaN := by
  intros hnan
  have hlower1 := hlower.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower1
  simp [hnan] at hlower1
  grind

/--
The result of 'IsLawfulLower' is unique and must be equal to the 'lower' computation.
If the value is a 'NaN', then we may have different 'NaNs, but we may not get
equality on the nose.
-/
@[simp]
theorem eq_lower_of_IsLawfulLower (e s : Nat) (he : 0 < e) (hs : 0 < s)
    (r : ExtRat)
    (x : PackedFloat e s)
    (hrnan : r ≠ .NaN)
    (hlower : SmtLibSemantics.IsLawfulLower r x) :
    x = lower e s he hs r := by
  apply eq_of_IsLawfulLower_of_IsLawfulLower
  · intros hcontra
    apply hrnan
    apply IsLawfulLower_eq_NaN_of_isNaN
    · exact hlower
    · grind only
  · apply Classical.byContradiction
    intros hcontra
    apply hrnan
    grind [ExtRat, lower]
  · apply hlower
  · exact IsLawfulLower_lower e s he hs r

/--
info: 'Fp.eq_lower_of_IsLawfulLower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_lower_of_IsLawfulLower

/--
the value of smtLibLower equals that of 'lower' on all non-NaN rationals.
-/
@[simp]
theorem smtLibLower_eq_lower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    SmtLibSemantics.smtLibLower.lower r = lower e s he hs r := by
  apply eq_of_IsLawfulLower_of_IsLawfulLower (r := r)
  · intros hcontra
    have := eq_lower_of_IsLawfulLower e s he hs r (SmtLibSemantics.smtLibLower.lower r) hr
    specialize this (by exact lsLawfulLower_smtLibLower e s he hs r)
    rw [this] at hcontra
    have := isNaN_lower_iff_eq_NaN e s he hs r
    grind only
  · intros hcontra
    apply hr
    grind only [→ PackedFloat.not_isZero_of_isNaN, lower, PackedFloat.isZero_getZero, #2962, #90ed]
  · exact lsLawfulLower_smtLibLower e s he hs r
  · exact IsLawfulLower_lower e s he hs r

/-- info: 'Fp.smtLibLower_eq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smtLibLower_eq_lower

/-### Upper bounds -/

theorem isLawfulUpper_smtLibUpper (e s : Nat) (he : 0 < e)  (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) := by
  simp [SmtLibSemantics.smtLibUpper]
  apply Classical.epsilon_spec
  have := IsLawfulUpper_upper e s he hs r
  grind only [#c7e1]

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


theorem IsLawfulUpper_eq_NaN_of_isNaN (e s : Nat) (r : ExtRat) (x : PackedFloat e s)
    (hupper : SmtLibSemantics.IsLawfulUpper r x) :
    x.isNaN = true → r = .NaN := by
  intros hnan
  have hupper1 := hupper.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper1
  simp [hnan] at hupper1
  grind only

/--
The result of 'IsLawfulLower' is unique and must be equal to the 'lower' computation.
-/
@[simp]
theorem eq_upper_of_IsLawfulUpper (e s : Nat) (he : 0 < e) (hs : 0 < s)
    (r : ExtRat)
    (x : PackedFloat e s)
    (hrnan : r ≠ .NaN)
    (hupper : SmtLibSemantics.IsLawfulUpper r x) :
    x = upper e s he hs r := by
  apply eq_of_IsLawfulUpper_of_IsLawfulUpper
  · intros hcontra
    apply hrnan
    apply IsLawfulUpper_eq_NaN_of_isNaN
    · exact hupper
    · grind only
  · apply Classical.byContradiction
    intros hcontra
    apply hrnan
    simp at hcontra
    grind only
  · apply hupper
  · exact IsLawfulUpper_upper e s he hs r

/--
info: 'Fp.eq_upper_of_IsLawfulUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_upper_of_IsLawfulUpper

@[simp]
theorem smtLibUpper_eq_upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    SmtLibSemantics.smtLibUpper.upper r = upper e s he hs r := by
  apply eq_of_IsLawfulUpper_of_IsLawfulUpper (r := r)
  · intros hcontra
    have := eq_upper_of_IsLawfulUpper e s he hs r (SmtLibSemantics.smtLibUpper.upper r) hr
    rw [this] at hcontra
    · have := isNaN_upper_iff_eq_NaN e s he hs r
      grind only
    · exact isLawfulUpper_smtLibUpper e s he hs r
  · intros hcontra
    apply hr
    have := isNaN_upper_iff_eq_NaN e s he hs r
    grind only
  · exact isLawfulUpper_smtLibUpper e s he hs r
  · exact IsLawfulUpper_upper e s he hs r

/-- info: 'Fp.smtLibUpper_eq_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smtLibUpper_eq_upper


@[simp]
theorem not_isNaN_lower_of_ne_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s).isNaN = false := by
  rw [smtLibLower_eq_lower e s he hs r hr]
  grind only [lower, → PackedFloat.not_isZero_of_isNaN, PackedFloat.isZero_getZero, #2962, #90ed]

/--
info: 'Fp.not_isNaN_lower_of_ne_NaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms not_isNaN_lower_of_ne_NaN

@[simp]
theorem not_isNaN_lower_neg_of_ne_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower (-r) : PackedFloat e s).isNaN = false := by
  apply not_isNaN_lower_of_ne_NaN e s he hs
  simp [ExtRat.neg_eq_NaN_iff, hr]



@[simp]
theorem not_isNaN_upper_of_ne_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s).isNaN = false := by
  by_cases hnan : (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s).isNaN
  · exfalso
    rw [smtLibUpper_eq_upper e s he hs r hr] at hnan
    have := isNaN_upper_iff_eq_NaN e s he hs r
    grind only
  · simp [hnan]

/--
info: 'Fp.not_isNaN_upper_of_ne_NaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms not_isNaN_upper_of_ne_NaN

theorem isLawfulUpper_upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) := by
  by_cases hr : r = .NaN
  · simp [hr]
  · have := smtLibUpper_eq_upper e s he hs r hr
    rw [this]
    exact IsLawfulUpper_upper e s he hs r

/-- info: 'Fp.IsLawfulUpper_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsLawfulUpper_upper


@[simp]
theorem embed_neg_eq_neg_embed {e s : Nat} (x : PackedFloat e s) :
    (SmtLibSemantics.RoundableEmbed.embed (-x) = - (SmtLibSemantics.RoundableEmbed.embed x : ExtRat)) := by
  simp [SmtLibSemantics.RoundableEmbed.embed]

-- lower(-x) = - upper x
@[simp]
theorem smtLibLower_neg_eq_neg_smtLibUpper {e s : Nat} (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower (-r) : PackedFloat e s) = - (SmtLibSemantics.smtLibUpper.upper r) := by
  rw [smtLibLower_eq_lower e s he hs]
  · rw [smtLibUpper_eq_upper e s he hs]
    · simp [upper]
    · simp [hr]
  · simp [hr]

-- upper(-x) = - lower x
@[simp]
theorem smtLibUpper_neg_eq_neg_smtLibLower {e s : Nat} (r : ExtRat) (hr : r ≠ .NaN) (he : 0 < e )(hs : 0 < s) :
    (SmtLibSemantics.smtLibUpper.upper (-r) : PackedFloat e s) = - (SmtLibSemantics.smtLibLower.lower r) := by
  rw [smtLibUpper_eq_upper e s he hs]
  · rw [smtLibLower_eq_lower e s he hs]
    · simp [upper]
    · simp [hr]
  · simp [hr]

/--
This tells us that `PackedFloat`s are perfectly approximated,
and that calling `lower` on a rational that represents a `PackedFloat`
gives us the same `PackedFloat` back, as long as it's not NaN.
-/
theorem smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN
  (he : 0 < e) (hs : 0 < s)
  (x : PackedFloat e s) (r : ExtRat)
  (hnum : ¬ x.isNaN)
  (hzero : ¬ x.isZero)
  (h : x.toExtRat = r) :
  (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) = x := by
  have hlower := lsLawfulLower_smtLibLower e s he hs r
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
    · grind only
    · grind only
    · simp
      grind only [PackedFloat.le_iff_eq_of_isNaN']
    · simp
      grind only
    · simp only [PackedFloat.toExtRat_eq_toExtRat'] at hlower1
      intros hxzero hlowrzero hxsign
      grind only
    · grind only
    · simp only [PackedFloat.toExtRat_eq_toExtRat'] at hlower hlower1 ⊢
      grind only
  grind only [PackedFloat.le_antisymm_of_ne_NaN, PackedFloat.le_iff_eq_of_isNaN']

  /--
info: 'Fp.smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN

/--
upper perfectly approximates PackedFloats, and calling `upper` on a rational that represents a `PackedFloat`
gives us the same `PackedFloat` back, as long as it's not NaN.
-/
theorem smtLibUpper_eq_self_of_eq_toExtRat_of_not_isNaN
  (he : 0 < e) (hs : 0 < s)
  (x : PackedFloat e s) (r : ExtRat)
  (hnum : ¬ x.isNaN)
  (hzero : ¬ x.isZero)
  (h : x.toExtRat = r) :
  (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) = x := by
  rw [show r = - (- r) by grind only [= ExtRat.neg_neg]]
  rw [smtLibUpper_neg_eq_neg_smtLibLower]
  · rw [smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN he hs (- x)]
    · simp
    · simp [hnum]
    · simp [hzero]
    · simp [he, hs]
      simp only [PackedFloat.toExtRat_eq_toExtRat'] at h
      grind only
  · simp at h
    simp; grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN]
  · simp [he]
  · simp [hs]

/--
info: 'Fp.smtLibUpper_eq_self_of_eq_toExtRat_of_not_isNaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtLibUpper_eq_self_of_eq_toExtRat_of_not_isNaN

/-# Rounding decision in terms of computable definitions -/


-- TDOO: add a 'computableRoundingDecision.

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

/-! # clearSignificand -/

@[simp]
theorem clearSignificand_sign (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).sign = uf.sign := by
  simp [UnpackedFloat.clearSignificand]

@[simp]
theorem clearSignificand_ex (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).ex = uf.ex := by
  simp [UnpackedFloat.clearSignificand]

/-- Clearing guard/sticky bits can only decrease the significand value. -/
theorem UnpackedFloat.clearSignificand_sig_toNat_le (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).sig.toNat ≤ uf.sig.toNat := by
  rw [UnpackedFloat.clearSignificand]
  simp only [BitVec.toNat_and]
  grind only [Nat.and_le_left]



/-- For a nonnegative unpacked float, clearing guard/sticky bits yields a nonnegative result. -/
theorem UnpackedFloat.clearSignificand_toRat_nonneg_of_sign_eq_false (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : uf.sign = false) :
    0 ≤ (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat := by
  simp [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat']
  generalize hcleared : uf.clearSignificand targetExponentWidth targetSignificandWidth = cleared
  have : 0 < (2 : Rat) ^ cleared.toExpInt := by grind only [Rat.two_pow_pos]
  have hsign : cleared.sign = false := by
    simp [← hcleared, UnpackedFloat.clearSignificand, h]
  simp [hsign]
  grind only [Rat.mul_nonneg]




/-- For a nonnegative unpacked float, clearing guard/sticky bits rounds toward zero:
    the cleared value is at most the original value. -/
theorem UnpackedFloat.clearSignificand_toRat_le_of_nonneg (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (hufsign : uf.sign = false) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat ≤ uf.toRat := by
  simp only [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat' , UnpackedFloat.toRat']
  generalize hcleared : uf.clearSignificand targetExponentWidth targetSignificandWidth = cleared
  have hsign : cleared.sign = false := by
    simp only [← hcleared, UnpackedFloat.clearSignificand, hufsign,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp [hsign, hufsign]
  have hexp : cleared.toExpInt = uf.toExpInt := by
    simp only [UnpackedFloat.toExpInt, ← hcleared, UnpackedFloat.clearSignificand,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp only [hexp, ge_iff_le]
  have : cleared.sig.toNat ≤ uf.sig.toNat := by
    rw [← hcleared]
    apply UnpackedFloat.clearSignificand_sig_toNat_le
  suffices (cleared.sig.toNat : Rat) ≤ (uf.sig.toNat : Rat) by
    apply Rat.mul_le_mul_of_nonneg_right
    · simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]; grind only
    · grind only [Rat.le_of_lt, Rat.two_pow_pos]
  simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]
  grind only

/-- For a nonnegative unpacked float, the error from clearing guard/sticky bits is bounded by
    2^(guardBitIdx + 1) ULPs at the significand level, i.e.,
    `x.toRat - cleared.toRat < 2^(guardBitIdx + 1) * 2^(x.toExpInt)`.
    This is the ULP of the target precision. -/
theorem clearSignificand_toRat_sub_lt (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : 0 ≤ uf.toRat) :
    uf.toRat - (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat <
      (2 : Rat) ^ ((uf.guardBitIndex targetExponentWidth targetSignificandWidth).toNat + 1) *
      (2 : Rat) ^ uf.toExpInt := by
  sorry

/--
The result of 'clearSignificand' results in an unpacked float
that can be represented in the target format, and has the same rational value as some `PackedFloat`.
-/
theorem exists_packedFloat_toRat_eq_clearSignificand_toRat (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    ∃ (pf : PackedFloat targetExponentWidth targetSignificandWidth),
      pf.toRat = (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat := by
  sorry



/-! # guardBitIndex -/

/--
The guard bit index when interpreted as a natural number
gives us the location of the guard bit inside the unpaked float.
sorry
-/
theorem UnpackedFloat.toNat_guardBitIndex_eq (hep : 1 < ep) (hsp : 0 < sp)
    -- TODO: I need a bound on `x.ex` to be at most `maxNormalExp`.
    -- TODO: I need a bound on `x.ex` to be at least `minSubnormalExp`.
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    -- (heusu : eu ≤ su)
    (x : UnpackedFloat eu su) :
    (x.guardBitIndex ep sp).toNat =
    (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat) := by
  have := @one_lt_exponentWidth ep sp
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)]
    · grind only
    · grind only
    · grind only

  rw [UnpackedFloat.guardBitIndex]
  rw [BitVec.toNat_add]
  simp
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      simp
      rw [Int.sub_toNat_eq_zero_of_le]
      · simp
        rw [Nat.mod_eq_of_lt]
        · have : su < 2 ^ su := by exact Nat.lt_two_pow_self
          grind only
      · grind only
    case isFalse h =>
      simp at h
      rw [Nat.mod_eq_of_lt]
      have : su < 2 ^ su := by exact Nat.lt_two_pow_self
      sorry
  · grind only
  · have := neg_two_pow_le_minNormalExp hep hsp heu
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    -- | This needs bounds on `minSubnormalExp ≤ x.ex.toInt` to prove this.
    -- ⊢ -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt
    sorry
  · have := minNormalExp_lt_two_pow hep hsp heu
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    --  This needs bounds on `x.ex.toInt ≤ maxNormalExp` to prove this.
    -- ⊢ minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1)
    sorry

theorem BitVec.eq_iff_getLsbD_eq (a b : BitVec w) : a = b ↔
    (∀ (i : Nat), a.getLsbD i = b.getLsbD i) := by
  constructor
  · intros h
    subst h
    grind only
  · intros h
    ext i hi
    simp only [← BitVec.getLsbD_eq_getElem]
    grind only [#0a30]


/--
`p iff q` iff `not p iff not q`.
-/
theorem iff_iff_not_iff_not {p q : Prop} :
    (p ↔ q) ↔ (¬ p ↔ ¬ q) := by
  grind


/-! # roundTowardZero -/

theorem toRat_roundTowardZero_eq_lower_of_nonneg (x : UnpackedFloat e s)
    (hx : 0 ≤ x.toRat) :
    (x.roundTowardZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

theorem toRat_roundTowardZero_eq_upper_of_neg (x : UnpackedFloat e s)
    (hx : x.toRat < 0) :
    (x.roundTowardZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry


/-# successorAwayFromZero -/

theorem toRat_successorAwayFromZero_eq_upper_of_nonneg (x : UnpackedFloat e s)
    (hx : 0 ≤ x.toRat) :
    (x.successorAwayFromZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

theorem toRat_successorAwayFromZero_eq_upper_of_neg (x : UnpackedFloat e s)
    (hx : x.toRat < 0) :
    (x.successorAwayFromZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

/-! # extractIsEven -/

@[simp]
theorem UnpackedFloat.extractIsEven_eq_isEven_lower_of_nonneg (x : UnpackedFloat e s)
    (hx : x.sign = false) :
    x.extractIsEven e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat)) := by
  simp [UnpackedFloat.extractIsEven]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem UnpackedFloat.extractIsEven_eq_isEven_upper_of_neg (x : UnpackedFloat e s)
    (hx : x.sign = true) :
    x.extractIsEven e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat)) := by
  simp [UnpackedFloat.extractIsEven]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry


/-! # extractGuardBit -/

theorem UnpackedFloat.extractGuardBit_eq_true_iff
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) :
    x.extractGuardBit ep sp = true ↔ x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat) := by
  simp [UnpackedFloat.extractGuardBit]
  constructor
  · intros h
    obtain h := BitVec.ne_iff_getLsbD_ne .. |>.mp h
    obtain ⟨i, hi⟩ := h
    simp at hi
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu] at hi
    grind only
  · intros h
    intros hcontra
    obtain hcontra := BitVec.eq_iff_getLsbD_eq .. |>.mp hcontra
    simp at hcontra
    specialize hcontra _ h (by grind)
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu] at hcontra
    grind only

/--
The guard bit is the bit at the lower index at '2' (when `su = sp + 2`),
plus the offset from the exponent difference, which accounts for shifts when we are subnormal.
-/
theorem UnpackedFloat.extractGuardBit_eq_getLsbD
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) :
    x.extractGuardBit ep sp =  x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat)  := by
  have := UnpackedFloat.extractGuardBit_eq_true_iff hep hsp heu hsu x
  grind only [#0e2e4e0bb1f1e395]

-- TODO: 'toRatSig' lemma about what the guardBit tracks.

theorem SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq_decide (r : Rat) :
    (smtLibRoundMethod e s smtLibV smtLibV).lowerHalf (ExtRat.Number r) =
    (r - ((smtLibRoundMethod e s smtLibV smtLibV).lower (ExtRat.Number r)).toRat ≤ 2^e) := by
  -- TODO: this is what I need to prove now.
  sorry

-- theorem le_toRatSig_of_extractGuardBit

@[simp]
theorem UnpackedFloat.extractGuardBit_eq_not_lowerHalf_of_nonneg (x : UnpackedFloat e s)
    (hx : x.sign = false) :
    x.extractGuardBit e s = ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat) := by
  -- simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem UnpackedFloat.extractGuardBit_eq_lowerHalf_of_neg (x : UnpackedFloat e s)
    (hx : x.sign = true) :
    x.extractGuardBit e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat) := by
  simp [UnpackedFloat.extractGuardBit]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem BitVec.and_allOnes_eq_self (bv : BitVec n) :
    bv &&& (BitVec.allOnes n) = bv := by
  ext i hi
  simp

@[simp]
theorem BitVec.allOnes_and_eq_self (bv : BitVec n) :
    (BitVec.allOnes n) &&& bv = bv := by
  ext i hi
  simp

/--
Zero extension to a larger width does not change the value.
-/
theorem BitVec.toNat_zeroExtend_of_le {n m : Nat} (bv : BitVec n) (h : n ≤ m) :
    (bv.zeroExtend m).toNat = bv.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le]
  grind only

/--
Zero extension to a smaller width does not change the value
if the value fits in the smaller size.
-/
theorem BitVec.toNat_zeroExtend_of_lt {n m : Nat} (bv : BitVec n) (h : bv.toNat  < 2 ^ m) :
    (bv.zeroExtend m).toNat = bv.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth]
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt]
  grind only



theorem extractStickyBit_eq_true_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su) :
  x.extractStickyBit ep sp = true ↔
    -- This makes sense,
    -- Consider when `su = sp + 2`.
    -- Then we're saying that some bit
    -- after the guard bit is nonzero.
     (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  simp [UnpackedFloat.extractStickyBit]
  rw [UnpackedFloat.toNat_guardBitIndex_eq]
  rw [show (su - 1 - (sp + 1)) = su - (sp + 2) by grind only]
  rw [show su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat =
       ((su + (minNormalExp ep - x.ex.toInt).toNat)) - (sp + 2) by grind only]
  · rw [show (su - (su + (minNormalExp ep - x.ex.toInt).toNat - (sp + 2))) =
        (sp + 2 - (minNormalExp ep - x.ex.toInt).toNat) by grind only]
    constructor
    · intros heq
      rw [BitVec.eq_iff_getLsbD_eq] at heq
      simp at heq
      obtain ⟨i, hi⟩ := heq
      exists i
      grind only
    · intros h
      simp at h
      intros hcontra
      rw [BitVec.eq_iff_getLsbD_eq] at hcontra
      simp at hcontra
      obtain ⟨i, hi⟩ := h
      specialize hcontra i (by grind)
      obtain ⟨hi1, hi2⟩ := hi
      grind
  · grind only
  · grind only
  · grind only
  · grind only

theorem extractStickyBit_eq_false_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su) :
  x.extractStickyBit ep sp = false ↔
    -- This makes sense,
    -- This says that all the lower bits are false.
     (∀ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat →
      x.sig.getLsbD i = false) := by
  have htrue := extractStickyBit_eq_true_iff hep hsp heu hsu x
  rw [iff_iff_not_iff_not] at htrue
  grind only [#c179, #0b53, #b326]

/--
The sticky bit tracks whether there is a bit
below the guard bit that is 1.
This is equivalent to saying that there exists some bit below the guard bit that is 1.
-/
theorem extractStickyBit_eq_decide
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su) :
  x.extractStickyBit ep sp = decide (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  by_cases hextract : x.extractStickyBit ep sp = true
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x
    grind only [#46e5, #0b53]
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x
    simp at this
    grind only [#46e5, #0b53]

@[simp]
theorem UnpackedFloat.extractStickyBit_eq_not_tieBreak_of_nonneg_of_guardBit
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hx : x.sign = false)
    (hguard : x.extractGuardBit ep sp = true) :
    x.extractStickyBit ep sp = ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat) := by
  simp [SmtLibSemantics.smtLibRoundMethod]
  rw [extractStickyBit_eq_decide]
  · sorry
  · grind only
  · grind only
  · grind only
  · grind only

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.
-/
theorem UnpackedFloat.toExtRat_round_eq_smtLibRound
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (rstar : Rat) -- rational number we are modelling.
    (hx : (rstar - hx).abs < (2 : Rat) ^ (-((sp + 1) : Int))) -- the rational is within 0.5 ulp of the unpacked float.
    -- | The sticky bitt tracks whether 'r' is exactly representable.
    -- (hsticky : (∃ (pf : PackedFloat ep sp), pf.toRat = rstar)  x.extractStickyBit ep sp = false)
      :
    (x.round rm (tep := ep) (tsp := sp) : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).toExtRat =
    ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm x.sign (ExtRat.Number x.toRat)).toExtRat := by
  simp
  rw [UnpackedFloat.round]
  sorry

end Fp
