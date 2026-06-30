import Fp.PackedFloat.Basic
import Fp.ExtRat
import Fp.EFixedPoint
import Fp.ExtDyadic.Basic

/-!
## Basic classification lemmas about `PackedFloat`

Mutual-exclusivity of the `isNaN`/`isInfinite`/`isZero`/`isNorm` predicates,
`isX_getY` lemmas relating predicates to constructors, the kind-case eliminator,
structural injectivity, and decidability instances.
-/

namespace PackedFloat

@[grind =>]
theorem isNaN_iff_ex_eq_sig_eq (pf : PackedFloat e s) (hs : 0 < s) :
    pf.isNaN ↔ (pf.ex = .allOnes e ∧ pf.sig ≠ 0#s) := by
  simp [isNaN]
  grind

@[grind =>]
theorem not_isNaN_iff_ex_ne_or_sig_ne (pf : PackedFloat e s) (hs : 0 < s) :
    (¬ pf.isNaN) ↔ (pf.ex ≠ .allOnes e ∨ pf.sig = 0#s) := by
  simp [isNaN]
  grind

@[grind =>]
theorem isInfinite_iff_ex_eq_sig_eq (pf : PackedFloat e s) (hs : 0 < s) :
    pf.isInfinite ↔ (pf.ex = .allOnes e ∧ pf.sig = 0#s) := by
  simp [isInfinite]
  grind

@[simp, grind →]
theorem eq_mkInfinity_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite →  ∃ (sign : Bool), pf = PackedFloat.getInfinity e s sign := by
  intro h
  simp [isInfinite] at h
  simp [PackedFloat.getInfinity]
  rcases pf with ⟨sign, ex, sig⟩
  simp_all


@[simp, grind .]
theorem ex_eq_of_isZero {pf : PackedFloat e s} (h : pf.isZero) :
    pf.ex = 0#e := by
  simp [isZero] at h
  simp [h]

@[simp]
theorem sig_eq_zero_if_isZero {pf : PackedFloat e s} (h : pf.isZero) :
    pf.sig = 0#s := by
  simp [isZero] at h
  simp [h]

/--
A packed float is zero iff the exponent and significand are zero.
-/
theorem isZero_iff_ex_eq_zero_and_sig_eq_zero {pf : PackedFloat e s} (he : 0 < e) :
    pf.isZero ↔ (pf.ex = 0#e ∧ pf.sig = 0#s) := by
  constructor
  · intro h
    simp only [isZero, BitVec.zero_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    simp [h]
  · intro h
    simp [isZero]
    grind only

@[simp, grind →]
theorem eq_mkZero_of_isZero {pf : PackedFloat e s} :
    pf.isZero → ∃ (sign : Bool), pf = PackedFloat.getZero e s sign := by
  intro h
  simp [isZero] at h
  simp [PackedFloat.getZero]
  rcases pf with ⟨sign, ex, sig⟩
  simp_all


@[simp, grind .]
theorem isZero_getZero {exWidth sigWidth : Nat} (sign : Bool) :
    (PackedFloat.getZero exWidth sigWidth sign).isZero = decide (0 < exWidth) := by
  simp [PackedFloat.getZero, isZero]
  grind

@[simp, grind .]
theorem eq_mkZero_of_isZero' {pf : PackedFloat e s} {sign : Bool} (he : 0 < e):
    (pf.isZero ∧ sign = pf.sign) ↔  pf = PackedFloat.getZero e s sign := by
  constructor
  · intros h
    simp [isZero] at h
    simp [PackedFloat.getZero]
    rcases pf with ⟨sign, ex, sig⟩
    simp_all
  · intros h
    rw [h]
    simp [he]

@[simp]
theorem isZero_getInfinity {exWidth sigWidth : Nat} (sign : Bool) :
    (PackedFloat.getInfinity exWidth sigWidth sign).isZero = false := by
  simp [PackedFloat.getInfinity, isZero]

@[simp, grind .]
theorem exp_eq_of_isNonzeroSubnorm {pf : PackedFloat e s}
    (h : pf.isNonzeroSubnorm := by solve | simp | grind) :
    pf.ex = 0#e := by
  simp [isNonzeroSubnorm] at h
  simp [h]

@[simp, grind .]
theorem toNat_ex_eq_of_isNonzeroSubnorm {pf : PackedFloat e s}
    (h : pf.isNonzeroSubnorm := by solve | simp | grind) :
    pf.ex.toNat = 0 := by
  simp [isNonzeroSubnorm] at h
  simp [h]


@[grind ., simp ←]
theorem isNorm_iff_ex_ne_allOnes_and_ex_ne_zero {pf : PackedFloat e s} :
    pf.isNorm ↔ (pf.ex ≠ .allOnes e ∧ pf.ex ≠ .zero e) := by
  simp [isNorm]

@[grind .]
theorem ex_ne_zero_if_isNorm {pf : PackedFloat e s} (h : pf.isNorm := by solve | simp | grind) :
    pf.ex != .zero e := by
  simp [isNorm] at h
  simp [h]

@[simp]
theorem sig_ne_zero_of_isNormOrNonzeroSubnorm_of_isNorm
    (pf : PackedFloat e s)
    (hnorm : pf.isNorm)
    (hsubnorm : ¬ pf.isNormOrNonzeroSubnorm) :
    pf.sig ≠ 0#s := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at hsubnorm
  grind

@[simp]
theorem ex_ne_zero_of_isNormOrNonzeroSubnorm_of_isNorm
    (pf : PackedFloat e s)
    (hnorm : pf.isNorm)
    (hsubnorm : ¬ pf.isNormOrNonzeroSubnorm) :
    pf.ex ≠ 0#e := by
  simp [isNorm] at hnorm
  simp [isNormOrNonzeroSubnorm] at hsubnorm
  grind


@[grind →]
theorem isZeroOrSubnorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → pf.isZeroOrSubnorm := by
  grind [isZero, isZeroOrSubnorm]

@[grind →]
theorem isZeroOrSubnorm_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → pf.isZeroOrSubnorm := by
  grind [isNonzeroSubnorm, isZeroOrSubnorm]


-- TODO: delete 'isNZero',
@[grind →]
theorem isZero_of_isNZero {pf : PackedFloat e s} :
    pf.isNZero → pf.isZero := by
  grind [isNZero, isZero]

@[grind →]
theorem isZero_of_isPZero {pf : PackedFloat e s} :
    pf.isPZero → pf.isZero := by
  grind [isPZero, isZero]

@[grind .]
theorem isZero_iff_isNZero_or_isPZero {pf : PackedFloat e s} :
    pf.isZero ↔ pf.isNZero ∨ pf.isPZero := by
  grind [isZero, isNZero, isPZero]


@[grind →]
theorem isNormOrSubnorm_of_isNorm (pf : PackedFloat e s) :
    pf.isNorm → pf.isNormOrNonzeroSubnorm := by
  grind [isNorm, isNormOrNonzeroSubnorm]


@[grind →]
theorem isNormOrSubnorm_of_isSubnorm (pf : PackedFloat e s) :
    pf.isNonzeroSubnorm → pf.isNormOrNonzeroSubnorm := by
  simp only [isNonzeroSubnorm, BitVec.zero_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    isNormOrNonzeroSubnorm, and_imp]
  intros he hex hsig
  simp [hex, hsig]
  grind

@[grind .]
theorem isNormOrSubnorm_eq_isNorm_or_isSubnorm (pf : PackedFloat e s) :
    pf.isNormOrNonzeroSubnorm = (pf.isNorm ∨ pf.isNonzeroSubnorm) := by
  simp [isNorm, isNonzeroSubnorm, isNormOrNonzeroSubnorm]
  by_cases he : e = 0
  · subst he
    grind
  · grind

@[grind →]
theorem not_isNaN_of_isNormOrSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isNaN := by
  grind [isNaN, isNormOrNonzeroSubnorm]

@[grind →]
theorem not_isInfinite_of_isNormOrSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isInfinite := by
  grind [isInfinite, isNormOrNonzeroSubnorm]

@[grind →]
theorem not_isZero_of_isNormOrSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isZero := by
  grind [isZero, isNormOrNonzeroSubnorm, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isInfinite_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isInfinite := by
  grind [isNaN, isInfinite]

@[grind →]
theorem not_isZero_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isZero := by
  grind [isNaN, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isSubnorm_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isNonzeroSubnorm := by
  grind [isNaN, isNonzeroSubnorm, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isNorm_of_isNaN {pf : PackedFloat e s} :
    pf.isNaN → !pf.isNorm := by
  grind [isNaN, isNorm]

@[grind →]
theorem not_isNaN_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isNaN := by
  grind [isNaN, isInfinite]

@[grind →]
theorem not_isZero_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isZero := by
  grind [isInfinite, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isSubnorm_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isNonzeroSubnorm := by
  grind [isInfinite, isNonzeroSubnorm]

@[grind →]
theorem not_isNorm_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → !pf.isNorm := by
  grind [isInfinite, isNorm]

@[grind →]
theorem not_isNaN_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isNaN := by
  grind [isNaN, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isInfinite_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isInfinite := by
  grind [isInfinite, isZero, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isSubnorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isNonzeroSubnorm := by
  grind [isNonzeroSubnorm, isZero]

@[grind →]
theorem not_isNorm_of_isZero {pf : PackedFloat e s} :
    pf.isZero → !pf.isNorm := by
  grind [isZero, isNorm]

@[grind →]
theorem not_isNaN_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isNaN := by
  grind [isNaN, isNonzeroSubnorm, BitVec.allOnes_ne_zero]

@[grind →]
theorem not_isInfinite_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isInfinite := by
  grind [isInfinite, isNonzeroSubnorm]

@[grind →]
theorem not_isZero_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isZero := by
  grind [isNonzeroSubnorm, isZero]

@[grind →]
theorem not_isNorm_of_isSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → !pf.isNorm := by
  grind [isNonzeroSubnorm, isNorm]

@[grind →]
theorem not_isNaN_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isNaN := by
  grind [isNaN, isNorm]

@[grind →]
theorem not_isInfinite_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isInfinite := by
  grind [isInfinite, isNorm]

@[grind →]
theorem not_isInfinite_of_isNormOrNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNormOrNonzeroSubnorm → !pf.isInfinite := by
  grind [isInfinite, isNormOrNonzeroSubnorm]

@[grind →]
theorem not_isZero_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isZero := by
  grind [isZero, isNorm]

@[grind →]
theorem not_isSubnorm_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → !pf.isNonzeroSubnorm := by
  grind [isNonzeroSubnorm, isNorm]

@[simp, grind! .]
theorem isInfinite_getInfinity (e s : Nat) (sign : Bool)  :
    (PackedFloat.getInfinity e s sign).isInfinite = decide (0 < s) := by
  simp only [isInfinite, getInfinity, BitVec.ofNat_eq_ofNat, BEq.rfl, BitVec.zero_eq, Bool.and_true,
    Bool.true_and]
  grind

@[simp, grind! .]
theorem isInfinite_getZero (e s : Nat) (sign : Bool):
    (PackedFloat.getZero e s sign).isInfinite = decide (e = 0 ∧ s ≠ 0) := by
  simp only [isInfinite, getZero, BitVec.zero_eq]
  grind

@[simp]
theorem isNaN_getInfinity_eq_false (sign : Bool) :
    (PackedFloat.getInfinity e s sign).isNaN = !(0 < s) := by
  simp [PackedFloat.getInfinity, isNaN]
  grind

theorem sigWidth_ge_one_of_isInfinite {pf : PackedFloat e s} :
    pf.isInfinite → s ≥ 1 := by
  grind [isInfinite]

theorem expWidth_ge_one_of_isZero {pf : PackedFloat e s} :
    pf.isZero → e ≥ 1 := by
  grind [isZero]

theorem expWidth_ge_one_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → e ≥ 1 := by
  grind [isNonzeroSubnorm]

theorem sigWidth_ge_one_of_isNonzeroSubnorm {pf : PackedFloat e s} :
    pf.isNonzeroSubnorm → s ≥ 1 := by
  grind [isNonzeroSubnorm]

theorem expWidth_ge_two_of_isNorm {pf : PackedFloat e s} :
    pf.isNorm → e ≥ 2 := by
  grind [isNorm]

@[simp]
theorem isNaN_getZero {e s : Nat} (sign : Bool) :
  (PackedFloat.getZero e s sign).isNaN  = decide (e = 0 ∧ s = 0) := by
  simp [PackedFloat.getZero, isNaN]
  grind

@[simp]
theorem isNaN_getNaN {e s : Nat}  :
    (PackedFloat.getNaN e s).isNaN = true := by
  simp [getNaN, isNaN]
  grind

@[simp]
theorem EquivUptoNaN.of_mkNaN_iff (x : PackedFloat e s) : EquivUptoNaN x (PackedFloat.getNaN e s) ↔ x.isNaN := by
  simp [EquivUptoNaN]
  intros hx
  subst hx
  simp

@[elab_as_elim]
theorem kindCasesNaNInfZeroNum {P : PackedFloat e s → Prop}
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
theorem isNaN_neg_iff_isNaN (pf : PackedFloat e s) : isNaN (-pf) ↔ isNaN pf := by
  simp [isNaN]

@[simp]
theorem neg_isInfinite_iff_isInfinite (pf : PackedFloat e s) :
    isInfinite (-pf) ↔ isInfinite pf := by
  simp [isInfinite]



@[simp]
theorem isNorm_neg (pf : PackedFloat e s) : (- pf).isNorm = pf.isNorm := by
  simp [PackedFloat.isNorm]



@[grind =]
theorem isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero {pf : PackedFloat e s} (h : ¬ pf.isNaN) (h2 : ¬ pf.isInfinite) (h3 : ¬ pf.isZero) :
    pf.isNormOrNonzeroSubnorm := by
  simp [PackedFloat.isNormOrNonzeroSubnorm]
  simp [PackedFloat.isNaN] at h
  simp [PackedFloat.isInfinite] at h2
  simp [PackedFloat.isZero] at h3
  grind

/--
Case splitting on the different values a packed float
can have: it can be nan, infinity, zero, or a nonzero normal/subnormal.+
-/
@[elab_as_elim]
theorem classification {P : PackedFloat e s → Prop}
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
          · grind only [→ isNormOrSubnorm_of_isNorm]
          · grind only

end PackedFloat
