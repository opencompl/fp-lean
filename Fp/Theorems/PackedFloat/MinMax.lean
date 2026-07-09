import Fp.Comparison
import Fp.SmtLibSemantics
import Fp.Theorems.PackedFloat.Comparison
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.PackUnpackRoundTrip

/-!
# `min`/`max` agree with the SMT-LIB min/max relations

This file relates the computable `PackedFloat.smtMin` / `PackedFloat.smtMax`
operators of `Fp/Comparison.lean` to the abstract BTRW15 relations `FpMinRel` /
`FpMaxRel` (SMT-LIB §V.B.2). Because min/max are *relations* (underspecified for
`(±0, ∓0)`), correctness is: the concrete output is always a valid witness of the
relation.

The proof reuses the ordering kernels proved in `Comparison.lean`
(`smtBgt_iff_toExtRat_gt`, `smtBlt_iff_toExtRat_lt`) together with three small
supporting facts:

* `UnpackedFloat.bltAux_flag_indep` / `EUnpackedFloat.bltAux_flag_indep` — the
  `xLTyOnDiffZeros` flag only changes the answer for differing-signed zeros, so
  whenever the two operands are not both zero the flag is irrelevant;
* `toExtRat_unpack_pack` — selecting an operand's `unpack` and re-packing
  preserves the `ExtRat` value (`min`/`max` only ever return one operand).
-/

set_option maxHeartbeats 1000000
-- The `min`/`max` selection is branch-dependent, so `simp only [cond_true, cond_false]`
-- intentionally lists both reductions even though only one fires per branch.
set_option linter.unusedSimpArgs false

open Fp.SmtLibSemantics

/-! ## Flag independence of the strict comparison away from differing zeros -/

/-- The `xLTyOnDiffZeros` flag of `UnpackedFloat.bltAux` only matters when the two
operands are both zero (differing-signed zeros). Off that case the flag is inert. -/
theorem UnpackedFloat.bltAux_flag_indep {e s : Nat} (b1 b2 : Bool) (x y : UnpackedFloat e s)
    (h : ¬(x.isZero = true ∧ y.isZero = true)) :
    UnpackedFloat.bltAux b1 x y = UnpackedFloat.bltAux b2 x y := by
  simp only [UnpackedFloat.bltAux]
  cases hxs : x.sign <;> cases hys : y.sign <;>
    simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true,
      Bool.not_false, cond_true, cond_false, Bool.and_self, Bool.false_or, Bool.or_false] <;>
    grind

/-- Lift `UnpackedFloat.bltAux_flag_indep` to `EUnpackedFloat`: the flag only enters
the both-finite branch, and there `EUnpackedFloat.isZero` reduces to the numeric
`UnpackedFloat.isZero`. NaN/∞ branches do not read the flag. -/
theorem EUnpackedFloat.bltAux_flag_indep {e s : Nat} (b1 b2 : Bool) (x y : EUnpackedFloat e s)
    (h : ¬(x.isZero = true ∧ y.isZero = true)) :
    EUnpackedFloat.bltAux b1 x y = EUnpackedFloat.bltAux b2 x y := by
  unfold EUnpackedFloat.bltAux
  by_cases hnan : (x.isNaN || y.isNaN) = true
  · simp only [hnan, cond_true]
  · rw [Bool.not_eq_true] at hnan
    by_cases hinf : (x.isInfinite || y.isInfinite) = true
    · simp only [hnan, hinf, cond_false, cond_true]
    · rw [Bool.not_eq_true] at hinf
      simp only [hnan, hinf, cond_false]
      apply UnpackedFloat.bltAux_flag_indep
      -- both `x`, `y` are `Number`s here, so `isZero` = `num.isZero`.
      obtain ⟨hxnan, hynan⟩ := Bool.or_eq_false_iff.mp hnan
      obtain ⟨hxinf, hyinf⟩ := Bool.or_eq_false_iff.mp hinf
      have hxnum : x.isNumber = true := by
        simp only [EUnpackedFloat.isNumber, EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite,
          beq_iff_eq] at *
        cases hst : x.state <;> simp_all
      have hynum : y.isNumber = true := by
        simp only [EUnpackedFloat.isNumber, EUnpackedFloat.isNaN, EUnpackedFloat.isInfinite,
          beq_iff_eq] at *
        cases hst : y.state <;> simp_all
      simp only [EUnpackedFloat.isZero, hxnum, hynum, Bool.true_and] at h
      exact h

/-! ## `EUnpackedFloat.isZero` embeds as `Number 0` -/

theorem EUnpackedFloat.toExtRat_eq_Number_zero_of_isZero {e s : Nat} (x : EUnpackedFloat e s)
    (h : x.isZero = true) : x.toExtRat = .Number 0 := by
  simp only [EUnpackedFloat.isZero, Bool.and_eq_true, EUnpackedFloat.isNumber, beq_iff_eq] at h
  obtain ⟨hst, hz⟩ := h
  have hnan : x.isNaN = false := by simp [EUnpackedFloat.isNaN, hst]
  have hinf : x.isInfinite = false := by simp [EUnpackedFloat.isInfinite, hst]
  simp only [EUnpackedFloat.toExtRat, hnan, hinf, cond_false]
  rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat'_eq_zero_of_isZero x.num hz]

namespace PackedFloat

/-! ## Re-packing a selected operand preserves the value -/

/-- `min`/`max` return one operand's `unpack`, re-packed. Re-packing an already
unpacked float preserves its `ExtRat` value (it is `Canonical`). -/
theorem toExtRat_unpack_pack {e s : Nat} (he : 1 < e) (hs : 0 < s) (pf : PackedFloat e s) :
    (pf.unpack.pack).toExtRat = pf.toExtRat := by
  have h1 : (pf.unpack.pack).unpack.toExtRat = (pf.unpack.pack).toExtRat :=
    PackedFloat.toExtRat_unpack_eq_toExtRat
  have h2 : (pf.unpack.pack).unpack = pf.unpack :=
    EUnpackedFloat.pack_unpack_of_Canonical he hs pf.unpack
      (EUnpackedFloat.Canonical_unpack he hs pf)
  rw [h2] at h1
  rw [← h1]
  exact PackedFloat.toExtRat_unpack_eq_toExtRat

/-! ## `toExtRat = NaN` characterises `isNaN` -/

theorem toExtRat_eq_NaN_iff_isNaN {e s : Nat} (f : PackedFloat e s) :
    f.toExtRat = .NaN ↔ f.isNaN := by
  rw [PackedFloat.toExtRat_eq_toExtRat']
  exact PackedFloat.toExtRat'_eq_NaN_iff_isNaN f

/-! ## The strict comparison used by `min`/`max`, away from differing zeros -/

/-- For non-NaN `f, g` whose values differ, `bgtAux` (with any `xOnDiffZeros`
flag) computes the strict order `g < f`. The flag is inert because differing
values are not both zero. -/
theorem bgtAux_eq_decide_of_ne {e s : Nat} (z : Bool) (f g : PackedFloat e s)
    (hf : f.isNaN = false) (hg : g.isNaN = false) (hne : f.toExtRat ≠ g.toExtRat) :
    PackedFloat.bgtAux z f g = decide (g.toExtRat < f.toExtRat) := by
  -- Not both operands are zero (else both would embed to `Number 0`, contradicting `hne`).
  have hnotboth : ¬(g.unpack.isZero = true ∧ f.unpack.isZero = true) := by
    rintro ⟨hz1, hz2⟩
    apply hne
    have e1 : g.unpack.toExtRat = .Number 0 :=
      EUnpackedFloat.toExtRat_eq_Number_zero_of_isZero _ hz1
    have e2 : f.unpack.toExtRat = .Number 0 :=
      EUnpackedFloat.toExtRat_eq_Number_zero_of_isZero _ hz2
    rw [← PackedFloat.toExtRat_unpack_eq_toExtRat (pf := f),
        ← PackedFloat.toExtRat_unpack_eq_toExtRat (pf := g), e1, e2]
  -- The flag is inert: `bgtAux z f g = bgtAux true f g`.
  have hflag : PackedFloat.bgtAux z f g = PackedFloat.bgtAux true f g := by
    show EUnpackedFloat.bltAux (!z) g.unpack f.unpack
        = EUnpackedFloat.bltAux (!true) g.unpack f.unpack
    exact EUnpackedFloat.bltAux_flag_indep _ _ _ _ hnotboth
  -- `bgtAux true` is `smtBgt true` off NaN, hence the strict order.
  have hsmt : PackedFloat.smtBgt true f g = PackedFloat.bgtAux true f g := by
    simp only [PackedFloat.smtBgt, hf, Bool.false_and, cond_false]
  have hiff := PackedFloat.smtBgt_iff_toExtRat_gt true f g hf hg
  rw [hsmt] at hiff
  rw [hflag, Bool.eq_iff_iff, decide_eq_true_iff]
  exact hiff

/-- The `max` analogue of `bgtAux_eq_decide_of_ne`, for `bltAux`. -/
theorem bltAux_eq_decide_of_ne {e s : Nat} (z : Bool) (f g : PackedFloat e s)
    (hf : f.isNaN = false) (hg : g.isNaN = false) (hne : f.toExtRat ≠ g.toExtRat) :
    PackedFloat.bltAux z f g = decide (f.toExtRat < g.toExtRat) := by
  have hnotboth : ¬(f.unpack.isZero = true ∧ g.unpack.isZero = true) := by
    rintro ⟨hz1, hz2⟩
    apply hne
    have e1 : f.unpack.toExtRat = .Number 0 :=
      EUnpackedFloat.toExtRat_eq_Number_zero_of_isZero _ hz1
    have e2 : g.unpack.toExtRat = .Number 0 :=
      EUnpackedFloat.toExtRat_eq_Number_zero_of_isZero _ hz2
    rw [← PackedFloat.toExtRat_unpack_eq_toExtRat (pf := f),
        ← PackedFloat.toExtRat_unpack_eq_toExtRat (pf := g), e1, e2]
  have hflag : PackedFloat.bltAux z f g = PackedFloat.bltAux false f g := by
    show EUnpackedFloat.bltAux z f.unpack g.unpack
        = EUnpackedFloat.bltAux false f.unpack g.unpack
    exact EUnpackedFloat.bltAux_flag_indep _ _ _ _ hnotboth
  have hsmt : PackedFloat.smtBlt false f g = PackedFloat.bltAux false f g := by
    simp only [PackedFloat.smtBlt, hf, Bool.false_and, cond_false]
  have hiff := PackedFloat.smtBlt_iff_toExtRat_lt false f g hf hg
  rw [hsmt] at hiff
  rw [hflag, Bool.eq_iff_iff, decide_eq_true_iff]
  exact hiff

/-! ## `smtMin` selects an operand -/

/-- `smtMin z f g` is one of `f`, `g` re-packed, chosen by
`c := f.isNaN ∨ bgtAux z f g`. -/
theorem minAux_eq_cond {e s : Nat} (z : Bool) (f g : PackedFloat e s) :
    PackedFloat.minAux z f g
      = (bif (f.isNaN || PackedFloat.bgtAux z f g) then g.unpack.pack else f.unpack.pack) := by
  have hc : (f.unpack.isNaN || EUnpackedFloat.bgtAux z f.unpack g.unpack)
      = (f.isNaN || PackedFloat.bgtAux z f g) := by
    rw [PackedFloat.isNaN_unpack_eq_isNaN]; rfl
  show (EUnpackedFloat.minAux z f.unpack g.unpack).pack = _
  rw [EUnpackedFloat.minAux, hc]
  cases (f.isNaN || PackedFloat.bgtAux z f g) <;> rfl

theorem maxAux_eq_cond {e s : Nat} (z : Bool) (f g : PackedFloat e s) :
    PackedFloat.maxAux z f g
      = (bif (f.isNaN || PackedFloat.bltAux z f g) then g.unpack.pack else f.unpack.pack) := by
  have hc : (f.unpack.isNaN || EUnpackedFloat.bltAux z f.unpack g.unpack)
      = (f.isNaN || PackedFloat.bltAux z f g) := by
    rw [PackedFloat.isNaN_unpack_eq_isNaN]; rfl
  show (EUnpackedFloat.maxAux z f.unpack g.unpack).pack = _
  rw [EUnpackedFloat.maxAux, hc]
  cases (f.isNaN || PackedFloat.bltAux z f g) <;> rfl

/-- The `ExtRat` value of `smtMin`, in terms of the selection boolean. -/
theorem toExtRat_minAux {e s : Nat} (he : 1 < e) (hs : 0 < s) (z : Bool) (f g : PackedFloat e s) :
    (PackedFloat.minAux z f g).toExtRat
      = (bif (f.isNaN || PackedFloat.bgtAux z f g) then g.toExtRat else f.toExtRat) := by
  rw [PackedFloat.minAux_eq_cond]
  cases (f.isNaN || PackedFloat.bgtAux z f g) <;>
    simp only [cond_true, cond_false] <;>
    exact PackedFloat.toExtRat_unpack_pack he hs _

theorem toExtRat_maxAux {e s : Nat} (he : 1 < e) (hs : 0 < s) (z : Bool) (f g : PackedFloat e s) :
    (PackedFloat.maxAux z f g).toExtRat
      = (bif (f.isNaN || PackedFloat.bltAux z f g) then g.toExtRat else f.toExtRat) := by
  rw [PackedFloat.maxAux_eq_cond]
  cases (f.isNaN || PackedFloat.bltAux z f g) <;>
    simp only [cond_true, cond_false] <;>
    exact PackedFloat.toExtRat_unpack_pack he hs _

end PackedFloat

/-! ## Reductions of the BTRW15 relations to `ExtRat` facts under `v = ·.toExtRat` -/

theorem fpLtRel_iff {e s : Nat} (v : RoundableEmbed (PackedFloat e s) ExtRat)
    (hv : ∀ x, v.embed x = x.toExtRat) (a b : PackedFloat e s) :
    FpLtRel v a b ↔ a.toExtRat < b.toExtRat := by
  unfold FpLtRel; rw [hv, hv]

theorem fpGtRel_iff {e s : Nat} (v : RoundableEmbed (PackedFloat e s) ExtRat)
    (hv : ∀ x, v.embed x = x.toExtRat) (a b : PackedFloat e s) :
    FpGtRel v a b ↔ b.toExtRat < a.toExtRat := by
  unfold FpGtRel; rw [hv, hv]

theorem fpEqRel_iff {e s : Nat} (v : RoundableEmbed (PackedFloat e s) ExtRat)
    (hv : ∀ x, v.embed x = x.toExtRat) (a b : PackedFloat e s) :
    FpSmtLibEqRel v a b ↔ a.toExtRat = b.toExtRat := by
  unfold FpSmtLibEqRel; rw [hv, hv]; simp only [instExtendedRat.smtLibEq]

theorem fpIsNaN_iff {e s : Nat} (v : RoundableEmbed (PackedFloat e s) ExtRat)
    (hv : ∀ x, v.embed x = x.toExtRat) (a : PackedFloat e s) :
    FpIsNaN v a ↔ a.isNaN := by
  unfold FpIsNaN; rw [hv]
  simp only [instExtendedRat.isNaN_eq, ExtRat.isNaN_iff, decide_eq_true_eq]
  exact PackedFloat.toExtRat_eq_NaN_iff_isNaN a

/-! ## Main theorems -/

/-- **BTRW15 §V.B.2, `min` relation.** `PackedFloat.smtMin` always produces a valid
witness of the abstract `FpMinRel` for the standard embedding `· .toExtRat`. -/
theorem PackedFloat.minAux_FpMinRel {e s : Nat} (he : 1 < e) (hs : 0 < s)
    (z : Bool) (f g : PackedFloat e s) :
    FpMinRel instPackedFloatExtRat f g (PackedFloat.minAux z f g) := by
  let v : RoundableEmbed (PackedFloat e s) ExtRat := instPackedFloatExtRat
  have hv : ∀ x : PackedFloat e s, v.embed x = x.toExtRat := fun _ => rfl
  show FpMinRel v f g (PackedFloat.minAux z f g)
  by_cases hf : f.isNaN
  · -- `f` is NaN: condition true, output is `g`.
    have hcond : (f.isNaN || PackedFloat.bgtAux z f g) = true := by rw [hf]; rfl
    have hsel : (PackedFloat.minAux z f g).toExtRat = g.toExtRat := by
      rw [PackedFloat.toExtRat_minAux he hs, hcond]; simp only [cond_true, cond_false]
    exact Or.inr (Or.inl ⟨Or.inr ((fpIsNaN_iff v hv f).mpr hf), (fpEqRel_iff v hv _ g).mpr hsel⟩)
  · have hfF : f.isNaN = false := by simpa using hf
    by_cases hg : g.isNaN
    · -- `g` is NaN (only): condition false, output is `f`.
      have hbgt : PackedFloat.bgtAux z f g = false := by
        have hgn : g.unpack.isNaN = true := by rw [PackedFloat.isNaN_unpack_eq_isNaN]; exact hg
        show EUnpackedFloat.bltAux (!z) g.unpack f.unpack = false
        unfold EUnpackedFloat.bltAux; simp only [hgn, Bool.true_or, cond_true]
      have hcond : (f.isNaN || PackedFloat.bgtAux z f g) = false := by rw [hfF, hbgt]; rfl
      have hsel : (PackedFloat.minAux z f g).toExtRat = f.toExtRat := by
        rw [PackedFloat.toExtRat_minAux he hs, hcond]; simp only [cond_true, cond_false]
      exact Or.inl ⟨Or.inr ((fpIsNaN_iff v hv g).mpr hg), (fpEqRel_iff v hv _ f).mpr hsel⟩
    · -- both non-NaN
      have hgF : g.isNaN = false := by simpa using hg
      by_cases heq : f.toExtRat = g.toExtRat
      · -- equal values: the eq disjunct holds regardless of the selection.
        refine Or.inr (Or.inr ⟨(fpEqRel_iff v hv f g).mpr heq, ?_⟩)
        cases hc : (f.isNaN || PackedFloat.bgtAux z f g)
        · exact Or.inl ((fpEqRel_iff v hv _ f).mpr (by rw [PackedFloat.toExtRat_minAux he hs, hc]; simp only [cond_true, cond_false]))
        · exact Or.inr ((fpEqRel_iff v hv _ g).mpr (by rw [PackedFloat.toExtRat_minAux he hs, hc]; simp only [cond_true, cond_false]))
      · -- differing values: `bgtAux` picks the strict order.
        have hbgt : PackedFloat.bgtAux z f g = decide (g.toExtRat < f.toExtRat) :=
          PackedFloat.bgtAux_eq_decide_of_ne z f g hfF hgF heq
        by_cases hlt : g.toExtRat < f.toExtRat
        · have hcond : (f.isNaN || PackedFloat.bgtAux z f g) = true := by
            rw [hfF, hbgt, Bool.false_or, decide_eq_true_eq]; exact hlt
          have hsel : (PackedFloat.minAux z f g).toExtRat = g.toExtRat := by
            rw [PackedFloat.toExtRat_minAux he hs, hcond]; simp only [cond_true, cond_false]
          exact Or.inr (Or.inl
            ⟨Or.inl ((fpLtRel_iff v hv g f).mpr hlt), (fpEqRel_iff v hv _ g).mpr hsel⟩)
        · have hcond : (f.isNaN || PackedFloat.bgtAux z f g) = false := by
            rw [hfF, hbgt, Bool.false_or, decide_eq_false_iff_not]; exact hlt
          have hsel : (PackedFloat.minAux z f g).toExtRat = f.toExtRat := by
            rw [PackedFloat.toExtRat_minAux he hs, hcond]; simp only [cond_true, cond_false]
          have hfg : f.toExtRat < g.toExtRat := by
            have hle : f.toExtRat ≤ g.toExtRat :=
              Classical.byContradiction fun hle =>
                hlt (ExtRat.lt_of_not_le
                  (fun h => hf ((PackedFloat.toExtRat_eq_NaN_iff_isNaN f).mp h))
                  (fun h => hg ((PackedFloat.toExtRat_eq_NaN_iff_isNaN g).mp h)) hle)
            exact ExtRat.lt_iff.mpr ⟨hle, heq⟩
          exact Or.inl
            ⟨Or.inl ((fpLtRel_iff v hv f g).mpr hfg), (fpEqRel_iff v hv _ f).mpr hsel⟩

/-- **BTRW15 §V.B.2, `max` relation.** `PackedFloat.smtMax` always produces a valid
witness of the abstract `FpMaxRel` for the standard embedding `· .toExtRat`. -/
theorem PackedFloat.maxAux_FpMaxRel {e s : Nat} (he : 1 < e) (hs : 0 < s)
    (z : Bool) (f g : PackedFloat e s) :
    FpMaxRel instPackedFloatExtRat f g (PackedFloat.maxAux z f g) := by
  let v : RoundableEmbed (PackedFloat e s) ExtRat := instPackedFloatExtRat
  have hv : ∀ x : PackedFloat e s, v.embed x = x.toExtRat := fun _ => rfl
  show FpMaxRel v f g (PackedFloat.maxAux z f g)
  by_cases hf : f.isNaN
  · have hcond : (f.isNaN || PackedFloat.bltAux z f g) = true := by rw [hf]; rfl
    have hsel : (PackedFloat.maxAux z f g).toExtRat = g.toExtRat := by
      rw [PackedFloat.toExtRat_maxAux he hs, hcond]; simp only [cond_true, cond_false]
    exact Or.inr (Or.inl ⟨Or.inr ((fpIsNaN_iff v hv f).mpr hf), (fpEqRel_iff v hv _ g).mpr hsel⟩)
  · have hfF : f.isNaN = false := by simpa using hf
    by_cases hg : g.isNaN
    · have hblt : PackedFloat.bltAux z f g = false := by
        have hgn : g.unpack.isNaN = true := by rw [PackedFloat.isNaN_unpack_eq_isNaN]; exact hg
        show EUnpackedFloat.bltAux z f.unpack g.unpack = false
        unfold EUnpackedFloat.bltAux; simp only [hgn, Bool.or_true, cond_true]
      have hcond : (f.isNaN || PackedFloat.bltAux z f g) = false := by rw [hfF, hblt]; rfl
      have hsel : (PackedFloat.maxAux z f g).toExtRat = f.toExtRat := by
        rw [PackedFloat.toExtRat_maxAux he hs, hcond]; simp only [cond_true, cond_false]
      exact Or.inl ⟨Or.inr ((fpIsNaN_iff v hv g).mpr hg), (fpEqRel_iff v hv _ f).mpr hsel⟩
    · have hgF : g.isNaN = false := by simpa using hg
      by_cases heq : f.toExtRat = g.toExtRat
      · refine Or.inr (Or.inr ⟨(fpEqRel_iff v hv f g).mpr heq, ?_⟩)
        cases hc : (f.isNaN || PackedFloat.bltAux z f g)
        · exact Or.inl ((fpEqRel_iff v hv _ f).mpr (by rw [PackedFloat.toExtRat_maxAux he hs, hc]; simp only [cond_true, cond_false]))
        · exact Or.inr ((fpEqRel_iff v hv _ g).mpr (by rw [PackedFloat.toExtRat_maxAux he hs, hc]; simp only [cond_true, cond_false]))
      · have hblt : PackedFloat.bltAux z f g = decide (f.toExtRat < g.toExtRat) :=
          PackedFloat.bltAux_eq_decide_of_ne z f g hfF hgF heq
        by_cases hlt : f.toExtRat < g.toExtRat
        · have hcond : (f.isNaN || PackedFloat.bltAux z f g) = true := by
            rw [hfF, hblt, Bool.false_or, decide_eq_true_eq]; exact hlt
          have hsel : (PackedFloat.maxAux z f g).toExtRat = g.toExtRat := by
            rw [PackedFloat.toExtRat_maxAux he hs, hcond]; simp only [cond_true, cond_false]
          exact Or.inr (Or.inl
            ⟨Or.inl ((fpGtRel_iff v hv g f).mpr hlt), (fpEqRel_iff v hv _ g).mpr hsel⟩)
        · have hcond : (f.isNaN || PackedFloat.bltAux z f g) = false := by
            rw [hfF, hblt, Bool.false_or, decide_eq_false_iff_not]; exact hlt
          have hsel : (PackedFloat.maxAux z f g).toExtRat = f.toExtRat := by
            rw [PackedFloat.toExtRat_maxAux he hs, hcond]; simp only [cond_true, cond_false]
          have hgf : g.toExtRat < f.toExtRat := by
            have hle : g.toExtRat ≤ f.toExtRat :=
              Classical.byContradiction fun hle =>
                hlt (ExtRat.lt_of_not_le
                  (fun h => hg ((PackedFloat.toExtRat_eq_NaN_iff_isNaN g).mp h))
                  (fun h => hf ((PackedFloat.toExtRat_eq_NaN_iff_isNaN f).mp h)) hle)
            exact ExtRat.lt_iff.mpr ⟨hle, fun h => heq h.symm⟩
          exact Or.inl
            ⟨Or.inl ((fpGtRel_iff v hv f g).mpr hgf), (fpEqRel_iff v hv _ f).mpr hsel⟩

/-! ## Two-tuple (`zpm`/`zmp`) public correctness

`smtMin`/`smtMax` take two independent tie-break booleans — `zpm` for the
`(+0,-0)` input tuple, `zmp` for the `(-0,+0)` tuple — and route the one selected
by the first operand's sign (`x = +0 ⇒ zpm`, `x = -0 ⇒ zmp`) into the single-flag
`minAux`/`maxAux`. So each reduces to the generalized `minAux_FpMinRel` /
`maxAux_FpMaxRel` at the selected flag, and `FpMinRel`/`FpMaxRel` (a disjunction
admitting either operand) is satisfied for every choice of `zpm`, `zmp`. -/

/-- **BTRW15 §V.B.2, `min` relation.** `PackedFloat.smtMin zpm zmp` always produces
a valid witness of the abstract `FpMinRel` for the standard embedding `·.toExtRat`,
for either independent tie-break choice. -/
theorem PackedFloat.smtMin_FpMinRel {e s : Nat} (he : 1 < e) (hs : 0 < s)
    (zpm zmp : Bool) (f g : PackedFloat e s) :
    FpMinRel instPackedFloatExtRat f g (PackedFloat.smtMin zpm zmp f g) := by
  show FpMinRel instPackedFloatExtRat f g
    (PackedFloat.minAux (bif f.sign then zmp else zpm) f g)
  exact PackedFloat.minAux_FpMinRel he hs _ f g

/-- **BTRW15 §V.B.2, `max` relation.** `PackedFloat.smtMax zpm zmp` always produces
a valid witness of the abstract `FpMaxRel` for the standard embedding `·.toExtRat`,
for either independent tie-break choice. -/
theorem PackedFloat.smtMax_FpMaxRel {e s : Nat} (he : 1 < e) (hs : 0 < s)
    (zpm zmp : Bool) (f g : PackedFloat e s) :
    FpMaxRel instPackedFloatExtRat f g (PackedFloat.smtMax zpm zmp f g) := by
  show FpMaxRel instPackedFloatExtRat f g
    (PackedFloat.maxAux (bif f.sign then zmp else zpm) f g)
  exact PackedFloat.maxAux_FpMaxRel he hs _ f g

-- Both min/max correctness theorems are `sorry`-free (standard axioms only).
/--
info: 'PackedFloat.smtMin_FpMinRel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PackedFloat.smtMin_FpMinRel

/--
info: 'PackedFloat.smtMax_FpMaxRel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PackedFloat.smtMax_FpMaxRel
