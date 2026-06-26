import Fp.Theorems.UnpackedFloat.Round.ExtractStickyBit

namespace Fp



/-! # Normalization commutes with negation -/

/-- Negating an `UnpackedFloat` commutes with `normalize` (passing the negated sign). -/
@[simp]
theorem UnpackedFloat.neg_normalize_eq_neg_normalize (x : UnpackedFloat e s) :
    (-x).normalize = -(x.normalize) := by
  simp only [UnpackedFloat.neg_def, UnpackedFloat.normalize, UnpackedFloat.neg,
    UnpackedFloat.mkZero]
  by_cases h : x.sig = 0#s
  · simp only [h, beq_self_eq_true, cond_true]
  · have : (x.sig == 0#s) = false := by simp [h]
    simp only [this, cond_false]

/-- If `x` is already normalized, so is `-x`. -/
theorem UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq (x : UnpackedFloat e s)
    (hxnorm : x.normalize = x) :
    (-x).normalize = -x := by
  rw [UnpackedFloat.neg_normalize_eq_neg_normalize, hxnorm]

/-- `EUnpackedFloat.normalize` is the identity whenever the underlying number (in the `Number`
state) is already normalized. This is the "correct statement" the rounding-circuit outputs need:
for non-`Number` states normalize is trivially identity, and for `Number` states it reduces to the
inner `UnpackedFloat.normalize` being a fixed point. -/
theorem EUnpackedFloat.normalize_eq_self_of_num (euf : EUnpackedFloat e s)
    (h : euf.isNumber = true → euf.num.normalize = euf.num) :
    euf.normalize = euf := by
  unfold EUnpackedFloat.normalize
  cases hst : euf.isNumber with
  | false => simp [hst]
  | true =>
    have hstate : euf.state = .Number := by
      simpa only [EUnpackedFloat.isNumber, beq_iff_eq] using hst
    simp only [hst, cond_true, h hst, UnpackedFloat.toEUnpackedFloat]
    rw [← hstate]

/-- `EUnpackedFloat.normalize` commutes with negation (it only touches the `num`, and negation
preserves the state). -/
theorem EUnpackedFloat.neg_normalize_eq_neg_normalize (x : EUnpackedFloat e s) :
    (-x).normalize = -(x.normalize) := by
  have hnum : (-x).num = -(x.num) := rfl
  have hstate : (-x).state = x.state := rfl
  unfold EUnpackedFloat.normalize EUnpackedFloat.isNumber
  rw [hstate]
  cases hst : (x.state == State.Number) <;> simp only [cond_false, cond_true]
  rw [hnum, UnpackedFloat.neg_normalize_eq_neg_normalize]
  rfl

/--
info: 'Fp.EUnpackedFloat.normalize_eq_self_of_num' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms EUnpackedFloat.normalize_eq_self_of_num

/-- The canonical zero is a `normalize` fixed point. -/
theorem UnpackedFloat.normalize_mkZero (sign : Bool) :
    (UnpackedFloat.mkZero sign : UnpackedFloat e s).normalize = UnpackedFloat.mkZero sign := by
  simp [UnpackedFloat.normalize, UnpackedFloat.mkZero]

/-- `normalize` is the identity on `mkNumber n` when `n` is already normalized. -/
theorem EUnpackedFloat.normalize_mkNumber_of_normalize {n : UnpackedFloat e s}
    (h : n.normalize = n) :
    (EUnpackedFloat.mkNumber n).normalize = EUnpackedFloat.mkNumber n :=
  EUnpackedFloat.normalize_eq_self_of_num _ (fun _ => by rw [EUnpackedFloat.num_mkNumber]; exact h)

/-- `normalize` is the identity on infinities (non-`Number` state). -/
theorem EUnpackedFloat.normalize_mkInfinity (sign : Bool) :
    (EUnpackedFloat.mkInfinity sign : EUnpackedFloat e s).normalize
      = EUnpackedFloat.mkInfinity sign :=
  EUnpackedFloat.normalize_eq_self_of_num _
    (fun h => by simp [EUnpackedFloat.isNumber, EUnpackedFloat.mkInfinity] at h)

/-- `normalize` is the identity on the (extended) canonical zero. -/
theorem EUnpackedFloat.normalize_mkZero (sign : Bool) :
    (EUnpackedFloat.mkZero sign : EUnpackedFloat e s).normalize = EUnpackedFloat.mkZero sign :=
  EUnpackedFloat.normalize_mkNumber_of_normalize (UnpackedFloat.normalize_mkZero sign)

/-# normalize -/

/--
`normalize` preserves `Rel`, provided normalizing does not underflow the
exponent. The precondition `hssub` is "the BitVec subtraction `ex - clz` does
not signed-underflow at width `eu`"; semantically this is the "no underflow at
normalize" condition. At the call sites this should follow from being in the
`¬ blastIsOverflowNonneg` branch combined with the value fitting in the
destination `(ep, sp)` format — but discharging that derivation is a separate
sorry to fill.
-/
theorem UnpackedFloat.normalize_Rel_of_Rel (_he : 1 < ep) (_hs : 0 < sp)
    (_heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (pf : PackedFloat ep sp)
    (hse : su - 1 < 2 ^ (eu - 1))
    (hssub : !x.ex.ssubOverflow (BitVec.setWidth eu x.sig.clz))
    (h : x.Rel pf) :
    x.normalize.Rel pf := by
  obtain ⟨hToRat, hSign⟩ := h
  apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
  · rw [UnpackedFloat.toRat'_normalize_eq_toRat' hse hssub]
    exact hToRat
  · simp only [UnpackedFloat.sign_normalize, beq_iff_eq, ite_self]
    exact hSign

/--
info: 'Fp.UnpackedFloat.normalize_Rel_of_Rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.normalize_Rel_of_Rel

theorem EUnpackedFloat.normalize_Rel_of_Rel (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : EUnpackedFloat eu su) (pf : PackedFloat ep sp)
    (hse : su - 1 < 2 ^ (eu - 1))
    (hssub : !x.num.ex.ssubOverflow (BitVec.setWidth eu x.num.sig.clz))
    (h : x.Rel pf) :
    x.normalize.Rel pf := by
  unfold EUnpackedFloat.normalize
  rcases hstate : x.state with rfl | rfl | rfl
  · simp [hstate, h]
  · simp [hstate, h]
  · simp [hstate]
    have hnumNorm :=
      UnpackedFloat.normalize_Rel_of_Rel he hs heu x.num pf hse hssub (by
        grind only [EUnpackeDFloat.num_Rel_of_Rel_of_eq_Number]
      )
    exact
      EUnpackedFloat.Rel_of_Rel_of_state_eq_Number x.num.normalize.toEUnpackedFloat pf rfl hnumNorm
/--
info: 'Fp.EUnpackedFloat.normalize_Rel_of_Rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EUnpackedFloat.normalize_Rel_of_Rel

end Fp
