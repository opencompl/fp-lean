import FpAgainstFloatModel.Basic

/-!
# Relation C — the `ExtRat` value bridge

The cleanest route to `PackedFloat ⇄ Float.Model` agreement goes through the extended
rationals `ExtRat`.  We define `modelToExtRat : Float.Model → ExtRat` (the model has no
rational semantics of its own) and prove it agrees with the project's `PackedFloat.toExtRat`
on the same bits.  At the `Rat` level the subnormal normalization difference **disappears**
(both denote the same rational) and NaN collapses to a single `.NaN`, so this relation is far
cleaner than the structural one.  It also lets us reuse the project's existing rational
correctness theorems (`mul_eq_mul`, `add_eq_add`, `div_eq_div`, the `smtB*` comparisons).
-/

set_option maxHeartbeats 2000000
open Float.Model (UnpackedFloat)
namespace FpAgainstFloatModel

def modelUnpackedToExtRat : UnpackedFloat → ExtRat
  | .notANumber => .NaN
  | .infinity s => .Infinity (s == .negative)
  | .zero _ => .Number 0
  | .finite s m e _ => .Number ((cond (s == .negative) (-1) 1) * (m : Rat) * (2 : Rat) ^ e)

def modelToExtRat (fa : Float.Model) : ExtRat := modelUnpackedToExtRat fa.unpack

theorem sign_div_pow_mul_zpow (a N : Rat) (k : Int) :
    a * (N / 2 ^ (52:Nat)) * 2 ^ k = a * N * 2 ^ (k - 52) := by
  rw [← Rat.zpow_natCast 2 52, ← Rat.zpow_div_zpow (by decide : (2:Rat) ≠ 0) k 52]
  grind

theorem sign_cond (b : Bool) : (cond (signToModel b == .negative) (-1) 1 : Rat) = b.toSign := by
  cases b <;> rfl

theorem modelUnpackedToExtRat_toModelUnpacked (pf : PackedFloat 11 52) :
    modelUnpackedToExtRat (toModelUnpacked pf) = pf.toExtRat := by
  rw [PackedFloat.toExtRat_eq_toExtRat']
  unfold toModelUnpacked PackedFloat.toExtRat'
  by_cases h1 : pf.isNaN
  · simp [h1, modelUnpackedToExtRat]
  · by_cases h2 : pf.isInfinite
    · simp only [h1, h2, ↓reduceIte, cond_false, cond_true, Bool.false_eq_true,
        modelUnpackedToExtRat, signToModel]
      cases pf.sign <;> rfl
    · by_cases h3 : pf.isZero
      · simp [h1, h2, h3, modelUnpackedToExtRat]
      · have hao : pf.ex ≠ BitVec.allOnes 11 := by
          intro hc
          by_cases hs : pf.sig = 0#52
          · exact h2 (by simp [PackedFloat.isInfinite, hc, hs])
          · exact h1 (by simp [PackedFloat.isNaN, hc, hs])
        by_cases h4 : pf.ex = 0#11
        · -- subnormal
          have hnorm : pf.isNorm = false := by simp [PackedFloat.isNorm, h4]
          simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte, cond_false, cond_true,
            Bool.false_eq_true, modelUnpackedToExtRat]
          rw [ExtRat.Number.injEq, PackedFloat.toRat, sign_cond, PackedFloat.toRatSig,
            PackedFloat.toRatExp, hnorm]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [show ((0:Rat) + (pf.sig.toNat:Rat)/2^(52:Nat)) = (pf.sig.toNat:Rat)/2^(52:Nat) from by grind,
            sign_div_pow_mul_zpow,
            show (-(↑(bias 11 - 1) : Int) - 52) = (-1074 : Int) from by decide]
        · -- normal
          have hao2 : pf.ex ≠ 2047#11 := by
            rw [show (2047#11 : BitVec 11) = BitVec.allOnes 11 from by decide]; exact hao
          have hnorm : pf.isNorm = true := by simp [PackedFloat.isNorm, hao2, h4]
          simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte, cond_false, cond_true,
            Bool.false_eq_true, modelUnpackedToExtRat]
          rw [ExtRat.Number.injEq, PackedFloat.toRat, sign_cond, PackedFloat.toRatSig,
            PackedFloat.toRatExp, hnorm]
          simp only [↓reduceIte]
          rw [show (1 + (pf.sig.toNat:Rat)/2^(52:Nat)) = ((2^52 + pf.sig.toNat : Nat):Rat)/2^(52:Nat) from by push_cast; grind,
            sign_div_pow_mul_zpow,
            show ((↑pf.ex.toNat - ↑(bias 11) : Int) - 52) = (↑pf.ex.toNat - 1075 : Int) from by
              rw [show bias 11 = 1023 from by decide]; omega]

/-! ## Bridge: `ModelEquiv` ⇒ equal `ExtRat` value

The easy direction of relation A ↔ C: equal bits (up to NaN) denote equal `ExtRat` values.
This converts the arithmetic agreements' *input* hypotheses (`ModelEquiv`) into `ExtRat`
equalities, ready to be combined with the project's rational op-correctness theorems. -/

/-- `modelToExtRat` on `fa` equals the model's `ExtRat` reading of its unpacking. -/
theorem modelToExtRat_eq (fa : Float.Model) :
    modelToExtRat fa = modelUnpackedToExtRat fa.unpack := rfl

/-- Bit-equality (up to NaN) implies equal `ExtRat` value. Always holds — NaN ↦ `.NaN`,
±0 ↦ `.Number 0`. -/
theorem toExtRat_eq_modelToExtRat_of_modelEquiv {a : PackedFloat 11 52} {fa : Float.Model}
    (h : a.ModelEquiv fa) : a.toExtRat = modelToExtRat fa := by
  rw [modelToExtRat_eq, ← (modelEquiv_iff_unpack.mp h)]
  exact (modelUnpackedToExtRat_toModelUnpacked a).symm

/-- `modelToExtRat fa` equals the `toExtRat` of interpreting `fa`'s bits as a `PackedFloat`.
The reverse-bridge anchor: it reduces `ExtRat`-equality to the project's own `toExtRat`
determinism (`eq_of_toExtRat'_eq`). -/
theorem modelToExtRat_eq_ofBits (fa : Float.Model) :
    modelToExtRat fa
      = (PackedFloat.ofBits 11 52 (fa.toBits.toBitVec.cast (by decide))).toExtRat := by
  rw [← modelUnpackedToExtRat_toModelUnpacked, toModelUnpacked_eq_unpack, modelToExtRat_eq]
  congr 1
  unfold Float.Model.unpack toBits64
  congr 1
  have h0 : (PackedFloat.ofBits 11 52 (fa.toBits.toBitVec.cast (by decide))).toBits
      = fa.toBits.toBitVec.cast (by decide) := by
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [PackedFloat.toBits, PackedFloat.ofBits, BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb,
      BitVec.getLsbD_cast]
    grind
  rw [h0]; exact BitVec.eq_of_toNat_eq rfl

/-- The model value is `.NaN` exactly for `NaN` floats. -/
theorem modelUnpackedToExtRat_eq_NaN_iff (u : UnpackedFloat) :
    modelUnpackedToExtRat u = .NaN ↔ u = .notANumber := by
  cases u <;> simp [modelUnpackedToExtRat]

/-- `modelToExtRat fa = .NaN ↔ fa.isNaN`. -/
theorem modelToExtRat_eq_NaN_iff (fa : Float.Model) :
    modelToExtRat fa = .NaN ↔ fa.isNaN := by
  rw [modelToExtRat_eq, model_isNaN_iff_unpack, modelUnpackedToExtRat_eq_NaN_iff]

/-! ## Reverse bridge:  `ExtRat`-equal ⇒ bits-equal  (relation C ⇒ A)

The payoff of relation C. Equal `ExtRat` values force equal bits (up to NaN), *except* that
`ExtRat` cannot see the sign of `±0` — so the zero case takes an extra `hzsign` witness (which
relation B supplies). Off zero, the project's own `toExtRat` determinism closes it. -/

open PackedFloat

/-- Interpret a `Float.Model`'s 64 bits as a `PackedFloat 11 52`. -/
def modelBits (fa : Float.Model) : PackedFloat 11 52 :=
  PackedFloat.ofBits 11 52 (fa.toBits.toBitVec.cast (by decide))

/-- `modelToExtRat fa` is the value of `fa`'s bits read as a `PackedFloat`. -/
theorem modelToExtRat_eq_modelBits (fa : Float.Model) :
    modelToExtRat fa = (modelBits fa).toExtRat := modelToExtRat_eq_ofBits fa

/-- `modelBits fa` carries exactly `fa`'s 64-bit pattern. -/
theorem toBits64_modelBits (fa : Float.Model) :
    toBits64 (modelBits fa) = fa.toBits.toBitVec := by
  have h0 : (modelBits fa).toBits = fa.toBits.toBitVec.cast (by decide) := by
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [modelBits, PackedFloat.toBits, PackedFloat.ofBits, BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb,
      BitVec.getLsbD_cast]
    grind
  rw [toBits64, h0]; exact BitVec.eq_of_toNat_eq rfl

/-- Value `0` (off `NaN`) forces `isZero`. Derived from the project's `toExtRat' ≤/< 0` iffs. -/
theorem isZero_of_toExtRat'_eq_zero {x : PackedFloat 11 52} (hn : ¬ x.isNaN)
    (h : x.toExtRat' = .Number 0) : x.isZero := by
  by_cases hz : x.isZero
  · exact hz
  · exfalso
    have hle : (x.toExtRat' : ExtRat) ≤ .Number 0 := by rw [h]; decide
    have hlt : ¬ (x.toExtRat' : ExtRat) < .Number 0 := by rw [h]; decide
    simp at hle hlt
    grind

/-- **Reverse bridge.** Equal `ExtRat` value ⇒ `ModelEquiv` (bits equal up to NaN). The zero
case needs the sign witness `hzsign` (relation B supplies it); everything else is forced. -/
theorem modelEquiv_of_toExtRat_eq {a : PackedFloat 11 52} {fa : Float.Model}
    (h : a.toExtRat = modelToExtRat fa)
    (hzsign : a.isZero → a.sign = (modelBits fa).sign) :
    a.ModelEquiv fa := by
  have ha' : a.toExtRat' = (modelBits fa).toExtRat' := by
    rw [← PackedFloat.toExtRat_eq_toExtRat', ← PackedFloat.toExtRat_eq_toExtRat', h,
      modelToExtRat_eq_modelBits]
  by_cases hna : a.isNaN
  · refine Or.inr ⟨hna, (modelToExtRat_eq_NaN_iff fa).mp ?_⟩
    rw [← h, PackedFloat.toExtRat_eq_toExtRat']
    exact (PackedFloat.toExtRat'_eq_NaN_iff_isNaN a).mpr hna
  · have hpfb_na : ¬ (modelBits fa).isNaN := by
      rw [← PackedFloat.toExtRat'_eq_NaN_iff_isNaN, ← ha', PackedFloat.toExtRat'_eq_NaN_iff_isNaN]
      exact hna
    by_cases hz : a.isZero
    · have hpfbz : (modelBits fa).isZero := by
        apply isZero_of_toExtRat'_eq_zero hpfb_na
        rw [← ha']; exact PackedFloat.toExtRat'_eq_zero_of_isZero a hz
      have ha_ez : a.ex = 0#11 ∧ a.sig = 0#52 := by
        simp only [PackedFloat.isZero, Bool.and_eq_true, beq_iff_eq] at hz; grind
      have hp_ez : (modelBits fa).ex = 0#11 ∧ (modelBits fa).sig = 0#52 := by
        simp only [PackedFloat.isZero, Bool.and_eq_true, beq_iff_eq] at hpfbz; grind
      refine Or.inl ?_
      rw [toBits64, ← toBits64_modelBits, toBits64, PackedFloat.toBits, PackedFloat.toBits,
        ha_ez.1, ha_ez.2, hp_ez.1, hp_ez.2, hzsign hz]
    · have hpfb_z : ¬ (modelBits fa).isZero := by
        intro hc
        exact hz (isZero_of_toExtRat'_eq_zero hna
          (ha' ▸ PackedFloat.toExtRat'_eq_zero_of_isZero (modelBits fa) hc))
      have haeq : a = modelBits fa :=
        PackedFloat.eq_of_toExtRat'_eq a (modelBits fa) hna hpfb_na hz hpfb_z ha'
      exact Or.inl (by rw [toBits64, haeq]; exact toBits64_modelBits fa)

end FpAgainstFloatModel
