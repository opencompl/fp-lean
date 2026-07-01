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

end FpAgainstFloatModel
