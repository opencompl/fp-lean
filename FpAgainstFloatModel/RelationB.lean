import FpAgainstFloatModel.ExtRat

/-!
# Relation B — the unpacked-value relation, completed

`unpack_unpackRel` proves that `PackedFloat.unpack` and the model's `unpack` denote the same
value (`UnpackedRel`).  The classification cases (NaN / infinity / zero) are structural; the
finite case's dyadic value equality (`DyadicEqNat`) is reduced — via relation C — to the fact
that the project's `unpackNum` and the model's `finite s m e` have the same `Rat` value.  This
sidesteps all the `BitVec` exponent / `clz`-shift arithmetic: both magnitudes equal `pf.toRat`,
so cancelling the (matching) sign gives `M₁·2^E₁ = M₂·2^E₂`, whence `DyadicEqNat`.
-/

set_option maxHeartbeats 4000000
open Float.Model (UnpackedFloat)
open PackedFloat
namespace FpAgainstFloatModel

/-! ## `DyadicEqNat` from a `Rat` value equality -/

/-- Casting a `Nat` dyadic magnitude `M · 2^(E-m)` (with `m ≤ E`) into `Rat`. -/
theorem cast_nat_pow (M : Nat) (E m : Int) (hEm : m ≤ E) :
    ((M * 2 ^ (E - m).toNat : Nat) : Rat) = (M : Rat) * 2 ^ (E - m) := by
  push_cast
  rw [← Rat.zpow_natCast 2 (E - m).toNat, Int.toNat_of_nonneg (by omega)]

/-- Value equality `M₁·2^E₁ = M₂·2^E₂` (in `Rat`) gives `DyadicEqNat`. -/
theorem DyadicEqNat.of_rat {M1 M2 : Nat} {E1 E2 : Int}
    (h : (M1 : Rat) * 2 ^ E1 = (M2 : Rat) * 2 ^ E2) : DyadicEqNat M1 E1 M2 E2 := by
  unfold DyadicEqNat
  have hm1 : min E1 E2 ≤ E1 := by omega
  have hm2 : min E1 E2 ≤ E2 := by omega
  have keyR : (M1:Rat) * 2 ^ (E1 - min E1 E2) = (M2:Rat) * 2 ^ (E2 - min E1 E2) := by
    rw [show E1 - min E1 E2 = E1 + (-(min E1 E2)) from by omega,
        show E2 - min E1 E2 = E2 + (-(min E1 E2)) from by omega,
        Rat.zpow_add (by decide : (2:Rat) ≠ 0), Rat.zpow_add (by decide : (2:Rat) ≠ 0)]
    grind
  have e1 := cast_nat_pow M1 E1 (min E1 E2) hm1
  have e2 := cast_nat_pow M2 E2 (min E1 E2) hm2
  have : ((M1 * 2 ^ (E1 - min E1 E2).toNat : Nat) : Rat)
      = ((M2 * 2 ^ (E2 - min E1 E2).toNat : Nat) : Rat) := by rw [e1, e2, keyR]
  exact_mod_cast this

/-- Same signed value (with nonzero sign multiplier) ⇒ `DyadicEqNat` on the magnitudes. -/
theorem dyadic_of_sign {s : Bool} {M1 M2 : Nat} {E1 E2 : Int} {v : Rat}
    (hp : (s.toSign : Rat) * M1 * 2 ^ E1 = v) (hm : (s.toSign : Rat) * M2 * 2 ^ E2 = v) :
    DyadicEqNat M1 E1 M2 E2 := by
  apply DyadicEqNat.of_rat
  have hs : (s.toSign : Rat) ≠ 0 := by exact_mod_cast Bool.toSign_ne_zero s
  grind

/-! ## The project `unpackNum`'s value -/

/-- Closed form of `unpackNum.toRat'`: `sign · sig.toNat · 2^(ex.toInt - 52)`. -/
theorem unpackNum_toRat'_eq (pf : PackedFloat 11 52) :
    pf.unpackNum.toRat' = pf.sign.toSign * (pf.unpackNum.sig.toNat : Rat)
      * 2 ^ (pf.unpackNum.ex.toInt - 52) := by
  rw [UnpackedFloat.toRat', UnpackedFloat.toSigNat, UnpackedFloat.toExpInt,
    PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign]
  congr 2
  omega

/-- The project's `unpackNum` has the same value as `pf` (off NaN/inf/zero). -/
theorem unpackNum_toRat_eq_toRat (pf : PackedFloat 11 52)
    (h1 : ¬ pf.isNaN) (h2 : ¬ pf.isInfinite) (h3 : ¬ pf.isZero) :
    pf.sign.toSign * (pf.unpackNum.sig.toNat : Rat) * 2 ^ (pf.unpackNum.ex.toInt - 52)
      = pf.toRat := by
  rw [← unpackNum_toRat'_eq, ← UnpackedFloat.toRat_eq_toRat']
  have hval : pf.unpack.toExtRat = pf.toExtRat := PackedFloat.toExtRat_unpack_eq_toExtRat
  rw [show pf.unpack = EUnpackedFloat.mkNumber pf.unpackNum from by simp [PackedFloat.unpack, h1, h2, h3],
    EUnpackedFloat.toExtRat_mkNumber, PackedFloat.toExtRat_eq_toExtRat'] at hval
  simp only [PackedFloat.toExtRat', h1, h2, cond_false, Bool.false_eq_true,
    ExtRat.Number.injEq] at hval
  exact hval

/-! ## Relation B holds: `unpack_unpackRel` -/

/-- `PackedFloat.unpack` agrees with the model's `unpack` — same value (`UnpackedRel`). -/
theorem unpack_unpackRel (pf : PackedFloat 11 52) :
    UnpackedRel pf.unpack (UnpackedFloat.unpack .binary64 (toBits64 pf)) := by
  rw [← toModelUnpacked_eq_unpack]
  by_cases h1 : pf.isNaN
  · unfold toModelUnpacked; simp only [h1, ↓reduceIte]; simp [PackedFloat.unpack, UnpackedRel, h1]
  · by_cases h2 : pf.isInfinite
    · unfold toModelUnpacked; simp only [h1, h2, ↓reduceIte]
      simp [PackedFloat.unpack, UnpackedRel, h1, h2, EUnpackedFloat.mkInfinity,
        EUnpackedFloat.isInfinite, EUnpackedFloat.isNaN]
    · by_cases h3 : pf.isZero
      · unfold toModelUnpacked; simp only [h1, h2, h3, ↓reduceIte, ↓reduceDIte]
        have hu : pf.unpack = EUnpackedFloat.mkZero pf.sign := by
          simp only [PackedFloat.unpack, h1, h2, h3, cond_false, cond_true, Bool.false_eq_true]
        rw [hu]; exact ⟨rfl, rfl⟩
      · -- finite
        have hun : pf.unpack = EUnpackedFloat.mkNumber pf.unpackNum := by
          simp [PackedFloat.unpack, h1, h2, h3]
        have hproj := unpackNum_toRat_eq_toRat pf h1 h2 h3
        have hsign : (EUnpackedFloat.mkNumber pf.unpackNum).num.sign = pf.sign :=
          PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign pf
        by_cases h4 : pf.ex = 0#11
        · -- subnormal
          have hpos : 0 < pf.sig.toNat := by
            rcases Nat.eq_zero_or_pos pf.sig.toNat with hh | hh
            · exfalso; apply h3
              have : pf.sig = 0#52 := by apply BitVec.eq_of_toNat_eq; simp [hh]
              simp [PackedFloat.isZero, h4, this]
            · exact hh
          have htm : toModelUnpacked pf
              = UnpackedFloat.finite (signToModel pf.sign) pf.sig.toNat (-1074) hpos := by
            unfold toModelUnpacked
            simp only [h1, h2, h3, h4, Bool.false_eq_true, reduceCtorEq, if_false, dif_neg,
              not_false_eq_true, ↓reduceDIte, ↓reduceIte]
          rw [htm, hun]
          refine ⟨rfl, by rw [hsign], ?_⟩
          apply dyadic_of_sign hproj
          have hc := modelUnpackedToExtRat_toModelUnpacked pf
          rw [htm, PackedFloat.toExtRat_eq_toExtRat'] at hc
          simp only [modelUnpackedToExtRat, PackedFloat.toExtRat', h1, h2, h3, cond_false,
            Bool.false_eq_true, ExtRat.Number.injEq, sign_cond] at hc
          exact hc
        · -- normal
          have hpos : 0 < 2 ^ 52 + pf.sig.toNat := Nat.add_pos_left (Nat.two_pow_pos 52) _
          have htm : toModelUnpacked pf
              = UnpackedFloat.finite (signToModel pf.sign) (2 ^ 52 + pf.sig.toNat)
                  ((pf.ex.toNat : Int) - 1075) hpos := by
            unfold toModelUnpacked
            simp only [h1, h2, h3, h4, Bool.false_eq_true, reduceCtorEq, if_false, dif_neg,
              not_false_eq_true, ↓reduceDIte, ↓reduceIte]
          rw [htm, hun]
          refine ⟨rfl, by rw [hsign], ?_⟩
          apply dyadic_of_sign hproj
          have hc := modelUnpackedToExtRat_toModelUnpacked pf
          rw [htm, PackedFloat.toExtRat_eq_toExtRat'] at hc
          simp only [modelUnpackedToExtRat, PackedFloat.toExtRat', h1, h2, h3, cond_false,
            Bool.false_eq_true, ExtRat.Number.injEq, sign_cond] at hc
          exact hc

end FpAgainstFloatModel
