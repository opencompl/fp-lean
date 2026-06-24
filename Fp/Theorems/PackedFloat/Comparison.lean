import Fp.Comparison
import Fp.SmtLibSemantics
import Fp.Theorems.PackedFloat.Ordering
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.Addition

/-!
# Comparison operators agree with the SMT-LIB binary relations

This file relates the computable comparison operators of `Fp/Comparison.lean`
(`smtBeq`, `smtBlt`, `smtBle`, `smtBge`, `smtBgt`, `ieeeBeq`) to the abstract
binary relations of BTRW15 **§V.B.2 ("Binary Relations")**, which on the set of
*non-NaN* floats `F_{ε,σ}` are defined purely through the embedding
`v = · .toExtRat`:

```
eq_{ε,σ}  = {(f,g) | v(f) = v(g)}
leq_{ε,σ} = {(f,g) | v(f) ≤ v(g)}
lt_{ε,σ}  = {(f,g) | v(f) < v(g)}
geq_{ε,σ} = {(f,g) | v(f) ≥ v(g)}
gt_{ε,σ}  = {(f,g) | v(f) > v(g)}
```

These relations live on `F_{ε,σ}` (floats *without* NaN): NaN is unordered, so
every statement below is guarded by `¬ a.isNaN ∧ ¬ b.isNaN`. On that domain the
`whenBothNaN` choice carried by the `smt*` order operators is irrelevant.

`smtBeq` (the `eq` relation) is proved and is `sorry`-free (it rests on
`UnpackedFloat.eq_of_toRat_eq_toRat_of_msb`, now discharged via the proven
binade-uniqueness lemma `Fp.Rat.mul_two_zpow_inj`). The order relations
(`smtBle`, `smtBgt`,
`smtBge`, `ieeeBeq`) are stated and left as `sorry` pending the ordering
analogue, the unpacked-level structural-vs-rational comparison
`UnpackedFloat.bltAux false a b = decide (a.toRat < b.toRat)` for normalized
`a, b`.
-/

set_option maxHeartbeats 1000000

open Fp.SmtLibSemantics

/-- For normalized (`sig.msb = true`) unpacked floats, the structural `beq`
agrees with rational equality. Reverse direction uses
`Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb`. -/
theorem UnpackedFloat.beq_iff_toRat_eq {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    x.beq y = true ↔ x.toRat = y.toRat := by
  have hxz : x.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hx; exact Bool.noConfusion hx
  have hyz : y.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hy; exact Bool.noConfusion hy
  constructor
  · intro h
    simp only [UnpackedFloat.beq, hxz, hyz, Bool.and_false, Bool.false_or,
      UnpackedFloat.structBeq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hsign, hex⟩, hsig⟩ := h
    cases x; cases y; simp_all
  · intro h
    have := Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb x y hx hy h
    subst this
    simp [UnpackedFloat.beq]

namespace PackedFloat

/--
**BTRW15 §V.B.2, `eq` relation.** For non-NaN `a, b`, the structural SMT
equality `smtBeq` holds iff the embedded values are equal:
`a.smtBeq b ↔ v(a) = v(b)` with `v = ·.toExtRat`.
-/
theorem smtBeq_iff_toExtRat_eq {e s : Nat} (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    a.smtBeq b = true ↔ a.toExtRat = b.toExtRat := by
  -- `v(a) = v(a')` via the closed form of `toExtRat'`.
  rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat']
  -- Reduce `smtBeq` to a comparison of the classification + `unpack`'s sign/num.
  simp only [PackedFloat.smtBeq, EUnpackedFloat.smtBeq, PackedFloat.isNaN_unpack_eq_isNaN,
    PackedFloat.isInfinite_unpack_eq_isInfinite, ha, hb, Bool.false_and, Bool.false_or,
    Bool.and_false]
  by_cases hai : a.isInfinite <;> by_cases hbi : b.isInfinite
  · -- both infinite: `Infinity a.sign = Infinity b.sign ↔ a.sign = b.sign`
    have hua : a.unpack = EUnpackedFloat.mkInfinity a.sign := by simp [PackedFloat.unpack, ha, hai]
    have hub : b.unpack = EUnpackedFloat.mkInfinity b.sign := by simp [PackedFloat.unpack, hb, hbi]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite a hai,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite b hbi]
    simp [hua, hub, hai, hbi, EUnpackedFloat.sign_mkInfinity, ExtRat.Infinity.injEq]
  · -- a infinite, b finite: both sides false (`Infinity ≠ Number`)
    have hb' : b.toExtRat' = .Number b.toRat := by simp [PackedFloat.toExtRat', hb, hbi]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite a hai, hb']
    simp [hai, hbi]
  · -- a finite, b infinite: both sides false (`Number ≠ Infinity`)
    have ha' : a.toExtRat' = .Number a.toRat := by simp [PackedFloat.toExtRat', ha, hai]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite b hbi, ha']
    simp [hai, hbi]
  · -- both finite: reduce to `beq` of the unpacked numbers vs `Number toRat` equality
    have ha' : a.toExtRat' = .Number a.toRat := by simp [PackedFloat.toExtRat', ha, hai]
    have hb' : b.toExtRat' = .Number b.toRat := by simp [PackedFloat.toExtRat', hb, hbi]
    rw [ha', hb']
    simp only [hai, hbi, Bool.false_and, Bool.and_false, Bool.false_or, Bool.not_false,
      Bool.true_and, ExtRat.Number.injEq]
    by_cases haz : a.isZero <;> by_cases hbz : b.isZero
    · -- both zero: `a.toRat = b.toRat` (both 0), `beq` true
      have hua : a.unpack = EUnpackedFloat.mkZero a.sign := by simp [PackedFloat.unpack, ha, hai, haz]
      have hub : b.unpack = EUnpackedFloat.mkZero b.sign := by simp [PackedFloat.unpack, hb, hbi, hbz]
      have har : a.toRat = 0 := by
        have h := PackedFloat.toExtRat'_eq_zero_of_isZero a haz; rw [ha'] at h; simpa using h
      have hbr : b.toRat = 0 := by
        have h := PackedFloat.toExtRat'_eq_zero_of_isZero b hbz; rw [hb'] at h; simpa using h
      simp [hua, hub, har, hbr, EUnpackedFloat.mkZero, UnpackedFloat.beq, UnpackedFloat.mkZero,
        UnpackedFloat.isZero]
    · -- a zero, b nonzero finite: `0 ≠ b.toRat`, `beq` false
      have hbn : b.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
      have hua : a.unpack = EUnpackedFloat.mkZero a.sign := by simp [PackedFloat.unpack, ha, hai, haz]
      have hub : b.unpack = EUnpackedFloat.mkNumber b.unpackNum := PackedFloat.unpack_eq_unpackNum_of b hbn
      have har : a.toRat = 0 := by
        have h := PackedFloat.toExtRat'_eq_zero_of_isZero a haz; rw [ha'] at h; simpa using h
      have hbr : b.toRat ≠ 0 := PackedFloat.toRat_ne_zero hbn
      have hbsig : b.unpackNum.sig ≠ 0#(s + 1) := by
        intro h; have := PackedFloat.msb_unpackNum_eq_true hbn; rw [h] at this; simp at this
      simp only [hua, hub, EUnpackedFloat.num_mkZero, EUnpackedFloat.num_mkNumber,
        UnpackedFloat.beq, UnpackedFloat.structBeq, UnpackedFloat.mkZero, UnpackedFloat.isZero]
      grind
    · -- a nonzero finite, b zero: symmetric
      have han : a.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
      have hua : a.unpack = EUnpackedFloat.mkNumber a.unpackNum := PackedFloat.unpack_eq_unpackNum_of a han
      have hub : b.unpack = EUnpackedFloat.mkZero b.sign := by simp [PackedFloat.unpack, hb, hbi, hbz]
      have har : a.toRat ≠ 0 := PackedFloat.toRat_ne_zero han
      have hbr : b.toRat = 0 := by
        have h := PackedFloat.toExtRat'_eq_zero_of_isZero b hbz; rw [hb'] at h; simpa using h
      have hasig : a.unpackNum.sig ≠ 0#(s + 1) := by
        intro h; have := PackedFloat.msb_unpackNum_eq_true han; rw [h] at this; simp at this
      simp only [hua, hub, EUnpackedFloat.num_mkZero, EUnpackedFloat.num_mkNumber,
        UnpackedFloat.beq, UnpackedFloat.structBeq, UnpackedFloat.mkZero, UnpackedFloat.isZero]
      grind
    · -- both nonzero finite: `a.toRat = b.toRat`, matched by `beq` via `beq_iff_toRat_eq`
      have han : a.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
      have hbn : b.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
      have hua : a.unpack = EUnpackedFloat.mkNumber a.unpackNum := PackedFloat.unpack_eq_unpackNum_of a han
      have hub : b.unpack = EUnpackedFloat.mkNumber b.unpackNum := PackedFloat.unpack_eq_unpackNum_of b hbn
      have hams : a.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true han
      have hbms : b.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hbn
      have hra : a.unpackNum.toRat = a.toRat := PackedFloat.unpackNum_toRat_eq_toRat han
      have hrb : b.unpackNum.toRat = b.toRat := PackedFloat.unpackNum_toRat_eq_toRat hbn
      rw [hua, hub]
      simp only [EUnpackedFloat.num_mkNumber,
        UnpackedFloat.beq_iff_toRat_eq a.unpackNum b.unpackNum hams hbms, hra, hrb]

-- `smtBeq_iff_toExtRat_eq` is `sorry`-free: it rests only on the standard axioms
-- plus the project's `BitVec.toNat_clz_cons`.
/--
info: 'PackedFloat.smtBeq_iff_toExtRat_eq' depends on axioms: [propext, BitVec.toNat_clz_cons, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtBeq_iff_toExtRat_eq

/--
**BTRW15 §V.B.2, `eq` relation (IEEE equality).** For non-NaN `a, b`, IEEE
equality coincides with `eq` (the two differ only at NaN):
`a.ieeeBeq b ↔ v(a) = v(b)`.
-/
theorem ieeeBeq_iff_toExtRat_eq {e s : Nat} (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    a.ieeeBeq b = true ↔ a.toExtRat = b.toExtRat := by
  sorry

/--
**BTRW15 §V.B.2, `lt` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBlt wbn a b ↔ v(a) < v(b)`.
-/
theorem smtBlt_iff_toExtRat_lt {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBlt wbn a b = true ↔ a.toExtRat < b.toExtRat := by
  sorry

/--
**BTRW15 §V.B.2, `leq` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBle wbn a b ↔ v(a) ≤ v(b)`.
-/
theorem smtBle_iff_toExtRat_le {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBle wbn a b = true ↔ a.toExtRat ≤ b.toExtRat := by
  sorry

/--
**BTRW15 §V.B.2, `gt` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBgt wbn a b ↔ v(a) > v(b)`, i.e. `v(b) < v(a)`.
-/
theorem smtBgt_iff_toExtRat_gt {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBgt wbn a b = true ↔ b.toExtRat < a.toExtRat := by
  sorry

/--
**BTRW15 §V.B.2, `geq` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBge wbn a b ↔ v(a) ≥ v(b)`, i.e. `v(b) ≤ v(a)`.
-/
theorem smtBge_iff_toExtRat_ge {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBge wbn a b = true ↔ b.toExtRat ≤ a.toExtRat := by
  sorry

end PackedFloat
