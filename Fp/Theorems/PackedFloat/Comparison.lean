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

All the comparison relations are proved sorry-free. The `eq` relation bottoms out
at `Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb`, the `lt`/`le` relations at
`bltAux_false_eq_decide_toRat_lt_of_finite` / `bleAux_true_eq_decide_toRat_le_of_finite`
(the ordering kernels introduced here); `gt`/`ge` are the swapped corollaries of
`lt`/`le`, and `ieeeBeq` agrees with `smtBeq` off-NaN. Everything else (the NaN
guard, the infinity boundary, the embedding into `ExtRat`) is discharged.
-/

set_option maxHeartbeats 1000000

open Fp.SmtLibSemantics

/-- For normalized (`sig.msb = true`) unpacked floats, the structural `beq`
agrees with rational equality. Reverse direction uses
`Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb`. -/
theorem UnpackedFloat.ieeeBeq_iff_toRat_eq {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    x.ieeeBeq y = true ↔ x.toRat = y.toRat := by
  have hxz : x.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hx; exact Bool.noConfusion hx
  have hyz : y.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hy; exact Bool.noConfusion hy
  constructor
  · intro h
    simp only [UnpackedFloat.ieeeBeq, hxz, hyz, Bool.and_false, Bool.false_or,
      UnpackedFloat.smtBeq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hsign, hex⟩, hsig⟩ := h
    cases x; cases y; simp_all
  · intro h
    have := Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb x y hx hy h
    subst this
    simp [UnpackedFloat.ieeeBeq]

/-- For normalized (`sig.msb = true`) unpacked floats, the structural strict
comparison `bltAux false` agrees with rational order. This is the ordering
analogue of `UnpackedFloat.ieeeBeq_iff_toRat_eq`: the sign decides the easy
mixed-sign cases, and within a fixed sign the binade/significand lexicographic
comparison matches the magnitude order via `Rat.mul_two_zpow_lt`. -/
theorem UnpackedFloat.bltAux_false_eq_decide_toRat_lt {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    UnpackedFloat.bltAux false x y = decide (x.toRat < y.toRat) := by
  -- normalized significands sit in the band `[2^(s-1), 2^s)`, hence are nonzero
  have hxlo : 2 ^ (s - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hx
  have hylo : 2 ^ (s - 1) ≤ y.sig.toNat := BitVec.le_toNat_of_msb_true hy
  have hxhi : x.sig.toNat < 2 ^ s := x.sig.isLt
  have hyhi : y.sig.toNat < 2 ^ s := y.sig.isLt
  have hppos := Nat.two_pow_pos (s - 1)
  have hxz : x.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hx; exact Bool.noConfusion hx
  have hyz : y.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hy; exact Bool.noConfusion hy
  -- value as `sign · magnitude`, with the magnitude `sig·2^(toExpInt)` positive
  have hvalx : x.toRat = (x.sign.toSign : Rat) *
      ((x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1))) := by
    rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat']
    simp only [UnpackedFloat.toNat_toSigNat_eq]; rw [Rat.mul_assoc]
  have hvaly : y.toRat = (y.sign.toSign : Rat) *
      ((y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1))) := by
    rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat']
    simp only [UnpackedFloat.toNat_toSigNat_eq]; rw [Rat.mul_assoc]
  have hMxpos : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1)) :=
    Rat.mul_positive (by exact_mod_cast (by omega : 0 < x.sig.toNat)) (Fp.Rat.two_pow_pos _)
  have hMypos : (0 : Rat) < (y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1)) :=
    Rat.mul_positive (by exact_mod_cast (by omega : 0 < y.sig.toNat)) (Fp.Rat.two_pow_pos _)
  -- magnitude order, both orientations, expressed structurally
  have hmagXY : ((x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1))
        < (y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1)))
      ↔ (x.ex.toInt < y.ex.toInt ∨ (x.ex.toInt = y.ex.toInt ∧ x.sig.toNat < y.sig.toNat)) := by
    rw [Rat.mul_two_zpow_lt hxlo hxhi hylo hyhi]
    simp only [UnpackedFloat.toExpInt]; omega
  have hmagYX : ((y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1))
        < (x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1)))
      ↔ (y.ex.toInt < x.ex.toInt ∨ (y.ex.toInt = x.ex.toInt ∧ y.sig.toNat < x.sig.toNat)) := by
    rw [Rat.mul_two_zpow_lt hylo hyhi hxlo hxhi]
    simp only [UnpackedFloat.toExpInt]; omega
  -- reduce to a `Prop` iff: `bltAux = true ↔ x.toRat < y.toRat`, then case on signs
  have key : UnpackedFloat.bltAux false x y = true ↔ x.toRat < y.toRat := by
    rw [hvalx, hvaly]
    unfold UnpackedFloat.bltAux
    cases hsx : x.sign <;> cases hsy : y.sign <;>
      simp only [hxz, hyz, toSign_true, toSign_false, Bool.and_self,
        Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.not_true,
        Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or, Bool.true_or, cond_true,
        cond_false, BitVec.slt_eq_decide, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, BitVec.ult_iff_toNat_lt, ← BitVec.toInt_inj, Rat.one_mul] <;>
      grind
  cases hb : UnpackedFloat.bltAux false x y
  · have hnp : ¬ (x.toRat < y.toRat) := by rw [← key]; simp [hb]
    simp [hnp]
  · have hp : x.toRat < y.toRat := key.mp hb
    simp [hp]

theorem UnpackedFloat.bleAux_true_eq_decide_toRat_le {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    UnpackedFloat.bleAux true x y = decide (x.toRat ≤ y.toRat) := by
  have hxlo : 2 ^ (s - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hx
  have hylo : 2 ^ (s - 1) ≤ y.sig.toNat := BitVec.le_toNat_of_msb_true hy
  have hxhi : x.sig.toNat < 2 ^ s := x.sig.isLt
  have hyhi : y.sig.toNat < 2 ^ s := y.sig.isLt
  have hppos := Nat.two_pow_pos (s - 1)
  have hxz : x.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hx; exact Bool.noConfusion hx
  have hyz : y.isZero = false := by
    simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h, BitVec.msb_zero] at hy; exact Bool.noConfusion hy
  have hvalx : x.toRat = (x.sign.toSign : Rat) *
      ((x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1))) := by
    rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat']
    simp only [UnpackedFloat.toNat_toSigNat_eq]; rw [Rat.mul_assoc]
  have hvaly : y.toRat = (y.sign.toSign : Rat) *
      ((y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1))) := by
    rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat']
    simp only [UnpackedFloat.toNat_toSigNat_eq]; rw [Rat.mul_assoc]
  have hMxpos : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1)) :=
    Rat.mul_positive (by exact_mod_cast (by omega : 0 < x.sig.toNat)) (Fp.Rat.two_pow_pos _)
  have hMypos : (0 : Rat) < (y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1)) :=
    Rat.mul_positive (by exact_mod_cast (by omega : 0 < y.sig.toNat)) (Fp.Rat.two_pow_pos _)
  -- magnitude ≤, both orientations, via ¬(strict swapped)
  have hmagXY : ((x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1))
        ≤ (y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1)))
      ↔ (x.ex.toInt < y.ex.toInt ∨ (x.ex.toInt = y.ex.toInt ∧ x.sig.toNat ≤ y.sig.toNat)) := by
    rw [← Rat.not_lt, Rat.mul_two_zpow_lt hylo hyhi hxlo hxhi]
    simp only [UnpackedFloat.toExpInt]; omega
  have hmagYX : ((y.sig.toNat : Rat) * (2 : Rat) ^ (y.toExpInt (s - 1))
        ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ (x.toExpInt (s - 1)))
      ↔ (y.ex.toInt < x.ex.toInt ∨ (y.ex.toInt = x.ex.toInt ∧ y.sig.toNat ≤ x.sig.toNat)) := by
    rw [← Rat.not_lt, Rat.mul_two_zpow_lt hxlo hxhi hylo hyhi]
    simp only [UnpackedFloat.toExpInt]; omega
  have key : UnpackedFloat.bleAux true x y = true ↔ x.toRat ≤ y.toRat := by
    rw [hvalx, hvaly]
    unfold UnpackedFloat.bleAux
    cases hsx : x.sign <;> cases hsy : y.sign <;>
      simp only [hxz, hyz, toSign_true, toSign_false, Bool.and_self,
        Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.not_true,
        Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or, Bool.true_or, cond_true,
        cond_false, BitVec.slt_eq_decide, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, BitVec.ule_iff_toNat_le, ← BitVec.toInt_inj, Rat.one_mul] <;>
      grind
  cases hb : UnpackedFloat.bleAux true x y
  · have hnp : ¬ (x.toRat ≤ y.toRat) := by rw [← key]; simp [hb]
    simp [hnp]
  · have hp : x.toRat ≤ y.toRat := key.mp hb
    simp [hp]

namespace PackedFloat

/-- **Ordering kernel.** For *finite* (non-NaN, non-infinite) packed floats, the
structural `bltAux false` comparison agrees with rational order. This is the
ordering analogue of `Fp.UnpackedFloat.eq_of_toRat_eq_toRat_of_msb` that powers
`smtBeq`: the both-nonzero case is the sign/binade/significand magnitude argument
(`UnpackedFloat.bltAux_false_eq_decide_toRat_lt`); the cases involving a zero use
that the unpacked zero has the minimal exponent (`BitVec.intMin`) and a zero
significand, so it compares below every nonzero magnitude of the same sign. -/
theorem bltAux_false_eq_decide_toRat_lt_of_finite {e s : Nat} (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hai : a.isInfinite = false) (hbi : b.isInfinite = false) :
    PackedFloat.bltAux false a b = decide (a.toRat < b.toRat) := by
  rw [PackedFloat.bltAux]
  by_cases haz : a.isZero <;> by_cases hbz : b.isZero
  · -- both zero: `0 < 0` is false, and zero is never `bltAux`-below zero
    have hua : a.unpack = EUnpackedFloat.mkZero a.sign := by simp [PackedFloat.unpack, ha, hai, haz]
    have hub : b.unpack = EUnpackedFloat.mkZero b.sign := by simp [PackedFloat.unpack, hb, hbi, hbz]
    have har : a.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero a haz
    have hbr : b.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero b hbz
    rw [hua, hub, EUnpackedFloat.bltAux]
    simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero, Bool.or_self,
      cond_false, EUnpackedFloat.num_mkZero, har, hbr]
    cases a.sign <;> cases b.sign <;>
      simp [UnpackedFloat.bltAux, UnpackedFloat.mkZero, UnpackedFloat.isZero,
        BitVec.slt_eq_decide, BitVec.ult_eq_decide]
  · -- a zero, b nonzero: reduces to the sign of `b`
    have hbn : b.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hua : a.unpack = EUnpackedFloat.mkZero a.sign := by simp [PackedFloat.unpack, ha, hai, haz]
    have hub : b.unpack = EUnpackedFloat.mkNumber b.unpackNum := PackedFloat.unpack_eq_unpackNum_of b hbn
    have hbms : b.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hbn
    have hrb : b.unpackNum.toRat = b.toRat := PackedFloat.unpackNum_toRat_eq_toRat hbn
    have har : a.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero a haz
    have hbrne : b.toRat ≠ 0 := PackedFloat.toRat_ne_zero hbn
    have hbpos : 0 < b.unpackNum.sig.toNat :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (BitVec.le_toNat_of_msb_true hbms)
    have hbnz : b.unpackNum.isZero = false := by
      simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at hbpos; simp at hbpos
    have hbmin := BitVec.toInt_intMin_le b.unpackNum.ex
    have hbmin' : BitVec.intMin (exponentWidth e s) = b.unpackNum.ex ∨
        (BitVec.intMin (exponentWidth e s)).toInt < b.unpackNum.ex.toInt := by
      rcases Int.lt_or_eq_of_le hbmin with h | h
      · exact Or.inr h
      · exact Or.inl (BitVec.toInt_inj.mp h)
    have hbsign : b.unpackNum.sign = decide (b.toRat < 0) := by
      have hne : b.unpackNum.toRat' ≠ 0 := by
        rw [← UnpackedFloat.toRat_eq_toRat', hrb]; exact hbrne
      rw [Fp.UnpackedFloat.sign_eq_decide_toRat'_lt_zero b.unpackNum hne,
        ← UnpackedFloat.toRat_eq_toRat', hrb]
    have hmz : ∀ {e' s' : Nat} (sgn : Bool),
        (UnpackedFloat.mkZero sgn : UnpackedFloat e' s').isZero = true := by
      intro e' s' sgn; simp [UnpackedFloat.isZero, UnpackedFloat.mkZero]
    rw [hua, hub, EUnpackedFloat.bltAux]
    simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNumber,
      EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
      Bool.false_or, Bool.or_false, cond_false, EUnpackedFloat.num_mkZero,
      EUnpackedFloat.num_mkNumber, har]
    unfold UnpackedFloat.bltAux
    simp only [UnpackedFloat.sign_mkZero, UnpackedFloat.ex_mkZero, UnpackedFloat.sig_mkZero,
      hmz, hbnz, BitVec.slt_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.zero_mod,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or, Bool.true_or,
      Bool.and_self, Bool.true_and, Bool.false_and, cond_true, cond_false]
    rw [hbsign]
    cases a.sign <;> rcases hbmin' with heq | hlt <;> grind
  · -- a nonzero, b zero: reduces to the sign of `a`
    have han : a.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hua : a.unpack = EUnpackedFloat.mkNumber a.unpackNum := PackedFloat.unpack_eq_unpackNum_of a han
    have hub : b.unpack = EUnpackedFloat.mkZero b.sign := by simp [PackedFloat.unpack, hb, hbi, hbz]
    have hams : a.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true han
    have hra : a.unpackNum.toRat = a.toRat := PackedFloat.unpackNum_toRat_eq_toRat han
    have hbr : b.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero b hbz
    have harne : a.toRat ≠ 0 := PackedFloat.toRat_ne_zero han
    have hapos : 0 < a.unpackNum.sig.toNat :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (BitVec.le_toNat_of_msb_true hams)
    have hanz : a.unpackNum.isZero = false := by
      simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at hapos; simp at hapos
    have hamin := BitVec.toInt_intMin_le a.unpackNum.ex
    have hamin' : BitVec.intMin (exponentWidth e s) = a.unpackNum.ex ∨
        (BitVec.intMin (exponentWidth e s)).toInt < a.unpackNum.ex.toInt := by
      rcases Int.lt_or_eq_of_le hamin with h | h
      · exact Or.inr h
      · exact Or.inl (BitVec.toInt_inj.mp h)
    have hasign : a.unpackNum.sign = decide (a.toRat < 0) := by
      have hne : a.unpackNum.toRat' ≠ 0 := by
        rw [← UnpackedFloat.toRat_eq_toRat', hra]; exact harne
      rw [Fp.UnpackedFloat.sign_eq_decide_toRat'_lt_zero a.unpackNum hne,
        ← UnpackedFloat.toRat_eq_toRat', hra]
    have hmz : ∀ {e' s' : Nat} (sgn : Bool),
        (UnpackedFloat.mkZero sgn : UnpackedFloat e' s').isZero = true := by
      intro e' s' sgn; simp [UnpackedFloat.isZero, UnpackedFloat.mkZero]
    rw [hua, hub, EUnpackedFloat.bltAux]
    simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNumber,
      EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
      Bool.false_or, Bool.or_false, cond_false, EUnpackedFloat.num_mkZero,
      EUnpackedFloat.num_mkNumber, hbr]
    unfold UnpackedFloat.bltAux
    simp only [UnpackedFloat.sign_mkZero, UnpackedFloat.ex_mkZero, UnpackedFloat.sig_mkZero,
      hmz, hanz, BitVec.slt_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.zero_mod,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or, Bool.true_or,
      Bool.and_self, Bool.true_and, Bool.false_and, cond_true, cond_false]
    rw [hasign]
    cases b.sign <;> rcases hamin' with heq | hlt <;> grind
  · -- both nonzero: the normalized magnitude kernel
    have han : a.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hbn : b.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hua : a.unpack = EUnpackedFloat.mkNumber a.unpackNum := PackedFloat.unpack_eq_unpackNum_of a han
    have hub : b.unpack = EUnpackedFloat.mkNumber b.unpackNum := PackedFloat.unpack_eq_unpackNum_of b hbn
    have hams : a.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true han
    have hbms : b.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hbn
    have hra : a.unpackNum.toRat = a.toRat := PackedFloat.unpackNum_toRat_eq_toRat han
    have hrb : b.unpackNum.toRat = b.toRat := PackedFloat.unpackNum_toRat_eq_toRat hbn
    rw [hua, hub, EUnpackedFloat.bltAux]
    simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
      cond_false, EUnpackedFloat.num_mkNumber]
    rw [UnpackedFloat.bltAux_false_eq_decide_toRat_lt a.unpackNum b.unpackNum hams hbms, hra, hrb]

set_option maxHeartbeats 1000000 in
theorem bleAux_true_eq_decide_toRat_le_of_finite {e s : Nat} (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hai : a.isInfinite = false) (hbi : b.isInfinite = false) :
    PackedFloat.bleAux true a b = decide (a.toRat ≤ b.toRat) := by
  rw [PackedFloat.bleAux]
  by_cases haz : a.isZero <;> by_cases hbz : b.isZero
  · -- both zero: `0 < 0` is false, and zero is never `bltAux`-below zero
    have hua : a.unpack = EUnpackedFloat.mkZero a.sign := by simp [PackedFloat.unpack, ha, hai, haz]
    have hub : b.unpack = EUnpackedFloat.mkZero b.sign := by simp [PackedFloat.unpack, hb, hbi, hbz]
    have har : a.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero a haz
    have hbr : b.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero b hbz
    rw [hua, hub, EUnpackedFloat.bleAux]
    simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero, Bool.or_self,
      cond_false, EUnpackedFloat.num_mkZero, har, hbr]
    cases a.sign <;> cases b.sign <;>
      simp [UnpackedFloat.bleAux, UnpackedFloat.mkZero, UnpackedFloat.isZero,
        BitVec.slt_eq_decide, BitVec.ule_eq_decide]
  · -- a zero, b nonzero: reduces to the sign of `b`
    have hbn : b.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hua : a.unpack = EUnpackedFloat.mkZero a.sign := by simp [PackedFloat.unpack, ha, hai, haz]
    have hub : b.unpack = EUnpackedFloat.mkNumber b.unpackNum := PackedFloat.unpack_eq_unpackNum_of b hbn
    have hbms : b.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hbn
    have hrb : b.unpackNum.toRat = b.toRat := PackedFloat.unpackNum_toRat_eq_toRat hbn
    have har : a.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero a haz
    have hbrne : b.toRat ≠ 0 := PackedFloat.toRat_ne_zero hbn
    have hbpos : 0 < b.unpackNum.sig.toNat :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (BitVec.le_toNat_of_msb_true hbms)
    have hbnz : b.unpackNum.isZero = false := by
      simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at hbpos; simp at hbpos
    have hbmin := BitVec.toInt_intMin_le b.unpackNum.ex
    have hbmin' : BitVec.intMin (exponentWidth e s) = b.unpackNum.ex ∨
        (BitVec.intMin (exponentWidth e s)).toInt < b.unpackNum.ex.toInt := by
      rcases Int.lt_or_eq_of_le hbmin with h | h
      · exact Or.inr h
      · exact Or.inl (BitVec.toInt_inj.mp h)
    have hbsign : b.unpackNum.sign = decide (b.toRat < 0) := by
      have hne : b.unpackNum.toRat' ≠ 0 := by
        rw [← UnpackedFloat.toRat_eq_toRat', hrb]; exact hbrne
      rw [Fp.UnpackedFloat.sign_eq_decide_toRat'_lt_zero b.unpackNum hne,
        ← UnpackedFloat.toRat_eq_toRat', hrb]
    have hmz : ∀ {e' s' : Nat} (sgn : Bool),
        (UnpackedFloat.mkZero sgn : UnpackedFloat e' s').isZero = true := by
      intro e' s' sgn; simp [UnpackedFloat.isZero, UnpackedFloat.mkZero]
    rw [hua, hub, EUnpackedFloat.bleAux]
    simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNumber,
      EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
      Bool.false_or, Bool.or_false, cond_false, EUnpackedFloat.num_mkZero,
      EUnpackedFloat.num_mkNumber, har]
    unfold UnpackedFloat.bleAux
    simp only [UnpackedFloat.sign_mkZero, UnpackedFloat.ex_mkZero, UnpackedFloat.sig_mkZero,
      hmz, hbnz, BitVec.slt_eq_decide, BitVec.ule_eq_decide, BitVec.toNat_ofNat, Nat.zero_mod,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or, Bool.true_or,
      Bool.and_self, Bool.true_and, Bool.false_and, cond_true, cond_false]
    rw [hbsign]
    cases a.sign <;> rcases hbmin' with heq | hlt <;> grind [Rat.not_lt]
  · -- a nonzero, b zero: reduces to the sign of `a`
    have han : a.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hua : a.unpack = EUnpackedFloat.mkNumber a.unpackNum := PackedFloat.unpack_eq_unpackNum_of a han
    have hub : b.unpack = EUnpackedFloat.mkZero b.sign := by simp [PackedFloat.unpack, hb, hbi, hbz]
    have hams : a.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true han
    have hra : a.unpackNum.toRat = a.toRat := PackedFloat.unpackNum_toRat_eq_toRat han
    have hbr : b.toRat = 0 := PackedFloat.toRat_eq_Zero_of_isZero b hbz
    have harne : a.toRat ≠ 0 := PackedFloat.toRat_ne_zero han
    have hapos : 0 < a.unpackNum.sig.toNat :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (BitVec.le_toNat_of_msb_true hams)
    have hanz : a.unpackNum.isZero = false := by
      simp only [UnpackedFloat.isZero, beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at hapos; simp at hapos
    have hamin := BitVec.toInt_intMin_le a.unpackNum.ex
    have hamin' : BitVec.intMin (exponentWidth e s) = a.unpackNum.ex ∨
        (BitVec.intMin (exponentWidth e s)).toInt < a.unpackNum.ex.toInt := by
      rcases Int.lt_or_eq_of_le hamin with h | h
      · exact Or.inr h
      · exact Or.inl (BitVec.toInt_inj.mp h)
    have hasign : a.unpackNum.sign = decide (a.toRat < 0) := by
      have hne : a.unpackNum.toRat' ≠ 0 := by
        rw [← UnpackedFloat.toRat_eq_toRat', hra]; exact harne
      rw [Fp.UnpackedFloat.sign_eq_decide_toRat'_lt_zero a.unpackNum hne,
        ← UnpackedFloat.toRat_eq_toRat', hra]
    have hmz : ∀ {e' s' : Nat} (sgn : Bool),
        (UnpackedFloat.mkZero sgn : UnpackedFloat e' s').isZero = true := by
      intro e' s' sgn; simp [UnpackedFloat.isZero, UnpackedFloat.mkZero]
    rw [hua, hub, EUnpackedFloat.bleAux]
    simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNumber,
      EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
      Bool.false_or, Bool.or_false, cond_false, EUnpackedFloat.num_mkZero,
      EUnpackedFloat.num_mkNumber, hbr]
    unfold UnpackedFloat.bleAux
    simp only [UnpackedFloat.sign_mkZero, UnpackedFloat.ex_mkZero, UnpackedFloat.sig_mkZero,
      hmz, hanz, BitVec.slt_eq_decide, BitVec.ule_eq_decide, BitVec.toNat_ofNat, Nat.zero_mod,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false, Bool.false_or, Bool.true_or,
      Bool.and_self, Bool.true_and, Bool.false_and, cond_true, cond_false]
    rw [hasign]
    cases b.sign <;> rcases hamin' with heq | hlt <;> grind [Rat.not_lt]
  · -- both nonzero: the normalized magnitude kernel
    have han : a.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hbn : b.isNormOrNonzeroSubnorm := by grind [PackedFloat.isNormOrNonzeroSubnorm]
    have hua : a.unpack = EUnpackedFloat.mkNumber a.unpackNum := PackedFloat.unpack_eq_unpackNum_of a han
    have hub : b.unpack = EUnpackedFloat.mkNumber b.unpackNum := PackedFloat.unpack_eq_unpackNum_of b hbn
    have hams : a.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true han
    have hbms : b.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hbn
    have hra : a.unpackNum.toRat = a.toRat := PackedFloat.unpackNum_toRat_eq_toRat han
    have hrb : b.unpackNum.toRat = b.toRat := PackedFloat.unpackNum_toRat_eq_toRat hbn
    rw [hua, hub, EUnpackedFloat.bleAux]
    simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
      cond_false, EUnpackedFloat.num_mkNumber]
    rw [UnpackedFloat.bleAux_true_eq_decide_toRat_le a.unpackNum b.unpackNum hams hbms, hra, hrb]

/--
**BTRW15 §V.B.2, `fp.eq` relation (IEEE equality).** For non-NaN `a, b`, IEEE
equality `ieeeBeq` holds iff the embedded values are equal (so +0 and -0 are
IEEE-equal): `a.ieeeBeq b ↔ v(a) = v(b)` with `v = ·.toExtRat`. (SMT-LIB core
`=`, `smtBeq`, is instead bit-exact and *distinguishes* signed zeros.)
-/
theorem ieeeBeq_iff_toExtRat_eq {e s : Nat} (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    a.ieeeBeq b = true ↔ a.toExtRat = b.toExtRat := by
  -- `v(a) = v(a')` via the closed form of `toExtRat'`.
  rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat']
  -- Reduce `ieeeBeq` to a comparison of the classification + `unpack`'s sign/num.
  simp only [PackedFloat.ieeeBeq, EUnpackedFloat.ieeeBeq, PackedFloat.isNaN_unpack_eq_isNaN,
    PackedFloat.isInfinite_unpack_eq_isInfinite, ha, hb, Bool.not_false, Bool.true_and,
    Bool.false_and, Bool.false_or, Bool.and_false]
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
      simp [hua, hub, har, hbr, EUnpackedFloat.mkZero, UnpackedFloat.ieeeBeq, UnpackedFloat.mkZero,
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
        UnpackedFloat.ieeeBeq, UnpackedFloat.smtBeq, UnpackedFloat.mkZero, UnpackedFloat.isZero]
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
        UnpackedFloat.ieeeBeq, UnpackedFloat.smtBeq, UnpackedFloat.mkZero, UnpackedFloat.isZero]
      grind
    · -- both nonzero finite: `a.toRat = b.toRat`, matched by `beq` via `ieeeBeq_iff_toRat_eq`
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
        UnpackedFloat.ieeeBeq_iff_toRat_eq a.unpackNum b.unpackNum hams hbms, hra, hrb]

-- `ieeeBeq_iff_toExtRat_eq` is `sorry`-free: it rests only on the standard axioms.
/--
info: 'PackedFloat.ieeeBeq_iff_toExtRat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ieeeBeq_iff_toExtRat_eq

/--
**BTRW15 §V.B.2, `lt` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBlt wbn a b ↔ v(a) < v(b)`.
-/
theorem smtBlt_iff_toExtRat_lt {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBlt wbn a b = true ↔ a.toExtRat < b.toExtRat := by
  rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat']
  -- `¬a.isNaN` collapses the `(NaN, NaN)` guard, leaving `bltAux false a b`.
  simp only [PackedFloat.smtBlt, ha, Bool.false_and, cond_false]
  by_cases hai : a.isInfinite <;> by_cases hbi : b.isInfinite
  · -- both infinite: `Infinity a.sign < Infinity b.sign ↔ -∞ < +∞`
    have hua : a.unpack = EUnpackedFloat.mkInfinity a.sign := by simp [PackedFloat.unpack, ha, hai]
    have hub : b.unpack = EUnpackedFloat.mkInfinity b.sign := by simp [PackedFloat.unpack, hb, hbi]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite a hai,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite b hbi, PackedFloat.bltAux,
        EUnpackedFloat.bltAux]
    simp only [hua, hub, hai, hbi, EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkInfinity,
      EUnpackedFloat.sign_mkInfinity, Bool.or_self, cond_false, Bool.true_or, cond_true]
    cases a.sign <;> cases b.sign <;> simp
  · -- a infinite, b finite: `Infinity a.sign < Number b.toRat ↔ a.sign` (only `-∞`)
    have hua : a.unpack = EUnpackedFloat.mkInfinity a.sign := by simp [PackedFloat.unpack, ha, hai]
    have hb' : b.toExtRat' = .Number b.toRat := by simp [PackedFloat.toExtRat', hb, hbi]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite a hai, hb', PackedFloat.bltAux,
        EUnpackedFloat.bltAux]
    simp only [hua, hai, hbi, PackedFloat.isNaN_unpack_eq_isNaN, hb,
      PackedFloat.isInfinite_unpack_eq_isInfinite, EUnpackedFloat.isNaN_mkInfinity,
      EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.sign_mkInfinity, Bool.or_false,
      Bool.false_or, Bool.or_self, cond_false, Bool.true_or, cond_true]
    cases a.sign <;> simp
  · -- a finite, b infinite: `Number a.toRat < Infinity b.sign ↔ ¬b.sign` (only `+∞`)
    have hub : b.unpack = EUnpackedFloat.mkInfinity b.sign := by simp [PackedFloat.unpack, hb, hbi]
    have ha' : a.toExtRat' = .Number a.toRat := by simp [PackedFloat.toExtRat', ha, hai]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite b hbi, ha', PackedFloat.bltAux,
        EUnpackedFloat.bltAux]
    simp only [hub, hai, hbi, PackedFloat.isNaN_unpack_eq_isNaN, ha,
      PackedFloat.isInfinite_unpack_eq_isInfinite, EUnpackedFloat.isNaN_mkInfinity,
      EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.sign_mkInfinity, Bool.or_false,
      Bool.false_or, Bool.or_self, cond_false]
    cases b.sign <;> simp
  · -- both finite: the ordering kernel
    have ha' : a.toExtRat' = .Number a.toRat := by simp [PackedFloat.toExtRat', ha, hai]
    have hb' : b.toExtRat' = .Number b.toRat := by simp [PackedFloat.toExtRat', hb, hbi]
    rw [PackedFloat.bltAux_false_eq_decide_toRat_lt_of_finite a b ha hb (by simp [hai]) (by simp [hbi]),
        ha', hb']
    simp [ExtRat.num_lt_num_iff]

-- `smtBlt_iff_toExtRat_lt` is `sorry`-free: like `ieeeBeq_iff_toExtRat_eq` it rests
-- only on the standard axioms.
/--
info: 'PackedFloat.smtBlt_iff_toExtRat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtBlt_iff_toExtRat_lt

/--
**BTRW15 §V.B.2, `leq` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBle wbn a b ↔ v(a) ≤ v(b)`.
-/
theorem smtBle_iff_toExtRat_le {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBle wbn a b = true ↔ a.toExtRat ≤ b.toExtRat := by
  rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat']
  -- `¬a.isNaN` collapses the `(NaN, NaN)` guard, leaving `bltAux false a b`.
  simp only [PackedFloat.smtBle, ha, Bool.false_and, cond_false]
  by_cases hai : a.isInfinite <;> by_cases hbi : b.isInfinite
  · -- both infinite: `Infinity a.sign < Infinity b.sign ↔ -∞ < +∞`
    have hua : a.unpack = EUnpackedFloat.mkInfinity a.sign := by simp [PackedFloat.unpack, ha, hai]
    have hub : b.unpack = EUnpackedFloat.mkInfinity b.sign := by simp [PackedFloat.unpack, hb, hbi]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite a hai,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite b hbi, PackedFloat.bleAux,
        EUnpackedFloat.bleAux]
    simp only [hua, hub, hai, hbi, EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkInfinity,
      EUnpackedFloat.sign_mkInfinity, Bool.or_self, cond_false, Bool.true_or, cond_true]
    cases a.sign <;> cases b.sign <;> simp
  · -- a infinite, b finite: `Infinity a.sign < Number b.toRat ↔ a.sign` (only `-∞`)
    have hua : a.unpack = EUnpackedFloat.mkInfinity a.sign := by simp [PackedFloat.unpack, ha, hai]
    have hb' : b.toExtRat' = .Number b.toRat := by simp [PackedFloat.toExtRat', hb, hbi]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite a hai, hb', PackedFloat.bleAux,
        EUnpackedFloat.bleAux]
    simp only [hua, hai, hbi, PackedFloat.isNaN_unpack_eq_isNaN, hb,
      PackedFloat.isInfinite_unpack_eq_isInfinite, EUnpackedFloat.isNaN_mkInfinity,
      EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.sign_mkInfinity, Bool.or_false,
      Bool.false_or, Bool.or_self, cond_false, Bool.true_or, cond_true]
    cases a.sign <;> simp
  · -- a finite, b infinite: `Number a.toRat < Infinity b.sign ↔ ¬b.sign` (only `+∞`)
    have hub : b.unpack = EUnpackedFloat.mkInfinity b.sign := by simp [PackedFloat.unpack, hb, hbi]
    have ha' : a.toExtRat' = .Number a.toRat := by simp [PackedFloat.toExtRat', ha, hai]
    rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite b hbi, ha', PackedFloat.bleAux,
        EUnpackedFloat.bleAux]
    simp only [hub, hai, hbi, PackedFloat.isNaN_unpack_eq_isNaN, ha,
      PackedFloat.isInfinite_unpack_eq_isInfinite, EUnpackedFloat.isNaN_mkInfinity,
      EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.sign_mkInfinity, Bool.or_false,
      Bool.false_or, Bool.or_self, cond_false]
    cases b.sign <;> simp
  · -- both finite: the ordering kernel
    have ha' : a.toExtRat' = .Number a.toRat := by simp [PackedFloat.toExtRat', ha, hai]
    have hb' : b.toExtRat' = .Number b.toRat := by simp [PackedFloat.toExtRat', hb, hbi]
    rw [PackedFloat.bleAux_true_eq_decide_toRat_le_of_finite a b ha hb (by simp [hai]) (by simp [hbi]),
        ha', hb']
    simp

/--
**BTRW15 §V.B.2, `gt` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBgt wbn a b ↔ v(a) > v(b)`, i.e. `v(b) < v(a)`.
-/
theorem smtBgt_iff_toExtRat_gt {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBgt wbn a b = true ↔ b.toExtRat < a.toExtRat := by
  have h : PackedFloat.smtBgt wbn a b = PackedFloat.smtBlt wbn b a := by
    simp only [PackedFloat.smtBgt, PackedFloat.smtBlt, PackedFloat.bgtAux, ha, hb,
      Bool.and_false, Bool.false_and, cond_false, Bool.not_true]
  rw [h]; exact PackedFloat.smtBlt_iff_toExtRat_lt wbn b a hb ha

/--
**BTRW15 §V.B.2, `geq` relation.** For non-NaN `a, b` and any `whenBothNaN`
choice: `smtBge wbn a b ↔ v(a) ≥ v(b)`, i.e. `v(b) ≤ v(a)`.
-/
theorem smtBge_iff_toExtRat_ge {e s : Nat} (wbn : Bool) (a b : PackedFloat e s)
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    PackedFloat.smtBge wbn a b = true ↔ b.toExtRat ≤ a.toExtRat := by
  have h : PackedFloat.smtBge wbn a b = PackedFloat.smtBle wbn b a := by
    simp only [PackedFloat.smtBge, PackedFloat.smtBle, PackedFloat.bgeAux, ha, hb,
      Bool.and_false, Bool.false_and, cond_false, Bool.not_false]
  rw [h]; exact smtBle_iff_toExtRat_le wbn b a hb ha


-- The four comparison relations are `sorry`-free: they rest only on the standard
-- axioms.
/--
info: 'PackedFloat.smtBle_iff_toExtRat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtBle_iff_toExtRat_le

/--
info: 'PackedFloat.smtBgt_iff_toExtRat_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtBgt_iff_toExtRat_gt

/--
info: 'PackedFloat.smtBge_iff_toExtRat_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtBge_iff_toExtRat_ge

/--
info: 'PackedFloat.ieeeBeq_iff_toExtRat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ieeeBeq_iff_toExtRat_eq

end PackedFloat
