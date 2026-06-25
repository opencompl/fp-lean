import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.PackedFloat.Negation
import Fp.Theorems.PackedFloat.Ordering
import Fp.Theorems.LowerUpperRound
import Fp.Theorems.PackedUnpackedRel

namespace Fp


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

/-! # extractIsEven -/

theorem and_oneHotBV_eq_zero_iff (x i : BitVec w)  :
    x &&& (BitVec.oneHotBV i) = 0#w ↔ x.getLsbD i.toNat = false := by
  constructor
  · intros h
    rw [BitVec.eq_iff_getLsbD_eq] at h
    simp at h
    specialize h i.toNat
    grind only [= BitVec.getLsbD_of_ge]
  · intros h
    ext k hk
    simp
    intros hk
    have := i.getElem_oneHotBV ⟨k, by omega⟩
    grind only [= BitVec.getLsbD_eq_getElem, = Fin.getElem_fin]

@[simp]
theorem BitVec.and_allOnes_eq_self (bv : BitVec n) :
    bv &&& (BitVec.allOnes n) = bv := by
  ext UnpackedFloat.blastExtractGuardBit
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

/--
Reducing a bitvector modulo `2^v` can be computed from either `toNat` or `toInt`,
provided `v` is no larger than the original width.
-/
theorem BitVec.toNat_mod_two_pow_of_toInt_of_le {w v : Nat} (x : BitVec w) (hle : v ≤ w) :
    (x.toInt % (2 ^ v : Nat)).toNat = x.toNat % 2 ^ v := by
  simp [BitVec.toInt]
  split
  · rw [Int.toNat_emod]
    · rw [show (2 ^ v : Int).toNat = 2 ^ v by exact Int.toNat_natCast _]
      rw [show ((x.toNat : Int).toNat) = x.toNat by exact Int.toNat_natCast _]
    · exact Int.natCast_nonneg _
    · exact Int.natCast_nonneg _
  · have hpowdvd : (2 ^ v : Int) ∣ (2 ^ w : Int) := by
      norm_cast
      exact Nat.pow_dvd_pow 2 hle
    have hmod :
        ((x.toNat : Int) - (2 ^ w : Int)) % (2 ^ v : Int) =
          (x.toNat : Int) % (2 ^ v : Int) := by
      rw [Int.sub_emod]
      have hzero : ((2 ^ w : Int) % (2 ^ v : Int)) = 0 := by
        exact Int.emod_eq_zero_of_dvd hpowdvd
      rw [hzero]
      simp
    change (((x.toNat : Int) - (2 ^ w : Int)) % (2 ^ v : Int)).toNat =
      x.toNat % 2 ^ v
    rw [hmod]
    rw [Int.toNat_emod]
    · rw [show (2 ^ v : Int).toNat = 2 ^ v by exact Int.toNat_natCast _]
      rw [show ((x.toNat : Int).toNat) = x.toNat by exact Int.toNat_natCast _]
    · exact Int.natCast_nonneg _
    · exact Int.natCast_nonneg _

/--
Truncating to a smaller width preserves `toInt` when the signed value already
fits in the target signed range.
-/
theorem BitVec.toInt_truncate_eq_of_toInt_range {w v : Nat} (x : BitVec w)
    (hv : 0 < v) (hle : v ≤ w)
    (hlo : -2 ^ (v - 1) ≤ x.toInt)
    (hhi : x.toInt < 2 ^ (v - 1)) :
    (x.truncate v).toInt = x.toInt := by
  rw [BitVec.truncate_eq_setWidth]
  have hset : x.setWidth v = BitVec.ofInt v x.toInt := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    exact (BitVec.toNat_mod_two_pow_of_toInt_of_le x hle).symm
  rw [hset]
  exact BitVec.toInt_ofInt_eq_self hv hlo hhi

/-- A smaller power `2 ^ m` divides any number rounded down to a multiple of a larger
power `2 ^ L` (i.e. `n / 2 ^ L * 2 ^ L`). -/
theorem Nat.two_pow_dvd_div_mul_two_pow (n : Nat) {m L : Nat} (h : m ≤ L) :
    2 ^ m ∣ n / 2 ^ L * 2 ^ L :=
  Nat.dvd_trans (Nat.pow_dvd_pow 2 h) ⟨n / 2 ^ L, Nat.mul_comm _ _⟩

/-- Re-reading a value rounded to a multiple of `2 ^ (a+b)` through a division by the
smaller `2 ^ b`: the result is the high part times `2 ^ a`. -/
theorem Nat.div_mul_two_pow_add_div_two_pow (n a b : Nat) :
    n / 2 ^ (a + b) * 2 ^ (a + b) / 2 ^ b = n / 2 ^ (a + b) * 2 ^ a := by
  rw [Nat.mul_div_assoc _ (Nat.pow_dvd_pow 2 (Nat.le_add_left b a)),
    Nat.pow_div (Nat.le_add_left b a) (by grind), Nat.add_sub_cancel]

end Fp
