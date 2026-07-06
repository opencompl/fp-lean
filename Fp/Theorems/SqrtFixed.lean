import Fp.Sqrt

/-!
# Correctness of the fixed-point integer square root

`fixedPointSqrt_iter` builds the result bit-by-bit from the MSB down, keeping the greedy
invariant that `working² ≤ xcomp < (working + 2^i)²` with `working` a multiple of `2^i`.
At `i = 0` this collapses to the bracket `working² ≤ xcomp < (working + 1)²`, i.e. `working`
is `⌊√xcomp⌋`, with a sticky bit recording whether the root is exact.

This file is the analogue of `DivisionFixed.lean` for square root: it is width-generic
(`n` is a variable) so it is proved by genuine induction, not `bv_decide`.
-/

namespace Fp

/-- Disjoint bitwise-or is addition: if `W` is a multiple of `2^(k+1)` then bit `k` of `W`
is clear, so OR-ing in `2^k` is the same as adding it. -/
theorem lor_two_pow_of_dvd {W k : Nat} (h : 2 ^ (k + 1) ∣ W) :
    W ||| 2 ^ k = W + 2 ^ k := by
  obtain ⟨m, rfl⟩ := h
  exact (Nat.two_pow_add_eq_or_of_lt (Nat.pow_lt_pow_succ (by omega)) m).symm

/-- `(2^n)^2 = 2^(2n)`. -/
theorem two_pow_sq {n : Nat} : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
  rw [← Nat.pow_mul]; congr 1; omega

theorem two_pow_lt {a b : Nat} (h : a < b) : (2 : Nat) ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by omega) h

/-- `1#n <<< loc` denotes `2 ^ loc` when `loc < n`. -/
theorem toNat_one_shiftLeft {n loc : Nat} (h : loc < n) :
    ((1 : BitVec n) <<< loc).toNat = 2 ^ loc := by
  have h1 : (1 : BitVec n).toNat = 1 := BitVec.toNat_one (by omega)
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h1, Nat.one_mul,
    Nat.mod_eq_of_lt (two_pow_lt h)]

/-- The greedy invariant of `fixedPointSqrt_iter`. -/
theorem fixedPointSqrt_iter_bracket {n : Nat} (xcomp : BitVec (2 * n)) :
    ∀ (i : Nat) (working : BitVec n), i ≤ n →
      2 ^ i ∣ working.toNat →
      working.toNat ^ 2 ≤ xcomp.toNat →
      xcomp.toNat < (working.toNat + 2 ^ i) ^ 2 →
      ∃ w : BitVec n,
        fixedPointSqrt_iter i xcomp working
          = w ++ BitVec.ofBool (decide (w.toNat ^ 2 ≠ xcomp.toNat)) ∧
        w.toNat ^ 2 ≤ xcomp.toNat ∧ xcomp.toNat < (w.toNat + 1) ^ 2 := by
  have hxlt : xcomp.toNat < 2 ^ (2 * n) := xcomp.isLt
  intro i
  induction i with
  | zero =>
    intro working _ _ hle hgt
    refine ⟨working, ?_, hle, by simpa using hgt⟩
    simp only [fixedPointSqrt_iter]
    have hwlt : working.toNat < 2 ^ (2 * n) :=
      Nat.lt_of_lt_of_le working.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    have hsq : (working.setWidth (2 * n) * working.setWidth (2 * n)).toNat = working.toNat ^ 2 := by
      simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hwlt]
      rw [← Nat.pow_two, Nat.mod_eq_of_lt (by rw [Nat.pow_two] at hle ⊢; omega)]
    have hiff : (working.setWidth (2 * n) * working.setWidth (2 * n) ≠ xcomp)
        ↔ (working.toNat ^ 2 ≠ xcomp.toNat) := by
      rw [ne_eq, ne_eq, BitVec.toNat_eq, hsq]
    simp only [hiff]
  | succ loc ih =>
    intro working hi hdvd hle hgt
    simp only [fixedPointSqrt_iter]
    have hloc : loc < n := by omega
    have hcand : (working ||| (1 : BitVec n) <<< loc).toNat = working.toNat + 2 ^ loc := by
      rw [BitVec.toNat_or, toNat_one_shiftLeft hloc]
      exact lor_two_pow_of_dvd hdvd
    have hclt : working.toNat + 2 ^ loc < 2 ^ n := by
      have hdn : 2 ^ (loc + 1) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
      have hsubdvd : 2 ^ (loc + 1) ∣ (2 ^ n - working.toNat) := by
        obtain ⟨q, hq⟩ := hdvd; obtain ⟨r, hr⟩ := hdn
        exact ⟨r - q, by rw [hr, hq, Nat.mul_sub]⟩
      have hpos : 0 < 2 ^ n - working.toNat := by have := working.isLt; omega
      have hge : 2 ^ (loc + 1) ≤ 2 ^ n - working.toNat := Nat.le_of_dvd hpos hsubdvd
      have hpow : 2 ^ (loc + 1) = 2 * 2 ^ loc := by rw [Nat.pow_succ]; omega
      omega
    have hcltbound : working.toNat + 2 ^ loc < 2 ^ (2 * n) :=
      Nat.lt_of_lt_of_le hclt (Nat.pow_le_pow_right (by omega) (by omega))
    have hsqbound : (working.toNat + 2 ^ loc) ^ 2 < 2 ^ (2 * n) := by
      calc (working.toNat + 2 ^ loc) ^ 2 < (2 ^ n) ^ 2 := Nat.pow_lt_pow_left hclt (by omega)
        _ = 2 ^ (2 * n) := two_pow_sq
    have hcsq : ((working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)
        * (working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)).toNat
        = (working.toNat + 2 ^ loc) ^ 2 := by
      simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, hcand, Nat.mod_eq_of_lt hcltbound]
      rw [← Nat.pow_two, Nat.mod_eq_of_lt hsqbound]
    have hdvd_loc : 2 ^ loc ∣ working.toNat :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
    by_cases hb : ((working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)
        * (working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)) ≤ xcomp
    · -- keep the bit
      have hbnat : (working.toNat + 2 ^ loc) ^ 2 ≤ xcomp.toNat := by
        rw [← hcsq]; exact BitVec.le_def.mp hb
      have hnew : (working ||| (BitVec.ofBool
          (((working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)
            * (working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)) ≤ xcomp)).setWidth n <<< loc).toNat
          = working.toNat + 2 ^ loc := by
        simp only [hb, decide_true]
        simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
          BitVec.toNat_ofBool, Bool.toNat_true, Nat.shiftLeft_eq]
        rw [Nat.one_mod_two_pow (by omega), Nat.one_mul, Nat.mod_eq_of_lt (two_pow_lt hloc)]
        exact lor_two_pow_of_dvd hdvd
      obtain ⟨w, hw1, hw2, hw3⟩ := ih _ (by omega)
        (by rw [hnew]; exact Nat.dvd_add hdvd_loc (Nat.dvd_refl _))
        (by rw [hnew]; exact hbnat)
        (by rw [hnew]
            have hp : working.toNat + 2 ^ loc + 2 ^ loc = working.toNat + 2 ^ (loc + 1) := by
              rw [Nat.pow_succ]; omega
            rw [hp]; exact hgt)
      exact ⟨w, hw1, hw2, hw3⟩
    · -- drop the bit
      have hnew : (working ||| (BitVec.ofBool
          (((working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)
            * (working ||| (1 : BitVec n) <<< loc).setWidth (2 * n)) ≤ xcomp)).setWidth n <<< loc).toNat
          = working.toNat := by
        simp only [hb, decide_false]
        simp [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
          BitVec.toNat_ofBool]
      have hbnat' : xcomp.toNat < (working.toNat + 2 ^ loc) ^ 2 := by
        rw [← hcsq]; exact BitVec.lt_def.mp (BitVec.not_le.mp hb)
      obtain ⟨w, hw1, hw2, hw3⟩ := ih _ (by omega)
        (by rw [hnew]; exact hdvd_loc)
        (by rw [hnew]; exact hle)
        (by rw [hnew]; exact hbnat')
      exact ⟨w, hw1, hw2, hw3⟩

/-- `xcomp = x` right-padded by `n-1` zeros, as a `Nat`: `x.toNat * 2^(n-1)`. -/
theorem toNat_xcomp {n : Nat} (hn : 0 < n) (x : BitVec (n + 1)) :
    (x.setWidth (2 * n) <<< (n - 1)).toNat = x.toNat * 2 ^ (n - 1) := by
  have hx2n : x.toNat < 2 ^ (2 * n) :=
    Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  have hprod : x.toNat * 2 ^ (n - 1) < 2 ^ (2 * n) := by
    calc x.toNat * 2 ^ (n - 1) < 2 ^ (n + 1) * 2 ^ (n - 1) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr x.isLt
      _ = 2 ^ (2 * n) := by rw [← Nat.pow_add]; congr 1; omega
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx2n, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hprod]

/-- Top-level bracket for `fixedPointSqrt`: given a leading bit (`2^(n-1) ≤ x.toNat`, ensuring
the result's MSB is `1`), the significand part `w` of `fixedPointSqrt x` satisfies
`w² ≤ x·2^(n-1) < (w+1)²` and the sticky bit records exactness. -/
theorem fixedPointSqrt_bracket {n : Nat} (hn : 0 < n) (x : BitVec (n + 1))
    (hx : 2 ^ (n - 1) ≤ x.toNat) :
    ∃ w : BitVec n,
      fixedPointSqrt x
        = w ++ BitVec.ofBool (decide (w.toNat ^ 2 ≠ x.toNat * 2 ^ (n - 1))) ∧
      w.toNat ^ 2 ≤ x.toNat * 2 ^ (n - 1) ∧ x.toNat * 2 ^ (n - 1) < (w.toNat + 1) ^ 2 := by
  have hxc := toNat_xcomp hn x
  have hw : ((1 : BitVec n) <<< (n - 1)).toNat = 2 ^ (n - 1) := toNat_one_shiftLeft (by omega)
  obtain ⟨w, hw1, hw2, hw3⟩ := fixedPointSqrt_iter_bracket
    (x.setWidth (2 * n) <<< (n - 1)) (n - 1) ((1 : BitVec n) <<< (n - 1))
    (by omega)
    (by rw [hw]; exact Nat.dvd_refl _)
    (by rw [hw, hxc, Nat.pow_two]; exact Nat.mul_le_mul_right _ hx)
    (by rw [hw, hxc]
        have h2 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
          have : 2 ^ n = 2 * 2 ^ (n - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          omega
        rw [h2, two_pow_sq]
        calc x.toNat * 2 ^ (n - 1) < 2 ^ (n + 1) * 2 ^ (n - 1) :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr x.isLt
          _ = 2 ^ (2 * n) := by rw [← Nat.pow_add]; congr 1; omega)
  refine ⟨w, ?_, ?_, ?_⟩
  · simp only [fixedPointSqrt]; rw [hxc] at hw1; exact hw1
  · rw [hxc] at hw2; exact hw2
  · rw [hxc] at hw3; exact hw3

end Fp

