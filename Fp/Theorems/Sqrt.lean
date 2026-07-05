import Fp.Theorems.SqrtFixed
import Fp.UnpackedFloat.Lemmas.Conversion

/-!
# Value characterization of `UnpackedFloat.sqrt`

Builds on `fixedPointSqrt_bracket` (`SqrtFixed.lean`): the unpacked square root's significand
is `2m + sticky` where `m = ⌊√Xa⌋` on the aligned, doubled-width input `Xa` and the sticky bit
records exactness. The exponent is halved (`sshiftRight 1`) and the sign is `+`.

Everything is stated at the `Nat` (`toNat`) level to avoid `BitVec` width bookkeeping
(the circuit mixes widths `1+s+1` and `s+2`).
-/

namespace Fp

open UnpackedFloat

/-- `((0#1 ++ sig) ++ 0#1).toNat = 2 * sig.toNat`. -/
theorem toNat_alignedSig {s : Nat} (sig : BitVec s) :
    (((0#1 ++ sig) ++ 0#1 : BitVec (1 + s + 1))).toNat = 2 * sig.toNat := by
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_or,
    Nat.or_zero, Nat.shiftLeft_eq, Nat.pow_one]
  omega

/-- `toNat` of `fixedPointSqrt aligned` in terms of its integer-sqrt `w` and sticky bit. -/
theorem toNat_fixedPointSqrt {n : Nat} {aligned : BitVec (n + 1)} {w : BitVec n}
    (hfp : fixedPointSqrt aligned = w ++ BitVec.ofBool (decide (w.toNat ^ 2 ≠ aligned.toNat * 2 ^ (n - 1)))) :
    (fixedPointSqrt aligned).toNat
      = 2 * w.toNat + (if w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) then 0 else 1) := by
  rw [hfp, BitVec.toNat_append, BitVec.toNat_ofBool, Nat.shiftLeft_eq]
  have hb : (decide (w.toNat ^ 2 ≠ aligned.toNat * 2 ^ (n - 1))).toNat
      = (if w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) then 0 else 1) := by
    by_cases h : w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) <;> simp [h]
  rw [hb]
  have hlt : (if w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) then (0:Nat) else 1) < 2 ^ 1 := by
    split <;> omega
  rw [Nat.mul_comm w.toNat (2 ^ 1), ← Nat.two_pow_add_eq_or_of_lt hlt w.toNat]

/-- Splitting off the low bit and re-appending it rebuilds the value:
`(v.extractMsb' 0 len ++ ofBool (v.getLsbD 0)).toNat = v.toNat` when `len + 1 = W`. -/
theorem reconstruct_toNat {W len : Nat} (v : BitVec W) (h : len + 1 = W) :
    ((v.extractMsb' 0 len) ++ BitVec.ofBool (v.getLsbD 0)).toNat = v.toNat := by
  rw [BitVec.toNat_append, BitVec.toNat_ofBool, BitVec.toNat_extractMsb'_zero v (by omega)]
  have hWlen : W - len = 1 := by omega
  rw [hWlen, Nat.shiftLeft_eq, Nat.pow_one]
  have hbit : (v.getLsbD 0).toNat = v.toNat % 2 := by
    have : v.getLsbD 0 = decide (v.toNat % 2 = 1) := by
      rw [BitVec.getLsbD, Nat.testBit_zero]
    rw [this]; by_cases h2 : v.toNat % 2 = 1 <;> simp [h2] <;> omega
  rw [hbit]
  have hdlt : v.toNat % 2 < 2 ^ 1 := by omega
  rw [Nat.mul_comm (v.toNat / 2) 2, ← Nat.two_pow_add_eq_or_of_lt hdlt (v.toNat / 2)]
  omega

/-- Value/bracket characterization of `UnpackedFloat.sqrt` on a normalized input.  `m = ⌊√Xa⌋`
where `Xa` is the doubled-width aligned significand; the significand is `2m + sticky`. -/
theorem UnpackedFloat.sqrt_bracket {e s : Nat} (hs : 0 < s) (x : UnpackedFloat e s)
    (hmsb : x.sig.msb = true) :
    ∃ (m Xa : Nat),
      Xa = (if x.ex.getLsbD 0 = false then 2 else 4) * x.sig.toNat * 2 ^ s ∧
      m ^ 2 ≤ Xa ∧ Xa < (m + 1) ^ 2 ∧
      (UnpackedFloat.sqrt x).sign = false ∧
      (UnpackedFloat.sqrt x).ex = x.ex.sshiftRight 1 ∧
      (UnpackedFloat.sqrt x).sig.toNat = 2 * m + (if m ^ 2 = Xa then 0 else 1) ∧
      (UnpackedFloat.sqrt x).sig.msb = true := by
  have hsiglo : 2 ^ (s - 1) ≤ x.sig.toNat := by
    have h := hmsb; rw [BitVec.msb_eq_decide] at h; simpa using h
  have hsig : x.sig.toNat < 2 ^ s := x.sig.isLt
  -- Common analysis for a given aligned significand with a leading bit.
  have core : ∀ (aligned : BitVec (1 + s + 1)) (C : Nat), aligned.toNat = C → 2 ^ s ≤ C →
      ∃ (m : Nat), m ^ 2 ≤ C * 2 ^ s ∧ C * 2 ^ s < (m + 1) ^ 2 ∧
        (fixedPointSqrt aligned).toNat = 2 * m + (if m ^ 2 = C * 2 ^ s then 0 else 1) ∧
        2 ^ s ≤ m := by
    intro aligned C hC hlead
    obtain ⟨w, hfp, hle, hgt⟩ := fixedPointSqrt_bracket (n := 1 + s) (by omega) aligned
      (by rw [hC, show 1 + s - 1 = s from by omega]; exact hlead)
    have hxc : aligned.toNat * 2 ^ (1 + s - 1) = C * 2 ^ s := by
      rw [hC, show 1 + s - 1 = s from by omega]
    have hval := toNat_fixedPointSqrt hfp
    rw [hxc] at hval hle hgt
    refine ⟨w.toNat, hle, hgt, hval, ?_⟩
    have h3 : (2 ^ s) ^ 2 ≤ C * 2 ^ s := by
      rw [Nat.pow_two]; exact Nat.mul_le_mul_right _ hlead
    have h4 : (2 ^ s) ^ 2 < (w.toNat + 1) ^ 2 := Nat.lt_of_le_of_lt h3 hgt
    rcases Nat.lt_or_ge (2 ^ s) (w.toNat + 1) with hlt | hge
    · omega
    · exact absurd h4 (Nat.not_lt.mpr (Nat.pow_le_pow_left hge 2))
  have hpow : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  -- unfold the significand structure and split on exponent parity
  simp only [UnpackedFloat.sqrt]
  by_cases hpar : x.ex.getLsbD 0 = false
  · obtain ⟨m, hle, hgt, hval, hm⟩ := core ((0#1 ++ x.sig) ++ 0#1) (2 * x.sig.toNat)
      (toNat_alignedSig x.sig) (by omega)
    have hrec := reconstruct_toNat (W := 1 + s + 1) (len := s + 1)
      (fixedPointSqrt ((0#1 ++ x.sig) ++ 0#1)) (by omega)
    refine ⟨m, 2 * x.sig.toNat * 2 ^ s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hpar]
    · simpa [hpar] using hle
    · simpa [hpar] using hgt
    · simp [hpar]
    · simp [hpar]
    · simp only [hpar, beq_self_eq_true, if_true]
      rw [hrec]; simpa [hpar] using hval
    · simp only [hpar, beq_self_eq_true, if_true]
      rw [BitVec.msb_eq_decide, hrec]
      have hb : 2 ^ (s + 1) ≤ (fixedPointSqrt ((0#1 ++ x.sig) ++ 0#1)).toNat := by
        rw [hval, Nat.pow_succ]; omega
      simpa using hb
  · have hpar' : x.ex.getLsbD 0 = true := by
      cases h : x.ex.getLsbD 0 <;> simp_all
    have h2pow : (2 : Nat) ^ (1 + s + 1) = 4 * 2 ^ s := by
      rw [show 1 + s + 1 = s + 2 from by omega, Nat.pow_add]; omega
    have hAsl : (((0#1 ++ x.sig) ++ 0#1 : BitVec (1 + s + 1)) <<< 1).toNat = 4 * x.sig.toNat := by
      rw [BitVec.toNat_shiftLeft, toNat_alignedSig, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨m, hle, hgt, hval, hm⟩ := core (((0#1 ++ x.sig) ++ 0#1) <<< 1) (4 * x.sig.toNat)
      hAsl (by omega)
    have hrec := reconstruct_toNat (W := 1 + s + 1) (len := s + 1)
      (fixedPointSqrt (((0#1 ++ x.sig) ++ 0#1) <<< 1)) (by omega)
    refine ⟨m, 4 * x.sig.toNat * 2 ^ s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hpar']
    · simpa [hpar'] using hle
    · simpa [hpar'] using hgt
    · simp [hpar']
    · simp [hpar']
    · simp only [hpar', Bool.true_eq_false, if_false, beq_iff_eq]
      rw [hrec]; simpa [hpar'] using hval
    · simp only [hpar', Bool.true_eq_false, if_false, beq_iff_eq]
      rw [BitVec.msb_eq_decide, hrec]
      have hb : 2 ^ (s + 1) ≤ (fixedPointSqrt (((0#1 ++ x.sig) ++ 0#1) <<< 1)).toNat := by
        rw [hval, Nat.pow_succ]; omega
      simpa using hb

end Fp
