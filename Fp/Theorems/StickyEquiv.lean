import Fp.Utils.Rat

/-!
# `StickyEquiv` — the general sticky-compression theory

A floating-point circuit that keeps a quotient/sum to `s` bits and OR-s a sticky
bit into the last position produces a value that is a *sticky compression*
(`StickyEquiv`) of the exact result. This file defines `StickyEquiv` and the two
operation-independent reduction steps shared by the addition and division proofs:
`StickyEquiv.of_sign_grid` (strip sign + grid weight) and `floor_sticky_within_one`
(the floor/remainder/sticky/shift core), plus the small `Rat`/`Nat` helpers.
-/

namespace Fp

def StickyEquiv (k : Int) (q r : Rat) : Prop :=
  q = r ∨ (∃ n : Int, ¬ (2 ∣ n) ∧ q = n * (2 : Rat) ^ k ∧ (r - q).abs < (2 : Rat) ^ k)

theorem StickyEquiv.rfl {k : Int} {q : Rat} : StickyEquiv k q q := Or.inl (Eq.refl q)

/-- A sticky compression of a value is zero only if the value itself is zero
(an odd multiple of `2^k` is nonzero). -/
theorem StickyEquiv.ne_zero_of_ne_zero {k : Int} {q r : Rat}
    (h : StickyEquiv k q r) (hr : r ≠ 0) : q ≠ 0 := by
  rcases h with h | ⟨n, hodd, hq, _⟩
  · grind
  · subst hq
    have hn : n ≠ 0 := by grind
    have h2 : (2 : Rat) ^ k ≠ 0 := Rat.two_pow_int_ne_zero
    exact Rat.mul_ne_zero_iff.mpr ⟨fun hcontra => hn (by exact_mod_cast hcontra), h2⟩


/-! ## `Rat.abs` helpers -/

theorem Rat.abs_neg_eq (x : Rat) : (-x).abs = x.abs := by
  unfold Rat.abs
  split <;> split <;> grind

theorem Rat.abs_mul_pos {x w : Rat} (hw : 0 < w) : (x * w).abs = x.abs * w := by
  unfold Rat.abs
  by_cases hx : x < 0
  · have hxw : x * w < 0 := by
      have h : 0 ≤ (-x) * w := Rat.mul_nonneg (by grind) (Rat.le_of_lt hw)
      grind
    rw [if_pos hxw, if_pos hx, Rat.neg_mul]
  · have hx' : 0 ≤ x := by grind
    have hxw : ¬ (x * w < 0) := by
      have h : 0 ≤ x * w := Rat.mul_nonneg hx' (Rat.le_of_lt hw)
      grind
    rw [if_neg hxw, if_neg hx]

theorem Rat.abs_div_pos {x w : Rat} (hw : 0 < w) : (x / w).abs = x.abs / w := by
  unfold Rat.abs
  by_cases hx : x < 0
  · have hxw : x / w < 0 := by
      have h : 0 ≤ (-x) / w := by
        rw [Rat.div_def]; exact Rat.mul_nonneg (by grind) (by grind [Rat.inv_pos])
      have : (-x) / w = -(x / w) := by rw [Rat.div_def, Rat.div_def]; grind
      grind
    rw [if_pos hxw, if_pos hx]
    rw [Rat.div_def, Rat.div_def]; grind
  · have hx' : 0 ≤ x := by grind
    have hxw : ¬ (x / w < 0) := by
      have h : 0 ≤ x / w := by rw [Rat.div_def]; exact Rat.mul_nonneg hx' (by grind [Rat.inv_pos])
      grind
    rw [if_neg hxw, if_neg hx]

/-- If the integer numerator `A − B·Y` lies strictly within `(−Y, Y)`, the
rational `(A − B·Y)/Y` has absolute value below one. -/
theorem Rat.abs_intSub_div_natCast_lt_one (A B Y : Nat) (hY : 0 < Y)
    (h : -(Y:Int) < (A:Int) - (B:Int)*(Y:Int) ∧ (A:Int) - (B:Int)*(Y:Int) < (Y:Int)) :
    (((A:Int) - (B:Int)*(Y:Int) : Rat)/(Y:Rat)).abs < 1 := by
  have hYr : (0:Rat) < (Y:Rat) := by grind
  rw [Rat.abs_div_pos hYr]
  rw [show (1:Rat) = (Y:Rat)/(Y:Rat) from (Rat.div_self_eq_one_of_ne_zero (by grind)).symm]
  rw [Rat.div_lt_div_self hYr]
  have h1 : (((A:Int) - (B:Int)*(Y:Int)):Rat) < (Y:Rat) := by exact_mod_cast h.2
  have h2 : (-(((A:Int) - (B:Int)*(Y:Int)):Rat)) < (Y:Rat) := by
    have hz : (-((A:Int) - (B:Int)*(Y:Int)) : Int) < (Y:Int) := by grind
    exact_mod_cast hz
  unfold Rat.abs
  split <;> grind

/-! ## `Nat`/`Rat` arithmetic helpers -/

/-- OR-ing the bottom bit: `m ||| 1` is `m` rounded down to even, plus one. -/
theorem Nat.lor_one_eq (m : Nat) : m ||| 1 = 2 * (m / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp
  | succ j =>
    simp only [Nat.testBit_succ]
    have h : (2 * (m / 2) + 1) / 2 = m / 2 := by grind
    simp [h]

theorem Rat.ofNat_div_decomp (D Y : Nat) (hY : 0 < Y) :
    (D:Rat)/(Y:Rat) = ((D/Y:Nat):Rat) + ((D%Y:Nat):Rat)/(Y:Rat) := by
  have h := Rat.ofNat_div_ofNat_eq_ofNat_div_add_ofNat_mod D Y (by grind)
  simp only [Rat.ofNat_eq_coe] at h
  exact h

/-- Rewrite the kept-vs-exact difference `(D/Y)·2^b − n` as a single fraction
over `Y` with an integer numerator. -/
theorem Rat.div_mul_two_pow_sub_natCast_eq (D n Y b : Nat) (hY : 0 < Y) :
    (D:Rat)/(Y:Rat) * (2:Rat)^b - (n:Rat)
      = (((D * 2^b : Nat) : Int) - (n:Int)*(Y:Int) : Rat) / (Y:Rat) := by
  have h2 : ((2^b:Nat):Rat) = (2:Rat)^b := by grind
  rw [← h2]; push_cast; rw [Rat.div_def, Rat.div_def]; grind

/-! ## L1: sign + grid stripper -/

/-- **L1.** Reduce a `StickyEquiv` goal whose two sides share a sign `sd = ±1`
and grid weight `2^k` to the integer-significand disjunction
`t = n ∨ (n odd ∧ |t − n| < 1)`.  Fully general — usable for any operation that
produces a kept integer significand `n` and an exact scaled value `t`. -/
theorem StickyEquiv.of_sign_grid {k : Int} {sd : Rat} {n : Int} {t : Rat}
    (hsd : sd = 1 ∨ sd = -1)
    (h : t = (n : Rat) ∨ (¬ (2 ∣ n) ∧ (t - (n : Rat)).abs < 1)) :
    StickyEquiv k (sd * (n : Rat) * 2 ^ k) (sd * t * 2 ^ k) := by
  have hpos : (0 : Rat) < (2 : Rat) ^ k := Rat.two_pow_pos k
  rcases h with heq | ⟨hodd, hlt⟩
  · exact Or.inl (by rw [heq])
  · unfold StickyEquiv
    generalize hw : (2 : Rat) ^ k = w at hpos ⊢
    right
    have key : ((t - (n : Rat)) * w).abs < w := by
      rw [Rat.abs_mul_pos hpos]
      have h1 := (Rat.mul_lt_mul_cancel_right_of_lt hpos).mpr hlt
      simpa using h1
    rcases hsd with rfl | rfl
    · refine ⟨n, hodd, by grind, ?_⟩
      have he : (1 : Rat) * t * w - 1 * (n : Rat) * w = (t - (n : Rat)) * w := by grind
      rw [he]; exact key
    · refine ⟨-n, by simpa [Int.dvd_neg] using hodd, ?_, ?_⟩
      · push_cast; grind
      · have he : (-1 : Rat) * t * w - (-1) * (n : Rat) * w = -((t - (n : Rat)) * w) := by grind
        rw [he, Rat.abs_neg_eq]; exact key

/-! ## L2: floor / remainder / sticky / shift core -/

/-- **L2.** For a Nat dividend `D`, divisor `Y > 0`, normalisation shift `b ≤ 1`
and kept significand `n = (⌊D/Y⌋·2^b) ||| sticky` (`sticky = D % Y ≠ 0`), the
exact scaled quotient `(D/Y)·2^b` either equals `n` (exact division) or `n` is
odd and the exact value lies strictly within one ulp of `n`. -/
theorem floor_sticky_within_one (D Y b : Nat) (hY : 0 < Y) (hb : b ≤ 1)
    (n : Nat) (hn : n = (D / Y * 2 ^ b) ||| (if D % Y = 0 then 0 else 1)) :
    ((D : Rat) / (Y : Rat) * (2:Rat) ^ b = (n : Rat))
      ∨ (¬ (2 ∣ (n : Int)) ∧
          ((D : Rat) / (Y : Rat) * (2:Rat) ^ b - (n : Rat)).abs < 1) := by
  have hcast : ((2^b:Nat):Rat) = (2:Rat)^b := by grind
  have hdecomp := Rat.ofNat_div_decomp D Y hY
  by_cases hrem : D % Y = 0
  · left
    rw [if_pos hrem, Nat.or_zero] at hn
    rw [hn, hdecomp, hrem]
    push_cast
    rw [← hcast]
    push_cast
    grind
  · right
    rw [if_neg hrem] at hn
    have hrem0 : 0 < D % Y := by grind
    have hremlt : D % Y < Y := Nat.mod_lt _ hY
    have hnval : n = 2 * ((D / Y * 2 ^ b) / 2) + 1 := by rw [hn]; exact Nat.lor_one_eq _
    clear hn hcast hdecomp
    refine ⟨by rw [hnval]; push_cast; grind, ?_⟩
    rw [Rat.div_mul_two_pow_sub_natCast_eq D n Y b hY]
    have hdm : Y * (D / Y) + D % Y = D := Nat.div_add_mod D Y
    have hz : -(Y:Int) < ((D * 2^b : Nat) : Int) - (n:Int)*(Y:Int)
        ∧ ((D * 2^b : Nat) : Int) - (n:Int)*(Y:Int) < (Y:Int) := by
      rcases (show b = 0 ∨ b = 1 by grind) with rfl | rfl
      · -- b = 0: split on the parity of `D / Y` to linearise `(D/Y/2)·Y`.
        simp only [Nat.pow_zero, Nat.mul_one] at hnval ⊢
        have hq : 2 * ((D / Y) / 2) + (D / Y) % 2 = D / Y := Nat.div_add_mod (D / Y) 2
        have hp : (D / Y) % 2 = 0 ∨ (D / Y) % 2 = 1 := by grind
        generalize hH : (D / Y) / 2 = qh at *
        generalize hQ : D / Y = q at *
        generalize hR : D % Y = r at *
        subst hnval
        rcases hp with hp | hp
        · have hqv : q = 2 * qh := by grind
          rw [hqv] at hdm; push_cast; push_cast at hdm; grind
        · have hqv : q = 2 * qh + 1 := by grind
          rw [hqv] at hdm; push_cast; push_cast at hdm; grind
      · -- b = 1: `(D/Y·2)/2 = D/Y`, no parity needed.
        simp only [Nat.pow_one] at hnval ⊢
        have hd2 : D / Y * 2 / 2 = D / Y := by grind
        rw [hd2] at hnval
        generalize hQ : D / Y = q at hnval hdm
        generalize hR : D % Y = r at hdm hremlt hrem0
        subst hnval
        push_cast
        push_cast at hdm
        grind
    exact Rat.abs_intSub_div_natCast_lt_one (D * 2^b) n Y hY hz

end Fp
