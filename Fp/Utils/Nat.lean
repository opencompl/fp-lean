import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Grind

@[simp, grind .]
theorem one_lt_two_pow_iff (x : Nat) : 1 < 2 ^ x ↔ 0 < x := by
  rw [show 1 = 2 ^ 0 by simp]
  rw [Nat.pow_lt_pow_iff_right]
  · grind only

theorem Nat.log2_eq_exists (n : Nat) (hn : n ≠ 0) :
  ∃ k, n.log2 = k ∧ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  let k := n.log2
  exists k
  simp [k]
  apply Nat.log2_eq_iff .. |>.mp <;> grind

grind_pattern Nat.log2_eq_exists => n.log2

theorem Nat.log2_le_log2_of_le {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  induction a using Nat.div2Induction generalizing b with
  | ind a ih =>
    match ha : a with
    | 0 => simp
    | 1 => simp
    | a' + 2 =>
      match hb : b with
      | 0 => simp_all
      | 1 => simp_all
      | b' + 2 =>
        simp only [succ_eq_add_one] at ha hb
        simp only [← ha, ← hb] at ⊢ h ih
        replace ih := ih (ha ▸ Nat.zero_lt_succ _) (Nat.div_le_div_right h)
        rewrite [Nat.log2_def a, Nat.log2_def b]
        simp only [ha, le_add_left, ↓reduceIte, hb, Nat.add_le_add_iff_right, ge_iff_le]
        simp [← ha, ← hb, ih]

grind_pattern Nat.log2_le_log2_of_le => 2^a ≤ 2^b


theorem Nat.log2_le_log2_add {a b : Nat} : a.log2 ≤ (a + b).log2 := by
  apply Nat.log2_le_log2_of_le
  apply Nat.le_add_right

theorem Nat.pow_pred_div (h : 0 < n) :
  2 ^ (n - 1) = (2 ^ n) / 2 := by
  grind [Nat.pow_pred_mul]

theorem Nat.two_pow_succ_div_two {n : Nat} :
  (2 ^ n + 1) / 2 = 2 ^ (n - 1) := by
  cases n <;> grind

@[grind ., simp]
theorem Nat.two_pow_plus_one_div_two_eq_two_pow (e : Nat) :
   (2^e + 1) / 2 = 2 ^ (e - 1) := by
  exact Nat.two_pow_succ_div_two
