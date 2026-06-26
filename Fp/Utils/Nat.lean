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

theorem Nat.mul_add_div'
    (a b c : Nat) (hc : c ≠ 0) :
    (c * a + b) / c = a + b / c := by
  apply Nat.mul_add_div
  omega

@[grind .]
theorem Nat.two_pow_ne_zero' (n : Nat) :
    2 ^ n ≠ 0 := by grind

/-- 'a/b' equals '(a/gcd(a, b)) / (b/gcd(a, b))'. -/
theorem Nat.gcd_div_gcd_eq (a b : Nat) :
    (a / Nat.gcd a b) / (b / Nat.gcd a b) = a / b := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_div_cancel']
    exact gcd_dvd_right a b


@[simp]
theorem Nat.four_le_two_pow_of_lt {n : Nat} (hn : 1 < n) : 4 ≤ 2 ^ n := by
  have : 2 ^ 2 ≤ 2 ^ n := by apply Fp.Nat.two_pow_le_two_pow_of_le; grind only
  simp at this
  assumption


/-- Reassociation: `Nat.mul_add_div` with the multiplier in `d` placed correctly. -/
theorem Nat.mul_add_div_of_pos {d k r : Nat} (hd : 0 < d) :
    (d * k + r) / d = k + r / d := by
  rw [Nat.add_div]
  · have : d * k / d = k := by
      exact mul_div_right k hd
    rw [this]
    simp only [mul_mod_right, Nat.zero_add, Nat.add_eq_left, ite_eq_right_iff, succ_ne_self,
      imp_false, Nat.not_le, gt_iff_lt]
    apply mod_lt r hd
  · grind only
attribute [grind ← ] Nat.pow_le_pow_of_le
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
