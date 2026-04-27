import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Grind
import Fp.Utils.Nat

@[grind]
def Int.monus (a b : Int) : Int :=
  if a < b then 0 else a - b

@[simp]
theorem Int.zero_le_monus (a b : Int) : 0 ≤ a.monus b := by
  grind

@[simp]
theorem Int.add_monus_eq_self_of_le {a b : Int} (h : a ≤ b) : a + a.monus b = a := by
  grind

theorem natCast_monus_natCast_eq_natCast_sub {m n : Nat} : Int.monus m n = ((m - n : Nat) : Int) := by
  grind
theorem Int.pow_div_self_eq_sub_one_of_pos (i : Int) (hi : i ≠ 0) (k : Nat) (hk : 0 < k) :
    (i ^ k) / i = i ^ (k - 1) := by
  have : ∃ k', k = k' + 1 := by exact Nat.exists_eq_add_one.mpr hk
  obtain ⟨k', hk'⟩ := this
  subst hk'
  simp [Int.pow_add]
  rw [Int.pow_one]
  rw [Int.mul_ediv_cancel]
  grind only

@[simp]
theorem Int.two_pow_div_two_eq_sub_one_of_pos (k : Nat) (hk : 0 < k) :
    ((2 : Int) ^ k) / 2 = 2 ^ (k - 1) := by
  apply Int.pow_div_self_eq_sub_one_of_pos
  · decide
  · exact hk
theorem Int.two_pow_succ_div_two {n : Nat} :
  (2 ^ n + 1) / 2 = (2 ^ (n - 1) : Int) := by
  cases n <;> grind
@[simp]
theorem Int.two_pow_plus_one_div_two_eq_two_pow (e : Nat) :
   ((2 : Int)^e + 1) / 2 = (2 : Int) ^ (e - 1) := by
  norm_cast
  exact Nat.two_pow_succ_div_two

@[simp]
theorem Int.sub_toNat_eq_zero_of_le {a b : Int} (h : a ≤ b) :
    (a - b).toNat = 0 := by
  simp
  grind only
