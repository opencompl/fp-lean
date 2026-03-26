import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Grind



theorem Rat.mul_ne_zero_iff {x y : Rat} : (¬ (x * y = 0)) ↔ x ≠ 0 ∧ y ≠ 0 := by
  grind

theorem Rat.ne_zero_of_zero_lt {r : Rat} (h : 0 < r) : r ≠ 0 := by
  grind

attribute [simp] Rat.zero_add
attribute [simp] Rat.add_zero
attribute [simp] Rat.zero_mul
attribute [simp] Rat.mul_zero
attribute [simp] Rat.mul_one
attribute [simp] Rat.one_mul

attribute [simp] Rat.natCast_eq_zero_iff
attribute [simp] Rat.natCast_inj
attribute [simp] Rat.intCast_inj


@[simp]
theorem Rat.mul_cancel_left {x y z : Rat} (hx : x ≠ 0) : x * y = x * z ↔ y = z := by
  grind


@[simp]
theorem Rat.mul_cancel_right {x y z : Rat} (hx : x ≠ 0) : y * x = z * x ↔ y = z := by
  grind

@[simp]
theorem Rat.natCast_ne_natCast_iff {r s : Nat} : (r : Rat) ≠ (s : Rat) ↔ r ≠ s := by
  apply not_congr; simp


@[simp]
theorem Rat.intCast_ne_intCast_iff {r s : Int} : (r : Rat) ≠ (s : Rat) ↔ r ≠ s := by
  apply not_congr; simp

/-- convert the sign bit to an integer value. Morally, this is (-1)^s -/
def signToInt (s : Bool) : Int :=
  if s then -1 else 1

/-- write the sign bit as two pow. -/
@[simp]
theorem signToInt_eq_negOne_pow_toNat (s : Bool) :
  signToInt s = (-1 : Int) ^ s.toNat := by
  cases s
  · simp [signToInt]
  · simp [signToInt]


@[simp, bv_normalize]
def lastPowerOfTwo_iter (m : Nat) (n : Nat) : Nat :=
  if m = 0 then
    1
  else if 2 ^ m < n then
    2 ^ m
  else
    lastPowerOfTwo_iter (m-1) n
  termination_by m

/--
Returns the largest power of two strictly less than `n`.

If no such number exists, returns `1` instead.
-/
@[simp, bv_normalize]
def lastPowerOfTwo (n : Nat) : Nat :=
  lastPowerOfTwo_iter ((n+1)/2) n

theorem sub_two_le { n : Nat } : n - 2 ≤ n := by
  omega

@[grind .]
theorem le_two_pow : n ≤ 2^n := by
  induction n
  case zero =>
    exact Nat.zero_le _
  case succ ih =>
    simp only [Nat.pow_add_one, Nat.mul_two]
    exact Nat.add_le_add ih Nat.one_le_two_pow

theorem two_pow_sub_one_le_two_pow (e : Nat) : 2^(e-1) ≤ 2^e :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem toEFixed_hPrec (e s : Nat) : 2 ^ (e - 1) + s - 2 < 2 ^ e + s := by
  have hexp0 : 0 < 2^e := Nat.two_pow_pos _
  have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
  omega



@[simp, grind .]
theorem Rat.div_cancel {p q d : Rat} (hd : d ≠ 0) :
    (p / d = q / d) <-> p = q := by
  rw [Rat.div_def, Rat.div_def]
  rw [Rat.mul_cancel_right]
  · grind

@[grind .]
theorem Rat.twoPowNeZero (n : Int) : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  grind only [Fp.Rat.two_pow_pos]

attribute [simp] Rat.zpow_natCast

theorem Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
    {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) (hac : 0 ≤ a) (hcc : 0 ≤ c) :
    a * c ≤ b * d := by
  apply (Rat.le_iff_sub_nonneg (a * c) (b * d)).mpr
  rw [show b = a + (b - a) by grind only]
  rw [Rat.add_mul]
  have : (b - a) ≥ 0 := by grind
  have : 0 ≤ a * d := by
    apply Rat.mul_nonneg <;> grind only
  rw [show a * d + (b - a) * d - a * c = (b - a) * d + a * (d - c) by grind only]
  have : 0 ≤ a * (d - c) := by
    apply Rat.mul_nonneg <;> grind only
  have : 0 ≤ (b - a) * d := by
    apply Rat.mul_nonneg <;> grind only
  grind only

theorem Rat.mul_lt_mul_of_lt_of_le_of_nonneg_of_nonneg
    {a b c d : Rat} (hab : a < b) (hcd : c ≤ d) (hac : 0 ≤ a) (hcc : 0 ≤ c) :
    a * c ≤ b * d := by
  apply (Rat.le_iff_sub_nonneg (a * c) (b * d)).mpr
  rw [show b = a + (b - a) by grind only]
  rw [Rat.add_mul]
  have : (b - a) ≥ 0 := by grind
  have : 0 ≤ a * d := by
    apply Rat.mul_nonneg <;> grind only
  rw [show a * d + (b - a) * d - a * c = (b - a) * d + a * (d - c) by grind only]
  have : 0 ≤ a * (d - c) := by
    apply Rat.mul_nonneg <;> grind only
  have : 0 ≤ (b - a) * d := by
    apply Rat.mul_nonneg <;> grind only
  grind only

theorem Rat.mul_lt_mul_of_le_of_lt_of_nonneg_of_nonneg
    {a b c d : Rat} (hab : a <=  b) (hcd : c < d) (hac : 0 ≤ a) (hcc : 0 ≤ c) :
    a * c ≤ b * d := by
  apply (Rat.le_iff_sub_nonneg (a * c) (b * d)).mpr
  rw [show b = a + (b - a) by grind only]
  rw [Rat.add_mul]
  have : (b - a) ≥ 0 := by grind
  have : 0 ≤ a * d := by
    apply Rat.mul_nonneg <;> grind only
  rw [show a * d + (b - a) * d - a * c = (b - a) * d + a * (d - c) by grind only]
  have : 0 ≤ a * (d - c) := by
    apply Rat.mul_nonneg <;> grind only
  have : 0 ≤ (b - a) * d := by
    apply Rat.mul_nonneg <;> grind only
  grind only

attribute [grind .] Rat.pow_pos

@[grind .]
theorem Rat.two_pow_int_ne_zero {n : Int} : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  apply Rat.zpow_pos
  grind only

@[grind .]
theorem Rat.two_pow_nat_ne_zero {n : Nat} : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  exact Nat.two_pow_pos n


@[grind ., simp]
theorem Rat.two_pow_ne_zero (n : Int) : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  grind

theorem Rat.zpow_sub_eq_zpow_mul_zpow {b : Rat} (hb : b ≠ 0)
    (x y: Int) : b ^ (x - y) = b ^ x * b ^ (-y) := by
  rw [Int.sub_eq_add_neg]
  rw [Rat.zpow_add hb]

theorem Rat.mul_sub (b x y : Rat) : b * (x - y) = b * x - b * y := by
  grind only

@[simp, grind .]
theorem Rat.one_le_two_pow_nat {n : Nat} : 1 ≤ (2 : Rat) ^ n := by
  induction n with
  | zero => grind
  | succ n ih =>
    rw [Rat.pow_succ]
    grind

theorem Rat.two_pow_le_two_pow_of_le {x y : Int} (h : x ≤ y) : (2 : Rat) ^ x ≤ (2 : Rat) ^ y := by
  rw [Rat.le_iff_sub_nonneg]
  rw [show (2 : Rat) ^ x = (2 : Rat) ^ x * 1 by grind only]
  rw [show y = x + (y - x) by grind only]
  rw [Rat.zpow_add (by grind only)]
  rw [← Rat.mul_sub]
  have : 1 ≤ (2 : Rat) ^ (y - x) := by
    have : ∃ (k : Nat), y - x = k := by
      exact Int.nonneg_def.mp h
    obtain ⟨k, hk⟩ := this
    rw [hk]
    simp
  grind only [Rat.mul_nonneg, Rat.le_of_lt, Fp.Rat.two_pow_pos]

theorem Rat.le_mul_of_one_le_of_le  {x y y' : Rat} (hx1 : 1 ≤ x) (hy : 0 ≤ y) (hy' : y ≤ y')
    : y ≤ x * y' := by
  suffices 1 * y ≤ x * y' by grind only
  apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
  · grind only
  · grind only
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]


theorem Rat.le_mul_self_of_le_one_of_nonneg {y} {x : Rat} (hx0 : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y)
    : x * y ≤ y := by
  suffices x * y ≤ 1 * y by grind only
  apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
  · grind only
  · grind only
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]

attribute [simp] Rat.le_refl
