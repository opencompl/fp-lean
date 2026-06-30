import Lean
import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Utils.Nat
import Fp.Grind

open Lean


def Rat.ofNat (n : Nat) : Rat := Rat.ofInt (n : Int)

attribute [grind! .] Nat.two_pow_pos
attribute [grind =, grind =_] Nat.pow_add


@[simp]
theorem Rat.ofNat_add (a b : Nat) :
    Rat.ofNat (a + b) = Rat.ofNat a + Rat.ofNat b := by
  simp [ofNat, ofInt]

@[simp]
theorem Rat.ofNat_mul (a b : Nat) :
    Rat.ofNat (a * b) = Rat.ofNat a * Rat.ofNat b := by
  simp [ofNat, ofInt]

theorem Rat.mul_cyclic_permute
    (a b c : Rat) :
    a * b * c = b * c * a := by grind

@[simp, grind .]
theorem Rat.ofNat_eq_zero_iff (n : Nat) :
    Rat.ofNat n = 0 ↔ n = 0 := by
  simp [ofNat, ofInt]

@[simp]
theorem Rat.self_mul_add_div (a b c : Rat) (hb : b ≠ 0) :
    (b * a + c) / b = a + c / b  := by
  grind

theorem Rat.ofNat_eq_coe ( n : Nat) :
    Rat.ofNat n = (n : Rat) := by
  simp [ofNat, ofInt]
  norm_cast

theorem Rat.ofNat_div_ofNat_eq_ofNat_div_add_ofNat_mod (a b : Nat) (hb : b ≠ 0):
    ((Rat.ofNat a) / (Rat.ofNat b)) =
    Rat.ofNat (a / b) + (ofNat (a % b)) / (ofNat b) := by
  have := Nat.div_add_mod a b
  rw [← this]
  simp
  grind

theorem Nat.mul_lt_of_lt_twoPow_of_le_twoPow
    {a b m n : Nat} (ha : a < 2 ^ m) (hb : b ≤ 2 ^ n) :
    a * b < 2 ^ (m + n) :=
  by
  rw [Nat.pow_add]
  apply Nat.mul_lt_mul_of_lt_of_le <;> grind

/-- rational that is 1/2^n -/
def Rat.twoPowInv (n : Nat) : Rat := (ofNat 1) / (ofNat (2^n))

@[simp]
theorem Rat.mkRat_add_mkRat_eq_mkRat_add (n₁ n₂ : Int) {d} (hd : d ≠ 0)  :
    mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d:= by
  rw [← normalize_eq_mkRat hd,
    ← normalize_eq_mkRat hd,
    normalize_add_normalize,
    normalize_eq_mkRat]
  rw [show n₁ * d + n₂ * d = (n₁ + n₂) * d by grind]
  rw [mkRat_mul_right hd]


/-- Two rational numbers with the same denominator are equal
iff the numerators are equal, when the denominator is nonzero. -/
@[simp]
theorem Rat.mkRat_eq_iff_numerator {n₁ n₂ : Int} {d : Nat} (hd : d ≠ 0):
    (mkRat n₁ d = mkRat n₂ d) ↔ (n₁ = n₂) := by
  constructor
  · intros heq
    rw [mkRat_eq_iff] at heq
    · rw [Int.mul_eq_mul_right_iff (by simpa using hd)] at heq
      exact heq
    · exact hd
    · exact hd
  · intros heq
    subst heq
    rfl

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
theorem Rat.mul_le_mul_cancel_right_of_lt {a b c : Rat} (hc : 0 < c) :
    a * c ≤ b * c ↔ a ≤ b := by
  constructor
  · intros h
    exact Rat.le_of_mul_le_mul_right h hc
  · intros h
    apply Rat.mul_le_mul_of_nonneg_right h <;> grind

@[simp]
theorem Rat.mul_lt_mul_cancel_right_of_lt {a b c : Rat} (hc : 0 < c) :
    a * c < b * c ↔ a < b := by
  constructor
  · intros h
    exact Rat.lt_of_mul_lt_mul_right h (by grind)
  · intros h
    apply Rat.mul_lt_mul_of_pos_right h <;> grind


@[simp]
theorem Rat.div_le_div_self {a b c : Rat} (hc : 0 < c) :
    a / c ≤ b / c ↔ a ≤ b := by
  rw [Rat.div_def, Rat.div_def]
  apply Rat.mul_le_mul_cancel_right_of_lt
  apply Rat.inv_pos .. |>.mpr
  grind

@[simp]
theorem Rat.div_lt_div_self {a b c : Rat} (hc : 0 < c) :
    a / c < b / c ↔ a < b := by
  rw [Rat.div_def, Rat.div_def]
  apply Rat.mul_lt_mul_cancel_right_of_lt
  apply Rat.inv_pos .. |>.mpr
  grind

@[simp]
theorem Rat.add_le_iff_le {a b c : Rat} : a + c ≤ b + c ↔ a ≤ b := by
  grind

@[simp]
theorem Rat.add_le_iff_le' {a b c : Rat} : c + a ≤  c + b ↔ a ≤ b := by
  grind


theorem Rat.lt_add_of_lt_of_nonneg {a b c : Rat} (hab : a < b) (hc : 0 ≤ c) :
  a < b + c := by grind

theorem Rat.le_add_of_le_of_nonneg {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) :
  a ≤ b + c := by grind



@[simp]
theorem
Rat.mul_cancel_left {x y z : Rat} (hx : x ≠ 0) : x * y = x * z ↔ y = z := by
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

theorem Rat.sub_mul (b x y : Rat) : (x - y) * b = x * b - y * b := by
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

@[simp]
theorem Rat.mul_self_pow_eq_pow_succ (a : Rat) (n : Nat) :
  a * a ^ n = a ^ (n + 1) := by
  rw [Rat.mul_comm]
  rw [← Rat.pow_succ]

@[simp]
theorem Rat.mul_self_zpow_eq_zpow_succ {a : Rat} {n : Int}
  (ha : a ≠ 0 := by solve | simp | grind) :
  a * a ^ n = a ^ (n + 1) := by
  rw [Rat.mul_comm]
  rw [Rat.zpow_add]
  · simp
  · simp [ha]

@[simp]
theorem Rat.ne_zero_of_one_le {a : Rat} (h : 1 ≤ a) : a ≠ 0 := by
  apply Classical.byContradiction
  intros hcontra
  simp at hcontra
  subst hcontra
  grind only

@[simp]
theorem Rat.ne_zero_of_one_lt {a : Rat} (h : 1 < a) : a ≠ 0 := by
  apply Classical.byContradiction
  intros hcontra
  simp at hcontra
  subst hcontra
  grind only

/--
Show that `n/d ≤ n` when `n` is nonnegative and `d` is at least 1.
-/
@[simp]
theorem Rat.div_le_self_of_nonneg_of_one_le (n d : Rat)
    (hn : 0 ≤ n) (hd : 1 ≤ d) :
    n / d ≤ n := by
  rw [Rat.div_def]
  suffices n * d⁻¹ ≤ n * 1 from by
    grind
  apply Rat.mul_le_mul_of_nonneg_left
  · suffices d⁻¹ * d ≤ 1 * d from by
      apply Rat.le_of_mul_le_mul_right (c := d)
      exact this
      grind only
    simp [Rat.inv_mul_cancel, hd]
  · grind only

theorem Rat.inv_mul_eq_div {a b : Rat}: a * b⁻¹ = a / b := by
  rw [Rat.div_def]

theorem Rat.mul_inv_eq_div {a b : Rat} : b⁻¹ * a = a / b := by
  rw [Rat.div_def]
  simp [Rat.mul_comm]

@[simp]
theorem Rat.inv_mul_mul_self_cancel {a b : Rat} (hb : b ≠ 0) : b⁻¹ * a * b = a := by
  grind

@[simp]
theorem Rat.inv_mul_mul_self_cancel' {a b : Rat} (hb : b ≠ 0) : b⁻¹ * (a * b) = a := by
  grind

@[simp]
theorem Rat.self_mul_mul_inv_cancel {a b : Rat} (hb : b ≠ 0) : b * a * b⁻¹ = a := by
  grind

@[simp]
theorem Rat.self_mul_mul_inv_cancel' {a b : Rat} (hb : b ≠ 0) : b * (a * b⁻¹) = a := by
  grind

@[simp]
theorem Rat.inv_mul_self_mul_cancel {a b : Rat} (hb : b ≠ 0) : b⁻¹ * (b * a) = a := by
  grind
@[simp]
theorem Rat.self_mul_inv_mul_cancel {a b : Rat} (hb : b ≠ 0) : b * (b⁻¹ * a) = a := by
  grind

/--
Multiplication is positive when both factors are positive.
-/
theorem Rat.mul_positive {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  apply Rat.lt_of_le_of_ne
  · apply Rat.mul_nonneg
    · grind only
    · grind only
  · intros hcontra
    have : a = 0 ∨ b = 0 := by grind
    rcases this with rfl | rfl <;> grind

/--
For positive numbers, the inverse is order-reversing.
-/
theorem Rat.inv_le_inv_of_le_of_positive {a b : Rat} (ha : 0 < a)
    (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  by_cases hb : b = 0
  · simp [hb]
    exact Fp.Rat.inv_nonneg (by grind)
  · by_cases ha : a = 0
    · simp [ha]
      subst ha
      grind
    · apply Rat.le_of_mul_le_mul_right (c := a * b)
      · simp [ha, hb, hab]
      · apply Rat.mul_positive
        · grind only
        · grind only

theorem Rat.inv_eq_div (a : Rat)  : a⁻¹ = 1 / a := by
  grind only

-- TODO: write a simp lemma
theorem Rat.zpow_neg_natCast_eq_one_div_zpow (a : Rat) (n : Nat)
    : a ^ (-n : Int) = 1 / a ^ n := by
  rw [Rat.zpow_neg]
  rw [Rat.inv_eq_div]
  rw [Rat.zpow_natCast]

theorem Rat.one_div_zpow_natCast_eq_zpow_neg (a : Rat) (n : Nat) : 1 / a ^ n = a ^ (- (n : Int)) := by
  rw [Rat.zpow_neg]
  rw [← inv_eq_div]
  simp

theorem Rat.one_div_zpow_eq_zpow_neg (a : Rat) (n : Int) : 1 / a ^ n = a ^ (-n) := by
  rw [Rat.zpow_neg]
  rw [← inv_eq_div]


@[simp]
theorem Rat.inv_zpow_eq_zpow_neg (a : Rat) (n : Int) : (a ^ n)⁻¹ = a ^ (-n) := by
  rw [Rat.inv_eq_div]
  rw [one_div_zpow_eq_zpow_neg]

@[simp]
theorem Rat.inv_zpow_natCast_eq_zpow_neg (a : Rat) (n : Nat) : (a ^ n)⁻¹ = a ^ (- (n : Int)) := by
  rw [Rat.inv_eq_div]
  rw [one_div_zpow_natCast_eq_zpow_neg]

theorem Rat.zpow_mul_zpow {a : Rat} (ha : a ≠ 0) (x y : Int) : a ^ x * a ^ y = a ^ (x + y) := by
  rw [Rat.zpow_add ha]

theorem Rat.zpow_div_zpow {a : Rat} (ha : a ≠ 0) (x y : Int) : a ^ x / a ^ y = a ^ (x - y) := by
  rw [zpow_sub_eq_zpow_mul_zpow ha x y]
  rw [Rat.div_def]
  rw [Rat.inv_zpow_eq_zpow_neg]

theorem Rat.div_zpow_eq_zpow_neg {n a : Rat} (i : Int) : n / a ^ i = n * a ^ (-i) := by
  rw [Rat.div_def]
  rw [Rat.inv_zpow_eq_zpow_neg]

theorem Rat.div_zpow_natCast_eq_zpow_neg {n a : Rat} (i : Nat) : n / a ^ i = n * a ^ (- (i : Int)) := by
  rw [Rat.div_def]
  rw [Rat.inv_zpow_natCast_eq_zpow_neg]

@[simp]
theorem Rat.natCast_sub_of_le {m n : Nat} (h : m ≤ n) :
  ((n - m : Nat) : Rat) = n - m := by
  have : ∃ k : Nat, n = m + k := by
    apply Nat.exists_eq_add_of_le
    exact h
  obtain ⟨k, hk⟩ := this
  subst hk
  simp
  grind only

theorem Rat.sub_div_eq_div_sub_div {a b c : Rat} :
  (a - b) / c = a / c - b / c := by
  grind only

theorem Rat.div_self_eq_one_of_ne_zero {a : Rat} (ha : a ≠ 0) : a / a = 1 := by
  grind

theorem Rat.div_self_eq_ite {a : Rat} : a / a = (if a = 0 then 0 else 1) := by
  grind

@[simp]
theorem Rat.neg_ne_zero_iff_ne_zero {a : Rat} : -a ≠ 0 ↔ a ≠ 0 := by
  grind

@[simp]
theorem Rat.neg_eq_zero_iff_eq_zero {a : Rat} : -a = 0 ↔ a = 0 := by
  grind


@[simp, grind =]
theorem Rat.mul_mul_eq_zero_iff_eq_zero_right {a b c : Rat}
  (ha : a ≠ 0) (hb : b ≠ 0) :
  a * b * c = 0 ↔ c = 0 := by grind

@[simp, grind =]
theorem Rat.mul_mul_eq_zero_iff_eq_zero_left {a b c : Rat}
  (hb : b ≠ 0) (hc : c ≠ 0) :
  a * b * c = 0 ↔ a = 0 := by grind

@[simp, grind =]
theorem Rat.mul_mul_eq_zero_iff_eq_zero_middle {a b c : Rat}
  (ha : a ≠ 0) (hc : c ≠ 0) :
  a * b * c = 0 ↔ b = 0 := by grind

@[simp]
theorem Rat.mul_eq_zero_iff_eq_zero₃ {a b c : Rat} :
  a * b * c = 0 ↔ a = 0 ∨ b = 0 ∨ c = 0 := by
  grind

theorem Rat.mul_eq_zero_iff_eq_zero₂ {a b : Rat} :
  a * b = 0 ↔ a = 0 ∨ b = 0 := by
  grind

@[simp]
theorem Rat.mul_ne_zero_iff_ne_zero₂ {a b : Rat} :
  a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  grind

@[simp]
theorem Rat.mul_ne_zero_iff_ne_zero₃ {a b c : Rat} :
  a * b * c ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
  grind

@[simp]
theorem neg_eq_neg_iff_eq {a b : Rat} : -a = -b ↔ a = b := by
  grind

/-! ## Utilities ported from DivisionFixed.lean

These support `fixedWidthDivideAtPrecision_abs_delta_eq` and similar
"truncated quotient is within one ULP of the real division" arguments. -/

theorem Rat.add_div (a b c : Rat) :
    (a + b) / c = a / c + b / c := by
  grind

theorem Rat.mul_div_cancel_left
    (a c : Rat) (hc : c ≠ 0) :
    (c * a) / c = a := by
  grind

theorem Rat.mul_div_cancel_right
    (a c : Rat) (hc : c ≠ 0) :
    (a * c) / c = a := by
  grind

@[simp]
theorem Rat.ofNat_one_eq_one :
    Rat.ofNat 1 = 1 := by
  simp [Rat.ofNat, Rat.ofInt]

theorem Rat.ofNat_one_div_eq_inv_ofNat
    (b : Nat) :
    Rat.ofNat 1 / Rat.ofNat b  = (Rat.ofNat b)⁻¹ := by
  rw [Rat.ofNat_one_eq_one]
  rw [Rat.div_def]
  grind

theorem Rat.twoPowInv_eq_inv (prec : Nat) :
    Rat.twoPowInv prec = (Rat.ofNat (2 ^ prec))⁻¹ := by
  simp only [Rat.twoPowInv]
  rw [Rat.ofNat_one_eq_one]
  rw [Rat.div_def]
  grind

theorem Rat.ofNat_two_pow_mul_twoPowInv_eq (n : Nat) (prec : Nat) :
    Rat.ofNat (n * 2 ^ prec) * Rat.twoPowInv prec = Rat.ofNat n := by
  rw [Rat.twoPowInv]
  rw [Rat.ofNat_mul]
  simp only [ofNat_one_eq_one]
  rw [Rat.div_def]
  simp only [Rat.one_mul]
  grind

theorem Rat.mul_inv_cancel_right'
    {a b : Rat} (hb : b ≠ 0 := by grind) :
    a * b * b⁻¹ = a := by
  rw [Rat.mul_assoc]
  rw [Rat.mul_inv_cancel]
  · grind
  · grind

/-- The gap between `y` and the floor approximation `⌊y*k⌋ * k⁻¹` is at most `k⁻¹`. -/
theorem Rat.self_sub_mul_floor_inv_le {y k  : Rat} (hk : 0 < k := by grind) :
    y  - (y * k).floor * k⁻¹ ≤ k⁻¹ := by
  have : (y * k) < (((y * k).floor + 1) : Int) := by
    apply Rat.lt_floor_add_one
  have := (calc
    (y * k) * k⁻¹ < (((y * k).floor + 1) : Int) * k⁻¹ := by
      apply Rat.mul_lt_mul_right .. |>.mpr
      · grind
      · apply Rat.inv_pos.mpr
        grind)
  have : y < (((y * k).floor + 1) : Int) * k⁻¹ := by
    rw [Rat.mul_assoc] at this
    rw [Rat.mul_inv_cancel] at this
    · grind
    · grind
  simp at this
  rw [Rat.add_mul] at this
  simp at this
  grind

@[simp]
theorem Rat.num_ofNat' (n : Nat) :
    (Rat.ofNat n).num = n := by
  simp [Rat.ofNat, Rat.ofInt]

@[simp]
theorem Rat.den_ofNat' (n : Nat) :
    (Rat.ofNat n).den = 1 := by
  simp [Rat.ofNat, Rat.ofInt]

theorem Rat.ofNat_div_ofNat_eq_mkRat {a b : Nat}  :
      Rat.ofNat a / Rat.ofNat b = mkRat a b := by
  rw [Rat.mkRat_eq_div]
  simp [Rat.ofNat, Rat.ofInt]
  by_cases hb : b  = 0
  · simp [hb]
  · norm_cast

/-- Natural number division agrees with the floor of the rational division. -/
theorem Rat.ofNat_div_ofNat_eq_floor_div {a b : Nat} (hb : b > 0 := by grind):
      Rat.ofNat (a / b) = (Rat.ofNat a / Rat.ofNat b).floor := by
  rw [Rat.floor_def]
  rw [Rat.ofNat_div_ofNat_eq_mkRat]
  simp [Rat.num_mkRat, Rat.den_mkRat]
  by_cases hb : b = 0
  · grind
  · simp only [hb, ↓reduceIte]
    rw [Nat.gcd_comm b a]
    norm_cast
    rw [Nat.gcd_div_gcd_eq]
    rfl

/-- Uniqueness of the normalized binary representation: if `a · 2^p = b · 2^q`
with the significands `a, b` in the normalized band `[2^(s-1), 2^s)`, then both
the significand and the binary exponent are determined (`a = b` and `p = q`).

Proof: WLOG `p ≤ q`. Cancelling `2^p` gives `a = b · 2^(q-p)` as naturals; if
`q - p ≥ 1` then `a = b · 2^(q-p) ≥ 2^(s-1) · 2 = 2^s`, contradicting `a < 2^s`.
So `p = q`, and then `a = b`. -/
theorem Rat.mul_two_zpow_inj {s a b : Nat} {p q : Int}
    (ha : 2 ^ (s - 1) ≤ a) (ha' : a < 2 ^ s)
    (hb : 2 ^ (s - 1) ≤ b) (hb' : b < 2 ^ s)
    (h : (a : Rat) * (2 : Rat) ^ p = (b : Rat) * (2 : Rat) ^ q) :
    a = b ∧ p = q := by
  -- a one-sided helper, applied in both orders to get the symmetric statement.
  suffices aux : ∀ (a b : Nat) (p q : Int), a < 2 ^ s → 2 ^ (s - 1) ≤ b →
      (a : Rat) * (2 : Rat) ^ p = (b : Rat) * (2 : Rat) ^ q → p ≤ q → a = b ∧ p = q by
    rcases (by omega : p ≤ q ∨ q ≤ p) with hpq | hqp
    · exact aux a b p q ha' hb h hpq
    · obtain ⟨hba, hqp'⟩ := aux b a q p hb' ha h.symm hqp
      exact ⟨hba.symm, hqp'.symm⟩
  clear ha ha' hb hb' h a b p q
  intro a b p q ha' hb h hpq
  have hkk : (((q - p).toNat : Nat) : Int) = q - p := Int.toNat_of_nonneg (by omega)
  -- cancel `2^p`: `a = b * 2^(q-p)` over `Rat`
  have hcancel : (a : Rat) = (b : Rat) * (2 : Rat) ^ (q - p) := by
    have hp0 : (2 : Rat) ^ p ≠ 0 := by have := Fp.Rat.two_pow_pos p; grind
    have hzeq : (2 : Rat) ^ q = (2 : Rat) ^ (q - p) * (2 : Rat) ^ p := by
      rw [← Rat.zpow_add (by decide : (2 : Rat) ≠ 0)]; congr 1; omega
    rw [hzeq, ← Rat.mul_assoc] at h
    grind
  -- convert to the natural-number equation `a = b * 2^(q-p).toNat`
  have hzc : (2 : Rat) ^ (q - p) = ((2 ^ (q - p).toNat : Nat) : Rat) := by
    rw [show q - p = (((q - p).toNat : Nat) : Int) from hkk.symm, Rat.zpow_natCast]
    norm_cast
  rw [hzc] at hcancel
  have hnat : a = b * 2 ^ (q - p).toNat := by exact_mod_cast hcancel
  -- the band bounds force the exponent gap to be `0`
  have hk0 : (q - p).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (q - p).toNat with h0 | hk1
    · exact h0
    · exfalso
      have hge : 2 ^ (s - 1) * 2 ^ (q - p).toNat ≤ b * 2 ^ (q - p).toNat :=
        Nat.mul_le_mul_right _ hb
      have hadd : 2 ^ (s - 1) * 2 ^ (q - p).toNat = 2 ^ (s - 1 + (q - p).toNat) :=
        (Nat.pow_add 2 (s - 1) (q - p).toNat).symm
      have hmono : 2 ^ s ≤ 2 ^ (s - 1 + (q - p).toNat) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ s ≤ a := by rw [hnat]; omega
      omega
  refine ⟨?_, by omega⟩
  rw [hnat, hk0]; simp

/-- Ordering of normalized binary representations: with significands `a, b` in
the normalized band `[2^(s-1), 2^s)`, the magnitude `a · 2^p` is ordered
lexicographically by `(p, a)`. This is the strict-ordering analogue of
`Rat.mul_two_zpow_inj`.

Proof: the only nontrivial step is `p < q ⇒ a·2^p < b·2^q`, which holds because
`a·2^p < 2^s·2^p = 2^(s+p) ≤ 2^((s-1)+q) = 2^(s-1)·2^q ≤ b·2^q` (using `p+1 ≤ q`
and `s ≤ (s-1)+1`). The full iff then follows by trichotomy on `p` vs `q`. -/
theorem Rat.mul_two_zpow_lt {s a b : Nat} {p q : Int}
    (ha : 2 ^ (s - 1) ≤ a) (ha' : a < 2 ^ s)
    (hb : 2 ^ (s - 1) ≤ b) (hb' : b < 2 ^ s) :
    ((a : Rat) * (2 : Rat) ^ p < (b : Rat) * (2 : Rat) ^ q) ↔ (p < q ∨ (p = q ∧ a < b)) := by
  -- the strict step `p < q ⇒ a·2^p < b·2^q`, applied in both orders below.
  have aux : ∀ (a b : Nat) (p q : Int), a < 2 ^ s → 2 ^ (s - 1) ≤ b → p < q →
      (a : Rat) * (2 : Rat) ^ p < (b : Rat) * (2 : Rat) ^ q := by
    intro a b p q ha' hb hpq
    have h2p : (0 : Rat) < (2 : Rat) ^ p := Fp.Rat.two_pow_pos p
    have h2q : (0 : Rat) < (2 : Rat) ^ q := Fp.Rat.two_pow_pos q
    -- `a·2^p < 2^s·2^p`
    have step1 : (a : Rat) * (2 : Rat) ^ p < ((2 ^ s : Nat) : Rat) * (2 : Rat) ^ p :=
      (Rat.mul_lt_mul_cancel_right_of_lt h2p).mpr (by exact_mod_cast ha')
    -- collapse the `2^k · 2^r` products into single powers
    have e1 : ((2 ^ s : Nat) : Rat) * (2 : Rat) ^ p = (2 : Rat) ^ ((s : Int) + p) := by
      rw [Rat.zpow_add (by decide : (2 : Rat) ≠ 0)]
      congr 1
      rw [Rat.zpow_natCast]; norm_cast
    have e2 : ((2 ^ (s - 1) : Nat) : Rat) * (2 : Rat) ^ q
        = (2 : Rat) ^ (((s - 1 : Nat) : Int) + q) := by
      rw [Rat.zpow_add (by decide : (2 : Rat) ≠ 0)]
      congr 1
      rw [Rat.zpow_natCast]; norm_cast
    have hmono : (2 : Rat) ^ ((s : Int) + p) ≤ (2 : Rat) ^ (((s - 1 : Nat) : Int) + q) :=
      Rat.two_pow_le_two_pow_of_le (by omega)
    have hbq : ((2 ^ (s - 1) : Nat) : Rat) * (2 : Rat) ^ q ≤ (b : Rat) * (2 : Rat) ^ q :=
      (Rat.mul_le_mul_cancel_right_of_lt h2q).mpr (by exact_mod_cast hb)
    have key : ((2 ^ s : Nat) : Rat) * (2 : Rat) ^ p ≤ (b : Rat) * (2 : Rat) ^ q :=
      calc ((2 ^ s : Nat) : Rat) * (2 : Rat) ^ p
          = (2 : Rat) ^ ((s : Int) + p) := e1
        _ ≤ (2 : Rat) ^ (((s - 1 : Nat) : Int) + q) := hmono
        _ = ((2 ^ (s - 1) : Nat) : Rat) * (2 : Rat) ^ q := e2.symm
        _ ≤ (b : Rat) * (2 : Rat) ^ q := hbq
    grind
  constructor
  · intro h
    rcases (by omega : p < q ∨ p = q ∨ q < p) with hlt | heq | hgt
    · exact Or.inl hlt
    · subst heq
      have h2p : (0 : Rat) < (2 : Rat) ^ p := Fp.Rat.two_pow_pos p
      have : (a : Rat) < (b : Rat) := (Rat.mul_lt_mul_cancel_right_of_lt h2p).mp h
      exact Or.inr ⟨rfl, by exact_mod_cast this⟩
    · exact absurd (aux b a q p hb' ha hgt) (by grind)
  · rintro (hlt | ⟨heq, hab⟩)
    · exact aux a b p q ha' hb hlt
    · subst heq
      have h2p : (0 : Rat) < (2 : Rat) ^ p := Fp.Rat.two_pow_pos p
      exact (Rat.mul_lt_mul_cancel_right_of_lt h2p).mpr (by exact_mod_cast hab)


@[simp]
theorem Rat.one_lt_two_pow_iff (x : Nat) : 1 < (2 : Rat) ^ x ↔ 1 ≤ x := by
  constructor
  · intros hlt
    have : x = 0 ∨ 1 ≤ x := by grind
    rcases this with rfl | this
    · grind
    · grind
  · intros hlt
    norm_cast
    have : ∃ y, x = y + 1 := by exact Nat.exists_eq_add_one.mpr hlt
    obtain ⟨y, hy⟩ := this
    subst hy
    simp
theorem Rat.div_le_of_le_mul (a b c : Rat) (hc : 0 < c) (hle : a ≤ b * c) : a / c ≤ b := by
  rw [Rat.div_def]
  apply Rat.mul_le_mul_cancel_right_of_lt (c := c) .. |>.mp
  · rw [show a * c⁻¹ * c = a by grind only]
    grind only
  · grind only
@[simp]
theorem Rat.div_add_eq_div_add_div (a b c : Rat) : a / c + b / c = (a + b) / c := by
  grind
@[simp]
theorem Rat.div_lt_cancel {a b c : Rat} (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [Rat.div_def, Rat.div_def]
  constructor
  · intros hlt
    rw [Rat.mul_lt_mul_right ] at hlt
    · grind only
    · grind only [= Rat.inv_pos]
  · intros hlt
    rw [Rat.mul_lt_mul_right]
    · grind only
    · grind only [= Rat.inv_pos]
@[simp]
theorem Rat.div_le_cancel {a b c : Rat} (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b := by
  rw [Rat.div_def, Rat.div_def]
  constructor
  · intros hle
    rw [Rat.mul_le_mul_cancel_right_of_lt] at hle
    · grind only
    · grind only [= Rat.inv_pos]
  · intros hle
    rw [Rat.mul_le_mul_cancel_right_of_lt]
    · grind only
    · grind only [= Rat.inv_pos]
theorem Rat.add_div_eq_add_div' (a b d : Rat)(hd : d ≠ 0) :
  a + b / d = (a * d + b) / d := by
  grind
attribute [grind .] Rat.natCast_eq_zero_iff
@[simp]
theorem Rat.natCast_ne_zero_iff {n : Nat} : ((n : Rat) ≠ 0) ↔ n ≠ 0 := by
  grind
theorem Rat.lt_mul_self_of_lt_one {y} {x : Rat} (hx0 : 0 ≤ x ∧ x < 1) (hy : 0 < y)
    : x * y < y := by
  suffices x * y < 1 * y by grind only
  apply Rat.lt_of_le_of_ne
  · apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg <;> grind only
  · intros hcontra
    rw [Rat.mul_cancel_right] at hcontra <;> grind only


/-- `ofNat (d*k + r) / ofNat d = ofNat k + ofNat (r%d) / ofNat d`, the "subdivide"
    of a Nat sum-with-remainder. Cleanly handles the case in the abs_delta proof. -/
theorem Rat.ofNat_mul_add_div_ofNat_eq {d k r : Nat} (hd : d ≠ 0) (hrd : r < d) :
    Rat.ofNat (d * k + r) / Rat.ofNat d
      = Rat.ofNat k + Rat.ofNat (r % d) / Rat.ofNat d := by
  rw [Rat.ofNat_div_ofNat_eq_ofNat_div_add_ofNat_mod _ _ hd]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hd)]
  rw [Nat.add_mul_mod_self_left]
  rw [Rat.ofNat_add]
  have hrlt : r / d ≤ k + r / d := Nat.le_add_left _ _
  simp [Rat.ofNat_eq_coe]
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.div_eq_of_lt]
    · grind
    · grind
  · grind
/-- Specialised: `ofNat (d * k + r) / ofNat d = ofNat k + ofNat r / ofNat d` when r < d. -/
theorem Rat.ofNat_mul_add_div_ofNat_eq_of_lt {d k r : Nat} (hd : d ≠ 0) (hr : r < d) :
    Rat.ofNat (d * k + r) / Rat.ofNat d
      = Rat.ofNat k + Rat.ofNat r / Rat.ofNat d := by
  rw [Rat.ofNat_mul_add_div_ofNat_eq (by grind) (by grind)]
  rw [Nat.mod_eq_of_lt hr]
theorem Rat.zpow_succ {q : Rat} (hq : q ≠ 0) {a : Int} : q ^ (a + 1) = q ^ a * q := by
  exact Rat.zpow_add_one hq a
theorem Rat.mul_add_self (a b : Rat) : a * b + a = a * (b + 1) := by
  rw [Rat.mul_add]
  simp
theorem Rat.zpow_sub {q : Rat} (hq : q ≠ 0) {a b : Int} : q ^ (a - b) = q ^ a * q ^ (-b) := by
  rw [Int.sub_eq_add_neg]
  rw [Rat.zpow_add hq]
