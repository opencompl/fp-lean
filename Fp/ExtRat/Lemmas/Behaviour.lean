import Fp.ExtRat.Lemmas.Order

/-!
## ExtRat SMT-LIB behaviour lemmas

NaN/defined-symbol/infinity behaviour specs plus remaining order/negation/abs/isNaN lemmas.
-/

namespace ExtRat

section NanBehaviour

/-# Table 1 of SMT-LIB spec -/

@[simp]
theorem NaN_add (x : ExtRat) : (.NaN + x) = .NaN := by
  rw [← ExtRat.add_def, ExtRat.add]

@[simp]
theorem add_NaN (x : ExtRat) : (x + .NaN) = ExtRat.NaN := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

@[simp]
theorem neg_NaN : -ExtRat.NaN = ExtRat.NaN := by
  rw [← ExtRat.neg_def, ExtRat.neg]

@[simp]
theorem NaN_mul (x : ExtRat) : (.NaN * x) = .NaN := by
  rw [← ExtRat.mul_def, ExtRat.mul]

@[simp]
theorem mul_NaN (x : ExtRat) : (x * .NaN) = .NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind [ExtRat]

@[simp, grind =]
theorem le_NaN (x : ExtRat) : ExtRat.NaN ≤ x ↔ x = ExtRat.NaN := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

@[simp, grind =]
theorem NaN_le (x : ExtRat) : x ≤ ExtRat.NaN ↔ x = ExtRat.NaN := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

end NanBehaviour

section DefinedSymbolsBehaviour
/-# Table 2 -/

theorem sub_eq_add_neg (x y : ExtRat) : (x - y) = (x + -y) := by
  rw [← ExtRat.sub_def, ← ExtRat.add_def, ← ExtRat.neg_def]
  unfold ExtRat.sub
  grind

theorem div_eq_mul_inv (x y : ExtRat) : (x / y) = (x * y.inv) := by
  rw [← ExtRat.div_def, ← ExtRat.mul_def]
  unfold ExtRat.div
  grind

@[simp]
theorem ge_eq_le_symm (x y : ExtRat) : (x ≥ y) = (y ≤ x) := by
  simp only [(· ≥ ·)]

theorem lt_eq_le_and_not_eq (x y : ExtRat) : (x < y) = (x ≤ y ∧ ¬ (x = y)) := by
  simp only [(· < ·), (· ≤ ·)]
  unfold ExtRat.lt ExtRat.le ExtRat.eq
  grind

theorem gt_eq_ge_and_not_eq (x y : ExtRat) : (x > y) = (x ≥ y ∧ ¬ (x = y)) := by
  simp only [(· > ·), (· ≥ ·), (· < ·), (· ≤ ·)]
  unfold ExtRat.le ExtRat.lt ExtRat.le ExtRat.eq
  grind

end DefinedSymbolsBehaviour
section InfinityBehaviour
/-# Table 3 -/

@[simp]
theorem plus_inf_le_iff_eq (x : ExtRat) : (.Infinity false ≤ x) ↔ x = .Infinity false := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem le_neg_inf_iff_eq (x : ExtRat) : (x ≤ .Infinity true) ↔ x = .Infinity true := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem number_le_plus_inf (r : Rat) : (ExtRat.Number r ≤ ExtRat.Infinity false) := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem neg_inf_le_number (r : Rat) : (ExtRat.Infinity true ≤ ExtRat.Number r) := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

@[simp]
theorem neg_plus_inf_eq_minus_inf : - (ExtRat.Infinity false) = (ExtRat.Infinity true) := by
  rw [← ExtRat.neg_def]
  unfold ExtRat.neg
  grind

@[simp]
theorem neg_minus_inf_eq_plus_inf : - (ExtRat.Infinity true) = (ExtRat.Infinity false) := by
  rw [← ExtRat.neg_def]
  unfold ExtRat.neg
  grind

@[simp]
theorem inv_plus_inf_eq_zero : (ExtRat.Infinity false).inv = ExtRat.Number 0 := by
  unfold ExtRat.inv
  grind

@[simp]
theorem inv_minus_inf_eq_zero : (ExtRat.Infinity true).inv = ExtRat.Number 0 := by
  unfold ExtRat.inv
  grind

@[simp]
theorem inv_inf_eq_zero (s : Bool) : (ExtRat.Infinity s).inv = ExtRat.Number 0 := by
  unfold ExtRat.inv
  grind

theorem add_comm (x y : ExtRat) : x + y = y + x := by
  rw [← ExtRat.add_def, ← ExtRat.add_def]
  unfold ExtRat.add
  grind

@[simp]
theorem add_inf_eq_inf_of_ne_of_ne (x : ExtRat)
    (hxInf : x ≠ .Infinity true) (hxNan : x ≠ .NaN) :
    x + .Infinity false = .Infinity false := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

@[simp]
theorem add_inf_eq_nan_of_eq (x : ExtRat) (hxInf : x = .Infinity true) :
    x + .Infinity false = .NaN := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

theorem add_neg_inf_eq_nan_of_eq (x : ExtRat) (hxInf : x = .Infinity false) :
    x + .Infinity true = .NaN := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

theorem add_neg_inf_eq_neg_inf_of_ne_of_ne (x : ExtRat)
    (hxInf : x ≠ .Infinity false) (hxNan : x ≠ .NaN) :
    x + .Infinity true = .Infinity true := by
  rw [← ExtRat.add_def]
  unfold ExtRat.add
  grind [ExtRat]

/-- +∞ × +∞ = +∞-/
@[simp]
theorem inf_mul_inf_eq_inf :
    ExtRat.Infinity false * ExtRat.Infinity false = ExtRat.Infinity false := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- +∞ × -∞ = -∞-/
@[simp]
theorem inf_mul_neg_inf_eq_neg_inf :
    ExtRat.Infinity false * ExtRat.Infinity true = ExtRat.Infinity true := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- -∞ × +∞ = -∞-/
@[simp]
theorem neg_inf_mul_inf_eq_neg_inf :
    ExtRat.Infinity true * ExtRat.Infinity false = ExtRat.Infinity true := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- -∞ × -∞ = +∞-/
@[simp]
theorem neg_inf_mul_neg_inf_eq_inf :
    ExtRat.Infinity true * ExtRat.Infinity true = ExtRat.Infinity false := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- ±∞ × 0 = NaN -/
@[simp]
theorem inf_mul_zero_eq_nan :
    ExtRat.Infinity b * ExtRat.Number 0 = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- ±∞ × NaN = NaN -/
@[simp]
theorem inf_mul_nan_eq_nan :
    ExtRat.Infinity b * ExtRat.NaN = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

/-- positive × +∞ = +∞ -/
@[simp]
theorem mul_inf_eq_inf_of_lt (x : ExtRat)
    (hxNan : x ≠ .NaN) (hxZero : 0 < x) :
    x * .Infinity false = .Infinity false := by
  rw [← ExtRat.mul_def]
  rw [← ExtRat.lt_def, ← ExtRat.zero_def] at hxZero
  unfold ExtRat.mul
  unfold ExtRat.lt ExtRat.le ExtRat.eq at hxZero
  grind [ExtRat]

/-- negative × +∞ = -∞ -/
theorem mul_inf_eq_neg_inf_of_lt (x : ExtRat)
    (hxNan : x ≠ .NaN) (hxZero : x < 0) :
    x * .Infinity false = .Infinity true := by
  rw [← ExtRat.mul_def]
  rw [← ExtRat.lt_def, ← ExtRat.zero_def] at hxZero
  unfold ExtRat.mul
  unfold ExtRat.lt ExtRat.le ExtRat.eq at hxZero
  -- grind [ExtRat] TODO: why doesn't grind work here?
  cases x
  · grind
  · grind
  · -- grind -- theory propagation does not work properly here,
    -- the rational fact 'a < 0' is not deduced
    simp only [Bool.false_bne]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      beq_eq_false_iff_ne, ne_eq] at hxZero
    simp only [hxZero, ↓reduceIte, Infinity.injEq, decide_eq_true_eq]
    grind

@[simp]
theorem number_mul_number_eq : ExtRat.Number r1 * ExtRat.Number r2 = ExtRat.Number (r1 * r2) := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem zero_mul_inf_eq : ExtRat.Number 0 * ExtRat.Infinity sign = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem inf_mul_zero_eq : ExtRat.Infinity sign * ExtRat.Number 0 = ExtRat.NaN := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem zero_mul_zero_eq_zero : ExtRat.Number 0 * ExtRat.Number 0 = ExtRat.Number 0 := by
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

@[simp]
theorem zero_inv_eq_inf : (ExtRat.Number 0).inv = ExtRat.Infinity false := by
  unfold ExtRat.inv
  grind


theorem mul_comm (x y : ExtRat) : x * y = y * x := by
  rw [← ExtRat.mul_def, ← ExtRat.mul_def]
  unfold ExtRat.mul
  grind

end InfinityBehaviour

theorem le_refl (x : ExtRat) : x ≤ x := by
  rw [← ExtRat.le_def]
  unfold ExtRat.le
  grind

theorem le_trans {x y z : ExtRat} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  rw [← ExtRat.le_def] at hxy hyz ⊢
  unfold ExtRat.le at hxy hyz ⊢
  grind

theorem le_antisymm {x y : ExtRat} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rw [← ExtRat.le_def] at hxy hyx
  unfold ExtRat.le at hxy hyx
  grind

/-! ## ExtRat negation theory -/

@[simp]
theorem neg_eq_NaN_iff (r : ExtRat) : -r = .NaN ↔ r = .NaN := by
  cases r <;> simp [← ExtRat.neg_def, ExtRat.neg]

@[simp, grind =]
theorem neg_neg (x : ExtRat) : -(-x) = x := by
  rw [← ExtRat.neg_def, ← ExtRat.neg_def]
  unfold ExtRat.neg
  grind

/--
Negation reverses the ordering on `ExtRat`: `x ≤ y ↔ -y ≤ -x`.
-/
theorem le_iff_neg_le_neg {x y : ExtRat} :
    x ≤ y ↔ -y ≤ -x := by
  cases x <;> cases y <;> simp [← ExtRat.le_def, ← ExtRat.neg_def, ExtRat.neg, ExtRat.le] <;> grind

/--
`x ≤ -y ↔ y ≤ -x`: move negation across `≤` from right to left.
-/
@[grind =]
theorem le_neg_iff_le_neg {x y : ExtRat} :
    x ≤ -y ↔ y ≤ -x := by
  rw [le_iff_neg_le_neg (x := x) (y := -y)]
  simp [neg_neg]

/--
`-x ≤ y ↔ -y ≤ x`: move negation across `≤` from left to right.
-/
@[grind =]
theorem neg_le_iff_neg_le {x y : ExtRat} :
    -x ≤ y ↔ -y ≤ x := by
  rw [le_iff_neg_le_neg (x := -x) (y := y)]
  simp [neg_neg]

/--
Negation is antitone: if `x ≤ y` then `-y ≤ -x`.
-/
@[simp]
theorem neg_le_neg {x y : ExtRat} (h : x ≤ y) : -y ≤ -x :=
  le_iff_neg_le_neg.mp h

@[simp]
theorem isNaN_iff (r : ExtRat) : isNaN r = decide (r = .NaN) := by
  simp [isNaN]
@[simp] theorem isNaN_NaN : isNaN ExtRat.NaN = true := rfl
@[simp] theorem isNaN_infinity (s : Bool) : isNaN (.Infinity s) = false := rfl
@[simp] theorem isNaN_number (r : Rat) : isNaN (.Number r) = false := rfl


@[simp]
theorem abs_NaN : abs ExtRat.NaN = ExtRat.NaN := by
  simp [abs]

theorem abs_infinity (s : Bool) : abs (.Infinity s) = .Infinity false := by
  simp [abs]

@[simp]
theorem abs_Number (n : Rat) : abs (.Number n) = .Number (n.abs) := by
  simp [abs]

instance : Std.IsPartialOrder ExtRat where
  le_refl := le_refl
  le_trans := by grind [le_trans]
  le_antisymm := by grind [le_antisymm]

end ExtRat
