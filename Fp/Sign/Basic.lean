import Fp.Grind

@[grind .]
def Bool.toSign (b : Bool) : Int :=
  if b then -1 else 1

@[simp]
theorem toSign_true : Bool.toSign true = -1 := rfl

@[simp]
theorem toSign_false : Bool.toSign false = 1 := rfl

@[simp]
theorem Bool.toSign_ne_zero (b : Bool) : b.toSign ≠ 0 := by
  cases b <;> simp [Bool.toSign]

theorem Bool.toSign_lt_zero_iff (b : Bool) : b.toSign < 0 ↔ b = true := by
  cases b <;> simp [Bool.toSign]

@[simp]
theorem toSign_xor_eq_toSign_mul_toSign (a b : Bool) :
  (a ^^ b).toSign = a.toSign * b.toSign := by grind [Bool.toSign]

@[simp]
theorem toSign_not_eq_neg_toSign (b : Bool) : (!b).toSign = - b.toSign := by
  cases b <;> simp [Bool.toSign]
