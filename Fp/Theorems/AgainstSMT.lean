import Fp

@[bv_normalize]
def twoE3M4 : PackedFloat 3 4 := PackedFloat.ofBits 3 4 0b01000000#8
@[bv_normalize]
def oneE3M4 : PackedFloat 3 4 := PackedFloat.ofBits 3 4 0b00110000#8

theorem add_comm (a b : PackedFloat 3 4)
  : (a + b) = (b + a) := by
  bv_decide

theorem add_monotone (a b c : PackedFloat 3 4) (hc : c.isNormOrSubnorm)
  : PackedFloat.smtBle a b → PackedFloat.smtBle (a + c) (b + c) := by
  bv_decide

theorem add_eq_mul_two (a : PackedFloat 3 4)
  : a + a = twoE3M4 * a := by
  bv_decide

theorem mul_comm (a b : PackedFloat 3 4)
  : a * b = b * a := by
  bv_decide

theorem mul_one_is_id (a : PackedFloat 3 4)
  (h : ¬a.isNaN)
  : a * oneE3M4 = a := by
  bv_decide

theorem div_one_is_id (a : PackedFloat 3 4)
  (h : ¬a.isNaN)
  : a / oneE3M4 = a := by
  bv_decide

theorem div_self_is_one (a : PackedFloat 3 4)
  (h : ¬a.isNaN ∧ ¬a.isInfinite ∧ ¬a.isZero)
  : a / a = oneE3M4 := by
  bv_decide

theorem rem_lt_abs_self (a b : PackedFloat 3 4)
  (h : a.isNormOrSubnorm)
  (hb : ¬b.isNaN ∧ ¬b.isZero)
  : PackedFloat.smtBlt (remainder a b) (b.abs) := by
  bv_decide
