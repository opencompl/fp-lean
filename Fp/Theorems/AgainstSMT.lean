import Fp

@[bv_normalize]
def twoE3M4 : PackedFloat 3 4 := PackedFloat.ofBits 3 4 0b01000000#8
@[bv_normalize]
def oneE3M4 : PackedFloat 3 4 := PackedFloat.ofBits 3 4 0b00110000#8

theorem add_comm (a b : PackedFloat 3 4)
  : (add a b .RNE) = (add b a .RNE) := by
  bv_decide

theorem add_monotone (a b c : PackedFloat 3 4) (hc : c.isNormOrSubnorm)
  : le a b → le (add a c .RNE) (add b c .RNE) := by
  bv_decide

theorem add_eq_mul_two (a : PackedFloat 3 4)
  : add a a .RNE = mul twoE3M4 a .RNE := by
  bv_decide

theorem mul_comm (a b : PackedFloat 3 4)
  : (mul a b .RNE) = (mul b a .RNE) := by
  bv_decide

theorem mul_one_is_id (a : PackedFloat 3 4)
  (h : ¬a.isNaN)
  : eq (mul a oneE3M4 .RNE) a := by
  bv_decide

theorem div_one_is_id (a : PackedFloat 3 4)
  (h : ¬a.isNaN)
  : eq (div a oneE3M4 .RNE) a := by
  bv_decide

theorem div_self_is_one (a : PackedFloat 3 4)
  (h : ¬a.isNaN ∧ ¬a.isInfinite ∧ ¬a.isZero)
  : (div a a .RNE) = oneE3M4 := by
  bv_decide

theorem rem_lt_abs_self (a b : PackedFloat 3 4)
  (h : a.isNormOrSubnorm)
  (hb : ¬b.isNaN ∧ ¬b.isZero)
  : lt (remainder a b) (abs b) := by
  bv_decide
