namespace Fp

attribute [simp] Rat.not_lt

attribute [grind .] Rat.pow_pos
attribute [grind .] Rat.pow_nonneg
attribute [grind .] Rat.le_of_lt
attribute [grind .] Rat.mul_nonneg
attribute [grind =] Rat.inv_pos
-- attribute [grind] Rat.zpow_pos
-- attribute [simp] Rat.inv_inv

attribute [grind →] Rat.mul_pos


@[grind ., grind →] -- I may also want grind → to know that a ⁻¹ is positive when a is positive.
theorem Rat.inv_nonneg {a : Rat} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  by_cases ha0 : a = 0 <;> grind

@[grind .]
theorem Rat.div_nonneg (a b : Rat) (hb : 0 ≤ b) (ha : 0 ≤ a) : 0 ≤ a / b := by grind

@[grind .]
theorem Rat.div_pos (a b : Rat) (hb : 0 < b) (ha : 0 < a) : 0 < a / b := by
  apply (Rat.lt_div_iff hb).mpr
  simp
  grind

@[grind .]
theorem Rat.two_pow_pos (n : Int) : 0 < (2 : Rat) ^ n := by exact Rat.zpow_pos rfl

@[grind =]
theorem Int.toNat_neg_eq_zero_of_nonpos {z : Int} (h : z ≤ 0) : z.toNat = 0 := by
  grind

@[grind .] -- What is a grind '.' pattern?
theorem mkRat_eq_mkRat_of_eq_of_eq
  {n1 n2 : Int}
  {d1 d2 : Nat}
  (hn : n1 = n2)
  (hd : d1 = d2)
  :
  mkRat n1 d1 = mkRat n2 d2 := by grind

@[simp]
theorem Bool.xor_eq_true_of_ne {b1 b2 : Bool} (h : b1 ≠ b2) :
  b1.xor b2 = true := by
  grind

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_sign_eq_one_of_eq
  {b1 b2 : Bool} (h : b1 = b2) :
  (-1) ^ b1.toNat * (-1) ^ b2.toNat = 1 := by
  grind [Bool.toNat]

@[grind =, grind .]
theorem neg_one_pow_toNat_eq_ite
  { b : Bool } :
  (-1) ^ b.toNat = if b then -1 else 1 := by
  grind [Bool.toNat]

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_sign_eq_neg_one_of_ne
  {b1 b2 : Bool} (h : b1 ≠ b2) :
  (-1) ^ b1.toNat * (-1) ^ b2.toNat = -1 := by
  grind [Bool.toNat]

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_toNat_eq_one_of_self
  {b : Bool} : (-1) ^ b.toNat * (-1) ^ b.toNat = 1 := by
  grind [Bool.toNat]

attribute [grind] Bool.toNat
attribute [grind funCC] mkRat

/-
@[grind .]
theorem Int.mul_congr (a a' b b' : Int)
  (ha : a = a') (hb : b = b') :
  a * b = a' * b' := by grind
-/

@[grind .]
theorem Int.mul_congr_right (a b b' : Int) (hb : b = b') :
  a * b = a * b' := by
  grind

theorem Nat.lt_mul_of_lt_of_pos {a b c : Nat} (hab : a < b) (hc : 0 < c) :
    a < b * c := by
  rw [show a = a * 1 by omega]
  exact Nat.mul_lt_mul_of_lt_of_le hab hc hc


/- # Grind sets for power of two reasoning. -/
-- @[grind! .]
theorem Nat.lt_two_pow_of_lt_two_pow_of_le {a n m : Nat}
    (ha : a < 2 ^ n := by grind) (hnm : n ≤ m := by grind) : a < 2 ^ m := by
  apply Nat.lt_of_lt_of_le
  · exact ha
  · refine Nat.pow_le_pow_right (by decide) hnm

attribute [grind =] Nat.mod_eq_of_lt

@[grind ←]
theorem Nat.two_pow_lt_two_pow_of_lt {n m : Nat}
    (hnm : n < m := by grind) : 2 ^ n < 2 ^ m := by
  apply (Nat.pow_lt_pow_iff_right ?_).mpr hnm
  · omega

@[grind ←]
theorem Nat.two_pow_le_two_pow_of_le {n m : Nat}
    (hnm : n ≤ m := by grind) : 2 ^ n ≤ 2 ^ m := by
  apply (Nat.pow_le_pow_iff_right ?_).mpr hnm
  · omega

attribute [grind =, grind =_] Nat.shiftLeft_eq



end Fp
