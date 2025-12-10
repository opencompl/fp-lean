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
  
