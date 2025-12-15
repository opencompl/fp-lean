import Lean

open Lean


/-- Absolute value of a rational number. -/
def Rat.abs (r : Rat) : Rat := if r < 0 then -r else r

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
