import Lean

open Lean


/-- Absolute value of a rational number. -/
def Rat.abs (r : Rat) : Rat := if r < 0 then -r else r

/-- rational that is 1/2^n -/
def Rat.twoPowInv (n : Nat) : Rat :=
  Rat.mk' 1 (2 ^ n)
      (by exact Ne.symm (NeZero.ne' (2 ^ n)))
      (reduced := by exact Nat.gcd_pow_right_of_gcd_eq_one rfl)

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
