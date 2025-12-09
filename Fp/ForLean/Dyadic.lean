open Lean



/-- make power of two as a dyadic number. -/
def Dyadic.twoPow (n : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec 1 (-n)

/-- the power of two as a rational number is what you'd expect it to be. -/
theorem Dyadic.twoPow_eq (n : Nat) :
    (Dyadic.twoPow n |>.toRat) = mkRat (2 ^ n) 1 := by
  simp only [twoPow]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  simp only [Int.neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, Nat.shiftLeft_zero]
  congr
  rw [Int.shiftLeft_eq]
  simp only [Int.one_mul]
