import Fp.Basic


/--
As a precondition, we assume that the number is at most the size of the max normal number
for the format we are rounding to.
-/
def PackedFloat.packedLowerNonneg
  (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=

  sorry

def PackedFloat.packedUpperNonneg
  (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=
  sorry

def PackedFloat.packedLowerNeg
  (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=
  x.neg.packedUpperNonneg eout sout m |>.neg

def PackedFloat.packedUpperNeg
  (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=
  x.neg.packedLowerNonneg eout sout m |>.neg

def PackedFloat.packedLower (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=
  bif x.sign then x.packedLowerNeg eout sout m else x.packedLowerNonneg eout sout m

def PackedFloat.packedUpper (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=
  bif x.sign then x.packedUpperNeg eout sout m else x.packedUpperNonneg eout sout m


/--
Round a 'PackedFloat' into a smaller format
with exponent width `eout` and significand width `sout`, using rounding mode `m`.
This only works for inputs where `e ≤ eout`, and `s + 2 ≤ sout`,
or when the number is already exactly representable in the smaller format (e.g., zero, subnormal, small).
-/
def PackedFloat.packedRound (x : PackedFloat e s) (eout sout : Nat) (m : RoundingMode) : PackedFloat e s :=
  -- step 1: check that exponent is in range for max value
  sorry
