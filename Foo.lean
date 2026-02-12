theorem concat_truncate_zero_eq_mul_pow2
    {n : Nat} (x : BitVec n) (tz : Nat) (htz : tz ≤ n) :
    ((x.truncate (n - tz)) ++ (0#tz) |>.cast (by omega)) = x * (1#n <<< tz) := by
  ext i
  simp
  rw [BitVec.getElem_append]
  have : 1#n <<< tz = BitVec.twoPow _ tz := by
    ext i
    simp
    by_cases hi : i < tz <;> simp [hi] <;> omega
  rw [this]
  rw [← BitVec.shiftLeft_eq_mul_twoPow]
  rw [BitVec.getElem_shiftLeft]
  by_cases hi : i < tz 
  · simp [hi]
  · simp [hi]
    rw [BitVec.getLsbD_eq_getElem]


/--
appending 'tz' trailing zeroes to the truncated 'x' is equal to
multiplying 'x' by 2^tz.
-/
theorem extractLsb'_append_zero_eq_mul_shiftLeft {n : Nat}
    (x : BitVec n) (tz : Nat) (htz : tz ≤ n) :
    ((x.extractLsb' 0 (n - tz) ++ (0#tz)).cast (by omega))
      = x * (1#n <<< tz) := by
  ext i
  simp only [BitVec.getElem_cast]
  rw [BitVec.getElem_append]
  have : 1#n <<< tz = BitVec.twoPow _ tz := by 
    ext i
    simp only [BitVec.getElem_shiftLeft, BitVec.getElem_one, BitVec.getElem_twoPow]
    by_cases hi : i < tz <;> simp [hi] <;> omega
  rw [this, ← BitVec.shiftLeft_eq_mul_twoPow, BitVec.getElem_shiftLeft]
  by_cases hi : i < tz
  · simp [hi]
  · simp [hi]
    rw [BitVec.getLsbD_eq_getElem]
