import Fp

set_option maxHeartbeats 2000000
/--
Remainder is degree 1 homogeneous with respect to multiplication, when said
multiplication is exact.
-/
theorem remainder_homogeneous (a b c : PackedFloat 5 2)
  (ha : isExactFloat 5 2 (e_mul a.toEFixed c.toEFixed))
  (hb : isExactFloat 5 2 (e_mul b.toEFixed c.toEFixed))
  (hc : isExactFloat 5 2 (e_mul (remainder a b).toEFixed c.toEFixed)
    ∧ ¬c.isZero ∧ ¬c.isInfinite)
  : mul (remainder a b) c .RNE = remainder (mul a c .RNE) (mul b c .RNE) := by
  bv_decide (timeout := 300)
