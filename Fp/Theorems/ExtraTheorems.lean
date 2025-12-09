import Fp

-- Expansion

theorem expand_preserves_value (a : EFixedPoint 34 16) (m : RoundingMode)
  : round 5 2 m (a.expand 38 18 (by omega) (by omega)) = round 5 2 m a := by
  bv_decide

theorem expand_self_is_id (a : EFixedPoint w e)
  : (a.expand w e (by omega) (by omega)) = a := by
  apply EFixedPoint.inj
  cases h : a.state <;> simp_all

-- Comparison

theorem e_lt_of_lt (a b : PackedFloat 5 2)
  : lt a b ↔ e_lt a.toEFixed b.toEFixed := by
  bv_decide

theorem le_of_e_le (m : RoundingMode) (a b : EFixedPoint 35 16)
  : e_le a b → le (round 5 2 m a) (round 5 2 m b) := by
  bv_decide

theorem e_le_of_le (a b : PackedFloat 5 2)
  : le a b ↔ e_le a.toEFixed b.toEFixed := by
  bv_decide

-- Rounding

/--
Every floating point number converted to fixed point form, is an exact
floating point number.
-/
theorem toEFixed_isExactFloat (a : PackedFloat 5 2)
  : isExactFloat 5 2 a.toEFixed := by
  bv_decide

/--
A fixed point number is an exact floating point number iff converting to
floating point and back should not change the denotation.
-/
theorem isExactFloat_iff_round_toEFixed (a : EFixedPoint 34 16) (m : RoundingMode)
  : isExactFloat 5 2 a ↔ a.equal_denotation (round 5 2 m a).toEFixed := by
  -- Note: two issues occur if we remove the enum bound lemma below:
  -- 1. `a.state` is assigned an arbitrary value outside of its bound
  -- 2. `m` is assigned an arbitrary value outside of its bound
  -- `bv_decide` currently cannot handle these cases for goals that require unfolding.
  -- However, it can support them. The first issue doesn't matter much as we don't
  -- plan to support `EFixedPoint` anyways. The second case,
  -- however, is more important as we do want to support arbitrary
  -- rounding modes. We're lucky here as the proof goes through anyway.
  have : a.state.enumToBitVec < 0b11#2 := by cases a.state <;> decide
  bv_decide

@[bv_normalize]
def escapeEnumPass (m : RoundingMode) : Prop := m.enumToBitVec < 0b101#3

theorem RoundingMode_enum_bound (m : RoundingMode)
  : escapeEnumPass m := by
  cases m <;> unfold escapeEnumPass <;> decide
  -- bv_decide -- error: wrong counter-example

/-- Fixed -> Float rounding is left inverse to Float -> Fixed conversion -/
theorem round_leftinv_toEFixed (x : PackedFloat 5 2) (mode : RoundingMode):
  (round _ _ mode x.toEFixed).equal_denotation x := by
  bv_decide

-- Addition

theorem f_add_comm (m : RoundingMode) (a b : FixedPoint 34 16)
  : (f_add m a b) = (f_add m b a) := by
  bv_decide

theorem e_add_comm (m : RoundingMode) (a b : EFixedPoint 34 16)
  : (e_add m a b) = (e_add m b a) := by
  simp [e_add]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp <;> simp_all only [eq_comm, f_add_comm]

theorem add_comm (m : RoundingMode) (a b : PackedFloat 5 2)
  : (add a b m) = (add b a m) := by
  simp [add, e_add_comm]

theorem add_neg_self_isZero_or_isNaN (a : PackedFloat 5 2) (m : RoundingMode)
  : (add a (neg a) m).isZero ∨ (add a (neg a) m).isNaN := by
  bv_decide

theorem add_zero_is_id (a : PackedFloat 5 2) (m : RoundingMode)
  (ha : ¬a.isNaN ∧ ¬a.isZero)
  : (add a (PackedFloat.getZero _ _) m) = a := by
  bv_decide


theorem e_add_monotone (m : RoundingMode) (a b c : EFixedPoint 34 16)
  (hc : c.state = .Number)
  : e_le a b → e_le (e_add m a c) (e_add m b c) := by
  bv_decide

theorem add_monotone (a b c : PackedFloat 5 2) (m : RoundingMode) (hc : c.isNormOrSubnorm)
  : le a b → le (add a c m) (add b c m) := by
  intro h
  apply le_of_e_le
  have hc' : c.toEFixed.state = .Number :=
    PackedFloat.isNumber_of_isNormOrSubnorm c hc
  apply e_add_monotone _ _ _ _ hc'
  exact (e_le_of_le _ _).mp h

/--
A floating-point subtraction is computed exactly iff the
operands are within a factor of two of each other.

* <https://en.wikipedia.org/wiki/Sterbenz_lemma>
-/
theorem sterbenz (a b : PackedFloat 5 2)
  (h : le a (doubleRNE b) ∧ le b (doubleRNE a))
  : isExactFloat 5 2 (e_add .RTZ a.toEFixed ((neg b).toEFixed)) := by
  bv_decide

-- Negation

theorem f_neg_involutive (a : FixedPoint 16 8)
  : f_neg (f_neg a) = a := by
  simp [f_neg]

theorem e_neg_involutive (a : EFixedPoint 16 8)
  : (e_neg (e_neg a)).equal_denotation a := by
  -- Similar issue to the one discussed above.
  -- Don't care about enum bounds for EFixedPoint.
  bv_normalize
  bv_decide

/--
Negation will always map an exact float to an exact float.
-/
theorem neg_exact (a : PackedFloat 5 2)
  : isExactFloat 5 2 (e_neg a.toEFixed) := by
  bv_decide

/--
`negfixed` and `neg` implement the same function.
-/
theorem negfixed_eq_neg (a : PackedFloat 5 2) (m : RoundingMode)
  : negfixed a m = neg a := by
  bv_decide

/--
Applying `neg` twice gives you the identity.
-/
theorem neg_involutive (a : PackedFloat e s) (h : ¬a.isNaN)
  : neg (neg a) = a := by
  unfold neg at ⊢
  simp only [h]
  simp_all

-- Subtraction

theorem subfixed_eq_sub (a b : PackedFloat 5 2) (m : RoundingMode)
  : subfixed a b m = sub a b m := by
  bv_decide

-- Multiplication

/--
`mulfixed` and `mul` implement the same function.
-/
theorem mulfixed_eq_mul (a b : PackedFloat 5 2) (m : RoundingMode)
  : (mul a b m) = (mulfixed a b m) := by
  bv_decide (timeout := 60)

theorem mul_comm (a b : PackedFloat 5 2) (m : RoundingMode)
  : (mul a b m) = (mul b a m) := by
  bv_decide

theorem mul_one_is_id (a : PackedFloat 5 2) (m : RoundingMode)
  : (mul a oneE5M2 m).equal_denotation a := by
  bv_decide

theorem add_eq_mul_two (a : PackedFloat 5 2) (m : RoundingMode)
  : add a a m = mul twoE5M2 a m := by
  bv_decide

theorem doubleRNE_eq_mul_two (a : PackedFloat 5 2)
  : doubleRNE a = mul twoE5M2 a .RNE := by
  bv_decide

-- Fixed-point multiplication
-- Bitblasting this is a bit too hard, so we'll prove these theorems manually

theorem f_mul_comm (a b : FixedPoint 34 16)
  : (f_mul a b) = (f_mul b a) := by
  simp [f_mul, Bool.xor_comm, BitVec.mul_comm]

theorem e_mul_comm (a b : EFixedPoint 34 16)
  : (e_mul a b) = (e_mul b a) := by
  simp [e_mul]
  cases ha2 : a.state <;> cases hb2 : b.state <;>
    simp_all [Bool.xor_comm, f_mul_comm]

theorem mulfixed_comm (a b : PackedFloat 5 2) (m : RoundingMode)
  : (mulfixed a b m) = (mulfixed b a m) := by
  simp [mulfixed, e_mul_comm]

-- Division

theorem div_one_is_id (a : PackedFloat 5 2)
  : (div a oneE5M2 .RTZ).equal_denotation a := by
  bv_decide

theorem div_self_is_one (a : PackedFloat 5 2)
  (h : ¬a.isNaN ∧ ¬a.isInfinite ∧ ¬a.isZero)
  : (div a a .RTZ) = oneE5M2 := by
  bv_decide

-- Other

theorem diff_zero_implies_equal (a b : PackedFloat 5 2) (m : RoundingMode)
  : (add a (neg b) m).isZero → ((a.isZero ∧ b.isZero) ∨ a = b) := by
  bv_decide

-- Square root

-- Remainder
/--
Modulo by a value will always be less or equal to the value itself
(by magnitude).
-/
theorem rem_le_abs_self (a b : PackedFloat 5 2)
  (h : a.isNormOrSubnorm)
  (hb : ¬b.isNaN ∧ ¬b.isZero)
  : le (remainder a b) (abs b) := by
    bv_decide

/--
Remainder is degree 1 homogeneous with respect to doubling.

The remainder function itself has the homogeneity property; the reason this
theorem may not apply to arbitrary multiplication is that the multiplication
has to be exact.
-/
theorem remainder_doubling_homogeneous (a b : PackedFloat 5 2)
  (h : ¬(doubleRNE a).isInfinite ∧ ¬(doubleRNE b).isInfinite)
  : doubleRNE (remainder a b) = remainder (doubleRNE a) (doubleRNE b) := by
  bv_decide
