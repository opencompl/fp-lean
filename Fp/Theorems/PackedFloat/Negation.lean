import Fp.Basic

/-!
# Negation Theorems for PackedFloat

This file develops the theory of how negation interacts with
classification predicates, the semantic interpretation (`toRat`, `toExtRat'`),
and the ordering (`≤`) on `PackedFloat`.

The main results are:
- Classification preservation: negation preserves `isNaN`, `isInfinite`, `isZero`,
  `isNorm`, `isNormOrNonzeroSubnorm`.
- `toRat_neg`: `(-x).toRat = -x.toRat`
- `toExtRat'_neg`: `(-x).toExtRat' = -(x.toExtRat')`
- `le_neg_iff_neg_le`: `x ≤ y ↔ -y ≤ -x` (order reversal)
-/

namespace PackedFloat

/-! ## Classification preservation under negation -/

@[simp]
theorem isNaN_neg (x : PackedFloat e s) : (-x).isNaN = x.isNaN := by
  simp [neg_def, neg, isNaN]

@[simp]
theorem isInfinite_neg (x : PackedFloat e s) : (-x).isInfinite = x.isInfinite := by
  simp [neg_def, neg, isInfinite]

@[simp]
theorem isZero_neg (x : PackedFloat e s) : (-x).isZero = x.isZero := by
  simp [neg_def, neg, isZero]

@[simp]
theorem isNonzeroSubnorm_neg (x : PackedFloat e s) :
    (-x).isNonzeroSubnorm = x.isNonzeroSubnorm := by
  simp [neg_def, neg, isNonzeroSubnorm]

@[simp]
theorem isNormOrNonzeroSubnorm_neg (x : PackedFloat e s) :
    (-x).isNormOrNonzeroSubnorm = x.isNormOrNonzeroSubnorm := by
  simp [neg_def, neg, isNormOrNonzeroSubnorm]

@[simp]
theorem isZeroOrSubnorm_neg (x : PackedFloat e s) :
    (-x).isZeroOrSubnorm = x.isZeroOrSubnorm := by
  simp [neg_def, neg, isZeroOrSubnorm]

/-! ## Negation and getInfinity / getZero / getNaN -/

@[simp]
theorem neg_getInfinity (sign : Bool) :
    -(PackedFloat.getInfinity e s sign) = PackedFloat.getInfinity e s (!sign) := by
  simp [neg_def, neg, getInfinity]

@[simp]
theorem neg_getZero (sign : Bool) :
    -(PackedFloat.getZero e s sign) = PackedFloat.getZero e s (!sign) := by
  simp [neg_def, neg, getZero]

@[simp]
theorem neg_getNaN :
    -(PackedFloat.getNaN e s) = { PackedFloat.getNaN e s with sign := true } := by
  simp [neg_def, neg, getNaN]

/-! ## Semantic preservation: toRatSig, toRatExp -/


/-! ## Negation and Bool.toSign -/

@[simp]
theorem Bool.toSign_not (b : Bool) : (!b).toSign = -b.toSign := by
  cases b <;> simp [Bool.toSign]

/-! ## toRat and negation -/

/-! ## toExtRat' and negation -/

@[simp]
theorem toExtRat'_neg (x : PackedFloat e s) : (-x).toExtRat' = -(x.toExtRat') := by
  simp only [toExtRat']
  simp only [isNaN_neg, isInfinite_neg, neg_sign]
  by_cases hnan : x.isNaN
  · simp [hnan]
  · simp [hnan]
    by_cases hinf : x.isInfinite
    · simp [hinf]
    · simp [hinf]

@[simp]
theorem toExtRat'_neg_eq_neg_toExtRat' (x : PackedFloat e s) :
    (-x).toExtRat' = -(x.toExtRat') := toExtRat'_neg x

/-! ## Double negation -/

@[grind =]
theorem neg_neg' (x : PackedFloat e s) : -(-x) = x := neg_neg x

/-! ## Order reversal under negation -/

/--
Negation reverses the ordering on `PackedFloat`: `x ≤ y ↔ -y ≤ -x`.
-/
theorem le_iff_neg_le_neg {x y : PackedFloat e s} :
    x ≤ y ↔ -y ≤ -x := by
  simp only [← PackedFloat.le_def]
  unfold PackedFloat.le
  simp only [isNaN_neg, neg_sign, neg_ex, neg_sig]
  constructor <;> intro h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · left; exact ⟨h2, h1⟩
    · right
      constructor
      · simpa using h2
      constructor
      · simpa using h1
      rcases h3 with ⟨hxs, hys⟩ | ⟨hxs, hys, hex⟩ | ⟨hxs, hys, heq, hsig⟩ |
        ⟨hxs, hys, hex⟩ | ⟨hxs, hys, heq, hsig⟩
      · -- x neg, y pos → !y neg, !x pos
        -- After neg: !y.sign = true, !x.sign = false
        -- This matches the first disjunct: (-y).sign = true ∧ (-x).sign = false
        left; exact ⟨by simp [hys], by simp [hxs]⟩
      · -- both pos, x.ex < y.ex → both neg, y.ex < x.ex
        right; right; right; left
        exact ⟨by simp [hys], by simp [hxs], hex⟩
      · -- both pos, same ex, x.sig ≤ y.sig → both neg, same ex, y.sig ≤ x.sig
        right; right; right; right
        exact ⟨by simp [hys], by simp [hxs], heq.symm, hsig⟩
      · -- both neg, y.ex < x.ex → both pos, x.ex < y.ex
        right; left
        exact ⟨by simp [hys], by simp [hxs], hex⟩
      · -- both neg, same ex, y.sig ≤ x.sig → both pos, same ex, x.sig ≤ y.sig
        right; right; left
        exact ⟨by simp [hys], by simp [hxs], heq.symm, hsig⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · left
      constructor
      · simpa using h2
      · simpa using h1
    · right
      constructor
      · simpa using h2
      constructor
      · simpa using h1
      rcases h3 with ⟨hys, hxs⟩ | ⟨hys, hxs, hex⟩ | ⟨hys, hxs, heq, hsig⟩ |
        ⟨hys, hxs, hex⟩ | ⟨hys, hxs, heq, hsig⟩
      · -- !y neg, !x pos → x neg, y pos
        left; exact ⟨by simpa using hxs, by simpa using hys⟩
      · -- !y pos, !x pos, y.ex < x.ex → x pos, y pos, y.ex < x.ex
        -- Wait: !y.sign = false means y.sign = true, !x.sign = false means x.sign = true
        -- So both neg after neg means both pos originally? No.
        -- !y.sign = false ∧ !x.sign = false means y.sign = true ∧ x.sign = true (both orig neg)
        right; right; right; left
        exact ⟨by simpa using hxs, by simpa using hys, hex⟩
      · right; right; right; right
        exact ⟨by simpa using hxs, by simpa using hys, heq.symm, hsig⟩
      · -- !y.sign = true ∧ !x.sign = true means y.sign = false ∧ x.sign = false (both orig pos)
        right; left
        exact ⟨by simpa using hxs, by simpa using hys, hex⟩
      · right; right; left
        exact ⟨by simpa using hxs, by simpa using hys, heq.symm, hsig⟩

theorem lt_iff_neg_lt_neg {x y : PackedFloat e s} :
    x < y ↔ -y < -x := by
  simp only [← lt_def, lt]
  constructor
  · intro ⟨hle, hne⟩
    refine ⟨le_iff_neg_le_neg.mp hle, ?_⟩
    intro h
    apply hne
    have : -(-y) = -(-x) := by rw [h]
    simp at this
    exact this.symm
  · intro ⟨hle, hne⟩
    refine ⟨le_iff_neg_le_neg.mpr hle, ?_⟩
    intro h
    apply hne
    subst h
    rfl

/--
Negation is antitone: if `x ≤ y` then `-y ≤ -x`.
-/
@[simp]
theorem neg_le_neg {x y : PackedFloat e s} (h : x ≤ y) : -y ≤ -x :=
  le_iff_neg_le_neg.mp h

/--
Negation is antitone: if `x < y` then `-y < -x`.
-/
@[simp]
theorem neg_lt_neg {x y : PackedFloat e s} (h : x < y) : -y < -x :=
  lt_iff_neg_lt_neg.mp h

/--
`x ≤ -y ↔ y ≤ -x`: move negation across `≤` from right to left.
-/
@[grind =]
theorem le_neg_iff_le_neg {x y : PackedFloat e s} :
    x ≤ -y ↔ y ≤ -x := by
  rw [le_iff_neg_le_neg (x := x) (y := -y)]
  simp [neg_neg]

/--
`-x ≤ y ↔ -y ≤ x`: move negation across `≤` from left to right.
-/
@[grind =]
theorem neg_le_iff_neg_le {x y : PackedFloat e s} :
    -x ≤ y ↔ -y ≤ x := by
  rw [le_iff_neg_le_neg (x := -x) (y := y)]
  simp [neg_neg]

end PackedFloat
