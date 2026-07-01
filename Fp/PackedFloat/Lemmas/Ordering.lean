import Fp.PackedFloat.Lemmas.Conversion

/-!
## Basic ordering lemmas about `PackedFloat`

Properties of `≤`/`<` on `PackedFloat` (reflexivity, antisymmetry, transitivity,
NaN/zero/sign-based facts).
-/

namespace PackedFloat

@[simp, grind .]
theorem le_of_lt {a b : PackedFloat e s} (h : a < b) : (a ≤ b) := by
  rw [← lt_def, lt] at h
  grind only

@[simp, grind .]
theorem ne_of_lt {a b : PackedFloat e s} (h : a < b) : ¬ (a = b) := by
  simp [← lt_def, lt] at h
  grind only

@[grind ., simp]
theorem lt_of_le_of_ne (a b : PackedFloat e s) (hle : a ≤ b) (hne : a ≠ b) :
    a < b := by
  simp [← lt_def, lt]
  grind only

theorem lt_iff_le_and_ne (a b : PackedFloat e s) : a < b ↔ (a ≤ b ∧ a ≠ b) := by
  simp [← lt_def, lt]

@[simp, grind .]
theorem minus_zero_le_plus_zero {e s} (he : 0 < e) :
    (PackedFloat.getZero e s true ≤ PackedFloat.getZero e s false) := by
  simp [getZero, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.isNaN]
  grind

@[simp, grind .]
theorem plus_zero_not_le_minus_zero (he : 0 < e) :
    ¬ (PackedFloat.getZero e s false ≤ PackedFloat.getZero e s true) := by
  simp [getZero, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.isNaN]
  grind

@[simp, grind .]
theorem le_refl (x : PackedFloat e s) : x ≤ x := by simp [← le_def, PackedFloat.le]

@[simp, grind .]
theorem le_NaN (x : PackedFloat e s) :
    x ≤ PackedFloat.getNaN e s ↔ x.isNaN := by
  by_cases hx : x.isNaN
  · simp only [← PackedFloat.le_def, PackedFloat.le, hx]
    simp only [isNaN_mkNaN, and_self, not_true_eq_false, false_and]
    grind
  · simp only [← PackedFloat.le_def, PackedFloat.le]
    simp [hx]

@[simp, grind .]
theorem NaN_le (x : PackedFloat e s)
    : PackedFloat.getNaN e s ≤ x ↔ x.isNaN := by
  simp only [← PackedFloat.le_def, PackedFloat.le]
  simp only [isNaN_getNaN]
  by_cases hx : x.isNaN
  · simp [hx]
  · simp [hx]

@[simp, grind .]
theorem le_iff_eq_of_isNaN (x y : PackedFloat e s)
  (hx : x.isNaN) : x ≤ y ↔ y.isNaN := by
  simp only [← PackedFloat.le_def, PackedFloat.le, hx]
  simp only [not_true_eq_false, false_and]
  grind

@[simp, grind .]
theorem le_iff_eq_of_isNaN' (x y : PackedFloat e s)
  (hy : y.isNaN) : x ≤ y ↔ x.isNaN := by
  simp only [← PackedFloat.le_def, PackedFloat.le, hy]
  simp only [not_true_eq_false]
  grind

@[simp]
theorem getInfinity_le_getInfinity_iff_of_lt (sign1 sign2 : Bool) (hs : 0 < s) :
    (PackedFloat.getInfinity e s sign1 ≤ PackedFloat.getInfinity e s sign2) ↔ (sign1 = false → sign2 = false) := by
  simp only [← PackedFloat.le_def, PackedFloat.le]
  simp [hs]
  grind


@[simp]
theorem PackedFloat.getZero_le_getZero_iff
    (he : 0 < e) (sign1 sign2 : Bool) :
    (PackedFloat.getZero e s sign1 ≤ PackedFloat.getZero e s sign2) ↔ (sign1 = false → sign2 = false) := by
  simp only [PackedFloat.isZero_getZero, he, decide_true, PackedFloat.le_iff_sign_eq_of_isZero,
    PackedFloat.sign_getZero]


@[grind .]
theorem le_antisymm_of_ne_NaN
  {x y : PackedFloat e s}
  (hxy : x ≤ y) (hyx : y ≤ x) (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) :
    x = y := by
  simp only [← PackedFloat.le_def] at hxy hyx
  simp only [PackedFloat.le] at hxy hyx
  simp [hx] at hxy hyx
  simp [hy] at hxy hyx
  grind [PackedFloat]

theorem le_antisymm_iff {x y : PackedFloat e s}
  (hxy : x ≤ y) (hyx : y ≤ x) :
  (x.isNaN ∧ y.isNaN) ∨ (¬ x.isNaN ∧ ¬ y.isNaN ∧ x = y) := by
  by_cases hx : x.isNaN
  · simp [hx]
    simp [hx] at hxy hyx
    grind
  · simp [hx]
    by_cases hy : y.isNaN
    · simp [hy]
      simp [hy] at hxy hyx
      grind
    · simp [hy]
      grind only [PackedFloat.le_antisymm_of_ne_NaN hxy hyx hx hy]

theorem le_trans
    {x y z : PackedFloat e s} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  simp only [← PackedFloat.le_def] at hxy hyz ⊢
  simp only [PackedFloat.le] at hxy hyz ⊢
  by_cases hx : x.isNaN
  · simp [hx] at hxy
    simp at hyz
    grind
  · simp [hx] at hxy
    simp at hyz
    by_cases hy : y.isNaN
    · simp [hy] at hxy
    · simp [hy] at hxy hyz
      by_cases hz : z.isNaN
      · simp [hz] at hxy hyz
      · simp [hz] at hxy hyz
        grind (splits := 10)
           only [BitVec.toNat_inj ]

/--
If `x = y = NaN`, then we can have `NaN₁ < NaN₂ `, since we have that `NaN₁ ≤ NaN₂`,
but also that `NaN₁ ≠ NaN₂`
-/
theorem lt_trans (x y z : PackedFloat e s)
  (hnan : x.isNaN = false ∨ y.isNaN = false)
  (hxy : x < y)
  (hyz : y < z) :
  x < z := by
  simp only [← PackedFloat.lt_def, PackedFloat.lt] at hxy hyz ⊢
  have : x ≤ z := by grind only [le_trans]
  simp [this]
  intros hcontra
  subst hcontra
  rcases hnan with hnan | hnan
  · grind only [le_iff_eq_of_isNaN, le_antisymm_of_ne_NaN]
  · grind only [le_iff_eq_of_isNaN, le_antisymm_of_ne_NaN]

/--
If `x = NaN₁` `y = NaN₂`, the we have that `x ≤ y` and `y ≤ x` since all NaNs
are comparable, but this does not imply that `x = y`.
-/
theorem eq_of_le_of_le_of_not_isNaN (x y : PackedFloat e s)
  (hxy : x ≤ y) (hyx : y ≤ x) (hnan : x.isNaN = false ∨ y.isNaN = false) :
  x = y := by grind only [le_iff_eq_of_isNaN, le_antisymm_of_ne_NaN]

@[simp, grind =]
theorem lt_iff_ne_of_isNaN_of_isNaN (x y : PackedFloat e s)
    (hx : x.isNaN) (hy : y.isNaN) : (x < y) ↔ x ≠ y := by
  rw [lt_iff_le_and_ne]
  simp [hx, hy]

@[simp, grind =]
theorem lt_iff_ne_and_isNaN_of_isNaN (x y : PackedFloat e s)
    (hx : x.isNaN) : (x < y) ↔ (y.isNaN = true ∧ x ≠ y) := by
  rw [lt_iff_le_and_ne]
  simp [hx]

@[simp, grind =]
theorem lt_iff_ne_and_isNaN_of_isNaN' (x y : PackedFloat e s)
    (hx : y.isNaN) : (x < y) ↔ (x.isNaN = true ∧ x ≠ y) := by
  rw [lt_iff_le_and_ne]
  simp [hx]

theorem lt_of_le_of_lt_of_not_isNaN (x y z : PackedFloat e s)
    (hnan : ¬ x.isNaN ∨ ¬ y.isNaN ∨ ¬ z.isNaN)
    (hxy : x ≤ y) (hyz : y < z) : x < z := by
  apply lt_of_le_of_ne
  · apply le_trans (y := y)
    · grind only
    · grind only [le_of_lt]
  · intros hcontra
    subst hcontra
    have : y ≤ x := by grind only [le_of_lt]
    have : x = y := by grind only [le_iff_eq_of_isNaN, le_antisymm_of_ne_NaN]
    subst this
    grind only [ne_of_lt]

theorem lt_of_lt_of_le_of_not_isNaN (x y z : PackedFloat e s)
    (hnan : ¬ x.isNaN ∨ ¬ y.isNaN ∨ ¬ z.isNaN)
    (hxy : x < y) (hyz : y ≤ z) : x < z := by
  apply lt_of_le_of_ne
  · apply le_trans (y := y)
    · grind only [le_of_lt]
    · grind only
  · intros hcontra
    subst hcontra
    have : x ≤ y := by grind only [le_of_lt]
    have : x = y := by grind only [le_iff_eq_of_isNaN, le_antisymm_of_ne_NaN]
    subst this
    grind only [ne_of_lt]

/--
Both amongst NaNs and amongst regular numbers, the ordering is total,
but not across these domains.
-/
theorem le_total_of_isNaN_eq_isNaN (x y : PackedFloat e s) (hnan : x.isNaN = y.isNaN)
    : x ≤ y ∨ y ≤ x := by
  simp [← le_def, le]
  by_cases hxnan : x.isNaN
  · simp [hxnan]
    simp [hxnan] at hnan
    grind only
  · simp [hxnan]
    have : y.isNaN = false := by grind only
    simp [this]
    grind only [BitVec.toNat_inj]

/--
floats are totally ordered amongst NaNs and regular numbers.
-/
theorem lt_trichotomy_of_isNaN_eq_isNaN (x y : PackedFloat e s)
    (hnan : x.isNaN = y.isNaN) :
    x < y ∨ x = y ∨ y < x := by
  by_cases heq : x = y
  · simp [heq]
  · simp [heq]
    have hle := le_total_of_isNaN_eq_isNaN x y hnan
    grind only [lt_of_le_of_ne]

/--
If the numbers are notNaN, then 'x ≤ y' if the x is negative and y is positive.
TODO: tag as grind.
-/
@[simp]
theorem le_of_sign_eq_true_sign_eq_false {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN) (hxsign : x.sign = true) (hysign : y.sign = false) :
    (x ≤ y) := by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only

@[simp]
theorem sign_eq_false_of_le_of_sign_eq_false_of_not_isNaN
    (x y : PackedFloat e s) (hxy : x ≤ y)
    (hnan : ¬ x.isNaN)
    (ynan : ¬ y.isNaN)
    (hySign : x.sign = false) : y.sign = false := by
  simp only [← PackedFloat.le_def] at hxy
  simp only [PackedFloat.le, hySign] at hxy
  grind only

@[simp]
theorem sign_eq_true_of_le_of_sign_eq_true_of_not_isNaN
    (x y : PackedFloat e s) (hxy : x ≤ y)
    (hnan : ¬ x.isNaN)
    (ynan : ¬ y.isNaN)
    (hySign : y.sign = true) : x.sign = true := by
  simp only [← PackedFloat.le_def] at hxy
  simp only [PackedFloat.le, hySign] at hxy
  grind only

/--
positive numbers are not greater than negative numbers, if they are not NaN.
-/
@[simp]
theorem not_le_of_sign_eq_of_sign_eq
    (x y : PackedFloat e s) (hxy : x ≤ y)
    (ynan : ¬ y.isNaN)
    (hySign : y.sign = true) (hxSign : x.sign = false) : ¬ (x ≤ y) := by
  simp only [← PackedFloat.le_def] at hxy
  simp only [PackedFloat.le, hySign] at hxy
  grind only


/--
If the numbers are notNaN, then 'x ≤ y' if the x is negative and y is positive.
-/
@[simp, grind .]
theorem not_le_of_sign_eq_false_of_sign_eq_true {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN) (hxsign : x.sign = false) (hysign : y.sign = true) :
    ¬ (x ≤ y) := by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only

@[simp, grind .]
theorem le_eq_of_sign_eq_false_of_sign_eq_false {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN := by solve | simp | grind)
    (hynan : ¬ y.isNaN := by solve | simp | grind)
    (hxsign : x.sign = false := by solve | simp | grind)
    (hysign : y.sign = false := by solve | simp | grind) :
    (x ≤ y) = ((x.ex.toNat < y.ex.toNat) ∨ (x.ex.toNat = y.ex.toNat ∧ x.sig.toNat ≤ y.sig.toNat)):= by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only [BitVec.toNat_inj]

@[simp, grind .]
theorem le_eq_of_sign_eq_true_of_sign_eq_true {x y : PackedFloat e s}
    (hxnan : ¬ x.isNaN := by solve | simp | grind)
    (hynan : ¬ y.isNaN := by solve | simp | grind)
    (hxsign : x.sign = true := by solve | simp | grind)
    (hysign : y.sign = true := by solve | simp | grind) :
    (x ≤ y) = ((y.ex.toNat < x.ex.toNat) ∨ (x.ex.toNat = y.ex.toNat ∧  y.sig.toNat ≤ x.sig.toNat)):= by
  rw [← PackedFloat.le_def, PackedFloat.le]
  grind only [BitVec.toNat_inj]

/--
Every number is less than +∞
-/
@[simp, grind =>]
theorem le_getInfinity_false_of_not_isNaN (hs : 0 < s) (y : PackedFloat e s) :
    (y ≤ PackedFloat.getInfinity e s false) ↔ ¬ y.isNaN := by
  by_cases hnan : y.isNaN
  · simp [hnan]
    grind only [→ not_isInfinite_of_isNaN, !isInfinite_getInfinity]
  · simp [hnan]
    rw [← PackedFloat.le_def, PackedFloat.le]
    simp [hnan, hs]
    by_cases hysign : y.sign
    · simp [hysign]
    · simp [hysign]
      grind only [=> isNaN_iff_ex_eq_sig_eq, usr Nat.pow_pos, usr BitVec.isLt,
        BitVec.eq_allOnes_iff_toNat_eq, = BitVec.toNat_ofNat, = BitVec.toNat_zero]

@[simp, grind →]
theorem eq_getInfinity_of_getInfinity_le (hs : 0 < s) (y : PackedFloat e s)
  (hle : PackedFloat.getInfinity e s false ≤ y) :
  y = .getInfinity e s false := by
  have : (getInfinity e s false).sign = false := by grind
  by_cases hysign : y.sign
  · have : ¬ ((getInfinity e s false) ≤ y) := by
      grind only [le_iff_eq_of_isNaN,
        le_antisymm_of_ne_NaN, not_le_of_sign_eq_false_of_sign_eq_true,
        => le_getInfinity_false_of_not_isNaN]
    grind only
  · simp at hysign
    have hle' := hle
    rw [le_eq_of_sign_eq_false_of_sign_eq_false] at hle'
    simp at hle'
    have : y.ex.toNat = 2 ^ e - 1 := by grind only [usr Nat.pow_pos, usr BitVec.isLt]
    have : y.sig = 0#s := by grind only [le_iff_eq_of_isNaN', !isInfinite_getInfinity,
      => isNaN_iff_ex_eq_sig_eq, eq_getInfinity_iff_isInfinity, → not_isNaN_of_isInfinite,
      BitVec.eq_allOnes_iff_toNat_eq]
    apply PackedFloat.ext <;> simp <;> grind


/--
If a number is +infty, then only +infty is larger than it.
-/
@[simp]
theorem PackedFloat.getInfinity_false_le_iff_eq (hs : 0 < s)
    (y : PackedFloat e s) :
    (PackedFloat.getInfinity e s false) ≤ y ↔ y = .getInfinity e s false := by
  constructor
  · intros h
    grind only [→ eq_getInfinity_of_getInfinity_le]
  · intros h
    subst h
    grind only [le_refl]


@[grind =>, simp]
theorem PackedFloat.getInfinity_true_le_of_not_isNaN (hs : 0 < s) (y : PackedFloat e s) :
    (PackedFloat.getInfinity e s true ≤ y) ↔ ¬ y.isNaN := by
  by_cases hnan : y.isNaN
  · simp [hnan]
    grind only [→ not_isInfinite_of_isNaN, !isInfinite_getInfinity]
  · simp [hnan]
    rw [← PackedFloat.le_def, PackedFloat.le]
    simp [hnan, hs]
    by_cases hysign : y.sign
    · simp [hysign]
      grind
    · simp [hysign]

@[simp]
theorem le_zero_iff_sign_eq_true {x : PackedFloat e s} (he : 0 < e):
    (x ≤ PackedFloat.getZero e s true) ↔ (x.sign = true ∧ ¬ x.isNaN) := by
  by_cases hxNaN : x.isNaN
  · grind only [→ not_isZero_of_isNaN, PackedFloat.le_iff_eq_of_isNaN, isZero_getZero]
  · simp [hxNaN]
    by_cases hxsign : x.sign
    · simp [hxsign]
      rw [← PackedFloat.le_def, PackedFloat.le]
      simp [hxNaN]
      simp [show ¬ e = 0 by grind]
      simp [hxsign]
      have := BitVec.toNat_inj (x := x.ex) (y := 0#_)
      simp at this
      grind
    · simp [hxsign]
      have : (getZero e s true).sign = true := by grind only [= sign_getZero]
      grind only [not_le_of_sign_eq_false_of_sign_eq_true]

@[simp]
theorem zero_le_iff_sign_eq_false {x : PackedFloat e s} (he : 0 < e) :
  (PackedFloat.getZero e s false ≤ x) ↔ (x.sign = false ∧ ¬ x.isNaN) := by
  by_cases hxNaN : x.isNaN
  · simp [hxNaN]
    grind
  · simp [hxNaN]
    by_cases hxsign : x.sign
    · simp [hxsign]
      rw [← PackedFloat.le_def, PackedFloat.le]
      simp [hxNaN]
      simp [show ¬ e = 0 by grind]
      simp [hxsign]
    · simp [hxsign]
      have : (getZero e s false).sign = false := by grind only [= sign_getZero]
      have := le_eq_of_sign_eq_false_of_sign_eq_false (x := (getZero e s false)) (y := x)
        (by grind) (by grind) (by grind) (by grind)
      simp at this
      grind





@[simp, grind =>]
theorem le_getInfinity_true_iff_eq (hs : 0 < s)
    (y : PackedFloat e s) :
    y ≤ PackedFloat.getInfinity e s true ↔ y = .getInfinity e s true := by
  constructor
  · intros h
    grind only [PackedFloat.le_iff_eq_of_isNaN, PackedFloat.le_iff_eq_of_isNaN', le_antisymm_of_ne_NaN,
      => PackedFloat.getInfinity_true_le_of_not_isNaN]
  · intros h
    subst h
    grind only [PackedFloat.le_refl]

end PackedFloat
