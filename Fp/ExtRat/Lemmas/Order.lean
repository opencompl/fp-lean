import Fp.ExtRat.Lemmas.Arithmetic

/-!
## ExtRat order lemmas

Lemmas about le/lt/eq/min/max on ExtRat.
-/

namespace ExtRat

@[simp]
theorem ExtRat.le_NaN_iff (x : ExtRat) : (x ≤ .NaN) = decide (x = .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.NaN_le_iff (x : ExtRat) : (.NaN ≤ x) = decide (x = .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.inf_false_le_iff (x : ExtRat) :
    -- +infty ≤ x ↔ x = +infty
    (.Infinity false ≤ x) = decide (x = .Infinity false) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.le_inf_false_iff (x : ExtRat) :
    -- x ≤ +infty ↔ x ≠ NaN
    (x ≤ ExtRat.Infinity false) ↔ (x ≠ .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.inf_true_le_iff (x : ExtRat) :
    -- -infty ≤ x ↔ x ≠ NaN
    (.Infinity true ≤ x) = decide (x ≠ .NaN) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.le_inf_true_iff (x : ExtRat) :
    -- x ≤ -infty ↔ x = -infty
    (x ≤ ExtRat.Infinity true) = decide (x = .Infinity true) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem number_le_infinity_iff {n : Rat} {sign : Bool}:
    (ExtRat.Number n ≤ ExtRat.Infinity sign) ↔ (sign = false) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem infinity_le_number_iff {n : Rat} {sign : Bool}:
    (ExtRat.Infinity sign ≤ ExtRat.Number n) ↔ (sign = true) := by
  simp [le, ← le_def]
  grind


@[simp]
theorem number_le_nan_iff {n : Rat} :
    (ExtRat.Number n ≤ ExtRat.NaN) = False := by
  simp [le, ← le_def]

@[simp]
theorem nan_le_number_iff {n : Rat} :
    (.NaN ≤ ExtRat.Number n) = False := by
  simp [le, ← le_def]

@[simp]
theorem nan_le_infinity_iff {sign : Bool}:
    (.NaN ≤ ExtRat.Infinity sign) = False := by
  simp [le, ← le_def]

@[simp]
theorem infinity_le_nan_iff {sign : Bool}:
    (ExtRat.Infinity sign ≤ .NaN) = False := by
  simp [le, ← le_def]



@[simp]
theorem ExtRat.num_le_num_iff (r1 r2 : Rat) :
  ((ExtRat.Number r1) ≤ (ExtRat.Number r2)) = decide (r1 ≤ r2) := by
  simp [le, ← le_def]

@[simp]
theorem ExtRat.le_refl {a : ExtRat} : a ≤ a := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.le_antisymm {a b : ExtRat} : (a ≤ b ∧ b ≤ a) ↔ a = b := by
  simp [le, ← le_def]
  grind

@[simp]
theorem ExtRat.eq_of_le_of_le {a b : ExtRat} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  simp [le, ← le_def] at h1 h2
  grind

@[simp]
theorem ExtRat.infinity_le_infinity_iff {s1 s2 : Bool} :
    (ExtRat.Infinity s1 ≤ ExtRat.Infinity s2) = decide (s1 = false → s2 = false) := by
  simp [le, ← le_def]
  grind

@[simp]
theorem eq_iff (x y : ExtRat) : x.eq y = decide (x = y) := by
  grind [ExtRat, eq]

@[simp, grind .]
theorem le_of_lt {a b : ExtRat} (h : a < b) : (a ≤ b) := by
  simp [← lt_def, lt] at h
  grind only

@[simp, grind .]
theorem ne_of_lt {a b : ExtRat} (h : a < b) : ¬ (a = b) := by
  simp [← lt_def, lt] at h
  grind only

theorem lt_iff {a b : ExtRat} : (a < b) ↔ (a ≤ b ∧ ¬ (a = b)) := by
  simp [← lt_def, lt]

@[simp]
theorem NaN_lt_elim {a : ExtRat} :  (.NaN < a) = False := by
  simp [lt_iff]
  grind only

@[simp]
theorem lt_NaN_elim {a : ExtRat} :  (a < .NaN) = False := by
  simp [lt_iff]

@[simp]
theorem lt_infty_true_elim {a : ExtRat} : (a < .Infinity true) = False := by
  simp [lt_iff]

@[simp]
theorem infty_true_lt_iff {a : ExtRat} : (.Infinity true < a) =
  decide (a ≠ .Infinity true ∧ a ≠ .NaN) := by
  simp [lt_iff]
  grind

@[simp]
theorem lt_infty_false_iff {a : ExtRat} : (a < .Infinity false) =
  decide (a ≠ .Infinity false ∧ a ≠ .NaN) := by
  simp [lt_iff]
  grind

@[simp]
theorem elim_infty_false_lt {a : ExtRat} : (.Infinity false < a) = False := by
  simp [lt_iff]
  grind

@[simp]
theorem num_lt_num_iff {r1 r2 : Rat} :
  ((ExtRat.Number r1) < (ExtRat.Number r2)) = decide (r1 < r2) := by
  simp [lt_iff]
  grind

theorem lt_of_not_le {a b : ExtRat} (ha : a ≠ .NaN) (hb : b ≠ .NaN)
  (h : ¬ (a ≤ b)) : (b < a) := by
  rcases a with rfl | sign | r
  · simp at ha
  · simp at ha
    rcases sign with rfl | rfl
    · simp at h
      simp
      grind only
    · simp at h
      grind only
  · simp at ha
    rcases b with rfl | sign' | r'
    · simp at hb
    · simp at hb
      rcases sign' with rfl | rfl
      · simp at h
      · simp at h
        simp
    · simp at hb
      simp at h
      simp
      grind only


/-- Unfold min into ite. Not a simp lemma, since we may want to rewrite
with higher level reasoning principles. -/
theorem min_eq_ite {a b : ExtRat} : min a b = if a ≤ b then a else b := rfl

theorem max_eq_ite {a b : ExtRat} : max a b = if a ≤ b then b else a := rfl
end ExtRat
