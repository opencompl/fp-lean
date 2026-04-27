import Fp.Theorems.UnpackedFloat.Round
import Fp.Theorems.PackedFloat.Successor

namespace Fp

section ComputableLowerUpper

open SmtLibSemantics

/-
### Computable Lower & Upper Bound
-/

/-- Enumerate bitvectors. -/
def enumerateBV (n : Nat) : { xs : List (BitVec n) // ∀ (x : BitVec n), x ∈ xs } :=
  let xs := List.range (2 ^ n)
  let vs := xs.map (fun x => BitVec.ofNat n x)
  ⟨vs, by
    intros x
    simp [vs, xs]
    exists x.toNat
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true]
    grind only [usr BitVec.isLt]
  ⟩

def enumerateBool : { xs : List Bool // ∀ (x : Bool), x ∈ xs } :=
  let xs := [true, false]
  ⟨xs, by
    intros x
    simp [xs]
  ⟩

def enumerateProduct {α β} (xs : { xs : List α // ∀ (a : α), a ∈ xs})
    (ys : { ys : List β // ∀ (b : β), b ∈ ys }) :
    { zs : List (α × β) // ∀ (z : α × β), z ∈ zs } :=
  let zs := xs.val.flatMap (fun x => ys.val.map (fun y => (x, y)))
  ⟨zs, by
    intros z
    obtain ⟨zx, zy⟩ := z
    simp [zs]
    grind only
  ⟩

def enumerateProduct3 {α β γ} (xs : { xs : List α // ∀ (a : α), a ∈ xs})
    (ys : { ys : List β // ∀ (b : β), b ∈ ys })
    (zs : { zs : List γ // ∀ (c : γ), c ∈ zs }) :
    { ws : List (α × β × γ) // ∀ (w : α × β × γ), w ∈ ws } :=
  let ws := xs.val.flatMap (fun x => ys.val.flatMap (fun y => zs.val.map (fun z => (x, y, z))))
  ⟨ws, by
    intros w
    obtain ⟨wx, wy, wz⟩ := w
    simp [ws]
    grind only
  ⟩

/--
enumerate all packed floats.
-/
def enumeratePackedFloatList (e s : Nat) :
    {xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs} :=
  let sign := enumerateBool
  let exp := enumerateBV e
  let sig := enumerateBV s
  let xs := enumerateProduct3 sign exp sig
  ⟨xs.val.map (fun (sign, exp, sig) => PackedFloat.mk sign exp sig), by
    intros x
    obtain ⟨sign, exp, sig⟩ := x
    simp
    rcases sign with rfl | rfl
    · simp
      grind only
    · simp
      grind only
  ⟩

/-- enumerate all packed floats as an array. -/
def enumeratePackedFloatArray (e s : Nat) :
    {xs : Array (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs} :=
  ⟨enumeratePackedFloatList e s |>.val.toArray, by
    intros x
    simp
    grind only [#968d]
  ⟩

/-- enmerate all packed floats which are not NaN.-/
def enumerateNonNanPackedFloatArray (e s : Nat) :
    {xs : Array (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ ¬ x.isNaN} :=
  let arr := enumeratePackedFloatArray e s
  let xs := arr.val.filter (fun pf => ¬ pf.isNaN)
  ⟨xs, by
    intros x
    simp [xs]
    grind only [#ca5c]
  ⟩

def enumerateNonNanPackedFloatList (e s : Nat) :
    {xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ ¬ x.isNaN} :=
  ⟨enumerateNonNanPackedFloatArray e s |>.val.toList, by
    intros x
    simp [Array.mem_toList_iff]
    grind only
  ⟩


def lowerList (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) :
    { xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ (¬ x.isNaN ∧ x.toExtRat ≤ r) } :=
    let arr := enumeratePackedFloatList e s
    let out := arr.val.filter (fun pf => ¬ pf.isNaN && pf.toExtRat ≤ r)
    ⟨out, by
      intros x
      constructor
      · intros hx
        simp [out, arr] at hx
        rw [PackedFloat.toExtRat_eq_toExtRat']
        grind only
      · intros hx
        grind only [= List.mem_filter, #f38e]
    ⟩

@[simp]
theorem mem_lowerList_iff (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) (pf : PackedFloat e s) :
    pf ∈ (lowerList e s r hr).val ↔ (¬ pf.isNaN ∧ pf.toExtRat ≤ r) := by
  have := lowerList e s r hr
  grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN,
    = PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, = PackedFloat.toExtRat'_eq_NaN_iff_isNaN,
    = PackedFloat.toExtRat'_eq_zero_of_isZero, = PackedFloat.toExtRat'_eq_toRat_of,
    = PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero, #d3b2, #96bca0d4ecd67426,
    #aefe0df31a27f84b]


@[simp]
theorem infty_mem_lowerList (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) (hs : 0 < s):
    PackedFloat.getInfinity e s true ∈ (lowerList e s r hr).val := by
    simp [hs]
    grind only

/--
the lowerList is nonempty when the significand is nonzero.
-/
@[grind! .]
theorem lowerList_nonempty (e s : Nat) (r : ExtRat) (hr : r ≠ .NaN) (hs : 0 < s) :
    (lowerList e s r hr).val.length ≠ 0 := by
  have := infty_mem_lowerList e s r hr hs
  grind only [usr List.length_pos_of_mem]

/--
on a non-NaN set of packed floats, compute the 'max'.
-/
def maxPackedFloatNonNaN
    (xs : List (PackedFloat e s)) (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    { pf : PackedFloat e s //
         ¬ pf.isNaN ∧ ∀ (x : PackedFloat e s), x ∈ xs → pf ≥ x } :=
  match xs with
  | [] => ⟨PackedFloat.getInfinity e s true, by
    constructor
    · grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN, !PackedFloat.toExtRat'_getInfinity]
    · intros x hx; simp at hx⟩
  | x :: xs =>
    let candidate := maxPackedFloatNonNaN xs (by simp; grind only [= List.mem_cons, #1c8d]) he hs
    if hc : candidate.val ≥ x then
      ⟨candidate, by
        constructor
        · grind
        · intros y hy; simp at hy; cases hy with
          | inl h => simp [h]; simp at hc; exact hc
          | inr h =>
            simp at hc
            have := (candidate.property.right) y h
            exact this⟩
    else
      ⟨x, by
        constructor
        · grind only [usr Subtype.property, = List.mem_cons, #1c8d]
        · intros y hy;
          simp at hy;
          rcases hy with h | h
          · simp [h]
          · simp
            simp at hc
            have := candidate.property.right y h
            simp at this
            apply PackedFloat.le_trans
            · exact this
            · apply PackedFloat.le_of_lt
              apply PackedFloat.lt_of_not_le
              · grind only [= PackedFloat.toExtRat'_eq_NaN_iff_isNaN, = List.mem_cons, #1c8d]
              · grind only [usr Subtype.property, = PackedFloat.isNaN_iff_toExtRat'_eq_NaN]
⟩

@[simp]
theorem not_isNaN_maxPackedFloatNaN (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    ¬ (maxPackedFloatNonNaN xs hxs he hs).val.isNaN := by
  have := (maxPackedFloatNonNaN xs hxs he hs).property
  simp [this]

/--
the result of 'maxPackedFloatNonNaN' is actually in the list when the list is nonempty.
-/
theorem maxFloatNonNaN_mem (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN)
    (hxsLen : xs.length ≠ 0)
    (he : 0 < e) (hs : 0 < s) :
    (maxPackedFloatNonNaN xs hxs he hs).val ∈ xs := by
  induction xs
  case nil => simp at hxsLen
  case cons x xs ih =>
    simp only [List.mem_cons]
    simp at ih
    simp [maxPackedFloatNonNaN]
    split
    case isTrue h =>
      simp
      rcases xs with rfl | ⟨x', xs'⟩
      · simp [maxPackedFloatNonNaN, hs] at h
        simp at ih
        simp
        simp at hxs
        subst h
        simp at hxs
        simp [maxPackedFloatNonNaN]
      · right
        apply ih
        · grind
        · simp
    case isFalse h =>
      simp
/--
all values in the list are less than the max.
-/
theorem le_maxPackedFloatNonNaN (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    ∀ x ∈ xs, x ≤ (maxPackedFloatNonNaN xs hxs he hs).val := by
  intros x hx
  obtain ⟨hnan, hle⟩ := (maxPackedFloatNonNaN xs hxs he hs).property
  simp at hle
  apply hle
  grind

/--
Every element in 'xs' is less than the 'max', when interpreted in the rationals.
-/
theorem le_maxPackedFloatNaN_toExtRat' (xs : List (PackedFloat e s))
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) :
    ∀ x ∈ xs, x.toExtRat' ≤ (maxPackedFloatNonNaN xs hxs he hs).val.toExtRat' := by
  intros x hx
  have := le_maxPackedFloatNonNaN xs hxs he hs x hx
  apply PackedFloat.toExtRat'_le_toExtRat'_of_le
  · grind only
  · grind only
  · grind
  · grind only
  · apply le_maxPackedFloatNonNaN
    · grind only

/--
To show that a rational 'r' is greater than the max,
it suffices to show that it is greater than all the elements in the list.
-/
theorem maxPackedFloatNaN_toExtRat'_le_of_toExtRat'_le (xs : List (PackedFloat e s))
    (hxsEmpty : xs ≠ [])
    (hxs : ∀ x ∈ xs, ¬ x.isNaN) (he : 0 < e) (hs : 0 < s) (r : ExtRat)
    (hr : ∀ x ∈ xs, x.toExtRat' ≤ r) :
    (maxPackedFloatNonNaN xs hxs he hs).val.toExtRat' ≤ r := by
  have := maxFloatNonNaN_mem xs hxs (by simp; grind only) he hs
  grind only [#e993]

/--
info: 'Fp.le_maxPackedFloatNaN_toExtRat'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms le_maxPackedFloatNaN_toExtRat'

theorem ExtRat.not_isNaN_of_le_of_not_isNaN (r1 r2 : ExtRat)
  (hr1 : r1 ≤ r2) (hr2 : r2 ≠ .NaN) : r1 ≠ .NaN := by
  intros hcontra
  simp at hr2
  apply hr2
  simp [hcontra] at hr1
  grind only
/--
lower is computable for all arguments.
-/
def lower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) : PackedFloat e s :=
if hr : r = .NaN then
  PackedFloat.getNaN e s
else if h0 : r = .Number 0 then
  PackedFloat.getZero e s false
else
  let arr := lowerList e s r (by simp [hr])
  let max := maxPackedFloatNonNaN arr.val (by simp; grind only [#1a7c]) he hs
  max.val


/--
The result of 'lower' is NaN iff the input is NaN.
-/
theorem isNaN_lower_iff_eq_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat):
    (lower e s he hs r).isNaN ↔ r = .NaN := by
  simp [lower]
  split
  case isTrue h =>
    simp [h]
  case isFalse h =>
    simp [h]
    by_cases hr : r = ExtRat.Number 0
    · simp [hr]
      grind
    · simp [hr]



/-- info: 'Fp.isNaN_lower_iff_eq_NaN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms isNaN_lower_iff_eq_NaN

/--
the 'lower' function indeed computes a lawful lower bound for every ExtRat.
This shows that lawful lower bounds exist for all rationals.
-/
@[simp]
theorem IsLawfulLower_lower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulLower r (lower e s he hs r) := by
  simp [lower]
  split
  case isTrue h =>
    subst h
    simp
  case isFalse h =>
    by_cases hr : r = .Number 0
    · simp [hr, he, hs]
    · simp [hr]
      constructor
      · simp only [smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm]
        apply maxPackedFloatNaN_toExtRat'_le_of_toExtRat'_le
        · grind
        · intros x hx
          simp at hx
          grind only
      · intros x hx
        simp only [smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', ExtRat.ge_eq_le_symm] at hx
        apply le_maxPackedFloatNonNaN
        simp only [mem_lowerList_iff, Bool.not_eq_true, PackedFloat.toExtRat_eq_toExtRat']
        constructor
        · grind only [= PackedFloat.toExtRat'_eq_NaN_iff_isNaN, = ExtRat.le_NaN]
        · grind only

/-- info: 'Fp.IsLawfulLower_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsLawfulLower_lower


/--
We know that that we have a lawful upper iff it's a lawful lower for the negated version.
-/
@[simp ←]
theorem IsLawfulUpper_iff_IsLawfulLower_neg_neg (r : ExtRat) (x : PackedFloat e s) :
    SmtLibSemantics.IsLawfulUpper r x ↔ SmtLibSemantics.IsLawfulLower (-r) (-x) := by
  simp only [IsLawfulUpper, smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm, IsLawfulLower, PackedFloat.toExtRat'_neg]
  constructor
  · intros h
    obtain ⟨hupper, hlower⟩ := h
    constructor
    · grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]
    · intros lower hlower'
      suffices x ≤ -lower by grind only [= PackedFloat.le_neg_iff_le_neg]
      apply hlower
      simp only [PackedFloat.toExtRat'_neg]
      grind only [= ExtRat.le_neg_iff_le_neg]
  · intros h
    obtain ⟨hlower, hupper⟩ := h
    constructor
    · grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]
    · intros upper hupper'
      suffices -upper ≤ -x by grind only [= PackedFloat.neg_le_iff_neg_le, = PackedFloat.neg_neg']
      apply hupper
      simp only [PackedFloat.toExtRat'_neg]
      grind only [= ExtRat.neg_le_iff_neg_le, = ExtRat.neg_neg]

/--
We have a lawful lower iff it's a lawful upper for the negated version.
-/
@[simp ←]
theorem IsLawfulLower_iff_IsLawfulUpper_neg_neg (r : ExtRat) (x : PackedFloat e s) :
    SmtLibSemantics.IsLawfulLower r x ↔ SmtLibSemantics.IsLawfulUpper (-r) (-x) := by
  rw [IsLawfulUpper_iff_IsLawfulLower_neg_neg]
  simp

def upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) : PackedFloat e s :=
  - lower e s he hs (-r)

@[simp]
theorem IsLawfulUpper_upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (upper e s he hs r) := by
  simp [upper]
  apply IsLawfulUpper_iff_IsLawfulLower_neg_neg .. |>.mpr
  simp

@[simp]
theorem isNaN_upper_iff_eq_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat):
    (upper e s he hs r).isNaN ↔ r = .NaN := by
  simp [upper]
  simp [isNaN_lower_iff_eq_NaN]

/-- info: 'Fp.IsLawfulUpper_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsLawfulUpper_upper

end ComputableLowerUpper
/-# IsLawfulLower, smtLibLower, and computable lower

We show that `smtLibLower` can always be replaced with `lower`
-/

/-### Lower bounds -/

theorem lsLawfulLower_smtLibLower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulLower r (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) := by
  simp [SmtLibSemantics.smtLibLower]
  apply Classical.epsilon_spec
  have := IsLawfulLower_lower e s he hs r
  grind only [#de43]

/--
two lawful lowers are equal to each other.
-/
theorem eq_of_IsLawfulLower_of_IsLawfulLower
    (e s : Nat) (r : ExtRat) (x y : PackedFloat e s)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hlowerx : SmtLibSemantics.IsLawfulLower r x)
    (hlowery : SmtLibSemantics.IsLawfulLower r y) :
    x = y := by
  have rlex := hlowerx.1
  have rley := hlowery.1
  have rlex' := hlowerx.2 y rley
  have rley' := hlowery.2 x rlex
  grind only [PackedFloat.le_antisymm_of_ne_NaN]


theorem IsLawfulLower_eq_NaN_of_isNaN (e s : Nat) (r : ExtRat) (x : PackedFloat e s)
    (hlower : SmtLibSemantics.IsLawfulLower r x) :
    x.isNaN = true → r = .NaN := by
  intros hnan
  have hlower1 := hlower.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower1
  simp [hnan] at hlower1
  grind

/--
The result of 'IsLawfulLower' is unique and must be equal to the 'lower' computation.
If the value is a 'NaN', then we may have different 'NaNs, but we may not get
equality on the nose.
-/
@[simp]
theorem eq_lower_of_IsLawfulLower (e s : Nat) (he : 0 < e) (hs : 0 < s)
    (r : ExtRat)
    (x : PackedFloat e s)
    (hrnan : r ≠ .NaN)
    (hlower : SmtLibSemantics.IsLawfulLower r x) :
    x = lower e s he hs r := by
  apply eq_of_IsLawfulLower_of_IsLawfulLower
  · intros hcontra
    apply hrnan
    apply IsLawfulLower_eq_NaN_of_isNaN
    · exact hlower
    · grind only
  · apply Classical.byContradiction
    intros hcontra
    apply hrnan
    grind [ExtRat, lower]
  · apply hlower
  · exact IsLawfulLower_lower e s he hs r

/--
info: 'Fp.eq_lower_of_IsLawfulLower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_lower_of_IsLawfulLower

/--
the value of smtLibLower equals that of 'lower' on all non-NaN rationals.
-/
@[simp]
theorem smtLibLower_eq_lower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    SmtLibSemantics.smtLibLower.lower r = lower e s he hs r := by
  apply eq_of_IsLawfulLower_of_IsLawfulLower (r := r)
  · intros hcontra
    have := eq_lower_of_IsLawfulLower e s he hs r (SmtLibSemantics.smtLibLower.lower r) hr
    specialize this (by exact lsLawfulLower_smtLibLower e s he hs r)
    rw [this] at hcontra
    have := isNaN_lower_iff_eq_NaN e s he hs r
    grind only
  · intros hcontra
    apply hr
    grind only [→ PackedFloat.not_isZero_of_isNaN, lower, PackedFloat.isZero_getZero, #2962, #90ed]
  · exact lsLawfulLower_smtLibLower e s he hs r
  · exact IsLawfulLower_lower e s he hs r

/-- info: 'Fp.smtLibLower_eq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smtLibLower_eq_lower

/-### Upper bounds -/

theorem isLawfulUpper_smtLibUpper (e s : Nat) (he : 0 < e)  (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) := by
  simp [SmtLibSemantics.smtLibUpper]
  apply Classical.epsilon_spec
  have := IsLawfulUpper_upper e s he hs r
  grind only [#c7e1]

/--
two lawful uppers are equal to each other.
-/
theorem eq_of_IsLawfulUpper_of_IsLawfulUpper
    (e s : Nat) (r : ExtRat) (x y : PackedFloat e s)
    (hxnan : ¬ x.isNaN) (hynan : ¬ y.isNaN)
    (hupperx : SmtLibSemantics.IsLawfulUpper r x)
    (huppery : SmtLibSemantics.IsLawfulUpper r y) :
    x = y := by
  have rlex := hupperx.1
  have rley := huppery.1
  have rlex' := hupperx.2 y rley
  have rley' := huppery.2 x rlex
  grind only [PackedFloat.le_antisymm_of_ne_NaN]


theorem IsLawfulUpper_eq_NaN_of_isNaN (e s : Nat) (r : ExtRat) (x : PackedFloat e s)
    (hupper : SmtLibSemantics.IsLawfulUpper r x) :
    x.isNaN = true → r = .NaN := by
  intros hnan
  have hupper1 := hupper.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hupper1
  simp [hnan] at hupper1
  grind only

/--
The result of 'IsLawfulLower' is unique and must be equal to the 'lower' computation.
-/
@[simp]
theorem eq_upper_of_IsLawfulUpper (e s : Nat) (he : 0 < e) (hs : 0 < s)
    (r : ExtRat)
    (x : PackedFloat e s)
    (hrnan : r ≠ .NaN)
    (hupper : SmtLibSemantics.IsLawfulUpper r x) :
    x = upper e s he hs r := by
  apply eq_of_IsLawfulUpper_of_IsLawfulUpper
  · intros hcontra
    apply hrnan
    apply IsLawfulUpper_eq_NaN_of_isNaN
    · exact hupper
    · grind only
  · apply Classical.byContradiction
    intros hcontra
    apply hrnan
    simp at hcontra
    grind only
  · apply hupper
  · exact IsLawfulUpper_upper e s he hs r

/--
info: 'Fp.eq_upper_of_IsLawfulUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eq_upper_of_IsLawfulUpper

@[simp]
theorem smtLibUpper_eq_upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    SmtLibSemantics.smtLibUpper.upper r = upper e s he hs r := by
  apply eq_of_IsLawfulUpper_of_IsLawfulUpper (r := r)
  · intros hcontra
    have := eq_upper_of_IsLawfulUpper e s he hs r (SmtLibSemantics.smtLibUpper.upper r) hr
    rw [this] at hcontra
    · have := isNaN_upper_iff_eq_NaN e s he hs r
      grind only
    · exact isLawfulUpper_smtLibUpper e s he hs r
  · intros hcontra
    apply hr
    have := isNaN_upper_iff_eq_NaN e s he hs r
    grind only
  · exact isLawfulUpper_smtLibUpper e s he hs r
  · exact IsLawfulUpper_upper e s he hs r

/-- info: 'Fp.smtLibUpper_eq_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smtLibUpper_eq_upper


@[simp]
theorem not_isNaN_lower_of_ne_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s).isNaN = false := by
  rw [smtLibLower_eq_lower e s he hs r hr]
  grind only [lower, → PackedFloat.not_isZero_of_isNaN, PackedFloat.isZero_getZero, #2962, #90ed]

/--
info: 'Fp.not_isNaN_lower_of_ne_NaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms not_isNaN_lower_of_ne_NaN

@[simp]
theorem not_isNaN_lower_neg_of_ne_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower (-r) : PackedFloat e s).isNaN = false := by
  apply not_isNaN_lower_of_ne_NaN e s he hs
  simp [ExtRat.neg_eq_NaN_iff, hr]



@[simp]
theorem not_isNaN_upper_of_ne_NaN (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s).isNaN = false := by
  by_cases hnan : (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s).isNaN
  · exfalso
    rw [smtLibUpper_eq_upper e s he hs r hr] at hnan
    have := isNaN_upper_iff_eq_NaN e s he hs r
    grind only
  · simp [hnan]

/--
info: 'Fp.not_isNaN_upper_of_ne_NaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms not_isNaN_upper_of_ne_NaN

theorem isLawfulUpper_upper (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    SmtLibSemantics.IsLawfulUpper r (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) := by
  by_cases hr : r = .NaN
  · simp [hr]
  · have := smtLibUpper_eq_upper e s he hs r hr
    rw [this]
    exact IsLawfulUpper_upper e s he hs r

/-- info: 'Fp.IsLawfulUpper_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsLawfulUpper_upper


@[simp]
theorem embed_neg_eq_neg_embed {e s : Nat} (x : PackedFloat e s) :
    (SmtLibSemantics.RoundableEmbed.embed (-x) = - (SmtLibSemantics.RoundableEmbed.embed x : ExtRat)) := by
  simp [SmtLibSemantics.RoundableEmbed.embed]

-- lower(-x) = - upper x
@[simp]
theorem smtLibLower_neg_eq_neg_smtLibUpper {e s : Nat} (he : 0 < e) (hs : 0 < s) (r : ExtRat) (hr : r ≠ .NaN) :
    (SmtLibSemantics.smtLibLower.lower (-r) : PackedFloat e s) = - (SmtLibSemantics.smtLibUpper.upper r) := by
  rw [smtLibLower_eq_lower e s he hs]
  · rw [smtLibUpper_eq_upper e s he hs]
    · simp [upper]
    · simp [hr]
  · simp [hr]

-- upper(-x) = - lower x
@[simp]
theorem smtLibUpper_neg_eq_neg_smtLibLower {e s : Nat} (r : ExtRat) (hr : r ≠ .NaN) (he : 0 < e )(hs : 0 < s) :
    (SmtLibSemantics.smtLibUpper.upper (-r) : PackedFloat e s) = - (SmtLibSemantics.smtLibLower.lower r) := by
  rw [smtLibUpper_eq_upper e s he hs]
  · rw [smtLibLower_eq_lower e s he hs]
    · simp [upper]
    · simp [hr]
  · simp [hr]

/--
This tells us that `PackedFloat`s are perfectly approximated,
and that calling `lower` on a rational that represents a `PackedFloat`
gives us the same `PackedFloat` back, as long as it's not NaN.
-/
theorem smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN
  (he : 0 < e) (hs : 0 < s)
  (x : PackedFloat e s) (r : ExtRat)
  (hnum : ¬ x.isNaN)
  (hzero : ¬ x.isZero)
  (h : x.toExtRat = r) :
  (SmtLibSemantics.smtLibLower.lower r : PackedFloat e s) = x := by
  have hlower := lsLawfulLower_smtLibLower e s he hs r
  have hlower1 := hlower.1
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ge_eq_le_symm] at hlower1

  have hlower2 := hlower.2
  subst h
  specialize (hlower2 x)
  simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat',
    ExtRat.ExtRat.le_refl, forall_const] at hlower2
  simp only [PackedFloat.toExtRat_eq_toExtRat']
  have : SmtLibSemantics.smtLibLower.lower x.toExtRat' ≤ x := by
    apply PackedFloat.le_of_toExtRat'_le_toExtRat'
    · grind only
    · grind only
    · simp
      grind only [PackedFloat.le_iff_eq_of_isNaN']
    · simp
      grind only
    · simp only [PackedFloat.toExtRat_eq_toExtRat'] at hlower1
      intros hxzero hlowrzero hxsign
      grind only
    · grind only
    · simp only [PackedFloat.toExtRat_eq_toExtRat'] at hlower hlower1 ⊢
      grind only
  grind only [PackedFloat.le_antisymm_of_ne_NaN, PackedFloat.le_iff_eq_of_isNaN']

  /--
info: 'Fp.smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN

/--
upper perfectly approximates PackedFloats, and calling `upper` on a rational that represents a `PackedFloat`
gives us the same `PackedFloat` back, as long as it's not NaN.
-/
theorem smtLibUpper_eq_self_of_eq_toExtRat_of_not_isNaN
  (he : 0 < e) (hs : 0 < s)
  (x : PackedFloat e s) (r : ExtRat)
  (hnum : ¬ x.isNaN)
  (hzero : ¬ x.isZero)
  (h : x.toExtRat = r) :
  (SmtLibSemantics.smtLibUpper.upper r : PackedFloat e s) = x := by
  rw [show r = - (- r) by grind only [= ExtRat.neg_neg]]
  rw [smtLibUpper_neg_eq_neg_smtLibLower]
  · rw [smtLibLower_eq_self_of_eq_toExtRat_of_not_isNaN he hs (- x)]
    · simp
    · simp [hnum]
    · simp [hzero]
    · simp [he, hs]
      simp only [PackedFloat.toExtRat_eq_toExtRat'] at h
      grind only
  · simp at h
    simp; grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN]
  · simp [he]
  · simp [hs]

/--
info: 'Fp.smtLibUpper_eq_self_of_eq_toExtRat_of_not_isNaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms smtLibUpper_eq_self_of_eq_toExtRat_of_not_isNaN


/-
theorem upper_eq_successorAwayFromZero_lower
theorem upper_eq_successorAwayFromZero_lower
-/
end Fp
