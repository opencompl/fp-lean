import Fp.Rounding
import Fp.SmtLibSemantics
import Fp.Theorems.Basic
import Fp.Theorems.Packing
import Fp.Theorems.Packing
import Fp.Theorems.Ordering
import Fp.Theorems.UnpackedRound

namespace Fp
open SmtLibSemantics

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
the 'lower' function indeed computes a lawful lower bound for every ExtRat.
This shows that lawful lower bounds exist for all rationals.
-/
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
/-
  {
    pf : PackedFloat e s //
    SmtLibSemantics.IsLawfulLower r pf
  } :=
  if hr : r = .NaN then
    ⟨PackedFloat.getNaN e s, by
      simp [hr, hs, IsLawfulLower]⟩
  else if h0 : r = .Number 0 then
    ⟨PackedFloat.getZero e s false, by
      simp [h0, hr, hs, IsLawfulLower]
      constructor
      · grind
      · intros lower hnan
        intros hlower
        rcases hlower with hlower | hlower
        · simp [hlower, he, hs]
        · grind only [PackedFloat.le_of_nonneg_of_neg, !PackedFloat.toExtRat'_getZero,
          = PackedFloat.isNaN_iff_toExtRat'_eq_NaN, = PackedFloat.sign_getZero]
    ⟩
  else
    let arr := lowerList e s r (by simp [hr])
    let max := maxPackedFloatNonNaN arr.val (by simp; grind only [#1a7c]) he hs
    have hmax : ∀ (pf : PackedFloat e s), pf.toExtRat' ≤ r → pf ≤ max := by
      sorry
        apply Ext
    have : max.val ∈ arr.val := by
      apply maxFloatNonNaN_mem
      · grind only [usr Subtype.property, !lowerList_nonempty]
    ⟨max, by
      have hmax := max.property.right
      have harr := arr.property
      simp [arr.property] at hmax

      constructor
      · simp
        have := max.property.right
        have := arr.property max |>.mp (by grind only)
        simp at this
        grind only
      · intros lower hlower
        simp at hlower
        have := max.property.right lower
        simp at this
        apply PackedFloat.le_of_toExtRat'_le_toExtRat'
        · grind only
        · grind only
        · intros hcontra
          simp [hcontra] at hlower
          grind only
        · grind only
        · intros hmax hlowerzero hmaxsign
          simp [hlowerzero, hmaxsign] at hlower
          sorry
        · sorry
        ·
          apply PackedFloat.toExtRat'_le_toExtRat'_of_le
          · grind
          · grind
          · grind
          · apply this
            rw [arr.property lower]
            simp only [Bool.not_eq_true, PackedFloat.toExtRat_eq_toExtRat']
            constructor
            · apply Classical.byContradiction
              intro hcontra
              simp at hcontra
              simp [hcontra] at hlower
              grind only
            · grind only
    ⟩
-/

structure PackedFloatEnumeration (e : Nat) (s : Nat) where ofEnumeration ::
  -- | Sorted array of packed float with its rational value. Only numbers,
  -- no infinities and NaNs.
  enumeration : Array (PackedFloat e s)


def PackedFloatEnumeration.mk (e s : Nat) : PackedFloatEnumeration e s where
  enumeration := Id.run do
    let mut arr : Array (PackedFloat e s) := #[]
    for sign in [true, false] do
      for exp in [:2^e] do
        for sig in [:2^s] do
          let pf : PackedFloat e s := PackedFloat.mk sign exp sig
          let er := pf.toExtRat
          let ExtRat.Number r := er
            | continue
          arr := arr.push pf
    arr.qsort (fun a b => a ≤ b)

def PackedFloatEnumeration.minNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  let num := enum.enumeration[0]!
  (num, num.toRat)

def PackedFloatEnumeration.maxNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  let num := enum.enumeration[enum.enumeration.size - 1]!
  (num, num.toRat)

def PackedFloatEnumeration.greatestLowerBound (enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut glb? := none
  for hi : i in [:arr.size] do
    let curPf := arr[i]
    let curRat := curPf.toRat
    if curRat <= r then
        -- is a lower bound
        glb? :=
          match glb? with
          | none => some (curPf, curRat)
          | some (_, glbRat) =>
            -- is larger than the current lower bound.
            if curRat > glbRat then
              some (curPf, curRat)
            else
              glb?
  glb?

def PackedFloatEnumeration.leastUpperBound (
    enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut lub? := none
  for hi : i in [0:arr.size] do
    let curPf := arr[i]
    let curRat := curPf.toRat
    if curRat >= r then
        -- is an upper bound
        lub? :=
          match lub? with
          | none => some (curPf, curRat)
          | some (_, lubRat) =>
            -- is smaller than the current upper bound.
            if curRat < lubRat then
              some (curPf, curRat)
            else
              lub?
  lub?

end Fp
