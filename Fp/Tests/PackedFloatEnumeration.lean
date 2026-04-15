import Fp.Rounding
import Fp.SmtLibSemantics
import Fp.Theorems.Basic
import Fp.Theorems.Packing
import Fp.Theorems.Packing

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

-- /-- enumerate only numbers -/
-- def enumerateNumberPackedFloatArray (e s : Nat) :
--     {xs : Array (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ ¬ x.isNaN ∧ ¬ x.isInfinite} :=
--   let arr := enumeratePackedFloatArray e s
--   let xs := arr.val.filter (fun pf => ¬ pf.isNaN && ¬ pf.isInfinite)
--   ⟨xs, by
--     intros x
--     simp [xs]
--     grind only [#ca5c]
--   ⟩

def lower (e s : Nat) (r : ExtRat) :
    { xs : List (PackedFloat e s) // ∀ (x : PackedFloat e s), x ∈ xs ↔ x.toExtRat ≤ r } :=
    let arr := enumeratePackedFloatList e s
    let out := arr.val.filter (fun pf => pf.toExtRat ≤ r)
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


def glbLower (e s : Nat) (he : 0 < e) (hs : 0 < s) (r : ExtRat) :
    { pf : PackedFloat e s //
      pf.toExtRat ≤ r ∧ (¬ r.isNaN → ∀ pf' : PackedFloat e s, pf'.toExtRat ≤ r → pf'.toExtRat ≤ pf.toExtRat) } :=
  if hr : r = .NaN then
    ⟨PackedFloat.getNaN e s, by
      simp [hr, hs]⟩
  else
    let arr := enumeratePackedFloatArray e s
    sorry

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
  enum.enumeration[0]!

def PackedFloatEnumeration.maxNumber (enum : PackedFloatEnumeration e s) : PackedFloat e s × Rat :=
  enum.enumeration[enum.enumeration.size - 1]!


def PackedFloatEnumeration.greatestLowerBound (enum : PackedFloatEnumeration e s)
    (r : Rat) : Option (PackedFloat e s × Rat) := Id.run do
  let arr := enum.enumeration
  let mut glb? := none
  for hi : i in [:arr.size] do
    let (curPf, curRat) := arr[i]
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
    let (curPf, curRat) := arr[i]
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
