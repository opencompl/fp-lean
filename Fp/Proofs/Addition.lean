import Init.Data.Dyadic
import Fp.Addition


open Lean

class HExOffset (e : Nat) (m : Nat) where
  h : e < m

instance HExOffsetSucc [hex : HExOffset e m] :
    HExOffset e (m + 1) where
  h := by
    have := hex.h
    omega

/-- Build a fixed point number from an integer. -/
def FixedPoint.ofInt (i : Int) [HExOffset e m] : FixedPoint m e :=
  {
    sign := i < 0
    val := BitVec.ofNat m (i.natAbs)
    hExOffset := HExOffset.h
  }

/-- Convert a fixed point number to an integer. -/
def FixedPoint.toInt [HExOffset e m] (f : FixedPoint m e) : Int :=
  let n := f.val.toNat
  if f.sign then
    -Int.ofNat n
  else
    Int.ofNat n

/-- convert the sign bit to an integer value. Morally, this is (-1)^s -/
def signToInt (s : Bool) : Int :=
  if s then -1 else 1

/-- write the sign bit as two pow. -/
@[simp]
theorem signToInt_eq_negOne_pow_toNat (s : Bool) :
  signToInt s = (-1 : Int) ^ s.toNat := by
  cases s
  · simp [signToInt]
  · simp [signToInt]


/-- make power of two as a dyadic number. -/
def Dyadic.twoPow (n : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec 1 (-n)

/-- the power of two as a rational number is what you'd expect it to be. -/
theorem Dyadic.twoPow_eq (n : Nat) :
    (Dyadic.twoPow n |>.toRat) = mkRat (2 ^ n) 1 := by
  simp only [twoPow]
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  simp only [Int.neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, Nat.shiftLeft_zero]
  congr
  rw [Int.shiftLeft_eq]
  simp only [Int.one_mul]

/-- Truncate a dyadic number to a fixed-point number. -/
def FixedPoint.ofDyadic [HExOffset e m] (d : Dyadic) : FixedPoint m e :=
  FixedPoint.ofInt <| (Dyadic.mul d (Dyadic.twoPow e)).toRat.num

/-- Convert a dyadic number to a fixed-point number. -/
def FixedPoint.toDyadic [HExOffset e m] (f : FixedPoint m e) : Dyadic :=
  Dyadic.ofIntWithPrec (f.val.toNat * (signToInt f.sign)) e

/-- Show that a dyadic number corresponds to a fixed-point number. -/
structure DyadicEqualsFixedPoint [HExOffset e m] (d : Dyadic) (f : FixedPoint m e) where
    h : FixedPoint.toDyadic f = d

theorem DyadicEqualsFixedPoint_of_eq [HExOffset e m]
  {d : Dyadic} {f : FixedPoint m e}
  (h : FixedPoint.toDyadic f = d) :
    DyadicEqualsFixedPoint d f :=
  ⟨h⟩

/-- The dyadic number equals the fixed point number. -/
notation (name := dyadicSim) f "∼d " d => (DyadicEqualsFixedPoint d f)

theorem Dyadic.eq_iff_toRat_eq (d₁ d₂ : Dyadic) :
    d₁ = d₂ ↔ d₁.toRat = d₂.toRat := by
  constructor
  · intros h
    subst d₁
    simp
  · intros h
    rw [← Dyadic.toRat_inj, h]

@[simp]
theorem Rat.mkRat_add_mkRat_eq_mkRat_add (n₁ n₂ : Int) {d} (hd : d ≠ 0)  :
    mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d:= by
  rw [← normalize_eq_mkRat hd,
    ← normalize_eq_mkRat hd,
    normalize_add_normalize,
    normalize_eq_mkRat]
  rw [show n₁ * d + n₂ * d = (n₁ + n₂) * d by grind]
  rw [mkRat_mul_right hd]


/-- Two rational numbers with the same denominator are equal
iff the numerators are equal, when the denominator is nonzero. -/
@[simp]
theorem Rat.mkRat_eq_iff_numerator {n₁ n₂ : Int} {d : Nat} (hd : d ≠ 0):
    (mkRat n₁ d = mkRat n₂ d) ↔ (n₁ = n₂) := by
  constructor
  · intros heq
    rw [mkRat_eq_iff] at heq
    · rw [Int.mul_eq_mul_right_iff (by simpa using hd)] at heq
      exact heq
    · exact hd
    · exact hd
  · intros heq
    subst heq
    rfl

theorem fp_add_dyadic [HExOffset e m] (da db : Dyadic) (fa fb : FixedPoint m e)
 (ha : fa ∼d da) (hb : fb ∼d db) (mode : RoundingMode)
  : (f_add mode fa fb) ∼d  (da + db) := by
  apply DyadicEqualsFixedPoint_of_eq
  rw [f_add]
  by_cases hsign : fa.sign = fb.sign
  case pos =>
    simp [hsign]
    rw [FixedPoint.toDyadic]
    simp
    obtain ⟨ha⟩ := ha
    obtain ⟨hb⟩ := hb
    subst ha
    subst hb
    rw [FixedPoint.toDyadic]
    rw [FixedPoint.toDyadic]
    rw [Dyadic.eq_iff_toRat_eq]
    simp
    -- extract out into a single theorem.
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
    simp
    norm_cast
    rw [Nat.mod_eq_of_lt]
    · rw [hsign]; grind
    · rw [Nat.pow_succ]; omega
  case neg => sorry
