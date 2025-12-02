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
  case neg =>
    simp [hsign]
    split
    case isTrue hlt =>
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
      rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
      rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
      rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
      simp
      norm_cast
      -- rw [Nat.mod_eq_of_lt]
      rw [BitVec.ult_eq_decide] at hlt
      simp at hlt
      have hfa : fa.val.toNat < 2^ m := by omega
      have hfb : fb.val.toNat < 2^ m := by omega
      rw [show (2 ^ (m + 1) - fa.val.toNat + fb.val.toNat) =
        (2 ^ (m + 1) + (fb.val.toNat - fa.val.toNat)) by omega]
      simp
      norm_cast
      rw [Nat.mod_eq_of_lt (by omega)]
      rcases hfa : fa.sign with rfl | rfl
      case false =>
        simp [hfa] at ⊢ hsign
        simp [hsign]
        omega
      case true =>
        simp [hfa] at ⊢ hsign
        simp [hsign]
        omega
    case isFalse hlt =>
      split
      case isTrue hlt =>
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
        rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
        rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
        rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
        simp
        norm_cast
        -- rw [Nat.mod_eq_of_lt]
        rw [BitVec.ult_eq_decide] at hlt
        simp at hlt
        have hfa : fa.val.toNat < 2^ m := by omega
        have hfb : fb.val.toNat < 2^ m := by omega
        rw [show (2 ^ (m + 1) - fb.val.toNat + fa.val.toNat) =
          (2 ^ (m + 1) + (fa.val.toNat - fb.val.toNat)) by omega]
        simp
        norm_cast
        rw [Nat.mod_eq_of_lt (by omega)]
        rcases hfa : fa.sign with rfl | rfl
        case false =>
          simp [hfa] at ⊢ hsign
          simp [hsign]
          omega
        case true =>
          simp [hfa] at ⊢ hsign
          simp [hsign]
          omega
      case isFalse hlt₂ =>
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
        rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
        rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
        simp
        norm_cast
        -- rw [Nat.mod_eq_of_lt]
        rw [BitVec.ult_eq_decide] at hlt
        simp at hlt
        rw [BitVec.ult_eq_decide] at hlt₂
        simp at hlt₂
        have : fa.val.toNat = fb.val.toNat := by omega
        rw [this]
        rcases hsign : fb.sign with rfl | rfl
        case false =>
          have : fa.sign = true := by simp_all
          simp [this]
          norm_cast
          simp [show - (fb.val.toNat : Int) + (fb.val.toNat : Int) = 0 by omega]
        case true =>
          have : fa.sign = false := by simp_all
          simp [this]
          norm_cast
          simp [show (fb.val.toNat : Int) + -(fb.val.toNat : Int) = 0 by omega]

/-- info: 'fp_add_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fp_add_dyadic


/-- absolute value of a dyadic number -/
def Dyadic.abs (d : Dyadic) : Dyadic :=
  if d < 0 then -d else d

/-- Distance between two dyadic numbers -/
def Dyadic.distance (d1 d2 : Dyadic) : Dyadic := (d1 - d2).abs


def Dyadic.numerator (d : Dyadic) : Int :=
  d.toRat.num

/--
Either 'fx' is closer to 'd' than y,
or 'fx' is and 'y' are equidistant, but
then 'fx' is even, and 'y' is odd.
-/
inductive CloseOrRounded [HExOffset m e]
    (d : Dyadic)
    (lim y : FixedPoint e m) : Prop
| close : (d.distance lim.toDyadic < d.distance y.toDyadic) → CloseOrRounded d lim y
| rounded
    (hdeq : d.distance lim.toDyadic = d.distance y.toDyadic)
    (hxEven: lim.toDyadic.numerator.natAbs % 2 = 0)
    (hyOdd : y.toDyadic.numerator.natAbs % 2 ≠ 0) :
    CloseOrRounded d lim y

/-- ClosestRNE means that 'x' is the closest to 'd' according to round to nearest even -/
def ClosestRNE [HExOffset m e] (d : Dyadic) (lim : FixedPoint e m) : Prop :=
    ∀ (y : FixedPoint e m),
     CloseOrRounded d lim y

/-- An inductive predicate that 'd' is correctly rounded to even to create 'e' -/
inductive GoodRNE
    (d : Dyadic)
    (e : Nat)
    (m : Nat)
    [hEx : HExOffset m e] :
    (e : EFixedPoint e m) → Prop
| posInfty : GoodRNE d e m (EFixedPoint.getInfinity false hEx.h)
| negInfty : GoodRNE d e m (EFixedPoint.getInfinity true hEx.h)
| fixedPoint (hx : ClosestRNE d x) : GoodRNE d e m (EFixedPoint.getFixedPoint x)


-- TOOD: show that GoodRNE is mutually exclusive.
-- TOOD: show that GoodRNE picks out a unique number.
-- TODO: show that the output of 'round' is always a GoodRNE.

/-

Now, we need a mechanization of rounding. This needs us to talk about the closest
floating point number to a given dyadic rational.
For now, let's pick RNE (round to nearest even) as our canonical rounding mode,
and just perform proofs on this.
-/

#check round
#check EFixedPoint.getNaN


/-
def round (x : FixedPoint width exOffset) :
  (exWidth sigWidth : Nat) (mode : RoundingMode) (x : EFixedPoint width exOffset)
  : PackedFloat exWidth sigWidth :=
-/
