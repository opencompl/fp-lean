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

instance HExOffsetPow [h : HExOffset exWidth sigWidth] :
   HExOffset (2 ^ (exWidth - 1) + sigWidth - 2) (2 ^ exWidth + sigWidth) where
  h := by
    have := h.h
    simp
    rcases exWidth with rfl | exWidth
    · simp
      omega
    · simp
      rw [Nat.pow_succ]
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

@[simp]
def FixedPoint.natAbs_toInt_eq_toNat [HExOffset e m] (f : FixedPoint m e) :
    (f.toInt).natAbs = f.val.toNat := by
  simp [FixedPoint.toInt]
  by_cases hsign : f.sign <;> simp [hsign]

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

def Rat.abs (r : Rat) : Rat :=
  if r < 0 then -r else r

/-- Pushes 'Dyadic.toRat' into a 'Dyadic.abs'. -/
@[simp]
theorem Dyadic.toRat_abs_eq_abs_toRat (d : Dyadic) :
    d.abs.toRat = d.toRat.abs := by
  simp [Dyadic.abs]
  have := Dyadic.toRat_lt_toRat_iff (x := d) (y := 0)
  simp at this
  by_cases hlt : d < 0 <;> simp [Rat.abs, hlt] <;> grind

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
inductive GoodRNEDyadic
    (d : Dyadic)
    (e : Nat)
    (m : Nat)
    [hEx : HExOffset m e] :
    (e : EFixedPoint e m) → Prop
| posInfty : GoodRNEDyadic   d e m (EFixedPoint.getInfinity false hEx.h)
| negInfty : GoodRNEDyadic   d e m (EFixedPoint.getInfinity true hEx.h)
| fixedPoint (hx : ClosestRNE d x) : GoodRNEDyadic d e m (EFixedPoint.getFixedPoint x)

-- TOOD: show that GoodRNEDyadic is mutually exclusive.
-- TOOD: show that GoodRNEDyadic picks out a unique number.
-- TODO: show that the output of 'round' is always a GoodRNEDyadic.


/-
Now, we need a mechanization of rounding. This needs us to talk about the closest
floating point number to a given dyadic rational.
For now, let's pick RNE (round to nearest even) as our canonical rounding mode,
and just perform proofs on this.
-/
-- #check round_to_packedFloat
#check EFixedPoint.getNaN


section Rounding

variable {exWidth sigWidth : Nat} [hExOffset : HExOffset exWidth sigWidth]


@[simp]
theorem round_rne_nan_eq_nan : round_to_packedFloat exWidth sigWidth RoundingMode.RNE
    (EFixedPoint.getNaN hExOffset.h) =
  PackedFloat.getNaN exWidth sigWidth := by
  simp [round_to_packedFloat]

@[simp]
theorem round_rne_infty_eq_infty (s : Bool) :
  round_to_packedFloat exWidth sigWidth RoundingMode.RNE
    (EFixedPoint.getInfinity s hExOffset.h) =
  PackedFloat.getInfinity exWidth sigWidth s := by
  simp [round_to_packedFloat]


/-- the is_over condition checks a bitvector right shift being not equal to zero. -/
theorem is_over_eq_decide (x : EFixedPoint width exOffset) (exWidth : Nat) :
    is_over x exWidth =
    decide (x.num.val >>> (exOffset + 2^(exWidth-1)) ≠ 0) := by
  simp [is_over]
  by_cases hx : ((x.num.val >>> (exOffset + 2^(exWidth-1))) = (BitVec.ofNat width 0))
  · simp [hx]
  · simp [hx]


/-- The 'is_over' condition checks that the absolute value of the number in the fixed point interpretation
is larger than the width times the largest representable number in exWidth bits. -/
theorem is_over_iff_decide_le_toNat
    (x : EFixedPoint width exOffset) (exWidth : Nat) :
    is_over x exWidth =
    decide (2^(exOffset + (2^(exWidth - 1))) ≤ x.num.val.toNat) := by
  rw [is_over_eq_decide]
  simp only [BitVec.ofNat_eq_ofNat, ne_eq, decide_not, Bool.not_eq_eq_eq_not]
  rw [← decide_not]
  simp only [decide_eq_decide]
  rw [← BitVec.toNat_inj]
  simp
  constructor
  · intros h
    rw [Nat.shiftRight_eq_div_pow] at h
    apply Nat.lt_of_div_eq_zero
    · apply Nat.two_pow_pos
    · exact h
  · intros h
    apply Nat.shiftRight_eq_zero
    exact h

/-- The 'is_over' condition checks that the absolute value of the number in the fixed point interpretation
is larger than the width times the largest representable number in exWidth bits. -/
theorem is_over_iff_decide_le_toDyadic [HExOffset exOffset width]
    (x : EFixedPoint width exOffset) (exWidth : Nat) :
    is_over x exWidth =
    decide (2^(exOffset + (2^(exWidth - 1))) ≤ x.num.toDyadic.abs) := by
  rw [is_over_iff_decide_le_toNat]
  simp
  rw [FixedPoint.toDyadic]
  rw [← Dyadic.toRat_le_toRat_iff]
  simp
  rw [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  simp
  norm_cast
  sorry



def PackedFloat.toDyadic [h : HExOffset (2 ^ (exWidth - 1) + sigWidth - 2) (2 ^ exWidth + sigWidth)]
    (pf : PackedFloat exWidth sigWidth) : Dyadic :=
  PackedFloat.toEFixed pf |>.num.toDyadic

-- @[bv_float_normalize]
-- def round_to_efixedpoint [HExOffset exWidth sigWidth] [h : HExOffset exWidth sigWidth] [HExOffset exWidth sigWidth] [HExOffset exOffset width]
--   (exWidth sigWidth : Nat) (mode : RoundingMode) (x : EFixedPoint width exOffset)
--   : EFixedPoint (2 ^ exWidth + sigWidth) (2 ^ (exWidth - 1) + sigWidth - 2) :=
--   if hNaN: x.state = .NaN then
--     EFixedPoint.getNaN sorry
--   else if hInfty : x.state = .Infinity then
--     -- +infty ↦ +infty
--     -- infty ↦ -infty
--     EFixedPoint.getInfinity x.num.sign (by sorry)
--   else
--     let exOffset' := 2^(exWidth - 1) + sigWidth - 2 -- new offset corresponding to EFixedPoint ~= output packedFloat.
--     -- trim bitvector
--     -- 'over' is x/2^(exOffset + 2^(exWidth-1)), but this is the following:
--     -- we take the EFixedpoint value, and interpret it as a rational, giving us
--     -- 'x / 2^exOffset'.
--     -- Then, we consider the largest exponent we can represent in the floating point format,
--     -- which is 'e := 2^(exWidth-1) - 1' (since ex is stored with a bias of '2^(exWidth-1) - 1').
--     -- Now, the largest FP number has exponent 'e', which means its value is
--     -- 'sig * 2^e' (where 'sig' is the significand interpreted as a rational).
--     -- So, this means that the largest FP number represents values up to
--     -- 'sig * 2^(2^(exWidth-1) - 1)'
--     -- Therefore, to check if 'x' overflows, we check if
--     -- 'x / 2^exOffset >= 2^(2^(exWidth-1) - 1)', or equivalently,
--     -- 'x >= 2^(exOffset + 2^(exWidth-1) - 1)'.
--     let xhi := x.num.val >>> exOffset
--     let xlo := x.num.val.truncate exOffset

--     -- | a := truncate high bits, keeping 2^(exWidth-1) bits
--     let a := (xhi).truncate (2^(exWidth-1))
--     -- | b := truncate low bits, keeping exOffset' bits
--     let b := truncateRight exOffset' xlo
--     let trimmed := a ++ b
--     -- largest output value.
--     let over := xhi >>> 2^(exWidth-1) -- over := does it overflow?
--     if hOverflow : over != 0 then
--       -- Overflow to Infinity
--       -- Unless we're rounding RTN/RTP to the opposite sign, or RTZ
--       -- in which case we overflow to MAX
--       if hround : (mode = .RTN ∧ ¬x.num.sign) ∨ (mode = .RTP ∧ x.num.sign) ∨ mode = .RTZ then
--         EFixedPoint.getMax _ _ x.num.sign (by sorry)
--         -- EFixedPoint.getMax _ _ x.num.sign
--       else
--         EFixedPoint.getInfinity x.num.sign (by sorry)
--         -- have : HExOffset (2 ^ (exWidth - 1) + sigWidth - 2) (2 ^ exWidth + sigWidth):= sorry
--         -- have : hMaxOut.toDyadic.abs < x.num.toDyadic.abs := sorry
--         -- PackedFloat.getInfinity _ _ x.num.sign
--     else
--       -- | This tells us the largest power of 2 we need to fit 'trimmed'.
--       let index := fls trimmed -- index of first 1 bit (most significant)
--       let sigWidthBV := BitVec.ofNat _ sigWidth -- bitvec of sigWidth
--       let ex : BitVec exWidth := -- exponent
--         if index ≤ sigWidthBV then
--           0
--         else
--           (index - sigWidthBV).truncate _
--       let truncSig : BitVec sigWidth :=
--         if ex = 0 then
--           trimmed.truncate _
--         else
--           (trimmed >>> (ex - 1)).truncate _
--       -- under = stuff that's left over?
--       let underWidth := exOffset - exOffset'
--       let under := x.num.val.truncate underWidth
--       let rem : BitVec (2^exWidth + underWidth) :=
--         if ex = 0 then
--           under.truncate _ <<< (1 <<< exWidth)
--         else
--           let totalShift : BitVec (exWidth+1) := ex.truncate _ - 1
--           truncateRight _ (trimmed <<< ((1 <<< exWidth) + sigWidth - 2 - totalShift)) |||
--           (under.truncate _ <<< ((1 <<< exWidth) - totalShift))
--       if shouldRoundAway mode x.num.sign (truncSig.getLsbD 0) rem then
--         if truncSig = BitVec.allOnes _ then
--           -- overflow to next exponent
--           {
--             sign := x.num.sign
--             ex := ex+1
--             sig := 0
--           }
--         else
--           -- add 1 to significand
--           {
--             sign := x.num.sign
--             ex
--             sig := truncSig + 1
--           }
--       else
--       -- leave everything the same
--       {
--         sign := x.num.sign
--         ex
--         sig := truncSig
--       }

def BitVec.monus {n : Nat} (a b : BitVec n) : BitVec n :=
  if a ≤ b then 0#n else a - b

@[simp]
theorem BitVec.sub_eq_zero_iff_eq (n : Nat) (a b : BitVec n) :
    a - b = 0#n ↔ a = b := by
  constructor
  · intro h
    rw [BitVec.sub_eq_iff_eq_add] at h
    simp at h
    simp [h]
  · intro h
    subst h
    simp

@[simp]
theorem BitVec.monus_eq_zero_iff_le (n : Nat) (a b : BitVec n) :
    BitVec.monus a b = 0#n ↔ a ≤ b := by
  simp [BitVec.monus]
  by_cases hle : a ≤ b
  · simp [hle]
    bv_omega
  · simp [hle]
    simp at hle
    constructor
    · bv_omega
    · intros h
      subst h
      bv_omega

@[simp]
theorem BitVec.monus_eq_minus_of_lt (n : Nat) (a b : BitVec n) (hlt : b < a) :
    BitVec.monus a b = a - b := by
  simp [BitVec.monus]
  intros h
  symm
  rw [BitVec.sub_eq_iff_eq_add]
  simp
  bv_omega


/-- Convert a bitvector to a fixed-point rational number with a given exponent. -/
def BitVec.toUnsignedFixedPointRat {n : Nat} (b : BitVec n) (exp : Nat) : Rat :=
  mkRat (b.toNat) (2 ^ exp)

/-#

rem: 2^exWidth + underWidth width
   : 2^exwidth + (exOffset - outputExOffset)
rem: fixed point representation of under.

output:>-------------------exwidth----<|>-------sigwidth-------<
                                            @<=========================i ndex
                                            @
                                            @
:                  (---2^(exWidth-1)---||---@outputExOffset---)
                   (---------TRIMMED--------------------------)
   (--------over--](---trimmedHi-------][-----trimmedLo-------)[-under-)
   (--------------xhi------------------][----------------xlo-----------]
x: (-----------------------------------@-------------------------------] WIDTH size. [Implicit * 2^-exOffset]
                                       @
                                       @
                                       @<=============================== exOffset


-/
@[bv_float_normalize]
def round_to_packedfloat' [h : HExOffset exWidth sigWidth] [HExOffset exOffset width]
  (exWidth sigWidth : Nat) (mode : RoundingMode) (x : EFixedPoint width exOffset)
  [HExOffset (2 ^ (exWidth - 1) + sigWidth - 2) (2 ^ exWidth + sigWidth)]
  (hOutputExOffsetSmaller : 2 ^ (exWidth - 1) + sigWidth - 2 < exOffset) -- outputExOffset < exOffset
  : PackedFloat exWidth sigWidth :=
  if hNaN: x.state = .NaN then
    PackedFloat.getNaN _ _ -- nan is propagated.
  else if hInfty : x.state = .Infinity then
    -- +infty ↦ +infty
    -- infty ↦ -infty
    PackedFloat.getInfinity _ _ x.num.sign
  else
    let ratX := BitVec.toUnsignedFixedPointRat x.num.val exOffset
    let outputExOffset := 2^(exWidth - 1) + sigWidth - 2 -- new EFixedPoint offset corresponding to EFixedPoint ~= output packedFloat.
    -- trim bitvector
    -- 'over' is x/2^(exOffset + 2^(exWidth-1)), but this is the following:
    -- we take the EFixedpoint value, and interpret it as a rational, giving us
    -- 'x / 2^exOffset'.
    -- Then, we consider the largest exponent we can represent in the floating point format,
    -- which is 'e := 2^(exWidth-1) - 1' (since ex is stored with a bias of '2^(exWidth-1) - 1').
    -- Now, the largest FP number has exponent 'e', which means its value is
    -- 'sig * 2^e' (where 'sig' is the significand interpreted as a rational).
    -- So, this means that the largest FP number represents values up to
    -- 'sig * 2^(2^(exWidth-1) - 1)'
    -- Therefore, to check if 'x' overflows, we check if
    -- 'x / 2^exOffset >= 2^(2^(exWidth-1) - 1)', or equivalently,
    -- 'x >= 2^(exOffset + 2^(exWidth-1) - 1)'.
    let xhi := x.num.val >>> exOffset
    have hXhi : xhi.toNat = x.num.val.toNat / (2 ^ exOffset) := by
      simp [xhi, Nat.shiftRight_eq_div_pow]
    let xlo := x.num.val.truncate exOffset
    have : xlo.toNat = x.num.val.toNat % (2 ^ exOffset) := by
      simp [xlo]
    have : x.num.val = (xhi <<< exOffset) ||| (xlo.zeroExtend _) := by
      ext i
      simp [xhi, xlo]
      by_cases hi : i < exOffset
      · simp [hi]
        rfl
      · simp [hi]
        simp [show exOffset + (i - exOffset) = i by omega]
        rfl
    let over := xhi >>> 2^(exWidth-1) -- over := does it overflow?
    have hOver : over.toNat = x.num.val.toNat / (2 ^ (exOffset + 2^(exWidth-1))) := by
      simp [over, hXhi, Nat.shiftRight_eq_div_pow]
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.pow_add]
    -- at this point, trimmed represents an EFixedPoint with offset 'outputExOffset'.
    -- of the original number 'x'.
    -- We can precisely quantify how many bits we have lost in the precision at this stage if we want to.
    -- largest output value.
    let hMaxOut := PackedFloat.getMax exWidth sigWidth x.num.sign
    if hOverflow : over != 0 then
      have : hMaxOut.toDyadic.abs < x.num.toDyadic.abs  := sorry
      -- Overflow to Infinity
      -- Unless we're rounding RTN/RTP to the opposite sign, or RTZ
      -- in which case we overflow to MAX
      if hround : (mode = .RTN ∧ ¬x.num.sign) ∨ (mode = .RTP ∧ x.num.sign) ∨ mode = .RTZ then
        PackedFloat.getMax _ _ x.num.sign
      else
        PackedFloat.getInfinity _ _ x.num.sign
    else
      -- | trimmedHi := truncate high bits, keeping 2^(exWidth-1) bits.
      -- But note that this is equal to 'xhi' as a value, since we are not overflowing.
      let trimmedHi := (xhi).truncate (2^(exWidth-1))
      have hTrimmedHi :
          trimmedHi.toNat = (x.num.val.toNat / (2 ^ (exOffset ))) := by
        simp [trimmedHi, hXhi]
        rw [Nat.mod_eq_of_lt]
        simp only [BitVec.ofNat_eq_ofNat, bne_iff_ne, ne_eq, Decidable.not_not] at hOverflow
        simp [over] at hOverflow
        rw [← BitVec.toNat_inj] at hOverflow
        simp at hOverflow
        rw [Nat.shiftRight_eq_div_pow] at hOverflow
        have hOverflow := Nat.lt_of_div_eq_zero (x := xhi.toNat) (k := 2 ^ (2^(exWidth-1))) (by apply Nat.two_pow_pos) hOverflow
        rw [hXhi] at hOverflow
        exact hOverflow
      -- | trimmedLo := truncate low bits, keeping exOffset' bits
      let trimmedLo := truncateRight outputExOffset xlo
      -- Drop the excess low bits, which are not representable given outputExOffset number of low bits.
      have hTrimmedLo : trimmedLo.toNat = (x.num.val.toNat % 2 ^ exOffset) >>> (exOffset - outputExOffset) := by
        simp only [truncateRight.eq_1, eq_mp_eq_cast, BitVec.truncate_eq_setWidth, trimmedLo]
        have : ¬ exOffset ≤ outputExOffset := by
          simp [outputExOffset]
          omega
        simp [this]
        simp [xlo]
        rw [Nat.mod_eq_of_lt]
        rw [Nat.shiftRight_eq_div_pow]
        have := Nat.mod_lt (x := x.num.val.toNat) (y := 2 ^ exOffset) (by omega)
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add]
        rw [show exOffset - outputExOffset + outputExOffset = exOffset by omega]
        omega
      let trimmed := trimmedHi ++ trimmedLo


      have : x.num.toDyadic.abs ≤ hMaxOut.toDyadic.abs := sorry
      -- Great, we are within range.
      -- | This is a bit counter-intuitive, I would have assumed we would have looked for 'fls' inside 'trimmedHi'??
      -- | This tells us the largest power of 2 we need to fit 'trimmed'.
      let firstNonzeroIndexTrimmedBV := fls trimmed -- index of first 1 bit (most significant)
      -- all bits at and above 'index' are zero.
      have hIndexGe : ∀ i, firstNonzeroIndexTrimmedBV.toNat ≤ i → trimmed.getLsbD i = false := by
        apply getLsbD_eq_false_of_ge_fls
      let sigWidthBV := BitVec.ofNat _ sigWidth -- bitvec of sigWidth
      -- outExponent : BitVec exWidth :=  (BitVec.monus index sigWidthBV).truncate _
      let outExponent : BitVec exWidth := (BitVec.monus firstNonzeroIndexTrimmedBV sigWidthBV).truncate _ -- new exponent.
        -- if firstNonzeroIndexTrimmedBV ≤ sigWidthBV then -- if our number is entirely contained in the significand, then exponent is zero.
        --   0
        -- else
        --   -- else, we need (index - sigWidthBV) bits of exponent.
        --   -- Interesting, TODO: if we had BitVec.monus, then this would be cleaner.
        --   (firstNonzeroIndexTrimmedBV - sigWidthBV).truncate _
      -- truncated significand, morally equal to 'trimmed >>> max(0, outExponent - 1)'
      let truncSig : BitVec sigWidth := (trimmed >>> (BitVec.monus outExponent 1#exWidth)).truncate _
      have : truncSig.toNat = trimmed.toNat / (2 ^ (outExponent.toNat - 1)) := by
        simp [truncSig]
        rw [Nat.shiftRight_eq_div_pow]
        rw [BitVec.monus]
        split
        case isTrue h =>
          simp
          have : outExponent.toNat = 1 := by
            rw [BitVec.le_def] at h
            simp at h
            sorry
          simp [this]
          rw [Nat.mod_eq_of_lt]
          apply Nat.lt_of_lt_of_le
          · apply BitVec.isLt
          · sorry
        case isFalse h =>
          simp at h
          rw [BitVec.toNat_sub_of_le]
          · sorry
          · bv_omega
        -- -- if the output exponent is zero, then we have enough space
        -- -- in the significand to hold everything.
        -- -- So we just take it.
        -- if outExponent = 0 then
        --   trimmed.truncate _
        -- else
        --   -- drop the stuff that's in the exponent,
        --   -- TODO: (why outExponent - 1?)
        --   --   Is it because we have a leading 1?
        --   -- and then truncate.
        --   (trimmed >>> (outExponent - 1)).truncate _
      -- under = stuff that's left over below the trimmed.
      let underWidth := exOffset - outputExOffset
      let under := x.num.val.truncate underWidth
      --- TODO: think about 'rem' tomorrow.
      -- when outExponent is zero, we truncate to (2^exWidth + underWidth), and then move the data
      -- by shifting left 2^exWidth

      let rem : BitVec (2^exWidth + underWidth) :=
        if hOutExponentEqZero : outExponent = 0 then
          -- [underMsb...  ...underLsb] [0.. [ 2^exWidth ] ..0]
          -- Set the high bits to the 2^exwidth part.
          let out := under.truncate (2^exWidth + underWidth) <<< (1 <<< exWidth)
          have outLowBits : ∀ i < 2^exWidth, out.getLsbD i = false := by
            simp [out]
            intros i hi hi'
            omega
          out
        else
          let outExponentMinusOne : BitVec (exWidth+1) := outExponent.truncate _ - 1
          have hOutExponentMinusOne : outExponentMinusOne.toNat =
            outExponent.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le]
            · simp
            · rw [BitVec.le_def]
              simp
              have : outExponent.toNat ≠ 0 := by
                intros hcontra
                apply hOutExponentEqZero
                apply BitVec.eq_of_toNat_eq
                simp [hcontra]
              omega
          -- push the bottom bits of trimmed into the high region (1 <<< exWidth),
          -- and then do ???
          let out := truncateRight (2^exWidth + underWidth) (trimmed <<< ((1<<<exWidth) + sigWidth - 2 - outExponentMinusOne)) |||
            -- push the 'under' bits to the high region (1 <<< exWidth), and then push it back by outExponentMinusOne.
            (under.zeroExtend (2^exWidth + underWidth) <<< ((1<<<exWidth) - outExponentMinusOne))
          have outLowBits : ∀ i < 2^exWidth, out.getLsbD i = false := by
              -- TODO: what the heck is going on here?
              sorry
          out
      if shouldRoundAway mode x.num.sign (truncSig.getLsbD 0) rem then
        if truncSig = BitVec.allOnes _ then
          -- overflow to next exponent
          {
            sign := x.num.sign
            ex := outExponent+1
            sig := 0
          }
        else
          -- add 1 to significand
          {
            sign := x.num.sign
            ex := outExponent
            sig := truncSig + 1
          }
      else
      -- leave everything the same
      {
        sign := x.num.sign
        ex := outExponent
        sig := truncSig
      }


omit hExOffset in
/--
If we are 'is_over' (i.e. the value overflows), the rounding gives infinity.
-/
@[simp]
theorem round_eq_infty_of_is_over {x : EFixedPoint width exOffset}
  (hover : is_over x exWidth = true) (hstate : x.state = .Number):
  round_to_packedFloat exWidth sigWidth RoundingMode.RNE x  =
  PackedFloat.getInfinity exWidth sigWidth x.num.sign := by
  simp only [round_to_packedFloat]
  simp only [hstate]
  simp only [reduceCtorEq, ↓reduceIte, bne_iff_ne, ne_eq, Bool.not_eq_true,
    false_and, or_self]
  simp [is_over] at hover
  simp [hover]



-- theorem round_rne_eq_infty_of_overflow

end Rounding
