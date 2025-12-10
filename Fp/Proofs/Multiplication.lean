import Fp.Basic
import Fp.Rounding
import Fp.Multiplication
import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat

@[grind .] -- What is a grind '.' pattern?
theorem mkRat_eq_mkRat_of_eq_of_eq
  {n1 n2 : Int}
  {d1 d2 : Nat}
  (hn : n1 = n2)
  (hd : d1 = d2)
  :
  mkRat n1 d1 = mkRat n2 d2 := by grind

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_sign_eq_one_of_eq 
  {b1 b2 : Bool} (h : b1 = b2) :
  (-1) ^ b1.toNat * (-1) ^ b2.toNat = 1 := by
  grind [Bool.toNat]

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_sign_eq_neg_one_of_ne 
  {b1 b2 : Bool} (h : b1 ≠ b2) :
  (-1) ^ b1.toNat * (-1) ^ b2.toNat = -1 := by
  grind [Bool.toNat]

@[simp]
theorem neg_one_pow_toNat_mul_neg_one_pow_toNat_eq_one_of_self
  {b : Bool} : (-1) ^ b.toNat * (-1) ^ b.toNat = 1 := by
  grind [Bool.toNat]

attribute [grind] Bool.toNat
attribute [grind funCC] mkRat


theorem f_mul_DyadicEqualsFixedPoint_mul
    [HExOffset e m] (da db : Dyadic) (fa fb : FixedPoint m e)
   (ha : fa ∼d da) (hb : fb ∼d db) 
  : (f_mul fa fb) ∼d  (da * db) := by
  apply DyadicEqualsFixedPoint_of_eq
  rw [f_mul]
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
    · rw [hsign]
      norm_cast
      -- TOO: should be simp lemma.
      simp [Nat.shiftLeft_eq, Int.toNat_add, Nat.pow_add, Int.neg_add]
      ac_nf
      apply mkRat_eq_mkRat_of_eq_of_eq
      · congr -- TODO: I should not need this 'congr'?
        grind
      · grind
    · rw [Nat.pow_add]
      apply Nat.mul_lt_mul'' 
      · omega
      · omega
  case neg =>
    simp [hsign]
    sorry

/--
info: 'f_mul_DyadicEqualsFixedPoint_mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms f_mul_DyadicEqualsFixedPoint_mul


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

