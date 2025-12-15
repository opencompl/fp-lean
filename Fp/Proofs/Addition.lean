import Fp.Proofs.Basic
import Init.Data.Dyadic
import Fp.Addition
import Fp.ForLean.Dyadic
import Fp.ForLean.Rat


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
