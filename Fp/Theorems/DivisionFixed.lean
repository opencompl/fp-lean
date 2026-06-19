import Fp.Utils.Rat

/-! ## Fixed-width division at precision (ported from DivisionFixed.lean)

A generic fixed-width divider that returns a quotient and sticky bit.
The key theorem `fixedWidthDivideAtPrecision_abs_delta_eq` says that the
truncated quotient is within one ULP of the true rational division. This
is the bound the rounder consumes via `roundRNE_congr_of_classify_eq`. -/

structure FixedWidthDivideAtPrecisionResult (outw : Nat) where
  quotient : BitVec outw
  sticky : Bool

/--
Returns the quotient of `x` and `y` computed at a fixed precision,
plus a sticky bit indicating whether there was any remainder.
-/
def fixedWidthDivideAtPrecision (x y : BitVec w) (prec : Nat) (outw : Nat)
    : FixedWidthDivideAtPrecisionResult outw :=
    let dividend := (x.setWidth outw <<< prec)
    let divisor := y.setWidth outw
    {
      quotient := dividend / divisor,
      sticky := (dividend % divisor ≠ 0)
    }

/-- Compute the quotient with the sticky bit appended as the least significant bit. -/
def FixedWidthDivideAtPrecisionResult.quotWithSticky {outw : Nat}
    (r : FixedWidthDivideAtPrecisionResult outw) : BitVec (outw + 1) :=
  r.quotient ++ BitVec.ofBool r.sticky

theorem toNat_quoteint_fixedWidthDivideAtPrecision_eq
    (x y : BitVec w) (prec : Nat) (outw : Nat) (hprec : w + prec = outw) :
    (fixedWidthDivideAtPrecision x y prec outw).quotient.toNat =
      (x.toNat * 2 ^ prec) / y.toNat := by
  simp [fixedWidthDivideAtPrecision]
  have hx_lt : x.toNat < 2^outw := by
    subst hprec
    have hxw : x.toNat < 2^w := x.isLt
    calc x.toNat < 2^w := hxw
      _ ≤ 2^(w+prec) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hy_lt : y.toNat < 2^outw := by
    subst hprec
    have hyw : y.toNat < 2^w := y.isLt
    calc y.toNat < 2^w := hyw
      _ ≤ 2^(w+prec) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  rw [Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt]
  rw [Nat.shiftLeft_eq]
  congr
  apply Nat.mod_eq_of_lt
  subst hprec
  have hxw : x.toNat < 2^w := x.isLt
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le hxw (Nat.le_refl _) (Nat.two_pow_pos _)

theorem remainder_fixedWidthDivideAtPrecision_eq_decide
    (x y : BitVec w) (prec : Nat) (outw : Nat) (hprec : w + prec = outw) :
    (fixedWidthDivideAtPrecision x y prec outw).sticky
      = (decide ((x.toNat * 2 ^ prec) % y.toNat ≠ 0)) := by
  simp [fixedWidthDivideAtPrecision]
  have hx_lt : x.toNat < 2^outw := by
    subst hprec
    have : x.toNat < 2^w := x.isLt
    calc x.toNat < 2^w := this
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hy_lt : y.toNat < 2^outw := by
    subst hprec
    have : y.toNat < 2^w := y.isLt
    calc y.toNat < 2^w := this
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hx : x.toNat % 2^outw = x.toNat := Nat.mod_eq_of_lt hx_lt
  have hy : y.toNat % 2^outw = y.toNat := Nat.mod_eq_of_lt hy_lt
  have hprod : x.toNat * 2 ^ prec < 2 ^ outw := by
    subst hprec
    have : x.toNat < 2^w := x.isLt
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le this (Nat.le_refl _) (Nat.two_pow_pos _)
  have hprod_mod : x.toNat * 2 ^ prec % 2 ^ outw = x.toNat * 2 ^ prec :=
    Nat.mod_eq_of_lt hprod
  constructor
  · intros h
    have := congrArg BitVec.toNat h
    simp [Nat.shiftLeft_eq, hx, hy, hprod_mod] at this
    grind
  · intros h
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftLeft_eq, hx, hy, hprod_mod]
    grind


/-- `ofNat (d*k + r) / ofNat d = ofNat k + ofNat (r%d) / ofNat d`, the "subdivide"
    of a Nat sum-with-remainder. Cleanly handles the case in the abs_delta proof. -/
theorem Rat.ofNat_mul_add_div_ofNat_eq {d k r : Nat} (hd : d ≠ 0) (hrd : r < d) :
    Rat.ofNat (d * k + r) / Rat.ofNat d
      = Rat.ofNat k + Rat.ofNat (r % d) / Rat.ofNat d := by
  rw [Rat.ofNat_div_ofNat_eq_ofNat_div_add_ofNat_mod _ _ hd]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hd)]
  rw [Nat.add_mul_mod_self_left]
  rw [Rat.ofNat_add]
  have hrlt : r / d ≤ k + r / d := Nat.le_add_left _ _
  simp [Rat.ofNat_eq_coe]
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.div_eq_of_lt]
    · grind
    · grind
  · grind

/-- Specialised: `ofNat (d * k + r) / ofNat d = ofNat k + ofNat r / ofNat d` when r < d. -/
theorem Rat.ofNat_mul_add_div_ofNat_eq_of_lt {d k r : Nat} (hd : d ≠ 0) (hr : r < d) :
    Rat.ofNat (d * k + r) / Rat.ofNat d
      = Rat.ofNat k + Rat.ofNat r / Rat.ofNat d := by
  rw [Rat.ofNat_mul_add_div_ofNat_eq (by grind) (by grind)]
  rw [Nat.mod_eq_of_lt hr]

/-- Reassociation: `Nat.mul_add_div` with the multiplier in `d` placed correctly. -/
theorem Nat.mul_add_div_of_pos {d k r : Nat} (hd : 0 < d) :
    (d * k + r) / d = k + r / d := by
  rw [Nat.add_div]
  · have : d * k / d = k := by
      exact mul_div_right k hd
    rw [this]
    simp only [mul_mod_right, Nat.zero_add, Nat.add_eq_left, ite_eq_right_iff, succ_ne_self,
      imp_false, Nat.not_le, gt_iff_lt]
    apply mod_lt r hd
  · grind only

theorem fixedWidthDivideAtPrecision_abs_delta_eq
  (n d : BitVec w) (prec : Nat) (hy : d.toNat ≠ 0) :
    ((Rat.ofNat n.toNat / Rat.ofNat d.toNat) -
      (Rat.ofNat ((n.toNat * 2 ^ prec) / d.toNat)) * Rat.twoPowInv prec) ≤
    Rat.twoPowInv prec := by
  -- Replay of the DivisionFixed.lean proof. Uses porting lemmas:
  --   `Rat.ofNat_mul_add_div_ofNat_eq_of_lt`, `Nat.mul_add_div_of_pos`,
  --   `Rat.mul_inv_cancel_right'`, `Rat.self_sub_mul_floor_inv_le`,
  --   `Rat.ofNat_div_ofNat_eq_floor_div`, `Rat.twoPowInv_eq_inv`,
  --   `Nat.two_pow_ne_zero'`.
  have hdmod := Nat.div_add_mod n.toNat d.toNat
  rw [← hdmod]
  generalize hk : n.toNat / d.toNat = k
  generalize hr : n.toNat % d.toNat = r
  have hrlt : r < d.toNat := by
    subst hr; exact Nat.mod_lt _ (Nat.pos_of_ne_zero hy)
  -- (d*k + r)/d = k + r/d on the LHS first term:
  rw [Rat.ofNat_mul_add_div_ofNat_eq_of_lt hy hrlt]
  -- second term: (d*k+r)*2^prec / d = k*2^prec + r*2^prec/d
  rw [Nat.add_mul]
  rw [show d.toNat * k * 2 ^ prec = d.toNat * (k * 2 ^ prec) by grind]
  rw [Nat.mul_add_div_of_pos (Nat.pos_of_ne_zero hy)]
  rw [Rat.ofNat_add, Rat.ofNat_mul, Rat.add_mul, Rat.twoPowInv_eq_inv]
  have hpow_ne : Rat.ofNat (2 ^ prec) ≠ 0 := by
    grind only [Rat.ofNat_eq_zero_iff, !Nat.two_pow_pos]
  rw [Rat.mul_inv_cancel_right' hpow_ne]
  -- after subtracting Rat.ofNat k from both sides:
  have hreduce :
      Rat.ofNat k + Rat.ofNat r / Rat.ofNat d.toNat
        - (Rat.ofNat k + Rat.ofNat (r * 2 ^ prec / d.toNat) * (Rat.ofNat (2 ^ prec))⁻¹)
      = Rat.ofNat r / Rat.ofNat d.toNat
        - Rat.ofNat (r * 2 ^ prec / d.toNat) * (Rat.ofNat (2 ^ prec))⁻¹ := by grind
  rw [hreduce]
  rw [Rat.ofNat_div_ofNat_eq_floor_div (Nat.pos_of_ne_zero hy)]
  have : (Rat.ofNat (r * 2 ^ prec) / Rat.ofNat d.toNat) =
    (Rat.ofNat (r) / Rat.ofNat d.toNat) * 2 ^ prec := by
      simp [Rat.ofNat_eq_coe] -- TODO: Drop Rat.ofNat
      grind
  rw [this]
  have : (Rat.ofNat (2 ^ prec))⁻¹ = ((2 : Rat) ^ prec)⁻¹ := by
    simp [Rat.ofNat_eq_coe]
  rw [this]
  apply Rat.self_sub_mul_floor_inv_le (y := Rat.ofNat r / Rat.ofNat d.toNat) (k := 2 ^ prec)

/--
info: 'fixedWidthDivideAtPrecision_abs_delta_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fixedWidthDivideAtPrecision_abs_delta_eq
