import Fp.Division
import Fp.Theorems.UnpackedFloat.Round
import Fp.Theorems.Multiplication

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


/--
The result of raw division, with un-normalized significand, exponent,
and an explicit remainder. The interpretation is given by `DivUnnormalized.toRat`.
The `quot` has `s + 2` bits to make room for the post-normalization shift
and the sticky/guard bits used by the rounder.
-/
structure DivUnnormalized (e s : Nat) where
  quot : BitVec (s + 2)
  rem  : BitVec (s + 2 + (s + 1))
  ex   : BitVec (e + 1)
  sign : Bool

namespace DivUnnormalized

/--
Compute the raw division: integer divide `x.sig << (s+1)` by `y.sig`,
recording quotient, remainder, signed exponent difference, and xored sign.
-/
@[bv_normalize]
def div (x y : UnpackedFloat e s) : DivUnnormalized e s :=
  {
    sign := sign
    -- Exponent guaranteed to fit in e+1 bits (no overflow):
    --   max: (2^(e-1) - 1) - (-2^(e-1))     = 2^e - 1
    --   min: -2^(e-1)     - (2^(e-1) - 1)   = -2^e + 1
    ex   := ex
    quot := quot
    rem  := rem
  }
  where
    sign     := x.sign ^^ y.sign
    ex       := x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1)
    divident : BitVec (s + 2 + (s + 1)) := x.sig.setWidth' (by omega) ++ 0#(s + 1)
    divisor  : BitVec (s + 2 + (s + 1)) := y.sig.setWidth' (by omega)
    quot     := (divident / divisor).truncate (s + 2)
    rem      := divident % divisor

/--
Rational interpretation: the *exact* quotient `(quot * divisor + rem) / (divisor * 2^(s+1))`
times `2^ex` times the sign. By the integer division identity
(`divident_eq_quot_mul_divisor_add_rem`) the numerator equals the divident
`x.sig * 2^(s+1)`, so the fraction is exactly `x.sig / y.sig` and the whole expression
equals `x.toRat / y.toRat` whenever `y.sig.toNat ≠ 0`
(see `toRat_divUnadjusted_eq_toRat_div_toRat`).
-/
def toRat (d : DivUnnormalized e s) (divisor : BitVec (s + 2 + (s + 1))) : Rat :=
  d.sign.toSign *
    (((d.quot.toNat * divisor.toNat + d.rem.toNat : Nat) : Rat) /
      (divisor.toNat * (2 : Rat) ^ (s + 1))) *
    (2 : Rat) ^ d.ex.toInt

/--
Normalize the quotient: if `quot` is in `[1, 2)` (msb = true) we keep it,
otherwise (`[1/2, 1)`) we shift it left by one and decrement the exponent.
The lsb of the resulting significand carries the sticky bit `rem ≠ 0`,
preserving information lost to the precision-limited quotient for the rounder.
-/
def divAdjustMsb (d : DivUnnormalized e s) : UnpackedFloat (e + 1) (s + 2) :=
  { sign, sig, ex }
  where
    sign := d.sign
    sig  := (d.quot <<< BitVec.ofBool (!d.quot.msb)) |||
            (BitVec.ofBool (d.rem != 0)).setWidth' (by omega)
    ex   := d.ex - (BitVec.ofBool (!d.quot.msb)).setWidth' (by omega)

end DivUnnormalized

/--
The division circuit decomposes as raw division then msb adjustment with sticky bit.
-/
theorem UnpackedFloat.div_eq_divAdjustMsb_divUnadjusted (x y : UnpackedFloat e s) :
    x.div y = (DivUnnormalized.div x y).divAdjustMsb := by rfl

/--
The divident `xs.setWidth'(...) ++ 0#(s+1)` has `toNat` equal to `xs.toNat * 2^(s+1)`.
-/
theorem DivUnnormalized.toNat_divident_eq {s : Nat} (xs : BitVec s) (h : s ≤ s + 2) :
    (xs.setWidth' h ++ 0#(s + 1) : BitVec (s + 2 + (s + 1))).toNat = xs.toNat * 2 ^ (s + 1) := by
  simp [BitVec.toNat_append, BitVec.toNat_setWidth', Nat.shiftLeft_eq]

/--
The divisor `ys.setWidth'(...)` has `toNat` equal to `ys.toNat` (it's a widening).
-/
theorem DivUnnormalized.toNat_divisor_eq {s : Nat} (ys : BitVec s) (h : s ≤ s + 2 + (s + 1)) :
    (ys.setWidth' h : BitVec (s + 2 + (s + 1))).toNat = ys.toNat := by
  have hlt : ys.toNat < 2 ^ (s + 2 + (s + 1)) :=
    Nat.lt_of_lt_of_le ys.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  simp [BitVec.toNat_setWidth', Nat.mod_eq_of_lt hlt]

/--
When `ys.msb = true`, the (widened) divisor is at least `2^(s-1)` (needs `0 < s`).
-/
theorem DivUnnormalized.divisor_ge {s : Nat} (ys : BitVec s)
    (hs : 0 < s) (hy : ys.msb = true) (h : s ≤ s + 2 + (s + 1)) :
    2 ^ (s - 1) ≤ (ys.setWidth' h : BitVec (s + 2 + (s + 1))).toNat := by
  rw [DivUnnormalized.toNat_divisor_eq ys h]
  exact BitVec.le_toNat_of_msb_true hy

/--
Quotient bound: `divident / divisor < 2^(s+2)` whenever `0 < s` and `ys.msb = true`.
This is the key bound that ensures truncating to `s + 2` bits is lossless.
-/
theorem DivUnnormalized.divident_div_divisor_lt {s : Nat} (xs ys : BitVec s)
    (hs : 0 < s) (hy : ys.msb = true)
    (h1 : s ≤ s + 2) (h2 : s ≤ s + 2 + (s + 1)) :
    let divident : BitVec (s + 2 + (s + 1)) := xs.setWidth' h1 ++ 0#(s + 1)
    let divisor  : BitVec (s + 2 + (s + 1)) := ys.setWidth' h2
    divident.toNat / divisor.toNat < 2 ^ (s + 2) := by
  intro divident divisor
  have hxlt : xs.toNat < 2 ^ s := xs.isLt
  have hge : 2 ^ (s - 1) ≤ divisor.toNat := DivUnnormalized.divisor_ge ys hs hy h2
  have hdivident_eq : divident.toNat = xs.toNat * 2 ^ (s + 1) :=
    DivUnnormalized.toNat_divident_eq xs h1
  apply Nat.div_lt_of_lt_mul
  rw [hdivident_eq]
  -- xs.toNat * 2^(s+1) < 2^s * 2^(s+1) = 2^(s-1) * 2^(s+2) ≤ divisor * 2^(s+2)
  have hk1 : xs.toNat * 2 ^ (s + 1) < 2 ^ s * 2 ^ (s + 1) :=
    (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hxlt
  have hk2 : 2 ^ s * 2 ^ (s + 1) = 2 ^ (s - 1) * 2 ^ (s + 2) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hk3 : 2 ^ (s - 1) * 2 ^ (s + 2) ≤ divisor.toNat * 2 ^ (s + 2) :=
    Nat.mul_le_mul_right _ hge
  omega

/--
The fundamental integer division identity: `divident = quot * divisor + rem`,
with `rem < divisor`. This is what relates `quot` to the true rational quotient.
-/
theorem DivUnnormalized.divident_eq_quot_mul_divisor_add_rem {x y : UnpackedFloat e s}
    (hs : 0 < s)
    (he: 2 < e)
    (hy : y.sig.msb = true) :
    let d := DivUnnormalized.div x y
    let divident : BitVec (s + 2 + (s + 1)) := x.sig.setWidth' (by omega) ++ 0#(s + 1)
    let divisor  : BitVec (s + 2 + (s + 1)) := y.sig.setWidth' (by omega)
    divident.toNat = d.quot.toNat * divisor.toNat + d.rem.toNat ∧
    d.rem.toNat < divisor.toNat := by
  -- introduce the let-bindings
  intro d divident divisor
  -- y.sig.toNat > 0 from msb=true (needs s ≥ 1, derived below).
  have hs_pos : 0 < s := by grind
  have hy_pos : 0 < y.sig.toNat := by
    have hge := BitVec.le_toNat_of_msb_true hy
    have : 0 < 2 ^ (s - 1) := by grind
    omega
  have hdivisor_pos : 0 < divisor.toNat := by
    simp [divisor]
    rw [Nat.mod_eq_of_lt]
    · grind
    · apply Nat.lt_trans (show y.sig.toNat < 2 ^ s by grind)
      apply Nat.pow_lt_pow_of_lt
      · grind
      · grind
  have hdiv_quot : d.quot = (divident / divisor).truncate (s + 2) := rfl
  have hdiv_rem : d.rem = divident % divisor := rfl
  refine ⟨?_, ?_⟩
  · -- divident = quot * divisor + rem (depends on the truncation being lossless)
    have hidentity : divident.toNat =
        (divident.toNat / divisor.toNat) * divisor.toNat + divident.toNat % divisor.toNat :=
      by exact Eq.symm (Nat.div_add_mod' divident.toNat divisor.toNat)
    have hbound : divident.toNat / divisor.toNat < 2 ^ (s + 2) :=
      DivUnnormalized.divident_div_divisor_lt x.sig y.sig hs_pos hy (by omega) (by omega)
    rw [hdiv_quot, hdiv_rem]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_udiv, BitVec.toNat_umod,
               Nat.mod_eq_of_lt hbound]
    exact hidentity
  · rw [hdiv_rem]
    simp [BitVec.toNat_umod]
    exact Nat.mod_lt _ hdivisor_pos


/--
Bound on the raw quotient: since `divident < 2^(2s+1)` and `divisor ≥ 2^(s-1)` (when y is
normalized: `y.sig.msb = true`), we get `quot < 2^(s+2)`, so truncation to `s + 2` bits
is lossless and leaves the msb-or-msb-1 invariant available for normalization.
-/
theorem DivUnnormalized.quot_lt_two_pow {x y : UnpackedFloat e s}
    (hs : 0 < s) (hy : y.sig.msb = true) :
    ((DivUnnormalized.div x y).quot).toNat < 2 ^ (s + 2) := by
  -- (truncate (s+2) of a `BitVec` of width ≥ s+2 is bounded by 2^(s+2) automatically)
  exact (DivUnnormalized.div x y).quot.isLt

/--
Closed-form `toNat` of the raw quotient: `(divident / divisor)`. The truncation in
`def quot := (divident / divisor).truncate (s+2)` is lossless thanks to `divident_div_divisor_lt`.
-/
theorem DivUnnormalized.quot_toNat_eq {x y : UnpackedFloat e s}
    (hs : 0 < s) (hy : y.sig.msb = true) :
    (DivUnnormalized.div x y).quot.toNat
      = (x.sig.toNat * 2 ^ (s + 1)) / y.sig.toNat := by
  -- quot = (divident / divisor).truncate (s+2) ; toNat = · % 2^(s+2)
  have hbound : x.sig.toNat * 2 ^ (s + 1) / y.sig.toNat < 2 ^ (s + 2) := by
    have h := DivUnnormalized.divident_div_divisor_lt x.sig y.sig hs hy
      (by omega : s ≤ s + 2) (by omega : s ≤ s + 2 + (s + 1))
    simp only at h
    rw [DivUnnormalized.toNat_divident_eq x.sig (by omega),
        DivUnnormalized.toNat_divisor_eq y.sig (by omega)] at h
    exact h
  simp only [DivUnnormalized.div, div.quot, div.divident, div.divisor,
    BitVec.toNat_setWidth, BitVec.toNat_udiv]
  rw [DivUnnormalized.toNat_divident_eq x.sig (by omega),
    DivUnnormalized.toNat_divisor_eq y.sig (by omega)]
  exact Nat.mod_eq_of_lt hbound

/--
Lower bound on the raw quotient: when both inputs are normalized (msb = true),
`quot ≥ 2^s`. This is what guarantees `divAdjustMsb` produces an msb-true result.
-/
theorem DivUnnormalized.quot_ge_pow {x y : UnpackedFloat e s}
    (hs : 0 < s) (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    2 ^ s ≤ (DivUnnormalized.div x y).quot.toNat := by
  rw [DivUnnormalized.quot_toNat_eq hs hy]
  -- need: 2^s ≤ (x.sig.toNat * 2^(s+1)) / y.sig.toNat
  -- by Nat.le_div_iff_mul_le, equivalent to: 2^s * y.sig.toNat ≤ x.sig.toNat * 2^(s+1)
  -- which holds since y.sig.toNat < 2^s and x.sig.toNat ≥ 2^(s-1), so:
  -- 2^s * y.sig.toNat < 2^s * 2^s = 2^(2s) and 2^(s-1) * 2^(s+1) = 2^(2s) ≤ x.sig.toNat * 2^(s+1).
  have hylt : y.sig.toNat < 2 ^ s := y.sig.isLt
  have hyge : 2 ^ (s - 1) ≤ y.sig.toNat := BitVec.le_toNat_of_msb_true hy
  have hxge : 2 ^ (s - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hx
  have hypos : 0 < y.sig.toNat := by
    have : 0 < 2 ^ (s - 1) := Nat.two_pow_pos _
    omega
  rw [Nat.le_div_iff_mul_le hypos]
  -- 2^s * y.sig.toNat ≤ 2^s * (2^s - 1) < 2^(2s) = 2^(s-1) * 2^(s+1) ≤ x.sig.toNat * 2^(s+1)
  have h1 : 2 ^ s * y.sig.toNat < 2 ^ s * 2 ^ s :=
    (Nat.mul_lt_mul_left (Nat.two_pow_pos _)).mpr hylt
  have h2 : 2 ^ s * 2 ^ s = 2 ^ (s - 1) * 2 ^ (s + 1) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have h3 : 2 ^ (s - 1) * 2 ^ (s + 1) ≤ x.sig.toNat * 2 ^ (s + 1) :=
    Nat.mul_le_mul_right _ hxge
  omega

/--
The exponent of the raw division result is *exactly* the difference of the input
exponents: the signed subtraction at width `e + 1` cannot wrap, since each operand
lies in `[-2^(e-1), 2^(e-1))` so the difference lies in `(-2^e, 2^e)`.
-/
theorem DivUnnormalized.toInt_ex_eq (x y : UnpackedFloat e s) (he : 0 < e) :
    (DivUnnormalized.div x y).ex.toInt = x.ex.toInt - y.ex.toInt := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_one.mpr he
  simp [DivUnnormalized.div, div.ex]
  rw [BitVec.toInt_signExtend_of_le (by lia)]
  rw [BitVec.toInt_signExtend_of_le (by lia)]
  have := x.ex.toInt_le
  have := y.ex.toInt_le
  have := x.ex.le_toInt
  have := y.ex.le_toInt
  rw [Int.bmod_eq_of_le] <;> grind

/--
The unadjusted result has the correct rational interpretation (= `x.toRat / y.toRat`).
This needs `y.sig` nonzero (so the division is well-defined), which follows from
`y.sig.msb = true`.
-/
theorem UnpackedFloat.toRat_divUnadjusted_eq_toRat_div_toRat {a b : UnpackedFloat e s}
    (hs : 0 < s) (he : 2 < e) (hb : b.sig.msb = true) :
    (DivUnnormalized.div a b).toRat (b.sig.setWidth' (by omega)) = a.toRat / b.toRat := by
  have hb_pos : 0 < b.sig.toNat := by
    have h1 := BitVec.le_toNat_of_msb_true hb
    have h2 : 0 < 2 ^ (s - 1) := Nat.two_pow_pos _
    omega
  obtain ⟨hident, -⟩ :=
    DivUnnormalized.divident_eq_quot_mul_divisor_add_rem (x := a) (y := b) hs he hb
  rw [DivUnnormalized.toNat_divident_eq a.sig (by omega)] at hident
  rw [DivUnnormalized.toNat_divisor_eq b.sig (by omega)] at hident
  -- hident : a.sig.toNat * 2^(s+1) = quot * b.sig.toNat + rem
  rw [DivUnnormalized.toRat]
  rw [DivUnnormalized.toNat_divisor_eq b.sig (by omega)]
  rw [← hident]
  rw [DivUnnormalized.toInt_ex_eq a b (by omega)]
  -- both sides are now pure rational arithmetic in sig/ex/sign
  rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat_eq_toRat',
      UnpackedFloat.toRat', UnpackedFloat.toRat']
  simp only [UnpackedFloat.toNat_toSigNat_eq, UnpackedFloat.toExpInt]
  rw [show (DivUnnormalized.div a b).sign = (a.sign ^^ b.sign) from rfl]
  have h2s : ((2 : Rat) ^ (s + 1)) ≠ 0 := Rat.two_pow_nat_ne_zero
  have hys : ((b.sig.toNat : Rat)) ≠ 0 := by
    grind only [Rat.natCast_eq_zero_iff]
  have hsb : (((b.sign.toSign : Int)) : Rat) ≠ 0 := by
    have h := Bool.toSign_ne_zero b.sign
    exact_mod_cast h
  have hpb : ((2 : Rat) ^ (-((((s - 1 : Nat)) : Int) - b.ex.toInt))) ≠ 0 :=
    Rat.two_pow_ne_zero _
  -- split the Nat-cast of the divident
  have hcast : ((a.sig.toNat * 2 ^ (s + 1) : Nat) : Rat)
      = (a.sig.toNat : Rat) * (2 : Rat) ^ (s + 1) := by push_cast; rfl
  rw [hcast]
  -- collect the powers of two: 2^(ea - eb) * 2^pb = 2^pa
  have hzpow : (2 : Rat) ^ (a.ex.toInt - b.ex.toInt)
        * (2 : Rat) ^ (-((((s - 1 : Nat)) : Int) - b.ex.toInt))
      = (2 : Rat) ^ (-((((s - 1 : Nat)) : Int) - a.ex.toInt)) := by
    rw [Rat.zpow_mul_zpow (by decide)]
    congr 1
    omega
  -- reconcile the signs: (sa ^^ sb).toSign * sb.toSign = sa.toSign
  have hsign : ((((a.sign ^^ b.sign).toSign : Int)) : Rat) * (((b.sign.toSign : Int)) : Rat)
      = (((a.sign.toSign : Int)) : Rat) := by
    have h : ((a.sign ^^ b.sign).toSign) * (b.sign.toSign) = a.sign.toSign := by
      rcases a.sign <;> rcases b.sign <;> decide
    exact_mod_cast h
  rw [← hzpow]
  -- turn the divisions into multiplications by inverses, supply the unit equations,
  -- and finish by commutative-ring reasoning
  have hmulinv : ∀ (x : Rat), x ≠ 0 → x * x⁻¹ = 1 := fun x hx => by
    rw [Rat.inv_mul_eq_div, Rat.div_self_eq_one_of_ne_zero hx]
  have hden1 : ((b.sig.toNat : Rat) * (2 : Rat) ^ (s + 1)) ≠ 0 :=
    Rat.mul_ne_zero_iff_ne_zero₂.mpr ⟨hys, h2s⟩
  have hden2 : ((((b.sign.toSign : Int)) : Rat) * (b.sig.toNat : Rat)
      * (2 : Rat) ^ (-((((s - 1 : Nat)) : Int) - b.ex.toInt))) ≠ 0 :=
    Rat.mul_ne_zero_iff_ne_zero₃.mpr ⟨hsb, hys, hpb⟩
  have hinv1 := hmulinv _ hden1
  have hinv2 := hmulinv _ hden2
  simp only [← Rat.inv_mul_eq_div]
  grind

/--
info: 'UnpackedFloat.toRat_divUnadjusted_eq_toRat_div_toRat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat_divUnadjusted_eq_toRat_div_toRat

/--
The exponent of the unadjusted division result lies in `[-2^e + 1, 2^e - 1]`,
so after subtracting one for the post-normalization shift it still fits in `e+1` bits.
-/
theorem DivUnnormalized.toInt_ex_bound (x y : UnpackedFloat e s) (he : 0 < e) :
    -2 ^ e + 1 ≤ (DivUnnormalized.div x y).ex.toInt ∧
    (DivUnnormalized.div x y).ex.toInt ≤ 2 ^ e - 1 := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_one.mpr he
  simp [DivUnnormalized.div, div.ex]
  rw [BitVec.toInt_signExtend_of_le (by lia)]
  rw [BitVec.toInt_signExtend_of_le (by lia)]
  have := x.ex.toInt_le
  have := y.ex.toInt_le
  rw [Int.bmod_eq_of_le] <;> grind

/--
`msb = true` for a `BitVec w` (with `0 < w`) iff `toNat ≥ 2^(w-1)`.
-/
theorem BitVec.msb_iff_toNat_ge {w : Nat} (b : BitVec w) :
    b.msb = true ↔ 2 ^ (w - 1) ≤ b.toNat := by
  refine ⟨BitVec.le_toNat_of_msb_true, fun hge => ?_⟩
  rw [BitVec.msb_eq_decide]
  exact decide_eq_true hge

/--
`msb = false` iff `toNat < 2^(w-1)`.
-/
theorem BitVec.msb_false_iff_toNat_lt {w : Nat} (b : BitVec w) :
    b.msb = false ↔ b.toNat < 2 ^ (w - 1) := by
  rw [Bool.eq_false_iff, Ne, BitVec.msb_iff_toNat_ge]
  omega

/--
After msb adjustment the significand has msb=true, provided both inputs are normalized
(msb-true). Proof: `quot ≥ 2^s` and `quot < 2^(s+2)`, so the shift-by-`!msb` operation
puts a 1 at position s+1. The OR with sticky only affects the lsb, so msb is preserved.
-/
theorem DivUnnormalized.divAdjustMsb_msb_eq_true {x y : UnpackedFloat e s}
    (hs : 0 < s) (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (DivUnnormalized.div x y).divAdjustMsb.sig.msb = true := by
  have hquot_lo : 2 ^ s ≤ (DivUnnormalized.div x y).quot.toNat :=
    DivUnnormalized.quot_ge_pow hs hx hy
  have hquot_hi : (DivUnnormalized.div x y).quot.toNat < 2 ^ (s + 2) :=
    (DivUnnormalized.div x y).quot.isLt
  -- show toNat of sig ≥ 2^(s+1)
  rw [BitVec.msb_iff_toNat_ge]
  have hwidth : (s + 2 - 1) = (s + 1) := by omega
  rw [hwidth]
  simp only [DivUnnormalized.divAdjustMsb, DivUnnormalized.divAdjustMsb.sig, BitVec.toNat_or,
    BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofBool]
  -- a ≤ a ||| b
  refine Nat.le_trans ?_ (Nat.left_le_or)
  -- now: 2^(s+1) ≤ q.toNat <<< (ofBool !q.msb).toNat % 2^(s+2)
  rcases hmsb : (DivUnnormalized.div x y).quot.msb with _ | _
  · -- false: shift by 1
    have hlt : (DivUnnormalized.div x y).quot.toNat < 2 ^ (s + 1) := by
      have := (BitVec.msb_false_iff_toNat_lt _).mp hmsb
      simpa using this
    have hbound : (DivUnnormalized.div x y).quot.toNat * 2 < 2 ^ (s + 2) := by
      have : (2 : Nat) ^ (s + 2) = 2 ^ (s + 1) * 2 := Nat.pow_succ 2 (s + 1)
      omega
    simp only [Bool.not_false, Bool.toNat_true, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt hbound]
    have hpows : (2 : Nat) ^ (s + 1) = 2 ^ s * 2 := Nat.pow_succ 2 s
    have hmul : 2 ^ s * 2 ≤ (DivUnnormalized.div x y).quot.toNat * 2 :=
      Nat.mul_le_mul_right _ hquot_lo
    omega
  · -- true: shift by 0, q.toNat ≥ 2^(s+1)
    have hge : 2 ^ (s + 1) ≤ (DivUnnormalized.div x y).quot.toNat := by
      have := (BitVec.msb_iff_toNat_ge _).mp hmsb
      simpa using this
    simp only [Bool.not_true, Bool.toNat_false, Nat.shiftLeft_zero, Nat.pow_zero,
      Nat.shiftLeft_eq, Nat.mul_one, Nat.mod_eq_of_lt hquot_hi]
    exact hge

/--
The lsb of the adjusted significand decomposes as `(msb-preserved quot.lsb) || sticky`:
in the unshifted case (`quot.msb = true`) the lsb is `quot.getLsbD 0 || (rem != 0)`,
while in the shifted case (`quot.msb = false`) the shift introduces a `0` so lsb = `(rem != 0)`.
Either way the OR captures all info "below position 1" — exactly what a sticky bit is.
-/
theorem DivUnnormalized.lsb_divAdjustMsb_eq
    {x y : UnpackedFloat e s} (hs : 0 < s) :
    let d := DivUnnormalized.div x y
    d.divAdjustMsb.sig.getLsbD 0 =
      ((d.quot.msb && d.quot.getLsbD 0) || (d.rem != 0)) := by
  simp only [DivUnnormalized.divAdjustMsb, DivUnnormalized.divAdjustMsb.sig,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.toNat_ofBool,
    BitVec.getLsbD_setWidth', BitVec.getLsbD_ofBool]
  -- after simp, both sides agree by case split on `quot.msb`.
  rcases hmsb : (DivUnnormalized.div x y).quot.msb <;> simp [hmsb]

/--
A significand with `msb = true` denotes a nonzero rational.
-/
theorem UnpackedFloat.toRat_ne_zero_of_msb_eq_true {x : UnpackedFloat e s}
    (h : x.sig.msb = true) : x.toRat ≠ 0 := by
  rw [UnpackedFloat.toRat_eq_toRat']
  have hzero : ¬ x.isZero := by
    simp only [UnpackedFloat.isZero, beq_iff_eq]
    intro hcon
    rw [hcon] at h
    simp [BitVec.msb_eq_decide] at h
  grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]

/--
The result of `x.div y` (unpacked, pre-rounding) is normalized.
-/
theorem UnpackedFloat.msb_div_eq_true_of_msb_eq_true {x y : UnpackedFloat e s}
    (hs : 0 < s) (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (x.div y).sig.msb = true := by
  rw [UnpackedFloat.div_eq_divAdjustMsb_divUnadjusted]
  exact DivUnnormalized.divAdjustMsb_msb_eq_true hs hx hy

/--
Rounding is determined by the rounder's classification of the input rational —
`isNaN`, `isZero`, `lower`, `upper`, `lowerHalf`, `tieBreak` — and by no other
property of the rational itself. So if two rationals `r1` and `r2` agree on these
classifiers, `roundRNE` returns the same packed float. This is the abstract
"close enough" property the sticky-bit machinery relies on: division produces a
quotient whose true value differs from the implementation's `toRat`, but the
sticky bit ensures all six classifiers agree, so the rounded results coincide.
-/
theorem Fp.SmtLibSemantics.RoundMethod.roundRNE_congr_of_classify_eq
    {ep sp : Nat} {R : Type} [inst : Fp.SmtLibSemantics.ExtendedNumber R]
    (rm : Fp.SmtLibSemantics.RoundMethod (PackedFloat ep sp) R)
    [DecidablePred inst.isNaN] [DecidablePred inst.isZero]
    [DecidablePred rm.lowerHalf] [DecidablePred rm.tieBreak]
    (sign : Bool) (r1 r2 : R)
    (hnan  : inst.isNaN  r1 ↔ inst.isNaN  r2)
    (hzero : inst.isZero r1 ↔ inst.isZero r2)
    (hlow  : rm.lower r1 = rm.lower r2)
    (hup   : rm.upper r1 = rm.upper r2)
    (hlh   : rm.lowerHalf r1 ↔ rm.lowerHalf r2)
    (htb   : rm.tieBreak r1 ↔ rm.tieBreak r2) :
    rm.roundRNE sign r1 = rm.roundRNE sign r2 := by
  -- roundRNE is a chain of `if`s over exactly these classifiers (plus `isEven`,
  -- which only inspects `lower r` / `upper r`). Each branch's result is either
  -- `lower r` or `upper r`, which agree by hypothesis. Discharge by structural
  -- case-split on the boolean classifiers.
  unfold Fp.SmtLibSemantics.RoundMethod.roundRNE Fp.SmtLibSemantics.RoundMethod.rounderForSign
  rw [hlow, hup]
  by_cases hN : inst.isNaN r1
  · simp [hN, hnan.mp hN]
  · have hN2 : ¬ inst.isNaN r2 := fun h => hN (hnan.mpr h)
    by_cases hZ : inst.isZero r1
    · simp [hN, hN2, hZ, hzero.mp hZ]
    · have hZ2 : ¬ inst.isZero r2 := fun h => hZ (hzero.mpr h)
      by_cases hTB : rm.tieBreak r1
      all_goals by_cases hLH : rm.lowerHalf r1
      all_goals first
        | (have hLH2 := hlh.mp hLH; have hTB2 := htb.mp hTB
           simp [hN, hN2, hZ, hZ2, hLH, hLH2, hTB, hTB2])
        | (have hTB2 := htb.mp hTB
           have hLH2 : ¬ rm.lowerHalf r2 := fun h => hLH (hlh.mpr h)
           simp [hN, hN2, hZ, hZ2, hLH, hLH2, hTB, hTB2])
        | (have hLH2 := hlh.mp hLH
           have hTB2 : ¬ rm.tieBreak r2 := fun h => hTB (htb.mpr h)
           simp [hN, hN2, hZ, hZ2, hLH, hLH2, hTB, hTB2])
        | (have hLH2 : ¬ rm.lowerHalf r2 := fun h => hLH (hlh.mpr h)
           have hTB2 : ¬ rm.tieBreak r2 := fun h => hTB (htb.mpr h)
           simp [hN, hN2, hZ, hZ2, hLH, hLH2, hTB, hTB2])

/-!
## Rounding congruence: rationals in the same float-grid gap round identically

The division circuit cannot produce the exact rational quotient: it produces a
truncated quotient whose lsb is a *sticky bit*. The contract is that the produced
value and the exact quotient always occupy the *same position* relative to the
target float grid (at significand widths `sp` and `sp + 1`), so every classifier
the rounder consults (`lower`, `upper`, `lowerHalf`, `tieBreak`, `isZero`,
`isNaN`) coincides on the two, hence rounding produces identical results.
This section proves that congruence; `roundRNE_congr_of_classify_eq` above
provides the final step.
-/

namespace Fp

/--
`r1` and `r2` occupy the same position relative to every packed float of format
`(e, s)`: each float compares (in both directions) identically against the two.
This is the abstract "same gap of the float grid" relation that makes the rounder
oblivious to the difference between `r1` and `r2`.
-/
def SmtLibSemantics.SamePosition (e s : Nat) (r1 r2 : ExtRat) : Prop :=
  ∀ pf : PackedFloat e s,
    ((pf.toExtRat ≤ r1) ↔ (pf.toExtRat ≤ r2)) ∧ ((r1 ≤ pf.toExtRat) ↔ (r2 ≤ pf.toExtRat))

/--
`lower` only depends on the `≤`-profile of its argument against the float grid:
if every float is `≤ r1` exactly when it is `≤ r2`, the two greatest lower bounds
coincide. Proven via uniqueness of lawful lower bounds, so the `Classical.epsilon`
in `smtLibLower` never needs to be evaluated.
-/
theorem SmtLibSemantics.smtLibLower_congr {e s : Nat} (he : 0 < e) (hs : 0 < s)
    {r1 r2 : ExtRat} (h1 : r1 ≠ .NaN) (h2 : r2 ≠ .NaN)
    (h : ∀ pf : PackedFloat e s, (pf.toExtRat ≤ r1) ↔ (pf.toExtRat ≤ r2)) :
    (SmtLibSemantics.smtLibLower.lower r1 : PackedFloat e s)
      = SmtLibSemantics.smtLibLower.lower r2 := by
  apply eq_of_IsLawfulLower_of_IsLawfulLower e s r2
  · simp [not_isNaN_lower_of_ne_NaN e s he hs r1 h1]
  · simp [not_isNaN_lower_of_ne_NaN e s he hs r2 h2]
  · obtain ⟨ha, hb⟩ := lsLawfulLower_smtLibLower e s he hs r1
    exact ⟨(h _).mp ha, fun pf hpf => hb pf ((h pf).mpr hpf)⟩
  · exact lsLawfulLower_smtLibLower e s he hs r2

/--
`upper` only depends on the `≥`-profile of its argument against the float grid.
-/
theorem SmtLibSemantics.smtLibUpper_congr {e s : Nat} (he : 0 < e) (hs : 0 < s)
    {r1 r2 : ExtRat} (h1 : r1 ≠ .NaN) (h2 : r2 ≠ .NaN)
    (h : ∀ pf : PackedFloat e s, (r1 ≤ pf.toExtRat) ↔ (r2 ≤ pf.toExtRat)) :
    (SmtLibSemantics.smtLibUpper.upper r1 : PackedFloat e s)
      = SmtLibSemantics.smtLibUpper.upper r2 := by
  apply eq_of_IsLawfulUpper_of_IsLawfulUpper e s r2
  · simp [not_isNaN_upper_of_ne_NaN e s he hs r1 h1]
  · simp [not_isNaN_upper_of_ne_NaN e s he hs r2 h2]
  · obtain ⟨ha, hb⟩ := isLawfulUpper_smtLibUpper e s he hs r1
    exact ⟨(h _).mp ha, fun pf hpf => hb pf ((h pf).mpr hpf)⟩
  · exact isLawfulUpper_smtLibUpper e s he hs r2

/--
**Rounding congruence.** If two rationals are zero-equivalent and occupy the same
position relative to every float at significand widths `sp` (the target format)
and `sp + 1` (the half-ulp grid that `lowerHalf`/`tieBreak` consult), then
RNE-rounding them gives the *same* packed float. In particular the guard/sticky
information implicit in `r1` (an inexactly-represented quotient) suffices to round
exactly like the true value `r2`.
-/
theorem SmtLibSemanticsQ.roundRNE_congr_of_samePosition {ep sp : Nat}
    (he : 0 < ep) (hs : 0 < sp) (sign : Bool) {r1 r2 : Rat}
    (hzero : r1 = 0 ↔ r2 = 0)
    (h : SmtLibSemantics.SamePosition ep sp (.Number r1) (.Number r2))
    (hS : SmtLibSemantics.SamePosition ep (sp + 1) (.Number r1) (.Number r2)) :
    (SmtLibSemantics.smtLibRoundMethod ep sp
        SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE
        sign (ExtRat.Number r1)
      = (SmtLibSemantics.smtLibRoundMethod ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE
          sign (ExtRat.Number r2) := by
  have hnan1 : (ExtRat.Number r1) ≠ .NaN := by simp
  have hnan2 : (ExtRat.Number r2) ≠ .NaN := by simp
  have hlow := SmtLibSemantics.smtLibLower_congr he hs hnan1 hnan2 (fun pf => (h pf).1)
  have hup := SmtLibSemantics.smtLibUpper_congr he hs hnan1 hnan2 (fun pf => (h pf).2)
  have hlowS := SmtLibSemantics.smtLibLower_congr he (by omega) hnan1 hnan2
    (fun pf => (hS pf).1)
  have hupS := SmtLibSemantics.smtLibUpper_congr he (by omega) hnan1 hnan2
    (fun pf => (hS pf).2)
  apply SmtLibSemantics.RoundMethod.roundRNE_congr_of_classify_eq
  · simp [SmtLibSemantics.instExtendedRat.isNaN_eq, ExtRat.isNaN_iff]
  · simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def,
      ExtRat.Number.injEq]
    exact hzero
  · simpa using hlow
  · simpa using hup
  · rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_embed_eq]
    rw [hlow, hlowS]
  · rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
      SmtLibSemantics.smtLibV_embed_eq]
    rw [hlow, hlowS, hup, hupS]

/--
info: 'Fp.SmtLibSemanticsQ.roundRNE_congr_of_samePosition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SmtLibSemanticsQ.roundRNE_congr_of_samePosition

/--
Reduce `SamePosition` over extended rationals to comparisons against the rational
values of *finite* floats: NaN and ±∞ compare against `Number`s in a way that does
not depend on the rational, so only finite floats can tell `r1` and `r2` apart.
-/
theorem SmtLibSemantics.samePosition_of_finite_agree (e s : Nat) {r1 r2 : Rat}
    (h : ∀ pf : PackedFloat e s, ¬ pf.isNaN → ¬ pf.isInfinite →
      ((pf.toRat ≤ r1) ↔ (pf.toRat ≤ r2)) ∧ ((r1 ≤ pf.toRat) ↔ (r2 ≤ pf.toRat))) :
    SmtLibSemantics.SamePosition e s (.Number r1) (.Number r2) := by
  intro pf
  rw [PackedFloat.toExtRat_eq_toExtRat']
  by_cases hnan : pf.isNaN
  · rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN pf hnan]
    simp
  · by_cases hinf : pf.isInfinite
    · rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite pf hinf]
      simp
    · have hfin : pf.toExtRat' = .Number pf.toRat := by
        simp only [PackedFloat.toExtRat']
        rw [show pf.isNaN = false by grind, show pf.isInfinite = false by grind]
        simp
      rw [hfin]
      have := h pf hnan hinf
      simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
      exact this

/--
If `q` does not lie (weakly) between `r1` and `r2` in either order, then it
compares identically against the two.
-/
theorem Rat.cmp_agree_of_not_separating {q r1 r2 : Rat}
    (h12 : ¬ (r1 ≤ q ∧ q ≤ r2)) (h21 : ¬ (r2 ≤ q ∧ q ≤ r1)) :
    ((q ≤ r1) ↔ (q ≤ r2)) ∧ ((r1 ≤ q) ↔ (r2 ≤ q)) := by
  constructor <;> constructor <;> intro hq <;> grind

/--
**The sticky-bit closeness property** — the analytic core of division correctness.

`(a.div b).toRat` is the `(sp + 3)`-bit truncation of the exact quotient
`a.toRat / b.toRat` with the sticky bit (`rem ≠ 0`) OR-ed into the lsb. Hence
* if `rem = 0` the two values are *equal*
  (`toRat_divUnadjusted_eq_toRat_div_toRat` plus the msb-adjustment being exact), and
* otherwise both values lie strictly between two consecutive multiples of the lsb
  of the `(sp + 3)`-bit quotient grid, with the circuit value sitting on the *odd*
  multiple closest to the exact quotient on the correct side. Every float with at
  most `sp + 2` significand bits is an *even* multiple of that lsb (or outside the
  relevant binade altogether), so no such float lies weakly between the two values.

Consequently every non-NaN, finite float `pf` of a format `(ep, s')` with
`s' ≤ sp + 1` compares identically against the two values; via
`samePosition_of_finite_agree` and `roundRNE_congr_of_samePosition`, the rounder's
`lower`, `upper`, `lowerHalf` and `tieBreak` classifications (i.e. the guard/sticky
decisions) all agree on them.

The grid-counting argument is not yet formalized (it mirrors the open guard-bit
lemmas in `Fp/Theorems/UnpackedFloat/Round.lean`); the statement has been validated
by exhaustive enumeration against the computable rounder for small formats.
-/
theorem UnpackedFloat.div_toRat_cmp_agree
    (hep : 2 < ep) (hsp : 0 < sp)
    {a b : UnpackedFloat (exponentWidth ep sp) (sp + 1)}
    (ha : a.sig.msb = true) (hb : b.sig.msb = true)
    {s' : Nat} (hs' : s' ≤ sp + 1)
    (pf : PackedFloat ep s') (hnan : ¬ pf.isNaN) (hinf : ¬ pf.isInfinite) :
    ((pf.toRat ≤ (a.div b).toRat) ↔ (pf.toRat ≤ a.toRat / b.toRat))
    ∧ (((a.div b).toRat ≤ pf.toRat) ↔ (a.toRat / b.toRat ≤ pf.toRat)) := by
  sorry

/--
The division circuit's output and the exact quotient occupy the same position of
the target float grid, at both significand widths the rounder consults.
-/
theorem UnpackedFloat.div_samePosition
    (hep : 2 < ep) (hsp : 0 < sp)
    {a b : UnpackedFloat (exponentWidth ep sp) (sp + 1)}
    (ha : a.sig.msb = true) (hb : b.sig.msb = true) :
    SmtLibSemantics.SamePosition ep sp
        (.Number (a.div b).toRat) (.Number (a.toRat / b.toRat))
    ∧ SmtLibSemantics.SamePosition ep (sp + 1)
        (.Number (a.div b).toRat) (.Number (a.toRat / b.toRat)) := by
  constructor
  · exact SmtLibSemantics.samePosition_of_finite_agree _ _
      (fun pf hn hi => UnpackedFloat.div_toRat_cmp_agree hep hsp ha hb (by omega) pf hn hi)
  · exact SmtLibSemantics.samePosition_of_finite_agree _ _
      (fun pf hn hi => UnpackedFloat.div_toRat_cmp_agree hep hsp ha hb (by omega) pf hn hi)

end Fp

/--
The rounded result of `(x.div y)` agrees with the rounding of the exact quotient
`x.toRat / y.toRat` at precision `(ep, sp)`. This is the analogue of the
multiplication exactness theorem, but stated in terms of the rounder's `Rel`
predicate because division is *not* exact: the circuit's `blastSmtLibRound` sees
`(a.div b).toRat` (truncated quotient + sticky bit), and the same-gap congruence
transports the rounder's verdict to the true quotient.
-/
theorem UnpackedFloat.toExtRat_round_div_Rel_smtLibRound_of_RNE
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    {a b : UnpackedFloat (exponentWidth ep sp) (sp + 1)}
    (ha : a.sig.msb = true) (hb : b.sig.msb = true)
    (sign : Bool) (hsign : sign = (a.sign ^^ b.sign)) :
    ((a.div b).blastSmtLibRound ep sp .RNE : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((Fp.SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          Fp.SmtLibSemantics.smtLibV Fp.SmtLibSemantics.smtLibV).round .RNE
        sign (ExtRat.Number (a.toRat / b.toRat))) := by
  have hdmsb : (a.div b).sig.msb = true :=
    UnpackedFloat.msb_div_eq_true_of_msb_eq_true (by omega) ha hb
  have hnorm : (a.div b).normalize = a.div b :=
    UnpackedFloat.normalize_eq_self_of_msb_eq_true (a.div b) hdmsb
  have hsign' : sign = (a.div b).sign := by
    rw [hsign]; rfl
  -- the bit-blasted rounder agrees with the spec rounder on the circuit's own value
  have h1 := Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE he hep hs
    (by omega) (by omega) (a.div b) sign hsign' ((a.div b).toRat) rfl hnorm
  -- the spec rounder cannot distinguish the circuit's value from the exact quotient
  have hd0 : (a.div b).toRat ≠ 0 := UnpackedFloat.toRat_ne_zero_of_msb_eq_true hdmsb
  have ha0 : a.toRat ≠ 0 := UnpackedFloat.toRat_ne_zero_of_msb_eq_true ha
  have hb0 : b.toRat ≠ 0 := UnpackedFloat.toRat_ne_zero_of_msb_eq_true hb
  have hq0 : a.toRat / b.toRat ≠ 0 := by grind
  obtain ⟨hPos, hPosS⟩ := Fp.UnpackedFloat.div_samePosition hep hs ha hb
  have hcongr := Fp.SmtLibSemanticsQ.roundRNE_congr_of_samePosition (by omega) hs sign
    (by grind) hPos hPosS
  rw [Fp.SmtLibSemantics.RoundMethod.round_RNE_eq] at h1 ⊢
  rw [← hcongr]
  exact h1

/-!
## `div_eq_div`: the division circuit against the SMT-LIB semantics

`SmtLibFunctions.div` rounds the exact extended-rational quotient `z = v(x) / v(y)`
with the result sign `xorSign x y` passed to the rounder (so zero results carry the
IEEE-754 sign), and special-cases the IEEE-754 divideByZero exception (`y = ±0` with
finite nonzero `x` yields `±∞` with the xor sign) — which is *not* a function of `z`,
because the embedding `v` collapses `±0`.

Historical note: an earlier transcription read
`if xorSign x y then neg (round rm true (-z)) else round rm false z`. That encoding
is the identity on the sign of `z` whenever `z` is zero or infinite (the trailing
`neg` undoes the inner negation), so it produced `+0` where IEEE 754 requires `-0`
(e.g. `(-0) / 5`) and the wrong infinity for division by `-0` (e.g. `5 / (-0) = +∞`
instead of `-∞`), making `div_eq_div` *false* in those sub-cases. This was confirmed
by exhaustively evaluating both semantics over all input pairs of the formats
`(ein, sin) = (3, 1)` and `(3, 2)` using the computable rounder of
`Fp/Theorems/LowerUpperRound/Functional.lean`: the old spec disagreed with the
(symfpu-validated) implementation on exactly the zero-sign cases listed above,
while the corrected spec agrees on *all* inputs.
-/

/-! ### ExtRat arithmetic helpers for the special-value cases -/

/-- `inv` of a nonzero number is the number's reciprocal. -/
theorem ExtRat.inv_number_of_ne_zero {r : Rat} (hr : r ≠ 0) :
    (ExtRat.Number r).inv = ExtRat.Number (1 / r) := by
  rw [ExtRat.inv]
  simp [hr]

/-- `∞ * r = ±∞` with the xor of the signs, for nonzero `r`. -/
theorem ExtRat.infinity_mul_number_of_ne_zero {s : Bool} {r : Rat} (hr : r ≠ 0) :
    (ExtRat.Infinity s) * (ExtRat.Number r) = ExtRat.Infinity (s ^^ decide (r < 0)) := by
  rw [← ExtRat.mul_def, ExtRat.mul]
  simp [hr]

/-- `r * ∞ = ±∞` with the xor of the signs, for nonzero `r`. -/
theorem ExtRat.number_mul_infinity_of_ne_zero {s : Bool} {r : Rat} (hr : r ≠ 0) :
    (ExtRat.Number r) * (ExtRat.Infinity s) = ExtRat.Infinity (s ^^ decide (r < 0)) := by
  rw [← ExtRat.mul_def, ExtRat.mul]
  simp [hr]

/-- `±∞ * ±∞ = ±∞` with the xor of the signs. -/
theorem ExtRat.infinity_mul_infinity_eq {s1 s2 : Bool} :
    (ExtRat.Infinity s1) * (ExtRat.Infinity s2) = ExtRat.Infinity (s1 ^^ s2) := by
  rw [← ExtRat.mul_def, ExtRat.mul]

/-- Division of numbers is the number of the division, for nonzero divisor. -/
theorem ExtRat.number_div_number_of_ne_zero {p q : Rat} (hq : q ≠ 0) :
    (ExtRat.Number p) / (ExtRat.Number q) = ExtRat.Number (p / q) := by
  rw [ExtRat.div_eq_mul_inv, ExtRat.inv_number_of_ne_zero hq, ExtRat.number_mul_number_eq]
  congr 1
  rw [Rat.div_def, Rat.div_def]
  grind

namespace Fp

/--
The division circuit `PackedFloat.div` agrees with the SMT-Lib semantics, modulo NaN payload.
Mirror of `mul_eq_mul`.
-/
theorem div_eq_div {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (rm : RoundingMode) (hrm : rm = .RNE) (a b : PackedFloat ein sin) :
    (Fp.SmtLibSemantics.SmtLibFunctions.div (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b).EquivUptoNaN
    (PackedFloat.div rm a b) := by
  have he0 : 0 < ein := by omega
  simp only [SmtLibSemantics.SmtLibFunctions.div, SmtLibSemantics.smtLibV_embed_eq,
    PackedFloat.toExtRat_eq_toExtRat', roundQ_eq, SmtLibSemantics.instExtendedRat.isZero,
    SmtLibSemantics.instExtendedRat.isNaN_eq]
  rw [PackedFloat.div, EUnpackedFloat.div]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    rw [ExtRat.div_eq_mul_inv]
    simp only [hnan, PackedFloat.toExtRat'_eq_NaN_of_isNaN, ExtRat.NaN_mul,
      PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
      PackedFloat.isNaN_unpack_eq_isNaN, Bool.true_or, cond_true,
      EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
    rw [if_neg (by simp [ExtRat.isNaN_iff])]
    simp
  case infCase signa =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      rw [ExtRat.div_eq_mul_inv]
      have hinv : (ExtRat.NaN).inv = ExtRat.NaN := rfl
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, hinv, ExtRat.mul_NaN,
        PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
        PackedFloat.isNaN_unpack_eq_isNaN, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [if_neg (by simp [ExtRat.ExtRat.zero_def])]
      simp
    case infCase signb =>
      rw [ExtRat.div_eq_mul_inv]
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, ExtRat.inv_inf_eq_zero,
        ExtRat.inf_mul_zero_eq,
        PackedFloat.unpack_getInfinity, ↓reduceIte, EUnpackedFloat.isNaN_mkInfinity,
        EUnpackedFloat.isInfinite_mkInfinity, Bool.true_and, Bool.true_or, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [if_neg (by simp [ExtRat.ExtRat.zero_def])]
      simp
    case zeroCase signb =>
      rw [if_pos (by
        refine ⟨?_, ?_, ?_⟩
        · rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [he0])]
          simp [ExtRat.ExtRat.zero_def]
        · rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])]
          simp [ExtRat.ExtRat.zero_def]
        · rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])]
          simp [ExtRat.isNaN_iff])]
      simp only [hsin, he0, PackedFloat.unpack_getInfinity, ↓reduceIte,
        PackedFloat.isZero_getZero,
        decide_true, PackedFloat.unpack_eq_mkZero_of_isZero,
        EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.isInfinite_mkZero,
        EUnpackedFloat.isZero_mkInfinity, EUnpackedFloat.isZero_mkZero,
        EUnpackedFloat.sign_num_mkInfinity, EUnpackedFloat.mkZero_num_sign,
        Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.true_or, Bool.or_self, cond_true, cond_false,
        EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp only [SmtLibSemantics.SmtLibFunctions.xorSign, PackedFloat.sign_getInfinity,
        PackedFloat.sign_getZero]
    case numCase hb =>
      have hbz : b.toRat ≠ 0 := b.toRat_ne_zero hb
      have hbsgn : decide (b.toRat < 0) = b.sign := by
        grind only [→ PackedFloat.sign_iff_toRat_neg]
      have hmul : b.toRat * ((1 : Rat) / b.toRat) = 1 := by grind
      have hinviff : ((1 : Rat) / b.toRat < 0) ↔ (b.toRat < 0) := by
        constructor
        · intro h1
          apply Classical.byContradiction
          intro h2
          have hq0 : 0 < b.toRat := by grind
          have hpos : 0 < b.toRat * (-((1 : Rat) / b.toRat)) :=
            Rat.mul_positive hq0 (by grind)
          grind
        · intro h1
          apply Classical.byContradiction
          intro h2
          have hq0 : 0 < (1 : Rat) / b.toRat := by grind
          have hpos : 0 < (-b.toRat) * ((1 : Rat) / b.toRat) :=
            Rat.mul_positive (by grind) hq0
          grind
      have hinvz : (1 : Rat) / b.toRat ≠ 0 := by grind
      have hinvsgn : decide ((1 : Rat) / b.toRat < 0) = b.sign := by
        rw [← hbsgn]
        grind
      have hz : (PackedFloat.getInfinity ein sin signa).toExtRat' / b.toExtRat'
            = ExtRat.Infinity (signa ^^ b.sign) := by
        rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin]),
            b.toExtRat'_eq_toRat_of hb]
        rw [ExtRat.div_eq_mul_inv, ExtRat.inv_number_of_ne_zero hbz,
            ExtRat.infinity_mul_number_of_ne_zero hinvz, hinvsgn]
        simp [PackedFloat.sign_getInfinity]
      rw [if_neg (by
        intro hC
        have h1 := hC.1
        rw [b.toExtRat'_eq_toRat_of hb] at h1
        rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def] at h1
        exact hbz (by simpa using h1))]
      rw [hz, Fp.roundQ_eq_round_of_Infinity he0 hsin]
      simp only [hsin, PackedFloat.unpack_getInfinity, ↓reduceIte,
        PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isNaN_mkNumber,
        EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isZero_mkInfinity, EUnpackedFloat.isZero_mkNumber,
        EUnpackedFloat.sign_num_mkInfinity, EUnpackedFloat.num_mkNumber,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign,
        Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.true_or, Bool.or_self, cond_true, cond_false,
        EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      apply PackedFloat.EquivUptoNaN.of_eq
      rfl
  case zeroCase signa =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      rw [ExtRat.div_eq_mul_inv]
      have hinv : (ExtRat.NaN).inv = ExtRat.NaN := rfl
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, hinv, ExtRat.mul_NaN,
        PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
        PackedFloat.isNaN_unpack_eq_isNaN, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [if_neg (by simp [ExtRat.ExtRat.zero_def])]
      simp
    case infCase signb =>
      have hz : (PackedFloat.getZero ein sin signa).toExtRat'
            / (PackedFloat.getInfinity ein sin signb).toExtRat' = ExtRat.Number 0 := by
        rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [he0]),
            PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])]
        rw [ExtRat.div_eq_mul_inv, ExtRat.inv_inf_eq_zero, ExtRat.number_mul_number_eq]
        simp
      rw [if_neg (by
        intro hC
        have h1 := hC.1
        rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])] at h1
        rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def] at h1
        simp at h1)]
      rw [hz, Fp.round_eq_mkZero_of_mkZero he0]
      simp only [hsin, he0, PackedFloat.isZero_getZero, decide_true,
        PackedFloat.unpack_eq_mkZero_of_isZero, PackedFloat.unpack_getInfinity, ↓reduceIte,
        EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkInfinity,
        EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkInfinity,
        EUnpackedFloat.isZero_mkZero, EUnpackedFloat.isZero_mkInfinity,
        EUnpackedFloat.mkZero_num_sign, EUnpackedFloat.sign_num_mkInfinity,
        Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.true_or, Bool.or_self, cond_true, cond_false,
        EUnpackedFloat.mkZero_pack_eq_getZero]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp only [SmtLibSemantics.SmtLibFunctions.xorSign, PackedFloat.sign_getZero,
        PackedFloat.sign_getInfinity]
    case zeroCase signb =>
      rw [ExtRat.div_eq_mul_inv]
      simp only [he0, PackedFloat.isZero_getZero, decide_true,
        PackedFloat.toExtRat'_eq_zero_of_isZero, ExtRat.zero_inv_eq_inf,
        ExtRat.zero_mul_inf_eq,
        PackedFloat.unpack_eq_mkZero_of_isZero, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isZero_mkZero,
        Bool.and_true, Bool.true_and, Bool.true_or, Bool.or_self, Bool.false_or,
        cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [if_neg (by
        intro hC
        exact hC.2.1 rfl)]
      simp
    case numCase hb =>
      have hbz : b.toRat ≠ 0 := b.toRat_ne_zero hb
      have hbnz : ¬ b.isZero := by grind
      have hz : (PackedFloat.getZero ein sin signa).toExtRat' / b.toExtRat'
            = ExtRat.Number 0 := by
        rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [he0]),
            b.toExtRat'_eq_toRat_of hb]
        rw [ExtRat.div_eq_mul_inv, ExtRat.inv_number_of_ne_zero hbz,
            ExtRat.number_mul_number_eq]
        simp
      rw [if_neg (by
        intro hC
        have h1 := hC.1
        rw [b.toExtRat'_eq_toRat_of hb] at h1
        rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def] at h1
        exact hbz (by simpa using h1))]
      rw [hz, Fp.round_eq_mkZero_of_mkZero he0]
      simp only [hsin, he0, PackedFloat.isZero_getZero, decide_true,
        PackedFloat.unpack_eq_mkZero_of_isZero,
        PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNumber,
        EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isZero_mkZero, EUnpackedFloat.isZero_mkNumber,
        EUnpackedFloat.mkZero_num_sign, EUnpackedFloat.num_mkNumber,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign,
        hbnz, Bool.false_eq_true, not_false_eq_true,
        PackedFloat.unpackNormOrNonzeroSubnorm_isZero_eq_of_not_isZero,
        Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.true_or, Bool.or_self, cond_true, cond_false,
        EUnpackedFloat.mkZero_pack_eq_getZero]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp only [SmtLibSemantics.SmtLibFunctions.xorSign, PackedFloat.sign_getZero]
  case numCase ha =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      rw [ExtRat.div_eq_mul_inv]
      have hinv : (ExtRat.NaN).inv = ExtRat.NaN := rfl
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, hinv, ExtRat.mul_NaN,
        PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
        PackedFloat.isNaN_unpack_eq_isNaN, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [if_neg (by simp [ExtRat.ExtRat.zero_def])]
      simp
    case infCase signb =>
      have hanz : ¬ a.isZero := by grind
      have hz : a.toExtRat' / (PackedFloat.getInfinity ein sin signb).toExtRat'
            = ExtRat.Number 0 := by
        rw [a.toExtRat'_eq_toRat_of ha,
            PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])]
        rw [ExtRat.div_eq_mul_inv, ExtRat.inv_inf_eq_zero, ExtRat.number_mul_number_eq]
        simp
      rw [if_neg (by
        intro hC
        have h1 := hC.1
        rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])] at h1
        rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def] at h1
        simp at h1)]
      rw [hz, Fp.round_eq_mkZero_of_mkZero he0]
      simp only [hsin, he0, PackedFloat.unpack_getInfinity, ↓reduceIte,
        PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isNaN_mkInfinity,
        EUnpackedFloat.isInfinite_mkNumber, EUnpackedFloat.isInfinite_mkInfinity,
        EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.isZero_mkInfinity,
        EUnpackedFloat.num_mkNumber, EUnpackedFloat.sign_num_mkInfinity,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign,
        hanz, Bool.false_eq_true, not_false_eq_true,
        PackedFloat.unpackNormOrNonzeroSubnorm_isZero_eq_of_not_isZero,
        Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.true_or, Bool.or_self, cond_true, cond_false,
        EUnpackedFloat.mkZero_pack_eq_getZero]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp only [SmtLibSemantics.SmtLibFunctions.xorSign, PackedFloat.sign_getInfinity]
    case zeroCase signb =>
      have haz : a.toRat ≠ 0 := a.toRat_ne_zero ha
      have hanz : ¬ a.isZero := by grind
      rw [if_pos (by
        refine ⟨?_, ?_, ?_⟩
        · rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [he0])]
          simp [ExtRat.ExtRat.zero_def]
        · rw [a.toExtRat'_eq_toRat_of ha]
          rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def]
          simp [haz]
        · rw [a.toExtRat'_eq_toRat_of ha]
          simp [ExtRat.isNaN_iff])]
      simp only [hsin, he0, PackedFloat.isZero_getZero, decide_true,
        PackedFloat.unpack_eq_mkZero_of_isZero,
        PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isInfinite_mkNumber, EUnpackedFloat.isInfinite_mkZero,
        EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.isZero_mkZero,
        EUnpackedFloat.num_mkNumber, EUnpackedFloat.mkZero_num_sign,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign,
        hanz, Bool.false_eq_true, not_false_eq_true,
        PackedFloat.unpackNormOrNonzeroSubnorm_isZero_eq_of_not_isZero,
        Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.true_or, Bool.or_self, cond_true, cond_false,
        EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp only [SmtLibSemantics.SmtLibFunctions.xorSign, PackedFloat.sign_getZero]
    case numCase hb =>
      -- The interesting case: both finite nonzero numbers. Reduce the implementation
      -- to `blastSmtLibRound (a.unpackNum.div b.unpackNum)` and apply
      -- `pack'_EquivUptoNaN_of_Rel` with `toExtRat_round_div_Rel_smtLibRound_of_RNE`.
      subst hrm
      have hbz : b.toRat ≠ 0 := b.toRat_ne_zero hb
      have haz : a.toRat ≠ 0 := a.toRat_ne_zero ha
      have hanz : ¬ a.isZero := by grind
      have hbnz : ¬ b.isZero := by grind
      rw [if_neg (by
        intro hC
        have h1 := hC.1
        rw [b.toExtRat'_eq_toRat_of hb] at h1
        rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def] at h1
        exact hbz (by simpa using h1))]
      rw [a.toExtRat'_eq_toRat_of ha, b.toExtRat'_eq_toRat_of hb,
          ExtRat.number_div_number_of_ne_zero hbz]
      simp only [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha,
        PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.num_mkNumber,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign,
        hanz, hbnz, Bool.false_eq_true, not_false_eq_true,
        PackedFloat.unpackNormOrNonzeroSubnorm_isZero_eq_of_not_isZero,
        Bool.false_or, Bool.or_false, Bool.false_and, Bool.and_false, Bool.or_self,
        cond_false]
      have hxor : SmtLibSemantics.SmtLibFunctions.xorSign a b = (a.sign ^^ b.sign) := by
        simp only [SmtLibSemantics.SmtLibFunctions.xorSign]
      rw [hxor]
      have hmsba : a.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true ha
      have hmsbb : b.unpackNum.sig.msb = true := PackedFloat.msb_unpackNum_eq_true hb
      have hquot : a.unpackNum.toRat / b.unpackNum.toRat = a.toRat / b.toRat := by
        have h1 : a.unpackNum.toRat = a.toRat := by grind
        have h2 : b.unpackNum.toRat = b.toRat := by grind
        rw [h1, h2]
      have hRel := UnpackedFloat.toExtRat_round_div_Rel_smtLibRound_of_RNE he hep hsin
        hmsba hmsbb (a.sign ^^ b.sign)
        (by simp [PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign])
      rw [hquot] at hRel
      rw [PackedFloat.EquivUptoNaN_symm]
      rw [EUnpackedFloat.pack_eq_pack']
      exact EUnpackedFloat.pack'_EquivUptoNaN_of_Rel hsin _ _ hRel

/-
The remaining `sorryAx` inputs of `div_eq_div` are exactly:
* `UnpackedFloat.div_toRat_cmp_agree` (this file) — the grid/sticky-bit closeness
  argument for the division circuit;
* `UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE` and its supporting lemmas
  (`Fp/Theorems/UnpackedFloat/Round.lean`) — the general rounder-correctness program;
* `EUnpackedFloat.pack'_EquivUptoNaN_of_Rel` (`Fp/Theorems/PackedUnpackedRel/Basic.lean`)
  — pack/unpack round-tripping on numbers.
-/
/--
info: 'Fp.div_eq_div' depends on axioms: [propext,
 sorryAx,
 BitVec.toNat_clz_cons,
 Classical.choice,
 PackedFloat.unpackNormOrNonzeroSubnorm_isZero_eq_of_not_isZero,
 Quot.sound]
-/
#guard_msgs in #print axioms div_eq_div

end Fp
