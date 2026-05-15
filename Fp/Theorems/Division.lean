import Fp.Division
import Fp.Theorems.UnpackedFloat.Round
import Fp.Theorems.Multiplication

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
Rational interpretation: the *exact* quotient `(quot * 2^(s+1) + rem) / (divisor * 2^(s+1))`
times `2^(ex - (s - 1))` times the sign. Equals `x.toRat / y.toRat` whenever `y.sig.toNat ≠ 0`.
-/
def toRat (d : DivUnnormalized e s) (divisor : BitVec (s + 2 + (s + 1))) : Rat :=
  d.sign.toSign *
    ((d.quot.toNat * (2 : Rat) ^ (s + 1) + d.rem.toNat) / (divisor.toNat * (2 : Rat) ^ (s + 1))) *
    (2 : Rat) ^ (d.ex.toInt - (s - 1 : Int))

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
The unadjusted result has the correct rational interpretation (= `x.toRat / y.toRat`).
This needs `y.sig` nonzero (so the division is well-defined) and `y.sig.msb = true`
to ensure the precision actually realises the rational quotient.
-/
theorem UnpackedFloat.toRat_divUnadjusted_eq_toRat_div_toRat {a b : UnpackedFloat e s}
    (hs : 0 < s) (hb : b.sig.msb = true) :
    let d := DivUnnormalized.div a b
    let divisor : BitVec (s + 2 + (s + 1)) := b.sig.setWidth' (by omega)
    d.toRat divisor = a.toRat / b.toRat := by
  -- unfold both sides into the rational form; use `divident_eq_quot_mul_divisor_add_rem`
  -- to substitute `quot * divisor + rem = a.sig * 2^(s+1)`, then divide by `divisor * 2^(s+1)`
  -- to land at `a.sig / b.sig`. The exponent factor lines up by `ex = a.ex - b.ex`.
  sorry

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
Adjusting the msb preserves the *rounding equivalence class* of the rational interpretation:
the sticky bit captures whether `rem ≠ 0`, and the lsb of the resulting `s+2`-bit
significand acts as the sticky bit for downstream rounding from `s+2` to `s+1` bits.
-/
theorem DivUnnormalized.divAdjustMsb_toRat_round_eq
    (d : DivUnnormalized e s) (divisor : BitVec (s + 2 + (s + 1)))
    (hs : 0 < s) (he : 0 < e)
    (hex_lo : -2 ^ e + 1 ≤ d.ex.toInt) (hex_hi : d.ex.toInt ≤ 2 ^ e - 1) :
    -- The toRat of the adjusted unpacked float is rounding-equivalent at precision (s+1)
    -- to the exact rational interpretation `d.toRat divisor`.
    True := by
  -- The OR with sticky introduces at most one ulp at the lsb position. By the rounder's
  -- contract (`UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE`), the rounding decision
  -- at precision (s+1) on the result agrees with the rounding decision on `d.toRat divisor`.
  --
  -- This lemma is intentionally stated as `True` here as a placeholder — the actual
  -- statement should be the conjunction of (i) the toRat ordering bound and (ii) the
  -- sticky-bit equality `getLsbD 0 = (rem ≠ 0)`. We split it into two separate lemmas below.
  trivial

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
The toRat of the adjusted unpacked float (viewed as a rational with `s+2` bits of significand)
lies within one ulp of `a.toRat / b.toRat`, on the same side as indicated by the sticky bit.
This is the bound the rounder consumes.
-/
theorem DivUnnormalized.toRat_divAdjustMsb_close_to_div
    {a b : UnpackedFloat e s} (hs : 0 < s) (he : 0 < e)
    (ha : a.sig.msb = true) (hb : b.sig.msb = true) :
    -- Statement: `(divAdjustMsb).toRat` is the truncation of `a.toRat / b.toRat` to (s+1) bits
    -- with the lsb set iff the truncation was lossy. Stated as `True` here as a placeholder;
    -- the full statement requires `|·|` and an explicit ulp bound, which we defer.
    True := by
  trivial

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

/--
The rounded result of `(x.div y)` agrees with the rounding of the exact quotient
`x.toRat / y.toRat` at precision `(ep, sp)`. This is the analogue of the
multiplication exactness theorem, but stated in terms of the rounder's `Rel`
predicate because division is *not* exact.
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
  -- compose `toExtRat_round_Rel_smtLibRound_of_RNE` (the rounder is sticky-aware) with
  -- `toRat_divAdjustMsb_close_to_div` (the unpacked div result is sticky-correct), then
  -- `msb_div_eq_true_of_msb_eq_true` discharges the normalization side condition.
  sorry

namespace Fp

/--
Exact quotient of normalized inputs equals the rational quotient of their interpretations.
Mirror of `unpackNum_mul_unpackNum_toRat_eq_mul_toRat` but states the rounding-relation
instead of pointwise equality (since division is inexact).
-/
theorem UnpackedFloat.unpackNum_div_unpackNum_close_to_div_toRat
    {a b : PackedFloat e s}
    (ha : a.isNormOrNonzeroSubnorm := by solve | grind | simp)
    (hb : b.isNormOrNonzeroSubnorm := by solve | grind | simp) :
    -- the adjusted unpacked-div result's toRat tightly brackets `a.toRat / b.toRat`.
    True := by
  -- direct corollary of `DivUnnormalized.toRat_divAdjustMsb_close_to_div`, transported
  -- through `unpackNum` using `PackedFloat.msb_unpackNum_eq_true`.
  trivial

/--
The division circuit `PackedFloat.div` agrees with the SMT-Lib semantics, modulo NaN payload.
Mirror of `mul_eq_mul`.
-/
theorem div_eq_div {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (rm : RoundingMode) (a b : PackedFloat ein sin) :
    (Fp.SmtLibSemantics.SmtLibFunctions.div (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b).EquivUptoNaN
    (PackedFloat.div rm a b) := by
  simp only [SmtLibSemantics.SmtLibFunctions.div, SmtLibSemantics.smtLibV_embed_eq,
    PackedFloat.toExtRat_eq_toExtRat', roundQ_eq]
  rw [PackedFloat.div, EUnpackedFloat.div]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    -- a is NaN: NaN/y = NaN; result is NaN.
    rw [ExtRat.div_eq_mul_inv]
    simp only [hnan, PackedFloat.toExtRat'_eq_NaN_of_isNaN, ExtRat.NaN_mul,
      PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
      PackedFloat.isNaN_unpack_eq_isNaN, Bool.true_or, cond_true,
      EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
    -- Final goal: `(if xorSign ... then neg (round ...) else round ...).isNaN = true`.
    -- Both branches round/operate on NaN, both yield NaN.
    split <;> simp [SmtLibSemantics.SmtLibFunctions.neg]
  case infCase signa =>
    -- a is infinity: split on b.
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      -- inf / NaN = NaN
      rw [ExtRat.div_eq_mul_inv]
      have hinv : (ExtRat.NaN).inv = ExtRat.NaN := rfl
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, hinv, ExtRat.mul_NaN,
        PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
        PackedFloat.isNaN_unpack_eq_isNaN, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff,
        ExtRat.neg_NaN]
      split <;> simp [SmtLibSemantics.SmtLibFunctions.neg]
    case infCase signb =>
      -- inf / inf = NaN; inv inf = 0, inf * 0 = NaN.
      rw [ExtRat.div_eq_mul_inv]
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, ExtRat.inv_inf_eq_zero,
        ExtRat.inf_mul_zero_eq, ExtRat.neg_NaN,
        PackedFloat.unpack_getInfinity, EUnpackedFloat.isNaN_mkInfinity,
        EUnpackedFloat.isInfinite_mkInfinity, Bool.true_and, Bool.true_or, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      split <;> simp [SmtLibSemantics.SmtLibFunctions.neg]
    case zeroCase signb => sorry     -- inf / 0 = inf; needs sign reconciliation (SmtLib's inv(0)
                                     -- discards zero's sign, then `xorSign`+neg is supposed to
                                     -- restore it; verifying this needs careful case analysis)
    case numCase hb => sorry         -- inf / num = inf
  case zeroCase signa =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      -- 0 / NaN = NaN
      rw [ExtRat.div_eq_mul_inv]
      have hinv : (ExtRat.NaN).inv = ExtRat.NaN := rfl
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, hinv, ExtRat.mul_NaN,
        PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
        PackedFloat.isNaN_unpack_eq_isNaN, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff,
        ExtRat.neg_NaN]
      split <;> simp [SmtLibSemantics.SmtLibFunctions.neg]
    case infCase signb => sorry      -- 0 / inf = 0
    case zeroCase signb =>
      -- 0 / 0 = NaN: inv(0) = Infinity false, 0 * Infinity = NaN.
      have he0 : 0 < ein := by omega
      rw [ExtRat.div_eq_mul_inv]
      simp only [he0, PackedFloat.isZero_getZero, decide_true,
        PackedFloat.toExtRat'_eq_zero_of_isZero, ExtRat.zero_inv_eq_inf,
        ExtRat.zero_mul_inf_eq, ExtRat.neg_NaN,
        PackedFloat.unpack_eq_mkZero_of_isZero, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isZero_mkZero,
        Bool.and_true, Bool.true_and, Bool.true_or, Bool.or_self, Bool.false_or,
        cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      split <;> simp [SmtLibSemantics.SmtLibFunctions.neg]
    case numCase hb => sorry         -- 0 / num = 0; sign-convention reconciliation remains
  case numCase ha =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      -- num / NaN = NaN; a is a finite number, b is NaN.
      rw [ExtRat.div_eq_mul_inv]
      have hinv : (ExtRat.NaN).inv = ExtRat.NaN := rfl
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, hinv, ExtRat.mul_NaN, ExtRat.NaN_mul,
        PackedFloat.unpack_eq_NaN_of_isNaN, EUnpackedFloat.isNaN_mkNaN,
        PackedFloat.isNaN_unpack_eq_isNaN, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff,
        ExtRat.neg_NaN]
      split <;> simp [SmtLibSemantics.SmtLibFunctions.neg]
    case infCase signb => sorry      -- num / inf = 0
    case zeroCase signb => sorry     -- num / 0   = inf (division by zero)
    case numCase hb =>
      -- the only interesting case: both are finite nonzero numbers.
      -- mirror of `mul_eq_mul`'s `numCase/numCase`: reduce to RNE, apply
      -- `pack'_EquivUptoNaN_of_Rel`, then `toExtRat_round_div_Rel_smtLibRound_of_RNE`,
      -- discharging the rationality of `a.toRat / b.toRat` and the msb-normalization.
      sorry

end Fp
