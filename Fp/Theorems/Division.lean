import Fp.Division
import Fp.Theorems.Addition
import Fp.Theorems.Multiplication
import Fp.Theorems.SmtLibSemanticsQ

/-!
# Division correctness via the sticky-bit (`StickyEquiv`) theory

Division is the operation that *forces* the sticky-bit machinery.  Compare the
two existing patterns:

* **Multiplication** is *exact* at the circuit level: the product of two `s`-bit
  significands fits in `2s` bits, so
  `UnpackedFloat.toRat_mulUnadjustedMsb_eq_toRat_mul_toRat` proves the circuit
  value *equals* the exact rational product, and `mul_eq_mul` rounds `r = x.toRat`
  on the nose via `toExtRat_round_Rel_smtLibRound_of_RNE`.
* **Addition** is *inexact*: alignment shifts drop low bits, so the circuit sum
  is only a `StickyEquiv` compression of the exact sum (`stickyEquiv_add`), and
  `add_eq_add` must round through the sticky bridge
  `blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`.

**Division behaves like addition, not multiplication.**  The quotient
`x.sig / y.sig` generically has a non-terminating binary expansion, so the
circuit (`UnpackedFloat.div`, `Fp/Division.lean`) keeps `s + 2` bits and folds
the leftover `rem != 0` into the bottom significand bit as a **sticky bit**.  The
kept value is therefore *not* the exact quotient — it is a `StickyEquiv`
compression of it.  This is exactly the fact "division rounding is not exact,
hence a sticky bit is generated", and it is what routes the correctness proof
through the same sticky bridge that addition uses.

This file mirrors the layering of `Fp/Theorems/Addition.lean`:
* Layer 3 — the circuit-level error bound (`stickyEquiv_div`, `msb_div_eq_true`).
* the `unpackNum` lift (`unpackNum_div_unpackNum_stickyEquiv`).
* Layer 1 — the big theorem `div_eq_div`.
-/

namespace Fp

open SmtLibSemantics

/-! ## Layer 3: circuit-level error bound (the sticky bit)

These are the bit-level facts about `UnpackedFloat.div`.  Like their addition
counterparts (`UnpackedFloat.stickyEquiv_add`, `UnpackedFloat.msb_add_eq_true`)
the Lean proofs are left as `sorry`; the pen-and-paper arguments are in the
docstrings.
-/

/--
**The division circuit is correct up to a sticky-bit error.**

For normalized inputs (`msb = true`) the circuit quotient `(x.div y).toRat` is a
sticky compression (`StickyEquiv`) of the exact quotient `x.toRat / y.toRat` at
the weight `2^((x.div y).toExpInt)` of the result's last significand bit.

This is *the* statement expressing that division rounding is inexact and hence
emits a sticky bit: the right `StickyEquiv` disjunct (`q` an odd multiple of the
ulp with `|r - q| < ulp`) is precisely "the sticky bit is set and the true value
lies strictly within one ulp".

Pen-and-paper proof.  `y.sig.msb = true` gives `y ≠ 0`, so the exact quotient is
well defined and (since `x.sig.msb = true ⇒ x ≠ 0`) nonzero.  The circuit forms
`divident = x.sig · 2^(s+1)` and `divisor = y.sig`, and computes
`quot = ⌊divident / divisor⌋`, `rem = divident mod divisor`, so
`divident = quot · divisor + rem` with `0 ≤ rem < divisor`.  Dividing by
`divisor · 2^(s+1)` and reinstating the exponents,
`x.toRat / y.toRat = (quot + rem/divisor) · 2^E` for the pre-normalization grid
weight `2^E`, with the fractional part `rem/divisor ∈ [0, 1)`.

* `rem = 0`: the division is exact, the OR-ed sticky bit is `false`, and the
  result equals the exact quotient — the left `StickyEquiv` disjunct.
* `rem ≠ 0`: OR-ing `rem != 0` into the bottom bit forces the kept value to an
  *odd* multiple of the grid weight, and the discarded fraction
  `rem/divisor · 2^E ∈ (0, 2^E)` places the exact quotient strictly within one
  grid step — the right disjunct.  The conditional normalization shift
  (`quot <<< !quot.msb`, halving the grid) preserves the invariant: when the
  quotient lands in `[1/2, 1)` it is shifted left by one and `E` decreases by
  one, and the (still set) sticky bit keeps the bottom bit odd.
-/
theorem UnpackedFloat.stickyEquiv_div {e s : Nat} (x y : UnpackedFloat e s)
    (hs : 0 < s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    StickyEquiv ((x.div y).toExpInt) ((x.div y).toRat) (x.toRat / y.toRat) := by
  sorry

/--
**The division circuit produces a normalized result** (for normalized inputs).

Pen-and-paper proof.  With `x.sig, y.sig ∈ [2^(s-1), 2^s)` the exact quotient
lies in `(1/2, 2)`, so `quot` (computed at `s + 2` bits) has either its top bit
set (quotient in `[1, 2)`) or its second bit set (quotient in `[1/2, 1)`).  In
the first case the msb is already `true`; in the second the conditional shift
`quot <<< !quot.msb` shifts left by one, setting the msb.  OR-ing the sticky bit
into the bottom never clears the msb.
-/
theorem UnpackedFloat.msb_div_eq_true {e s : Nat} (x y : UnpackedFloat e s)
    (hs : 0 < s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (x.div y).sig.msb = true := by
  sorry

/-! ## The `unpackNum` lift -/

/--
The unpacked quotient of two `isNormOrNonzeroSubnorm` packed floats is a sticky
compression of the exact rational quotient.  Mirrors
`UnpackedFloat.unpackNum_add_unpackNum_stickyEquiv`.
-/
theorem UnpackedFloat.unpackNum_div_unpackNum_stickyEquiv
    {e s : Nat} {a b : PackedFloat e s} (hs : 0 < s)
    (ha : a.isNormOrNonzeroSubnorm) (hb : b.isNormOrNonzeroSubnorm) :
    StickyEquiv ((a.unpackNum.div b.unpackNum).toExpInt)
      ((a.unpackNum.div b.unpackNum).toRat) (a.toRat / b.toRat) := by
  have hra := PackedFloat.unpackNum_toRat_eq_toRat (pf := a) ha
  have hrb := PackedFloat.unpackNum_toRat_eq_toRat (pf := b) hb
  rw [← hra, ← hrb]
  exact UnpackedFloat.stickyEquiv_div a.unpackNum b.unpackNum (by omega)
    (PackedFloat.msb_unpackNum_eq_true ha) (PackedFloat.msb_unpackNum_eq_true hb)

/-! ## Layer 1: the big theorem

The statement mirrors `Fp.mul_eq_mul` / `Fp.add_eq_add`: the SMT-LIB division
(exact rational division followed by SMT-LIB rounding) agrees with the
bit-blasted `PackedFloat.div` up to the NaN bit pattern, for RNE.

The proof dispatches the NaN / ∞ / zero / divide-by-zero special cases following
`mul_eq_mul`'s branch structure (which matches `EUnpackedFloat.div`'s guards),
and in the Number/Number branch feeds `unpackNum_div_unpackNum_stickyEquiv` into
`UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv` (the same sticky
bridge addition uses), closing with `EUnpackedFloat.pack'_EquivUptoNaN_of_Rel`.
The bridge's width side conditions `exponentWidth ein sin ≤ eu` and
`sin + 3 ≤ su` hold because `UnpackedFloat.div` on `unpackNum` outputs width
`(exponentWidth ein sin + 1, sin + 3)`.
-/
set_option maxHeartbeats 1000000 in
theorem div_eq_div {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (rm : RoundingMode) (hrm : rm = .RNE) (a b : PackedFloat ein sin) :
    (Fp.SmtLibSemantics.SmtLibFunctions.div
        (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b).EquivUptoNaN
      (PackedFloat.div rm a b) := by
  sorry

end Fp
