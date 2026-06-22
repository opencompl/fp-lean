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

/-! ## ExtRat arithmetic helpers for the special-value cases

Mirror the helpers used by `Fp.mul_eq_mul`'s special-value dispatch, specialised
to division/inverse.  Declared outside `namespace Fp` so they live in the
`ExtRat` namespace. -/

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

/-- Division of numbers is the number of the division, for nonzero divisor. -/
theorem ExtRat.number_div_number_of_ne_zero {p q : Rat} (hq : q ≠ 0) :
    (ExtRat.Number p) / (ExtRat.Number q) = ExtRat.Number (p / q) := by
  rw [ExtRat.div_eq_mul_inv, ExtRat.inv_number_of_ne_zero hq, ExtRat.number_mul_number_eq]
  congr 1
  rw [Rat.div_def, Rat.div_def]
  grind

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

This is a statement about the *post-normalization* significand
`(x.div y).sig = quot <<< !quot.msb`, **not** about the raw quotient `quot`,
whose msb is genuinely `false` in one of the two cases below.

Pen-and-paper proof.  As `s`-bit numbers, `msb = true` means
`x.sig, y.sig ∈ [2^(s-1), 2^s)`, so the exact ratio `x.sig / y.sig ∈ (1/2, 2)`.
The circuit forms `quot = ⌊x.sig · 2^(s+1) / y.sig⌋` at `s + 2` bits — where the
msb is bit `s+1` — so `quot ∈ (2^s, 2^(s+2))`.  Two cases:

* **Ratio ∈ [1, 2)**: `quot ∈ [2^(s+1), 2^(s+2))`, bit `s+1` is set, so
  `quot.msb = true` already and `!quot.msb = false` (the shift is by `0`).
* **Ratio ∈ (1/2, 1)**: `quot ∈ (2^s, 2^(s+1))`, bit `s` is set but bit `s+1`
  is clear — i.e. **the raw `quot.msb` is `false`**.  Then `!quot.msb = true`,
  so `quot <<< 1` moves bit `s` up to bit `s+1`; since `quot < 2^(s+1)` this
  cannot overflow `s+2` bits, so the shifted value lies in `(2^(s+1), 2^(s+2))`
  and its msb is `true`.  The matching exponent decrement is the `- !quot.msb`
  term on `ex` (`Fp/Division.lean`).

In both cases the normalized significand has msb `true`, and OR-ing the sticky
bit `rem != 0` into bit `0` never clears it.
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
          simp [ExtRat.isNaN_iff]
        · rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _ (by simp [hsin])]
          simp [ExtRat.ExtRat.zero_def])]
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
        exact hC.2.2 ExtRat.ExtRat.zero_def.symm)]
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
          simp [ExtRat.isNaN_iff]
        · rw [a.toExtRat'_eq_toRat_of ha]
          rw [show (0 : ExtRat) = ExtRat.Number 0 from ExtRat.ExtRat.zero_def]
          simp [haz])]
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
      -- The interesting case: both finite nonzero numbers. The exact quotient is a
      -- sticky compression of the circuit value, so we round through the **addition
      -- sticky bridge** `blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv` rather than
      -- the exact-rounding route. There is no cancellation sub-case: a quotient of
      -- nonzero finite numbers is always nonzero.
      subst hrm
      have hbz : b.toRat ≠ 0 := b.toRat_ne_zero hb
      have haz : a.toRat ≠ 0 := a.toRat_ne_zero ha
      have hanz : ¬ a.isZero := by grind
      have hbnz : ¬ b.isZero := by grind
      have hqne : a.toRat / b.toRat ≠ 0 := by grind
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
      rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
      apply EUnpackedFloat.pack'_EquivUptoNaN_of_Rel hsin
      apply UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv he hep hsin
        (eu := exponentWidth ein sin + 1) (su := sin + 1 + 2) (by omega) (by omega)
        (a.unpackNum.div b.unpackNum) _ _ hqne
      · apply UnpackedFloat.normalize_eq_self_of_msb_eq_true
        exact UnpackedFloat.msb_div_eq_true _ _ (by omega)
          (PackedFloat.msb_unpackNum_eq_true ha) (PackedFloat.msb_unpackNum_eq_true hb)
      · exact UnpackedFloat.unpackNum_div_unpackNum_stickyEquiv hsin ha hb

end Fp
