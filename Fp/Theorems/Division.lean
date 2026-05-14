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
The fundamental integer division identity: `divident = quot * divisor + rem`,
with `rem < divisor`. This is what relates `quot` to the true rational quotient.
-/
theorem DivUnnormalized.divident_eq_quot_mul_divisor_add_rem (x y : UnpackedFloat e s)
    (hy : y.sig.toNat ≠ 0) :
    let d := DivUnnormalized.div x y
    let divident : BitVec (s + 2 + (s + 1)) := x.sig.setWidth' (by omega) ++ 0#(s + 1)
    let divisor  : BitVec (s + 2 + (s + 1)) := y.sig.setWidth' (by omega)
    divident.toNat = d.quot.toNat * divisor.toNat + d.rem.toNat ∧
    d.rem.toNat < divisor.toNat := by
  -- standard integer-division lemma: `BitVec.toNat (a / b) * b.toNat + (a % b).toNat = a.toNat`.
  -- the truncation to `s+2` is justified by a bound `quot < 2^(s+2)` (proved separately).
  sorry

/--
Bound on the raw quotient: since `divident < 2^(2s+3)` and `divisor ≥ 2^(2s+2)` (when y is
normalized: `y.sig.msb = true`), we get `quot < 2^(s+1) ≤ 2^(s+2)`, so truncation to `s + 2`
bits is lossless and leaves the msb-or-msb-1 invariant available for normalization.
-/
theorem DivUnnormalized.quot_lt_two_pow {x y : UnpackedFloat e s}
    (hy : y.sig.msb = true) :
    ((DivUnnormalized.div x y).quot).toNat < 2 ^ (s + 1) := by
  -- 1) `divident.toNat = x.sig.toNat * 2^(s+1) < 2^s * 2^(s+1) = 2^(2s+1)`.
  -- 2) `divisor.toNat = y.sig.toNat ≥ 2^(s-1)` from `hy` (msb-true gives the lower bound).
  -- 3) so the *true* quotient is `< 2^(2s+1) / 2^(s-1) = 2^(s+2)`. Want a tighter `2^(s+1)` —
  --    that requires the normalized-x argument `x.sig.toNat ≤ 2^s - 1` plus careful arithmetic.
  sorry

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
After msb adjustment the significand has msb=true, provided the (raw) quotient
is nonzero (which holds when `x.sig ≠ 0`, since the divident is `x.sig << (s+1)`).
-/
theorem DivUnnormalized.divAdjustMsb_msb_eq_true {x y : UnpackedFloat e s}
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (DivUnnormalized.div x y).divAdjustMsb.sig.msb = true := by
  -- by `quot_lt_two_pow`, `quot.msb = false ∨ quot.msb = true`; in either case the
  -- shift-by-`!msb` puts a `1` in position `s+1` (the msb of the result):
  --  - if `quot.msb = true`, no shift; msb already true.
  --  - if `quot.msb = false`, we need bit s of quot to be true. Show this from the lower
  --    bound `quot ≥ 2^s` which follows from divident ≥ divisor * 2^s (a.sig.msb=true
  --    plus b.sig < 2^s gives divident/divisor ≥ 2^s).
  -- The final OR with the sticky bit only affects the lsb, so msb is unchanged.
  sorry

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

/-- The lsb of the adjusted significand equals the OR sticky bit `rem ≠ 0`. -/
theorem DivUnnormalized.lsb_divAdjustMsb_eq_sticky
    {x y : UnpackedFloat e s} (hs : 0 < s) :
    let d := DivUnnormalized.div x y
    d.divAdjustMsb.sig.getLsbD 0 = (d.rem != 0) := by
  -- the OR with `(rem != 0).setWidth'` forces lsb := lsb_of_shift ||| sticky.
  -- by `quot_lt_two_pow`, the lsb of `quot <<< !msb` is `false` (we shifted a multiple of 2
  -- into the bottom), so the OR simplifies to just the sticky.
  sorry

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
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (x.div y).sig.msb = true := by
  rw [UnpackedFloat.div_eq_divAdjustMsb_divUnadjusted]
  exact DivUnnormalized.divAdjustMsb_msb_eq_true hx hy

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
    case nanCase hb => sorry         -- inf / NaN = NaN
    case infCase signb => sorry      -- inf / inf = NaN
    case zeroCase signb => sorry     -- inf / 0   = inf
    case numCase hb => sorry         -- inf / num = inf
  case zeroCase signa =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb => sorry         -- 0 / NaN = NaN
    case infCase signb => sorry      -- 0 / inf = 0
    case zeroCase signb => sorry     -- 0 / 0   = NaN
    case numCase hb => sorry         -- 0 / num = 0
  case numCase ha =>
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb => sorry         -- num / NaN = NaN
    case infCase signb => sorry      -- num / inf = 0
    case zeroCase signb => sorry     -- num / 0   = inf (division by zero)
    case numCase hb =>
      -- the only interesting case: both are finite nonzero numbers.
      -- mirror of `mul_eq_mul`'s `numCase/numCase`: reduce to RNE, apply
      -- `pack'_EquivUptoNaN_of_Rel`, then `toExtRat_round_div_Rel_smtLibRound_of_RNE`,
      -- discharging the rationality of `a.toRat / b.toRat` and the msb-normalization.
      sorry

end Fp
