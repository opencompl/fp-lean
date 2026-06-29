import Fp.Theorems.StickyEquiv
import Fp.Theorems.Multiplication

/-!
# `RoundEquiv` — sticky compressions are invisible to rounding

The SMT-LIB rounder only consults a value’s sign, its zero-test, and its position
relative to the representable values of the target format `(e, s)` and the half-ulp
format `(e, s+1)`. `RoundEquiv`/`SameSideOfPacked` capture exactly this observable
data, and `roundEquiv_of_stickyEquiv` shows a sticky compression preserves it.
-/

namespace Fp

open SmtLibSemantics

/-! ## Layer 2a: the SMT-LIB rounder only sees "sides" of representables -/

/--
`q` and `r` lie on the same (weak) side of every representable value of the
format `(e, s)`.  Since `smtLibLower`/`smtLibUpper` are characterized by
lawfulness conditions stated purely in terms of `embed pf ≤ ·` and
`· ≤ embed pf`, two rationals that are `SameSideOfPacked` (for the format
and its extended-by-one-bit sibling) have identical lower/upper/lowerHalf/
tieBreak data and hence round identically.
-/
def SameSideOfPacked (e s : Nat) (q r : Rat) : Prop :=
  ∀ pf : PackedFloat e s,
    ((pf.toExtRat ≤ ExtRat.Number q) ↔ (pf.toExtRat ≤ ExtRat.Number r)) ∧
    ((ExtRat.Number q ≤ pf.toExtRat) ↔ (ExtRat.Number r ≤ pf.toExtRat))

/--
Everything the SMT-LIB rounding function can observe about a (nonzero)
rational: its sign, and its position relative to the representable values of
the target format `(e, s)` and of the half-ulp format `(e, s+1)` (the latter
determines the `lowerHalf` and `tieBreak` predicates).
-/
structure RoundEquiv (e s : Nat) (q r : Rat) : Prop where
  zero_iff : q = 0 ↔ r = 0
  pos_iff : 0 < q ↔ 0 < r
  neg_iff : q < 0 ↔ r < 0
  side : SameSideOfPacked e s q r
  sideS : SameSideOfPacked e (s + 1) q r

theorem RoundEquiv.refl {e s : Nat} (q : Rat) : RoundEquiv e s q q :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun _ => ⟨Iff.rfl, Iff.rfl⟩, fun _ => ⟨Iff.rfl, Iff.rfl⟩⟩

/-- `smtLibLower` is determined by the `SameSideOfPacked` data. -/
theorem smtLibLower_lower_congr {e s : Nat} {q r : Rat}
    (h : SameSideOfPacked e s q r) :
    (SmtLibSemantics.smtLibLower (X := PackedFloat e s) (R := ExtRat)).lower (ExtRat.Number q) =
    (SmtLibSemantics.smtLibLower (X := PackedFloat e s) (R := ExtRat)).lower (ExtRat.Number r) := by
  simp only [SmtLibSemantics.smtLibLower]
  congr 1
  funext pf
  apply propext
  simp only [SmtLibSemantics.IsLawfulLower, SmtLibSemantics.smtLibV_embed_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(h pf).1.mp h1, fun x' hx' => h2 x' ((h x').1.mpr hx')⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(h pf).1.mpr h1, fun x' hx' => h2 x' ((h x').1.mp hx')⟩

/-- `smtLibUpper` is determined by the `SameSideOfPacked` data. -/
theorem smtLibUpper_upper_congr {e s : Nat} {q r : Rat}
    (h : SameSideOfPacked e s q r) :
    (SmtLibSemantics.smtLibUpper (X := PackedFloat e s) (R := ExtRat)).upper (ExtRat.Number q) =
    (SmtLibSemantics.smtLibUpper (X := PackedFloat e s) (R := ExtRat)).upper (ExtRat.Number r) := by
  simp only [SmtLibSemantics.smtLibUpper]
  congr 1
  funext pf
  apply propext
  simp only [SmtLibSemantics.IsLawfulUpper, SmtLibSemantics.smtLibV_embed_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(h pf).2.mp h1, fun x' hx' => h2 x' ((h x').2.mpr hx')⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(h pf).2.mpr h1, fun x' hx' => h2 x' ((h x').2.mp hx')⟩

/--
The SMT-LIB rounding function cannot distinguish `RoundEquiv`-related
nonzero rationals: it only consults `lower`/`upper` (at widths `s` and
`s+1`), the zero test and the sign tests, all of which agree.
-/
theorem round_congr_of_RoundEquiv {e s : Nat} {q r : Rat}
    (rm : RoundingMode) (sign : Bool)
    (h : RoundEquiv e s q r) (hq : q ≠ 0) :
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
      rm sign (ExtRat.Number q) =
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
      rm sign (ExtRat.Number r) := by
  have hr : r ≠ 0 := by grind [RoundEquiv]
  have hlow : (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower (ExtRat.Number q) =
      (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower (ExtRat.Number r) := by
    simp only [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
    exact smtLibLower_lower_congr h.side
  have hupp : (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper (ExtRat.Number q) =
      (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper (ExtRat.Number r) := by
    simp only [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq]
    exact smtLibUpper_upper_congr h.side
  have hlowS : (SmtLibSemantics.smtLibLower (X := PackedFloat e (s+1)) (R := ExtRat)).lower (ExtRat.Number q) =
      SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) :=
    smtLibLower_lower_congr h.sideS
  have huppS : (SmtLibSemantics.smtLibUpper (X := PackedFloat e (s+1)) (R := ExtRat)).upper (ExtRat.Number q) =
      SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) :=
    smtLibUpper_upper_congr h.sideS
  have hlh : (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number q) ↔
      (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) := by
    rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_embed_eq]
    rw [smtLibLower_lower_congr h.side, hlowS]
  have htb : (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number q) ↔
      (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) := by
    rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
    simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_upper_eq,
      SmtLibSemantics.smtLibV_embed_eq]
    rw [smtLibLower_lower_congr h.side, smtLibUpper_upper_congr h.side, hlowS, huppS]
  rcases rm
  case RNE =>
    simp only [SmtLibSemantics.RoundMethod.round_RNE_eq, SmtLibSemantics.RoundMethod.roundRNE]
    simp [hq, hr, hlow, hupp, hlh, htb]
  case RNA =>
    simp only [SmtLibSemantics.RoundMethod.round_RNA_eq, SmtLibSemantics.RoundMethod.roundRNA]
    simp [hq, hr, hlow, hupp, hlh, htb, h.pos_iff, h.neg_iff]
  case RTP =>
    simp only [SmtLibSemantics.RoundMethod.round_RTP_eq, SmtLibSemantics.RoundMethod.roundRTP]
    simp [hq, hr, hlow, hupp]
  case RTN =>
    simp only [SmtLibSemantics.RoundMethod.round_RTN_eq, SmtLibSemantics.RoundMethod.roundRTN]
    simp [hq, hr, hlow, hupp]
  case RTZ =>
    simp only [SmtLibSemantics.RoundMethod.round_RTZ_eq, SmtLibSemantics.RoundMethod.roundRTZ]
    simp [hq, hr, hlow, hupp, h.pos_iff, h.neg_iff]

/--
The `sign` argument of the SMT-LIB rounder is only consulted when the value
being rounded is zero; for nonzero values it is irrelevant.  (For addition,
the spec's zero-sign `addSign rm a b` differs from the circuit's sign
bookkeeping, but only the `r = 0` case can see this.)
-/
theorem round_eq_round_of_ne_zero {e s : Nat}
    (rm : RoundingMode) (sign sign' : Bool) (r : Rat) (hr : r ≠ 0) :
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
      rm sign (ExtRat.Number r) =
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
      rm sign' (ExtRat.Number r) := by
  rcases rm <;>
    simp [SmtLibSemantics.RoundMethod.roundRNE, SmtLibSemantics.RoundMethod.roundRNA,
      SmtLibSemantics.RoundMethod.roundRTP, SmtLibSemantics.RoundMethod.roundRTN,
      SmtLibSemantics.RoundMethod.roundRTZ, hr]

/-! ## Layer 2b: sticky compressions are invisible to rounding -/

/--
**A sticky compression is invisible to rounding.**

If `x` is a normalized (`msb = true`) unpacked float of significand width
`su ≥ sp + 3` and `r` is any rational with `StickyEquiv x.toExpInt x.toRat r`,
then `x.toRat` and `r` round identically in the target format `(ep, sp)`.

Pen-and-paper proof.  Write `q = x.toRat`, `k = x.toExpInt`.  If `q = r` the
claim is trivial; otherwise `q = n·2^k` with `n` odd and `0 < |r - q| < 2^k`.
Since `x.sig.msb = true` and `su ≥ sp + 3`, we have `|q| ≥ 2^(k + sp + 2)`,
i.e. `q` carries at least two bits *below* the ulp of the format
`(ep, sp + 1)` at `q`'s magnitude.  Every representable value `v` of
`(ep, sp + 1)` (and a fortiori of `(ep, sp)`) is:
* in `q`'s binade or above: an integer multiple of `2^(k+1)`, hence
  `|v - q| ≥ 2^k` because `q` is an odd multiple of `2^k`;
* in a binade strictly below `q`'s: then `|v| ≤ 2^E ≤ |q| - 2^k` where
  `2^E` is the bottom of `q`'s binade (using again that `q` is an odd
  multiple of `2^k`, so `|q| ≥ 2^E + 2^k`).
In both cases `v ∉ (q - 2^k, q + 2^k) \ {±...}`, i.e. no representable value
lies strictly between `q` and `r` nor equals either of them on the wrong
side; hence all predicates `v ≤ ·`, `· ≤ v` agree on `q` and `r`.  The sign
data agrees because `|q| ≥ 2^k > |r - q|` keeps `r` in `q`'s open half-line.
-/
theorem roundEquiv_of_stickyEquiv {ep sp eu su : Nat}
    (he : 1 < ep) (hs : 0 < sp) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hmsb : x.sig.msb = true)
    {r : Rat} (hr : StickyEquiv x.toExpInt x.toRat r) :
    RoundEquiv ep sp x.toRat r := by
  sorry

end Fp
