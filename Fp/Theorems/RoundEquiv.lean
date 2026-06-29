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
theorem PackedFloat.toRatSig_lt_two {e s} (pf : PackedFloat e s) : pf.toRatSig < 2 := by
  by_cases h : pf.isNorm
  · exact PackedFloat.toRatSig_lt_two_of_not_isNorm pf h
  · have := PackedFloat.toRatSig_lt_one_of_not_isNorm pf h; grind

theorem PackedFloat.abs_toRat_eq {e s} (pf : PackedFloat e s) :
    (pf.toRat).abs = pf.toRatSig * 2 ^ pf.toRatExp := by
  have hsig0 := PackedFloat.zero_le_toRatSig pf
  have hpos : (0:Rat) < 2 ^ pf.toRatExp := Rat.two_pow_pos _
  have hnn : 0 ≤ pf.toRatSig * 2 ^ pf.toRatExp := Rat.mul_nonneg hsig0 (Rat.le_of_lt hpos)
  rw [PackedFloat.toRat, Rat.abs_mul_pos hpos]
  congr 1
  have hts : (pf.sign.toSign : Rat) = 1 ∨ (pf.sign.toSign : Rat) = -1 := by
    cases pf.sign <;> simp [Bool.toSign]
  rcases hts with h | h <;> rw [h]
  · rw [Rat.one_mul]; unfold Rat.abs; rw [if_neg (by grind)]
  · rw [show (-1:Rat) * pf.toRatSig = -(pf.toRatSig) by grind, Rat.abs_neg_eq]
    unfold Rat.abs; rw [if_neg (by grind)]

theorem PackedFloat.abs_toRat_lt {e s} (pf : PackedFloat e s) :
    (pf.toRat).abs < 2 ^ (pf.toRatExp + 1) := by
  have hpos : (0:Rat) < 2 ^ pf.toRatExp := Rat.two_pow_pos _
  rw [PackedFloat.abs_toRat_eq]
  have h1 := (Rat.mul_lt_mul_cancel_right_of_lt hpos).mpr (PackedFloat.toRatSig_lt_two pf)
  have h2 : (2:Rat) * 2 ^ pf.toRatExp = 2 ^ (pf.toRatExp + 1) := by
    rw [Rat.zpow_add (by grind)]; grind
  grind

-- F1: pf.toRat is an integer multiple of 2^(toRatExp - s)
theorem PackedFloat.toRat_eq_int_mul {e s} (pf : PackedFloat e s) :
    ∃ M : Int, pf.toRat = (M : Rat) * 2 ^ (pf.toRatExp - (s:Int)) := by
  have hexp : (2:Rat) ^ pf.toRatExp = 2 ^ (pf.toRatExp - (s:Int)) * (2:Rat) ^ s := by
    rw [← Rat.zpow_natCast 2 s, Rat.zpow_mul_zpow (by grind)]
    congr 1; grind
  have hv : (2:Rat) ^ s ≠ 0 := Rat.two_pow_nat_ne_zero
  by_cases hn : pf.isNorm
  · refine ⟨pf.sign.toSign * (2 ^ s + pf.sig.toNat), ?_⟩
    rw [PackedFloat.toRat, PackedFloat.toRatSig_eq_of_isNorm hn, hexp]
    push_cast
    generalize (2:Rat) ^ (pf.toRatExp - (s:Int)) = w
    generalize (2:Rat) ^ s = v at hv ⊢
    grind
  · refine ⟨pf.sign.toSign * pf.sig.toNat, ?_⟩
    rw [PackedFloat.toRat, PackedFloat.toRatSig_eq_of_not_isNorm hn, hexp]
    push_cast
    generalize (2:Rat) ^ (pf.toRatExp - (s:Int)) = w
    generalize (2:Rat) ^ s = v at hv ⊢
    grind


theorem two_zpow_eq_natCast {e2 : Int} (h0 : 0 ≤ e2) :
    (2:Rat) ^ e2 = ((2 ^ e2.toNat : Nat) : Rat) := by
  rw [show e2 = (e2.toNat : Int) by grind, Rat.zpow_natCast]; push_cast; grind

theorem one_le_abs_intCast (z : Int) (hz : z ≠ 0) : (1:Rat) ≤ (z:Rat).abs := by
  rcases (by grind : 0 < z ∨ z < 0) with h | h
  · have hr : (1:Rat) ≤ (z:Rat) := by exact_mod_cast (by grind : (1:Int) ≤ z)
    unfold Rat.abs; rw [if_neg (by grind)]; exact hr
  · have hr : (1:Rat) ≤ ((-z : Int):Rat) := by exact_mod_cast (by grind : (1:Int) ≤ -z)
    have he : ((-z:Int):Rat) = -(z:Rat) := by push_cast; grind
    rw [he] at hr
    unfold Rat.abs; rw [if_pos (by grind)]; exact hr

theorem abs_intCast_eq (z : Int) : (z:Rat).abs = (z.natAbs : Rat) := by
  rcases (by grind : 0 ≤ z ∨ z < 0) with h | h
  · have h0 : (0:Rat) ≤ (z:Rat) := by exact_mod_cast h
    have hz : (z:Rat) = (z.natAbs : Rat) := by exact_mod_cast (Int.natAbs_of_nonneg h).symm
    unfold Rat.abs; rw [if_neg (by grind), hz]
  · have h0 : (z:Rat) < 0 := by exact_mod_cast h
    have hz : -(z:Rat) = (z.natAbs : Rat) := by
      have h2 := Int.ofNat_natAbs_of_nonpos (by grind : z ≤ 0)
      have : ((z.natAbs:Int):Rat) = ((-z:Int):Rat) := by exact_mod_cast h2
      push_cast at this; grind
    unfold Rat.abs; rw [if_pos (by grind)]; rw [← hz]

theorem PackedFloat.core_bound {ep s' : Nat} (k n : Int) (q : Rat)
    (hn : ¬ 2 ∣ n) (hq : q = (n : Rat) * 2 ^ k) (hmag : 2 ^ (k + (s':Int) + 1) ≤ q.abs)
    (pf : PackedFloat ep s') :
    2 ^ k ≤ (q - pf.toRat).abs := by
  obtain ⟨M, hM⟩ := PackedFloat.toRat_eq_int_mul pf
  have hpk : (0:Rat) < 2 ^ k := Rat.two_pow_pos _
  have hub := PackedFloat.abs_toRat_lt pf
  have hfac : q - pf.toRat
      = ((n : Rat) - (M : Rat) * 2 ^ (pf.toRatExp - (s':Int) - k)) * 2 ^ k := by
    rw [hq, hM, show pf.toRatExp - (s':Int) = (pf.toRatExp - (s':Int) - k) + k by grind,
      Rat.zpow_add (by grind)]
    grind
  rw [hfac, Rat.abs_mul_pos hpk]
  suffices h : (1:Rat) ≤ ((n : Rat) - (M : Rat) * 2 ^ (pf.toRatExp - (s':Int) - k)).abs by
    have := (Rat.mul_le_mul_cancel_right_of_lt hpk).mpr h; grind
  by_cases hcase : k + (s':Int) + 1 ≤ pf.toRatExp
  · -- Case A: M·2^(..) is an even integer ⇒ n − it is odd ⇒ |·| ≥ 1
    have he2 : 0 ≤ pf.toRatExp - (s':Int) - k := by grind
    have he2' : 1 ≤ (pf.toRatExp - (s':Int) - k).toNat := by grind
    rw [two_zpow_eq_natCast he2]
    have hcast : (n : Rat) - (M : Rat) * ((2 ^ (pf.toRatExp - (s':Int) - k).toNat : Nat) : Rat)
        = ((n - M * 2 ^ (pf.toRatExp - (s':Int) - k).toNat : Int) : Rat) := by push_cast; grind
    rw [hcast]
    apply one_le_abs_intCast
    have h2 : (2:Int) ∣ 2 ^ (pf.toRatExp - (s':Int) - k).toNat := by
      rw [show (pf.toRatExp - (s':Int) - k).toNat = ((pf.toRatExp - (s':Int) - k).toNat - 1) + 1
        by grind, Int.pow_succ]; grind
    have h3 : (2:Int) ∣ M * 2 ^ (pf.toRatExp - (s':Int) - k).toNat := by
      obtain ⟨w, hw⟩ := h2; exact ⟨M * w, by rw [hw]; grind⟩
    grind
  · -- Case B: |M| < 2^(s'+1) ≤ |n|, M and n integers ⇒ |M| ≤ |n| - 1 ⇒ |n − M·2^(≤0)| ≥ 1
    have hpfabs : (pf.toRat).abs = (M:Rat).abs * 2 ^ (pf.toRatExp - (s':Int)) := by
      rw [hM]; exact Rat.abs_mul_pos (Rat.two_pow_pos _)
    have hMlt : (M:Rat).abs < 2 ^ ((s':Int)+1) := by
      rw [hpfabs] at hub
      have hrw : (2:Rat) ^ (pf.toRatExp + 1) = 2 ^ ((s':Int)+1) * 2 ^ (pf.toRatExp - (s':Int)) := by
        rw [Rat.zpow_mul_zpow (by grind)]; congr 1; grind
      rw [hrw] at hub
      exact (Rat.mul_lt_mul_cancel_right_of_lt (Rat.two_pow_pos _)).mp hub
    have hqabs : q.abs = (n:Rat).abs * 2 ^ k := by rw [hq]; exact Rat.abs_mul_pos hpk
    have hnge : (2:Rat) ^ ((s':Int)+1) ≤ (n:Rat).abs := by
      rw [hqabs] at hmag
      have hrw : (2:Rat) ^ (k + (s':Int) + 1) = 2 ^ ((s':Int)+1) * 2 ^ k := by
        rw [Rat.zpow_mul_zpow (by grind)]; congr 1; grind
      rw [hrw] at hmag
      exact (Rat.mul_le_mul_cancel_right_of_lt hpk).mp hmag
    -- integer gap: M.natAbs < n.natAbs
    have hcnat : (2:Rat) ^ ((s':Int)+1) = ((2 ^ (s'+1) : Nat) : Rat) := by
      rw [show ((s':Int)+1) = ((s'+1 : Nat):Int) by push_cast; grind, Rat.zpow_natCast]
      push_cast; grind
    have hMn : M.natAbs < 2 ^ (s'+1) := by
      rw [abs_intCast_eq, hcnat] at hMlt; exact_mod_cast hMlt
    have hnn : 2 ^ (s'+1) ≤ n.natAbs := by
      rw [abs_intCast_eq, hcnat] at hnge; exact_mod_cast hnge
    have hgap : M.natAbs + 1 ≤ n.natAbs := by grind
    have hMle : (M:Rat).abs + 1 ≤ (n:Rat).abs := by
      rw [abs_intCast_eq, abs_intCast_eq]
      have : ((M.natAbs + 1 : Nat) : Rat) ≤ ((n.natAbs : Nat) : Rat) := by exact_mod_cast hgap
      push_cast at this; grind
    -- |M·2^E'| ≤ |M|  (E' ≤ 0)
    have hE'le : (2:Rat) ^ (pf.toRatExp - (s':Int) - k) ≤ 1 := by
      have h1 : (2:Rat) ^ (pf.toRatExp - (s':Int) - k) ≤ 2 ^ (0:Int) :=
        Rat.two_pow_le_two_pow_of_le (by grind)
      grind
    have hMnn : 0 ≤ (M:Rat).abs := by rw [abs_intCast_eq]; exact_mod_cast Nat.zero_le _
    have htle : ((M:Rat) * 2 ^ (pf.toRatExp - (s':Int) - k)).abs ≤ (M:Rat).abs := by
      rw [Rat.abs_mul_pos (Rat.two_pow_pos _)]
      have := Rat.mul_le_mul_of_nonneg_left hE'le hMnn; grind
    -- reverse triangle
    have htri : (n:Rat).abs - ((M:Rat) * 2 ^ (pf.toRatExp - (s':Int) - k)).abs
        ≤ ((n:Rat) - (M:Rat) * 2 ^ (pf.toRatExp - (s':Int) - k)).abs := by
      unfold Rat.abs; split <;> split <;> split <;> grind
    grind


theorem Number_le_Number {a b : Rat} : (ExtRat.Number a ≤ ExtRat.Number b) ↔ a ≤ b := by
  rw [← ExtRat.le_def]; simp [ExtRat.le]

theorem side_iff_of_bounds (k : Int) (q r v : Rat)
    (hv : 2 ^ k ≤ (q - v).abs) (hrq : (r - q).abs < 2 ^ k) :
    (v ≤ q ↔ v ≤ r) ∧ (q ≤ v ↔ r ≤ v) := by
  have hpos : (0:Rat) < 2 ^ k := Rat.two_pow_pos _
  unfold Rat.abs at hv hrq
  split at hv <;> split at hrq <;> constructor <;> constructor <;> intro h <;> grind

theorem PackedFloat.sameSide_of_core {ep s' : Nat} (he : 0 < ep) (hs : 0 < s')
    (k n : Int) (q r : Rat)
    (hn : ¬ 2 ∣ n) (hq : q = (n : Rat) * 2 ^ k)
    (hmag : 2 ^ (k + (s':Int) + 1) ≤ q.abs) (hrq : (r - q).abs < 2 ^ k) :
    SameSideOfPacked ep s' q r := by
  intro pf
  rw [PackedFloat.toExtRat_eq_toExtRat']
  cases pf using PackedFloat.kindCasesNaNInfZeroNum with
  | nanCase pf hpf =>
    rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN pf hpf]
    simp only [ExtRat.le_NaN, ExtRat.NaN_le]
    grind
  | infCase sign =>
    rw [PackedFloat.toExtRat'_getInfinity hs]
    cases sign
    · simp only [ExtRat.plus_inf_le_iff_eq, ExtRat.number_le_plus_inf]; grind
    · simp only [ExtRat.le_neg_inf_iff_eq, ExtRat.neg_inf_le_number]; grind
  | zeroCase sign =>
    rw [PackedFloat.toExtRat'_getZero sign he]
    simp only [Number_le_Number]
    have hv : 2 ^ k ≤ (q - 0).abs := by
      have hle : (2:Rat) ^ k ≤ 2 ^ (k + (s':Int) + 1) := Rat.two_pow_le_two_pow_of_le (by grind)
      grind
    exact side_iff_of_bounds k q r 0 hv hrq
  | numCase pf hpf =>
    rw [PackedFloat.toExtRat'_eq_toRat_of hpf]
    simp only [Number_le_Number]
    have hv := PackedFloat.core_bound k n q hn hq hmag pf
    exact side_iff_of_bounds k q r pf.toRat hv hrq

theorem roundEquiv_of_stickyEquiv {ep sp eu su : Nat}
    (he : 1 < ep) (hs : 0 < sp) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su) (hmsb : x.sig.msb = true)
    {r : Rat} (hr : StickyEquiv x.toExpInt x.toRat r) :
    RoundEquiv ep sp x.toRat r := by
  rcases hr with heq | ⟨n, hodd, hqn, hrq⟩
  · rw [heq]; exact RoundEquiv.refl r
  · -- magnitude |x.toRat| ≥ 2^(toExpInt + su - 1)
    have habs : (x.toRat).abs = (x.sig.toNat : Rat) * 2 ^ x.toExpInt := by
      rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.abs_toRat'_eq]
    have hsiglo : (2:Rat) ^ (su - 1) ≤ (x.sig.toNat : Rat) := by
      have h := hmsb; rw [BitVec.msb_eq_decide] at h
      have hnat : 2 ^ (su - 1) ≤ x.sig.toNat := by simpa using h
      exact_mod_cast hnat
    have hpk : (0:Rat) < 2 ^ x.toExpInt := Rat.two_pow_pos _
    have hmag0 : (2:Rat) ^ (x.toExpInt + (su:Int) - 1) ≤ (x.toRat).abs := by
      rw [habs]
      have hrw : (2:Rat) ^ (x.toExpInt + (su:Int) - 1) = 2 ^ (su - 1) * 2 ^ x.toExpInt := by
        rw [← Rat.zpow_natCast 2 (su-1), Rat.zpow_mul_zpow (by grind)]
        congr 1; rw [show ((su-1:Nat):Int) = (su:Int) - 1 by
          rw [Int.natCast_sub (by grind)]; push_cast; grind]
        grind
      rw [hrw]
      exact Rat.mul_le_mul_of_nonneg_right hsiglo (Rat.le_of_lt hpk)
    have hsig1 : (1:Rat) < (x.sig.toNat : Rat) := by
      have h := hmsb; rw [BitVec.msb_eq_decide] at h
      have hnat : 2 ^ (su - 1) ≤ x.sig.toNat := by simpa using h
      have h2n : 2 ≤ 2 ^ (su - 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (su - 1) := Nat.pow_le_pow_right (by grind) (by grind)
      have : 1 < x.sig.toNat := by grind
      exact_mod_cast this
    have hqabs : (2:Rat) ^ x.toExpInt < (x.toRat).abs := by
      rw [habs]
      have h1 : (1:Rat) * 2 ^ x.toExpInt < (x.sig.toNat:Rat) * 2 ^ x.toExpInt :=
        (Rat.mul_lt_mul_cancel_right_of_lt hpk).mpr hsig1
      grind
    have hrqq : (r - x.toRat).abs < (x.toRat).abs := by grind
    have hmagS : ∀ s' : Nat, s' + 1 ≤ su - 1 → (2:Rat) ^ (x.toExpInt + (s':Int) + 1) ≤ (x.toRat).abs := by
      intro s' hs'
      have : (2:Rat) ^ (x.toExpInt + (s':Int) + 1) ≤ 2 ^ (x.toExpInt + (su:Int) - 1) :=
        Rat.two_pow_le_two_pow_of_le (by grind)
      grind
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold Rat.abs at hrqq; split at hrqq <;> grind
    · unfold Rat.abs at hrqq; split at hrqq <;> grind
    · unfold Rat.abs at hrqq; split at hrqq <;> grind
    · exact PackedFloat.sameSide_of_core (by grind) hs x.toExpInt n x.toRat r hodd hqn
        (hmagS sp (by grind)) hrq
    · exact PackedFloat.sameSide_of_core (by grind) (by grind) x.toExpInt n x.toRat r hodd hqn
        (hmagS (sp+1) (by grind)) hrq

/-- info: 'Fp.roundEquiv_of_stickyEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundEquiv_of_stickyEquiv

end Fp
