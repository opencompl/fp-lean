import Fp.Theorems.RoundRNE
import Fp.Theorems.RoundRNA
import Fp.Theorems.RoundRTN
import Fp.Theorems.RoundRTP
import Fp.Theorems.RoundRTZ

/-!
# Master rounding bridge: circuit ↔ SMT-LIB spec for ALL rounding modes

This file collects the per-mode circuit↔SMT-LIB bridge theorems into a single
statement quantified over `mode : RoundingMode`, dispatching by cases to the
mode-specific lemma.  The five per-mode exact-value bridges live in:
* `Fp/Theorems/UnpackedFloat/Round/RNE.lean` — `..._of_RNE`
* `Fp/Theorems/RoundRNA.lean`, `RoundRTN.lean`, `RoundRTP.lean`, `RoundRTZ.lean`
  — `..._of_RNA` / `_of_RTN` / `_of_RTP` / `_of_RTZ`

Four master theorems are provided, mirroring the four per-mode variants:
* `toExtRat_round_Rel_smtLibRound` — exact-value bridge (the primary result),
* `blastSmtLibRound_finite` — its finiteness companion,
* `blastSmtLibRound_Rel_round_of_stickyEquiv` — the sticky-compression bridge,
* `blastSmtLibRound_finite_of_stickyEquiv` — its finiteness companion.
-/

namespace Fp

/-- **Master exact-value rounding bridge (all modes).** For every rounding
`mode`, the bit-blasted rounder applied to a normalized `x` agrees (up to NaN,
via `Rel`) with the SMT-LIB rounder applied to the exact value `r = x.toRat`.
Dispatches to the mode-specific `toExtRat_round_Rel_smtLibRound_of_*`. -/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound
    {ep sp eu su : Nat}
    (mode : RoundingMode)
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp mode : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round mode sign (ExtRat.Number r)) := by
  cases mode with
  | RNE => exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE he hep hs heu hsu x sign hsign r hr hxnorm
  | RNA => exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNA he hep hs heu hsu x sign hsign r hr hxnorm
  | RTN => exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTN he hep hs heu hsu x sign hsign r hr hxnorm
  | RTP => exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTP he hep hs heu hsu x sign hsign r hr hxnorm
  | RTZ => exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RTZ he hep hs heu hsu x sign hsign r hr hxnorm

/-- **Master finiteness companion (all modes).** When the circuit is a finite
`Number`, the SMT-LIB round of the exact value is neither NaN nor infinite. -/
theorem UnpackedFloat.blastSmtLibRound_finite
    {ep sp eu su : Nat}
    (mode : RoundingMode)
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x)
    (hmsb : x.sig.msb = true) :
    (x.blastSmtLibRound ep sp mode : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round mode sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round mode sign (ExtRat.Number r)).isInfinite := by
  cases mode with
  | RNE => exact UnpackedFloat.blastSmtLibRound_finite_of_RNE he hep hs heu hsu x sign hsign r hr hxnorm hmsb
  | RNA => exact UnpackedFloat.blastSmtLibRound_finite_of_RNA he hep hs heu hsu x sign hsign r hr hxnorm hmsb
  | RTN => exact UnpackedFloat.blastSmtLibRound_finite_of_RTN he hep hs heu hsu x sign hsign r hr hxnorm hmsb
  | RTP => exact UnpackedFloat.blastSmtLibRound_finite_of_RTP he hep hs heu hsu x sign hsign r hr hxnorm hmsb
  | RTZ => exact UnpackedFloat.blastSmtLibRound_finite_of_RTZ he hep hs heu hsu x sign hsign r hr hxnorm hmsb

/-- **Master sticky-compression bridge (all modes).** As the exact-value bridge,
but `r` need only be a sticky compression of `x.toRat`. -/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_stickyEquiv
    {ep sp eu su : Nat}
    (mode : RoundingMode)
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp mode : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round mode sign (ExtRat.Number r)) := by
  cases mode with
  | RNE => exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RNA => exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RNA_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RTN => exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RTN_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RTP => exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RTP_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RTZ => exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RTZ_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr

/-- **Master finiteness companion of the sticky-compression bridge (all modes).** -/
theorem UnpackedFloat.blastSmtLibRound_finite_of_stickyEquiv
    {ep sp eu su : Nat}
    (mode : RoundingMode)
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp mode : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round mode sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round mode sign (ExtRat.Number r)).isInfinite := by
  cases mode with
  | RNE => exact UnpackedFloat.blastSmtLibRound_finite_of_RNE_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RNA => exact UnpackedFloat.blastSmtLibRound_finite_of_RNA_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RTN => exact UnpackedFloat.blastSmtLibRound_finite_of_RTN_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RTP => exact UnpackedFloat.blastSmtLibRound_finite_of_RTP_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr
  | RTZ => exact UnpackedFloat.blastSmtLibRound_finite_of_RTZ_of_stickyEquiv he hep hs heu hsu x sign r hrne hxnorm hr

/-- info: 'Fp.UnpackedFloat.toExtRat_round_Rel_smtLibRound' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.toExtRat_round_Rel_smtLibRound

/-- info: 'Fp.UnpackedFloat.blastSmtLibRound_finite' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnpackedFloat.blastSmtLibRound_finite

end Fp
