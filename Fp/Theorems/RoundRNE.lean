import Fp.Theorems.RoundEquiv

/-!
# RNE (round nearest, ties to even) rounding: the sticky-compression bridge

This file holds the `stickyEquiv` generalizations of the RNE exact-value bridge,
moved here from `Fp/Theorems/Addition.lean` so that every rounding mode has one
top-layer bridge file (`RoundRNE`, `RoundRNA`, `RoundRTN`, `RoundRTP`, `RoundRTZ`).

The RNE *exact-value* bridges themselves — `toExtRat_round_Rel_smtLibRound_of_RNE`
and `blastSmtLibRound_finite_of_RNE` — remain in
`Fp/Theorems/UnpackedFloat/Round/RNE.lean` (the `UnpackedFloat.Round` aggregator
layer), because they are reused by `Multiplication`.  Only the sticky wrappers,
which depend on the mode-generic `RoundEquiv` machinery, live here.
-/

namespace Fp

/--
The bit-blasted rounder applied to the circuit result agrees with the
SMT-LIB rounder applied to the *exact* value, provided the circuit result is
a sticky compression of the exact value.  This generalizes
`UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE` (which requires
`r = x.toRat` on the nose, as is the case for multiplication).
-/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RNE : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE sign (ExtRat.Number r)) := by
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RNE x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RNE sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE he hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm

/--
**Finiteness companion of `blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`.**

When the circuit is a finite `Number`, the SMT-LIB round of the exact value `r`
is neither NaN nor infinite.  Since the rounder cannot distinguish `r` from the
circuit's sticky-compressed value `x.toRat` (`roundEquiv_of_stickyEquiv`), the
round of `r` equals the round of `x.toRat`, so this reduces to the exact-value
finiteness lemma `blastSmtLibRound_finite_of_RNE`.
-/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RNE_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RNE : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RNE x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RNE sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.blastSmtLibRound_finite_of_RNE he hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm hmsb hstate

end Fp
