import Fp.UnpackedRoundNaive
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing

/-!
## Bridge Theorems: Naive Rounding ↔ SMT-LIB Semantics

Sorry'd theorems connecting each named component of `UnpackedFloat.roundNaive`
to its corresponding SMT-LIB `RoundMethod` concept.

The proof strategy is:
1. Each component theorem bridges one bitvector computation to one SMT-LIB concept.
2. The main theorem `roundNaive_pack_eq_smtLibRound` composes them all.
-/

namespace Fp
namespace UnpackedRoundNaive

open SmtLibSemantics SmtLibSemanticsQ

/-! ### Component-level bridge theorems

Each theorem connects a bitvector computation from `RoundingContext` to the
corresponding SMT-LIB definition, under suitable preconditions.
-/

set_option warn.sorry false

/-- The bitvector `computeLowerHalf` agrees with `smtLibRoundMethodQ.lowerHalf`.

When the guard bit is 0, the lower bound at precision `s` equals the lower bound
at precision `s+1`, so `lowerHalf` holds. When the guard bit is 1, they differ. -/
theorem computeLowerHalf_eq_smtLibLowerHalf
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf) :
    computeLowerHalf ctx =
    decide ((smtLibRoundMethodQ eout sout).lowerHalf
      (ExtRat.Number ctx.inUf.toRat)) := by
  sorry

/-- The bitvector `computeTieBreak` agrees with `smtLibRoundMethodQ.tieBreak`.

The tie-break holds exactly when guard = 1 and sticky = 0, meaning the
rational value is exactly at the midpoint between `lower` and `upper`. -/
theorem computeTieBreak_eq_smtLibTieBreak
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf) :
    computeTieBreak ctx =
    decide ((smtLibRoundMethodQ eout sout).tieBreak
      (ExtRat.Number ctx.inUf.toRat)) := by
  sorry

/-- The bitvector `computeIsEven` agrees with `roundableIsEven_of_packedFloat`
applied to the lower representable value.

The LSB of the truncated significand is checked by masking with `lsbMask`,
which corresponds to checking the last bit of `lower.sig` after packing. -/
theorem computeIsEven_eq_smtLibIsEven
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf) :
    computeIsEven ctx =
    roundableIsEven_of_packedFloat.isEven
      (SmtLibSemantics.smtLibLower.lower
        (ExtRat.Number ctx.inUf.toRat) : PackedFloat eout sout) := by
  sorry

/-- The bitvector rounding decision (`roundingDecision`) agrees with the
SMT-LIB mode-by-mode case analysis.

This theorem says: given that lowerHalf, tieBreak, and isEven all match their
SMT-LIB counterparts, the rounding decision (round up or not) agrees with
the SMT-LIB definition that picks between `lower` and `upper`. -/
theorem roundingDecision_eq_smtLib_choice
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf)
    (mode : RoundingMode)
    (sign : Bool)
    (hNotNaN : ¬ (instExtendedRat.isNaN (ExtRat.Number ctx.inUf.toRat)))
    (hNotZero : ¬ (instExtendedRat.isZero (ExtRat.Number ctx.inUf.toRat))) :
    let shouldRoundUp := roundingDecision
      (mode := mode) (sign := ctx.inUf.sign)
      (significandEven := computeIsEven ctx)
      (guardBit := computeGuardBit ctx)
      (stickyBit := computeStickyBit ctx)
      (_exact := false)
    -- When shouldRoundUp = true, SMT-LIB picks `upper`; when false, SMT-LIB picks `lower`.
    (if shouldRoundUp
     then SmtLibSemantics.smtLibUpper.upper (ExtRat.Number ctx.inUf.toRat)
     else SmtLibSemantics.smtLibLower.lower (ExtRat.Number ctx.inUf.toRat)
     : PackedFloat eout sout) =
    (smtLibRoundMethodQ eout sout).round mode sign (ExtRat.Number ctx.inUf.toRat) := by
  sorry

/-! ### Main bridge theorem

Composes all component theorems to show that `roundNaive` (= `round`)
agrees with the SMT-LIB specification after packing.
-/

/-- The main equivalence: packing the result of `roundNaive` gives the same
`PackedFloat` as the SMT-LIB round method.

This bridges the bitvector circuit (`UnpackedFloat.round`) to the
mathematical specification (`smtLibRoundMethodQ.round`). -/
theorem roundNaive_pack_eq_smtLibRound
    {expWidth sigWidth eout sout : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : inUf.sig.msb = true)
    (rm : RoundingMode) (sign : Bool) :
    (UnpackedFloat.roundNaive
      (targetExponentWidth := eout) (targetSignificandWidth := sout)
      inUf rm).pack =
    (smtLibRoundMethodQ eout sout).round rm sign
      (ExtRat.Number inUf.toRat) := by
  sorry

/-- Corollary: since `roundNaive = round`, we get the bridge for the original circuit. -/
theorem round_pack_eq_smtLibRound
    {expWidth sigWidth eout sout : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : inUf.sig.msb = true)
    (rm : RoundingMode) (sign : Bool) :
    (UnpackedFloat.round
      (targetExponentWidth := eout) (targetSignificandWidth := sout)
      inUf rm).pack =
    (smtLibRoundMethodQ eout sout).round rm sign
      (ExtRat.Number inUf.toRat) := by
  rw [← roundNaive_eq_round]
  exact roundNaive_pack_eq_smtLibRound inUf hprec hnorm rm sign

end UnpackedRoundNaive
end Fp
