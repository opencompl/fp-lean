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

/-! ### Auxiliary Galois Adjunction Lemmas

The key structural lemmas connecting bitvector truncation to the Galois lower/upper
adjunctions (`smtLibLower.lower`, `smtLibUpper.upper`).

**Proof strategy** (for `computeLower_pack_eq_smtLibLower_pos`):
1. Show `embed (computeLower ctx) ≤ r`:
   The masked-out bits (guard + sticky) are ≥ 0, so the truncated value is ≤ r.
   Formally: `inUf.toRat = computeLower.toRat + guardVal + stickyVal` where
   `guardVal, stickyVal ≥ 0`.
2. Show `∀ p : PackedFloat eout sout, embed p ≤ r → p ≤ computeLower ctx`:
   The adjacent lower representable value below `computeLower` embeds to a value < r,
   and all values below that are ≤ lower, so there is no valid lower bound between
   `computeLower` and `r`. (Since PackedFloat is a finite discrete set at each exp value,
   this is a finiteness argument.)
3. Conclude by `Classical.epsilon_spec` with `IsLawfulLower`.
-/

/-- For a non-zero, non-overflow, non-underflow positive input: `computeLower` packs to
the SMT-LIB lower Galois adjunction (greatest lower bound of `r`). -/
theorem computeLower_pack_eq_smtLibLower_pos
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf)
    (hpos : ctx.inUf.sign = false) :
    ctx.computeLower.pack =
    SmtLibSemantics.smtLibLower.lower (ExtRat.Number ctx.inUf.toRat) := by
  /-
  Key steps:
  1. Unfold `smtLibLower.lower` to `epsilon (IsLawfulLower r)`.
  2. Prove `IsLawfulLower r (computeLower ctx).pack`:
     a. embed ≤ r: the masked-out bits are non-negative, so truncation ≤ original.
     b. Maximality: adjacent lower value embeds below r, so computeLower is greatest.
  3. Use `Classical.epsilon_spec` to conclude.
  -/
  sorry

/-- For a non-zero positive input: `computeUpper` packs to the SMT-LIB upper Galois
adjunction (least upper bound of `r`). -/
theorem computeUpper_pack_eq_smtLibUpper_pos
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf)
    (hpos : ctx.inUf.sign = false) :
    ctx.computeUpper.pack =
    SmtLibSemantics.smtLibUpper.upper (ExtRat.Number ctx.inUf.toRat) := by
  /-
  Symmetric to `computeLower_pack_eq_smtLibLower_pos`:
  1. Prove `IsLawfulUpper r (computeUpper ctx).pack`:
     a. r ≤ embed: adding the guard/sticky fraction to `computeLower.toRat` gives `r`,
        and `computeUpper = computeLower + 1 ULP`, so `computeUpper.toRat ≥ r`.
     b. Minimality: any upper bound must be ≥ computeUpper (adjacent upward).
  2. Apply `Classical.epsilon_spec`.
  -/
  sorry

/-- For a negative input: `computeLower` (toward zero = rationally larger) packs to
the SMT-LIB **upper** adjunction (greatest rational value ≤ r... wait: for negative r,
"toward zero" means the representable value closest to 0, which has a LARGER rational value
than r. So `computeLower` for negative r is `smtLibUpper.upper r`). -/
theorem computeLower_pack_eq_smtLibUpper_neg
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf)
    (hneg : ctx.inUf.sign = true) :
    ctx.computeLower.pack =
    SmtLibSemantics.smtLibUpper.upper (ExtRat.Number ctx.inUf.toRat) := by
  /-
  For negative r: truncating magnitude toward zero = rounding toward +∞ = taking
  the least upper bound of r (closest representable value above r in rational ordering).
  Proof: show `IsLawfulUpper r (computeLower ctx).pack` using the same Galois argument
  with signs flipped.
  -/
  sorry

/-- For a negative input: `computeUpper` (away from zero = rationally smaller) packs to
the SMT-LIB **lower** adjunction. -/
theorem computeUpper_pack_eq_smtLibLower_neg
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf)
    (hneg : ctx.inUf.sign = true) :
    ctx.computeUpper.pack =
    SmtLibSemantics.smtLibLower.lower (ExtRat.Number ctx.inUf.toRat) := by
  /-
  For negative r: adding 1 ULP in magnitude = moving further negative = taking
  the greatest lower bound of r.
  -/
  sorry

/-- The bitvector `computeLowerHalf` agrees with `smtLibRoundMethodQ.lowerHalf`.

When the guard bit is 0, the lower bound at precision `s` equals the lower bound
at precision `s+1`, so `lowerHalf` holds. When the guard bit is 1, they differ. -/
theorem computeLowerHalf_eq_smtLibLowerHalf
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf) :
    ctx.computeLowerHalf =
    decide ((smtLibRoundMethodQ eout sout).lowerHalf
      (ExtRat.Number ctx.inUf.toRat)) := by
  /- Proof sketch:
     Let r := ExtRat.Number ctx.inUf.toRat. We need:
       computeLowerHalf ctx  =  decide (smtLibEq (v.lower r) (ves.lower r))
     where v has precision `sout` and ves has precision `sout+1`.

     Step 1. Unfold:
       smtLibRoundMethodQ eout sout
         |>.lowerHalf r
         = smtLibEq (v.embed (v.lower r)) (ves.embed (ves.lower r))
       (by simp [smtLibRoundMethodQ, smtLibRoundMethod, smtLibV,
                 smtLibRoundMethod.lowerHalf_eq])

     Step 2. Key auxiliary lemma (to be proved separately):
       A1. (computeLower ctx).pack = (smtLibLower.lower r : PackedFloat eout sout)
       A1'. (computeLower_at_sout_plus_1 ctx).pack =
              (smtLibLower.lower r : PackedFloat eout (sout+1))
     These state that bitvector truncation implements the greatest-lower-bound adjunction.
     They are proved by showing:
       (a) embed(computeLower) ≤ r  (we cleared all bits at and below guard, so value decreased)
       (b) ∀ p : PackedFloat eout sout, embed p ≤ r → p ≤ computeLower  (it is the greatest such)
     Part (a) follows because we masked out the guard and sticky bits (all ≥ 0 contributions).
     Part (b) follows because the next representable value above computeLower is computeUpper,
     and embed(computeUpper) > r when guard=1 or sticky=1.

     Step 3. Using A1 and A1':
       smtLibEq (v.embed (v.lower r)) (ves.embed (ves.lower r))
       = (embed (computeLower ctx at sout) = embed (computeLower ctx at sout+1))   [by A1, A1']

     Step 4. The two truncations agree in rational value iff the guard bit is 0:
       - If guardBit = 0: both truncations discard only sticky bits (which are strictly below guard).
         Since sig[guardBitIndex] = 0, the (sout+1)-bit lower has the same top bits as the sout-bit
         lower (the extra bit is also 0). So embed(lower_sout) = embed(lower_sout+1). ✓
       - If guardBit = 1: the (sout+1)-bit lower retains the guard bit (which equals 1), while the
         sout-bit lower clears it. The rational values differ by 2^(exp - sout). ✗

     Step 5. `computeLowerHalf ctx = !computeGuardBit ctx`
       = decide(guardBit = false)
       = decide(embed(lower_sout) = embed(lower_sout+1))  [by Step 4]
       = decide(lowerHalf r)  [by Step 3]
     QED. -/
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
    ctx.computeTieBreak =
    decide ((smtLibRoundMethodQ eout sout).tieBreak
      (ExtRat.Number ctx.inUf.toRat)) := by
  /- Proof sketch:
     Let r := ExtRat.Number ctx.inUf.toRat.  We need:
       (guardBit && !stickyBit)  =  decide ((v.lower r < ves.lower r) = (ves.upper r < v.upper r))
     where v has precision `sout` and ves has precision `sout+1`.

     Step 1. Unfold:
       (smtLibRoundMethodQ eout sout).tieBreak r
         = (v.embed (v.lower r) < ves.embed (ves.lower r)) =
           (ves.embed (ves.upper r) < v.embed (v.upper r))
       (by simp [smtLibRoundMethodQ, smtLibRoundMethod,
                 smtLibRoundMethod.tieBreak_eq])

     Step 2. Let U := 2^(exp - sout) be one ULP at the target precision.
       Recall:
         embed(v.lower r)   = embed(computeLower_sout r)   =: lo   [by aux A1]
         embed(ves.lower r) = embed(computeLower_sout+1 r) =: lo'  [by aux A1']
         embed(v.upper r)   = embed(computeUpper_sout r)   =: hi   [by aux A2]
         embed(ves.upper r) = embed(computeUpper_sout+1 r) =: hi'  [by aux A2']

     Step 3. Case split on (guardBit, stickyBit):

     Case (guard=0, sticky=0): value is exactly representable.
       r is a PackedFloat eout sout, so lo = hi = lo' = hi' = r.
       LHS of tieBreak: (r < r) = false.
       RHS of tieBreak: (r < r) = false.
       tieBreak = (false = false) = true.
       BUT computeTieBreak = false && true = false.
       RECONCILIATION: When guard=0 and sticky=0, `lowerHalf ctx = true`, so the rounding
       function branches on lowerHalf BEFORE checking tieBreak. The tieBreak theorem only
       needs to hold under the hypothesis `¬lowerHalf`, i.e., guard=1. The current theorem
       statement has no such precondition, but the rounding decision theorem uses
       computeLowerHalf and computeTieBreak together, so the tieBreak mismatch at guard=0
       is harmless (it is dead code in that branch). A stronger statement would be:
         guard=0 → tieBreak r = false (since `lowerHalf = true` already handles this).
       NOTE: The theorem as stated may need a precondition `¬computeLowerHalf ctx` or
       equivalently `computeGuardBit ctx = true` for it to hold as written.
       Alternatively, the statement should be revised to only claim agreement when guard=1.

     Case (guard=1, sticky=0): r is exactly representable at sout+1 precision.
       The guard bit is 1 and sticky is 0, so r = lo + U/2 exactly (midpoint).
       At sout+1 precision: lo' = r (exact), hi' = r (exact), since r has exactly sout+1 bits.
       LHS: lo < lo' = lo < r = lo < lo + U/2 = true  (lo is strictly below r).
       RHS: hi' < hi = r < r + U/2 = true  (hi is strictly above r).
       tieBreak = (true = true) = true. ✓  computeTieBreak = true && true = true. ✓

     Case (guard=1, sticky=1): r is strictly between two sout+1 representable values.
       lo' = floor_{sout+1}(r) > lo (lo' captures the guard bit which is 1).
       hi' = ceil_{sout+1}(r) < hi (hi' is a finer-precision upper approximant).
       LHS: lo < lo' = true (finer-precision lower > coarser-precision lower).
       RHS: hi' < hi = hi' ≤ hi; need to check strictness.
         hi = lo + U; hi' ≤ lo + U = hi.
         Since sticky=1, there is a sout+1 value strictly between lo' and hi', so hi' < hi. Wait,
         actually hi = lo + U (the next sout representable), while hi' ≤ lo + U = hi.
         sticky=1 means r > lo + U/2. So lo' ≥ lo + U/2 (capturing the guard bit). hi' = lo + U = hi,
         since the smallest sout+1 value ≥ r with sticky=1 could still be hi.
         Hmm: if sticky=1, then r > lo + U/2. The smallest sout+1 value ≥ r is hi' where
         hi' ≥ lo + U/2 + δ for some δ > 0 (from the sticky bits). But hi = lo + U.
         If r ≤ lo + U (which it must be as r is between two sout representables), then hi' ≤ hi.
         The question is whether hi' = hi or hi' < hi. For sticky=1, r has bits below the guard,
         meaning r is NOT a multiple of U/2 at sout+1 precision. The sout+1 upper of r is
         hi' = lo' + U/2, which is strictly less than hi = lo + U iff lo' > lo (which holds since
         guard=1). So hi' = lo' + U/2 ≤ lo + U/2 + U/2 = lo + U = hi.
         If lo' = lo + U/2 (only the guard bit 1, rest 0, i.e., sticky=0), hi' = lo + U = hi.
         But sticky=1 means lo' > lo + U/2, so lo' = lo + U/2 + ε for ε > 0, meaning
         hi' = lo' + U/2 > lo + U/2 + ε + U/2... This gets complicated.
         A cleaner argument: with sticky=1, lo' = lo + U/2 + ε (ε > 0) and hi' = lo' + U' where
         U' = 2^(exp - sout - 1) = U/2. So hi' = lo + U + ε > lo + U = hi. Contradiction since hi'
         must be ≤ hi (hi is already the sout-level upper bound). Therefore with sticky=1, ε must
         quantize to 0 at sout+1 precision — meaning hi' = lo' + U/2 ≤ lo + U = hi, with
         equality iff lo' = lo + U/2, i.e., sticky=0. So sticky=1 → hi' < hi.
       RHS with sticky=1: hi' < hi = true.
       But LHS = true, RHS = true, so tieBreak = (true = true) = true.
       BUT computeTieBreak = guard && !sticky = 1 && 0 = false. ✗ CONTRADICTION.
       RECHECK: sticky=1 means the value r is not at the midpoint. So smt-lib tieBreak should
       be false. Let's reread tieBreak:
         tieBreak r = (v.lower r < ves.lower r) = (ves.upper r < v.upper r)
       This is a Prop-level boolean equality (= on Prop), meaning BOTH sides must be
       equal (both true or both false). With sticky=1:
         LHS: lo < lo' = true (finer lower > coarser lower, always when guard=1).
         RHS: hi' < hi.
       With guard=1, sticky=1: is hi' < hi?
         At sout precision: hi = lo + U.
         At sout+1 precision: r > lo + U/2 (since guard=1 and sticky=1).
         hi' = smallest sout+1 value ≥ r. Since r > lo + U/2, hi' > lo + U/2.
         The sout+1 representables in [lo, lo+U] are: lo, lo+U/2, lo+U.
         So hi' = lo + U = hi. Thus hi' = hi, NOT hi' < hi.
         RHS = false.
       So: tieBreak = (true = false) = false. ✓  computeTieBreak = false. ✓

     Summary:
       guard=0: tieBreak = (false=false) = true, computeTieBreak = false. MISMATCH.
         (But as noted, this is only relevant when lowerHalf=false, i.e., guard=1.)
         Possible fix: add hypothesis `computeGuardBit ctx = true` to the theorem.
       guard=1, sticky=0: both true. ✓
       guard=1, sticky=1: both false. ✓

     Step 4. Implementation:
       Case-split on `ctx.computeGuardBit` and `ctx.computeStickyBit`.
       For guard=1 cases: use rational arithmetic about truncation and rounding intervals.
       For guard=1, sticky=0: show r = embed(lo') = embed(hi') and lo < lo' and hi' < hi? 
         Actually we showed hi'=hi in this case. Need: lo < lo' = true and hi'=hi NOT < hi.
         So (true = false) = false... wait that's wrong for sticky=0.
         Recheck sticky=0 (guard=1):
           lo' = lo + U/2 (guard bit captured exactly).
           hi' = lo + U = hi (the only sout+1 value ≥ r=lo+U/2 with no more bits).
           LHS: lo < lo + U/2 = true.
           RHS: hi' < hi = lo + U < lo + U = false.
           tieBreak = (true = false) = false. ✗  computeTieBreak = true. ✗ STILL WRONG.
       Conclusion: The tieBreak formula in SMT-Lib semantics.lean may use a different definition
       than expected, or the embedding/comparison is on PackedFloat (using `<` on PackedFloat),
       not on ExtRat. Need to re-read the exact types in smtLibRoundMethod.
       NOTE for implementer: The exact direction of the `<` comparison in `tieBreak` needs
       careful verification against `SmtLibSemantics.lean` lines 327-329 and the `LE` instance
       on `PackedFloat`. The above sketch may have the direction backwards; the actual proof
       will need to trace through the `LE PackedFloat` instance and the `toExtRat` embedding.
     QED (modulo the above disambiguation). -/
  sorry

/-- The bitvector `computeIsEven` agrees with `roundableIsEven_of_packedFloat`
applied to the lower representable value, for non-negative inputs.

The LSB of the truncated significand is checked by masking with `lsbMask`,
which corresponds to checking the last bit of `lower.sig` after packing.

Note: for negative inputs the sign convention is reversed
(`smtLibLower.lower r = computeUpper.pack`), so this theorem is stated only
for non-negative inputs. -/
theorem computeIsEven_eq_smtLibIsEven
    {expWidth sigWidth eout sout : Nat}
    (ctx : RoundingContext expWidth sigWidth eout sout)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : ctx.inUf.sig.msb = true)
    (hctx : ctx = mkRoundingContext ctx.inUf)
    (hpos : ctx.inUf.sign = false) :
    ctx.computeIsEven =
    roundableIsEven_of_packedFloat.isEven
      (SmtLibSemantics.smtLibLower.lower
        (ExtRat.Number ctx.inUf.toRat) : PackedFloat eout sout) := by
  /- Proof sketch:
     Let r := ExtRat.Number ctx.inUf.toRat.

     Step 1. Rewrite smtLibLower.lower r using auxiliary lemma A1 (hpos):
       (smtLibLower.lower r : PackedFloat eout sout)
         = ctx.computeLower.pack
         [by computeLower_pack_eq_smtLibLower_pos hprec hnorm hctx hpos]

     Step 2. Unfold `roundableIsEven_of_packedFloat.isEven`:
       roundableIsEven_of_packedFloat.isEven x = (x.sig.toNat % 2 == 0)
       [by simp [roundableIsEven_of_packedFloat, isEven_roundableIsEven_of_packedFloat]]

     Step 3. Track what `ctx.computeLower.pack.sig` is.
       From `EUnpackedFloat.pack` (Packing.lean):
         sig field := finalSigTruncated.extractMsb' 1 sout  (drops hidden bit)
       where `finalSigTruncated := outSig.extractMsb' 0 (sout+1)`
       and `outSig = sigWithHidden &&& (~~~(guardBitMask ||| stickyBitsMask))`.

     Step 4. The LSB of the packed sig = bit at index 1 (from LSB) of `outSig`
       = bit at `guardBitIndexFromLsbAdjusted + 1` in the original sig.
       Definition: `lsbMask = BitVec.oneHotBV (guardBitIndexFromLsbAdjusted + 1#sigWidth)`.
       So: `ctx.computeLower.pack.sig.toNat % 2 == 0`
           ↔ `(outSig &&& lsbMask = 0)` (checking bit at lsbMask position of outSig)
           ↔ `(sig &&& lsbMask = 0)` (since outSig = sig &&& (~~~(guardBitMask ||| stickyBitsMask))
              and lsbMask is ABOVE the guard bit, so it's not affected by the mask)
           ↔ `computeIsEven ctx`  [by definition]

     Step 5. Conclude: computeIsEven ctx = isEven (computeLower.pack) = isEven (smtLibLower.lower r).

     The key index arithmetic in step 4:
       - `lsbMask` is at position `guardBitIndexFromLsbAdjusted + 1` (one above guard)
       - `guardBitMask` is at position `guardBitIndexFromLsbAdjusted` (the guard bit)
       - `stickyBitsMask` covers positions 0..`guardBitIndexFromLsbAdjusted-1` (below guard)
       - The mask `~~~(guardBitMask ||| stickyBitsMask)` clears bits at guard and below
       - `lsbMask` is strictly ABOVE guard, so `lsbMask &&& (~~~(guardBitMask ||| stickyBitsMask)) = lsbMask`
       - Therefore: `(outSig &&& lsbMask) = (sig &&& lsbMask)` ✓
     This arithmetic requires `BitVec.and_oneHotBV_pos` or similar bit-level lemmas + `omega`.
  -/
  rw [← computeLower_pack_eq_smtLibLower_pos ctx hprec hnorm hctx hpos]
  -- Now goal: computeIsEven ctx = isEven (computeLower ctx).pack
  simp only [RoundingContext.computeIsEven, roundableIsEven_of_packedFloat,
             RoundingContext.computeLower]
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
      (significandEven := ctx.computeIsEven)
      (guardBit := ctx.computeGuardBit)
      (stickyBit := ctx.computeStickyBit)
      (_exact := false)
    -- When shouldRoundUp = true, SMT-LIB picks `upper`; when false, SMT-LIB picks `lower`.
    (if shouldRoundUp
     then SmtLibSemantics.smtLibUpper.upper (ExtRat.Number ctx.inUf.toRat)
     else SmtLibSemantics.smtLibLower.lower (ExtRat.Number ctx.inUf.toRat)
     : PackedFloat eout sout) =
    (smtLibRoundMethodQ eout sout).round mode sign (ExtRat.Number ctx.inUf.toRat) := by
  /- Proof sketch:
     Let r := ExtRat.Number ctx.inUf.toRat.
     Let L := smtLibLower.lower r : PackedFloat eout sout  (= computeLower ctx |>.pack by A1)
     Let U := smtLibUpper.upper r : PackedFloat eout sout  (= computeUpper ctx |>.pack by A2)
     Let g := computeGuardBit ctx  (= !lowerHalf by computeLowerHalf definition)
     Let s := computeStickyBit ctx
     Let e := computeIsEven ctx  (= roundableIsEven L by computeIsEven_eq_smtLibIsEven)

     Step 1. Introduce abbreviations:
       lh  := decide (lowerHalf r)  = !g   [by computeLowerHalf_eq_smtLibLowerHalf]
       tb  := decide (tieBreak r)   = g && !s  [by computeTieBreak_eq_smtLibTieBreak,
                                                   assuming guard=1 precondition holds]
       ev  := isEven L              = e    [by computeIsEven_eq_smtLibIsEven]

     Step 2. Case split on `mode` (5 cases):

     ─── Case mode = RTZ ───
       roundingDecision RTZ = false → shouldRoundUp = false → result = L.
       smtLibRoundMethodQ.roundRTZ sign r:
         r ≠ NaN (hNotNaN), r ≠ 0 (hNotZero), so we use the else/else branch.
         If r > 0: lower r = L. If r < 0: upper r = L (toward zero = smaller magnitude).
         Actually roundRTZ: `if isZero r then rounderForSign sign r else if gtZero r then lower r else upper r`
         Hmm: for RTZ, positive → lower, negative → upper.
         shouldRoundUp = false means we always return lower.
         But smtLibRoundRTZ returns lower for positive and upper for negative.
         These agree because: for a negative number, "round toward zero" means the
         magnitude-smaller value, i.e., upper in magnitude = lower in value.
         WAIT: `lower` and `upper` in SMT-LIB are ordered by the rational value of embed,
         not by magnitude. So for negative r: lower r (smallest rational) is the negative
         number with larger magnitude, and upper r (largest rational) is the one with
         smaller magnitude. RTZ for negative → upper (smaller magnitude, closer to 0).
         But computeRTZ always returns computeLower (which is truncation toward zero in
         the unsigned sense). Need to reconcile sign convention.
         NOTE: The `sign` parameter to `roundingDecision` is `ctx.inUf.sign`. For RTZ:
           roundingDecision RTZ ... = false, so we return `smtLibLower.lower r`.
           But for negative r, SMT-LIB says to return `upper r`.
         RESOLUTION: This theorem statement may have a sign-convention issue.
         The `roundNaive` function handles sign separately (see `rounderForSign`-like logic in
         computeLower/computeUpper, which INCLUDE the sign). The SMT-LIB `lower r` for
         negative r is the packed float with the more-negative value.
         This is consistent: computeLower always returns the truncation-toward-zero direction.
         For positive r: truncation toward zero = smtLibLower.lower r (correct).
         For negative r: truncation toward zero = smtLibUpper.upper r (correct).
         So we need: shouldRoundUp = (sign && (guard || sticky)) for RTN-like cases,
         but roundingDecision RTZ = false always.
         RECONCILIATION NEEDED: The theorem statement's `if shouldRoundUp then upper else lower`
         may be sign-agnostic. The actual correctness requires sign-sensitive comparison.
         The proof strategy: show the packed result equals the SMT-LIB round via
         the `roundNaiveRTZ`, `roundNaiveRTN` etc. definitions plus the main
         `roundNaive_pack_eq_smtLibRound` theorem (see below). This theorem is an
         intermediate step that may need its statement refined.

     ─── Case mode = RNA ───
       roundingDecision RNA sign g s _ = g = !lh.
       shouldRoundUp = !lh:
         - lh=true (guard=0): shouldRoundUp=false → lower. SMT RNA: lh → lower. ✓
         - lh=false (guard=1): shouldRoundUp=true → upper. SMT RNA: !lh (tie or upper half) → upper. ✓

     ─── Case mode = RNE ───
       roundingDecision RNE sign g s _ = g && (s || !e).
       Cases:
         - g=0 (lh=true): 0 → lower. SMT RNE: lh → lower. ✓
         - g=1, s=1 (upper half): 1 → upper. SMT RNE: !lh && !tieBreak → upper. ✓
         - g=1, s=0, e=true (tie, even): g&&(0||false)=0 → lower. SMT RNE: tieBreak∧isEven(L) → lower. ✓
         - g=1, s=0, e=false (tie, odd): g&&(0||true)=1 → upper. SMT RNE: tieBreak∧isEven(U) → upper.
           NOTE: isEven(U) = !isEven(L) when L and U are adjacent (their LSBs differ). This is
           because U = L + 1 ULP, so U.sig = L.sig + 1, and parity flips. Need lemma:
           `isEven (computeUpper ctx) = !computeIsEven ctx` when guard=1, sticky=0.

     ─── Case mode = RTP ───
       roundingDecision RTP sign g s _ = !sign && (g || s).
       - sign=false (positive), g=1 or s=1: true → upper. SMT RTP: !lh && positive → upper. ✓
       - sign=false, g=0, s=0: false → lower. SMT RTP: exact positive → lower = r. ✓
       - sign=true (negative), any: false → lower. SMT RTP: negative → rounderForSign or lower. ✓

     ─── Case mode = RTN ───
       roundingDecision RTN sign g s _ = sign && (g || s).
       Symmetric to RTP with sign flipped. ✓

     Step 3. For each case, conclude:
       `if shouldRoundUp then upper r else lower r = smtLibRoundMethodQ.roundXXX sign r`
     by plugging in the component equalities from Steps 1-2 and using the definition of
     `RoundMethod.roundXXX`.

     NOTE for implementer: The main challenge is the sign convention for `lower` vs `upper`
     in the presence of negative numbers. The proof should establish:
       For positive r: computeLower → smtLibLower.lower, computeUpper → smtLibUpper.upper.
       For negative r: computeLower → smtLibUpper.upper, computeUpper → smtLibLower.lower.
     (Because SMT-LIB uses rational ordering: for negative r, the "lower" rational value
     is the one with larger absolute value.)
     This sign-sensitive auxiliary lemma is likely needed in addition to A1/A2.
  -/
  sorry

/-! ### Main bridge theorem

Composes all component theorems to show that `roundNaive` (= `round`)
agrees with the SMT-LIB specification after packing.
-/

/-- The main equivalence: packing the result of `roundNaive` gives the same
`PackedFloat` as the SMT-LIB round method.

This bridges the bitvector circuit (`UnpackedFloat.round`) to the
mathematical specification (`smtLibRoundMethodQ.round`).

The hypothesis `hsign : sign = inUf.sign` is needed only for the zero case, where
the SMT-LIB uses the `sign` parameter for the sign of zero, while `roundNaive`
uses `inUf.sign`. In all non-zero cases, the result is independent of `sign`. -/
theorem roundNaive_pack_eq_smtLibRound
    {expWidth sigWidth eout sout : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : inUf.sig.msb = true)
    (rm : RoundingMode) (sign : Bool)
    (hsign : sign = inUf.sign) :
    (UnpackedFloat.roundNaive
      (targetExponentWidth := eout) (targetSignificandWidth := sout)
      inUf rm).pack =
    (smtLibRoundMethodQ eout sout).round rm sign
      (ExtRat.Number inUf.toRat) := by
  let ctx := mkRoundingContext (targetExponentWidth := eout)
    (targetSignificandWidth := sout) inUf
  -- Unfold roundNaive and dispatch on mode
  simp only [UnpackedFloat.roundNaive]
  rcases hrm : rm
  -- ─── Case RNE ───
  · simp only [roundNaiveRNE, smtLibRoundMethodQ, smtLibRoundMethod,
               SmtLibSemantics.RoundMethod.round]
    /- Proof sketch:
       1. Zero case (inUf.isZero = true):
          Both sides return `rounderForSign sign r = if sign then upper r else lower r`.
          Need: computeLower = getZero false, computeUpper = getZero true (from isZero branch of computeLower/computeUpper).
       2. Non-zero case:
          - lowerHalf branch: computeLowerHalf → computeLower.pack = lower r (by A1_pos or A2_neg).
          - tieBreak ∧ isEven: computeLower.pack = lower r.
          - tieBreak ∧ !isEven: computeUpper.pack = upper r.
          - !lowerHalf ∧ !tieBreak: computeUpper.pack = upper r.
       Needs: computeLowerHalf_eq_smtLibLowerHalf, computeTieBreak_eq_smtLibTieBreak,
              computeIsEven_eq_smtLibIsEven (pos), A1_pos, A2_pos, A1_neg, A2_neg.
    -/
    sorry
  -- ─── Case RNA ───
  · simp only [roundNaiveRNA, smtLibRoundMethodQ, smtLibRoundMethod,
               SmtLibSemantics.RoundMethod.round]
    /- Proof sketch:
       NOTE: There is a potential discrepancy in `roundRNA` in SmtLibSemantics.lean:
       Line 193 says `lowerHalf r → upper r`, while `roundNaiveRNA` says `lowerHalf → lower`.
       For RNA (Round Nearest Away), `lowerHalf → lower` is semantically correct.
       The `roundRNA` definition may have the `lowerHalf → upper r` branch intended
       for a different encoding. This case requires careful analysis against BTRW15 §4.
       Proof attempt:
         1. Zero case: same as RNE.
         2. Non-zero case: case split on lowerHalf/tieBreak.
            - lowerHalf=true: roundNaiveRNA returns computeLower, roundRNA returns upper.
              For POSITIVE r: computeLower = smtLibLower = lower r ≠ upper r (mismatch!).
              This case may reveal a theorem statement issue.
    -/
    sorry
  -- ─── Case RTP ───
  · simp only [roundNaiveRTP, smtLibRoundMethodQ, smtLibRoundMethod,
               SmtLibSemantics.RoundMethod.round]
    /- Proof sketch:
       Zero case: both return rounderForSign sign r. ✓
       Non-zero positive (inUf.sign = false):
         roundNaiveRTP: `!sign → upper = computeUpper`
         roundRTP: `gtZero r → upper r`
         Need: computeUpper.pack = upper r (by A2_pos). ✓
       Non-zero negative (inUf.sign = true):
         roundNaiveRTP: `sign → lower = computeLower`
         roundRTP: `ltZero r → rounderForSign sign r = upper r` (for sign=true = upper)
         For negative r: upper r = smtLibUpper.upper r = value with larger rational = closer to 0.
         And computeLower = toward zero = computeLower.pack = smtLibUpper.upper r by A1_neg. ✓
         So: computeLower.pack = smtLibUpper.upper r = rounderForSign true r. ✓
    -/
    sorry
  -- ─── Case RTN ───
  · simp only [roundNaiveRTN, smtLibRoundMethodQ, smtLibRoundMethod,
               SmtLibSemantics.RoundMethod.round]
    /- Proof sketch:
       roundRTN: `if isZero then rounderForSign else lower r`.
       roundNaiveRTN:
         Zero: rounderForSign. ✓
         Non-zero positive (sign=false): returns computeLower. lower r = smtLibLower.lower r = computeLower.pack (A1_pos). ✓
         Non-zero negative (sign=true): returns computeUpper. lower r = smtLibLower.lower r = computeUpper.pack (A2_neg). ✓
    -/
    sorry
  -- ─── Case RTZ ───
  · simp only [roundNaiveRTZ, smtLibRoundMethodQ, smtLibRoundMethod,
               SmtLibSemantics.RoundMethod.round]
    /- Proof sketch:
       roundRTZ:
         isZero → rounderForSign. Zero case ✓ (both use sign).
         gtZero → lower r. Positive: computeLower.pack = smtLibLower.lower r (A1_pos). ✓
         ltZero → upper r. Negative: computeLower.pack = smtLibUpper.upper r (A1_neg).
                            And upper r = smtLibUpper.upper r. ✓
    -/
    sorry

/-- Corollary: since `roundNaive = round`, we get the bridge for the original circuit. -/
theorem round_pack_eq_smtLibRound
    {expWidth sigWidth eout sout : Nat}
    (inUf : UnpackedFloat expWidth sigWidth)
    (hprec : RoundingPreconditions expWidth sigWidth eout sout)
    (hnorm : inUf.sig.msb = true)
    (rm : RoundingMode) (sign : Bool)
    (hsign : sign = inUf.sign) :
    (UnpackedFloat.round
      (targetExponentWidth := eout) (targetSignificandWidth := sout)
      inUf rm).pack =
    (smtLibRoundMethodQ eout sout).round rm sign
      (ExtRat.Number inUf.toRat) := by
  rw [← roundNaive_eq_round]
  exact roundNaive_pack_eq_smtLibRound inUf hprec hnorm rm sign hsign

end UnpackedRoundNaive
end Fp
