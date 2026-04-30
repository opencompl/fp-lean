# PLAN: filling `toExtRat_round_Rel_smtLibRound_of_RNE`

Target: `Fp/Theorems/UnpackedFloat/Round.lean:568`.

```
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) (rstar : Rat) ... :
    (x.blastSmtLibRound ep sp .RNE).Rel
      ((smtLibRoundMethod ep sp smtLibV smtLibV).round .RNE x.sign (.Number x.toRat))
```

The proof is sketched as a case-split mirroring the structure of `blastSmtLibRoundRNE`
(`Fp/UnpackedRound.lean:718`) and `RoundMethod.roundRNE` (`Fp/SmtLibSemantics.lean:206`).
Each non-overflow branch is supposed to chain
`EUnpackedFloat.normalize_Rel_of_Rel ∘ truncateFittingExponent_Rel_of_Rel ∘ {blastUpper, blastLower, blastRounderForSign}`
to discharge `Rel`.

There are two classes of `sorry`:
  - **Direct sorries** in the main proof body.
  - **Indirect sorries** in the helper lemmas it `apply`s.

## Strategy issues to fix BEFORE filling sorries

### Issue 1 — `EUnpackedFloat.Rel` is too permissive (likely a typo)

`Fp/Theorems/PackedUnpackedRel/Basic.lean:35-38`:

```lean
def EUnpackedFloat.Rel (euf : ...) (pf : ...) :=
  (euf.isNaN ↔ pf.isNaN) ∨
  (euf.isInfinite ↔ pf.isInfinite ∧ euf.sign = pf.sign) ∨
  (¬ euf.isNaN ∧ ¬ euf.isInfinite ∧ euf.num.Rel pf)
```

`↔` has lower precedence than `∧`. The first disjunct simplifies to
`euf.isNaN = pf.isNaN`. So whenever `euf` and `pf` are both non-NaN (the
common case), disjunct 1 is `false ↔ false = true`, and `Rel` is **trivially
satisfied for any pair of non-NaN values**. The relation effectively constrains
nothing.

The constructor `Rel_of_isNaN_of_isNaN` and `Rel_of_isInfinite_of_isInfinite_and_sign`
build `Rel` from `∧`-style premises, which strongly suggests `↔` was a typo.

**Fix:** change both `↔` to `∧`:
```lean
def EUnpackedFloat.Rel ... :=
  (euf.isNaN ∧ pf.isNaN) ∨
  (euf.isInfinite ∧ pf.isInfinite ∧ euf.sign = pf.sign) ∨
  (¬ euf.isNaN ∧ ¬ euf.isInfinite ∧ euf.num.Rel pf)
```

The three named `Rel_of_...` constructors continue to work unchanged.

### Issue 2 — `hsu : sp + 2 ≤ su` is unsatisfiable at every call site

Every call site to `EUnpackedFloat.normalize_Rel_of_Rel` and
`EUnpackedFloat.truncateFittingExponent_Rel_of_Rel` in this proof feeds a value
of type `EUnpackedFloat _ (sp + 1)` — never `sp + 2 ≤ ...`:

- `blastRounderForSign x ep sp : EUnpackedFloat (eu+1) (sp+1)` — feeds
  `truncateFittingExponent`, so the lemma is invoked with `_su := sp+1`.
  Required `sp + 2 ≤ sp + 1` is false.
- `_.truncateFittingExponent ep sp : EUnpackedFloat (exponentWidth ep sp) (sp+1)`
  — feeds `normalize`, with `_su := sp+1`. Same false.

That is *exactly* why every `(by sorry)` in the main proof appears as the 4th
argument: it's filling `hsu`, and `hsu` is unprovable.

**Fix:** weaken the precondition. `normalize` only shifts `sig`/`ex` and never
touches widths, and the proof of `truncateFittingExponent_Rel_of_Rel` only needs
the truncated exponent to fit (not extra significand bits). The right
precondition is essentially `sp ≤ su` — and for `normalize` you can probably
drop `hsu` entirely.

Concretely:
- Drop `hsu` from `EUnpackedFloat.normalize_Rel_of_Rel` and
  `UnpackedFloat.normalize_Rel_of_Rel`.
- In `truncateFittingExponent_Rel_of_Rel`, replace `hsu : sp + 2 ≤ su` with
  whatever is needed for `ex.truncate` to be value-preserving (see Issue 3).

After this, every `(by sorry)` precondition collapses to `(by omega)` or
disappears.

### Issue 3 — `truncateFittingExponent_Rel_of_Rel` as stated is *false*

`UnpackedFloat.truncateFittingExponent` (`Fp/UnpackedRound.lean:224`) returns
`{ uf with ex := uf.ex.truncate (exponentWidth tep tsp), ... }`. This preserves
`toRat'` only when `uf.ex.toInt` lies in the range expressible by
`exponentWidth tep tsp` bits. Otherwise the truncation silently changes the
exponent's value.

The lemma needs an additional hypothesis along the lines of
`uf.ex.toInt` is within the range `[minNormalExp tep, maxNormalExp tep]`
(or simply `BitVec.toInt`-fits-in-narrower-width). At the call site this is
guaranteed by the surrounding `¬ blastIsOverflowNonneg ...` branch. Plumb
that hypothesis into the lemma.

### Issue 4 — duplication

Seven of the eight non-overflow branches do exactly the same chain
(`normalize_Rel_of_Rel ∘ truncateFittingExponent_Rel_of_Rel ∘ {Upper|Lower}`).
Extract one lemma:

```
lemma blastSmtLibRound_branch_Rel
  ... (h : (case_result : EUnpackedFloat _ (sp+1)).Rel pf) :
  (case_result.truncateFittingExponent ep sp).normalize.Rel pf
```

and the seven branches all become a one-line `apply ...`.

---

## Sorry inventory (ranked)

### Tier 0 — trivial after Issue 2 is fixed (≈30 min)

| # | Location | Subgoal |
|---|---|---|
| T0.1 | line 601 (zero,sign) | `hsu` precondition |
| T0.2 | line 602 (zero,sign) | `hsu` precondition |
| T0.3 | line 621 | `hsu` |
| T0.4 | line 622 | `hsu` |
| T0.5 | line 627 | `hsu` |
| T0.6 | line 628 | `hsu` |
| T0.7 | line 639 | `hsu` |
| T0.8 | line 640 | `hsu` |
| T0.9 | line 648 | `hsu` |
| T0.10 | line 649 | `hsu` |
| T0.11 | line 654 | `hsu` |
| T0.12 | line 655 | `hsu` |
| T0.13 | line 662 | `hsu` |
| T0.14 | line 663 | `hsu` |

After Issue 2, these become `omega`/`grind`.

### Tier 1 — easy, mechanical (≈1 hour)

| # | Location | What |
|---|---|---|
| T1.1 | line 617 | RNE: lowerHalf ∧ tieBreak ∧ evenUpper picks `blastUpper`. Mirror lines 622-623 with `blastUpper_Rel_smtLibUpper`. |
| T1.2 | `UnpackedFloat.normalize_Rel_of_Rel` (line 526) | Show `normalize` preserves `toRat'` and `sign`. Case `sig = 0`: `mkZero` has `toRat' = 0`; `pf.toRat = uf.toRat' = 0` so `pf.isZero`, sign matches via `Rel`. Case `sig ≠ 0`: `sig << clz` and `ex - clz` preserve `sigNat * 2^expInt`. |
| T1.3 | `EUnpackedFloat.normalize_Rel_of_Rel` (line 534) | Case-split on state; `Number` reduces to T1.2; `Inf`/`NaN` are identities for `normalize`. |

### Tier 2 — medium, bit-level reasoning (≈2-3 hours each)

| # | Location | What |
|---|---|---|
| T2.1 | `blastIsEvenUpper_iff_smtLibIsEven_upper` (line 476) | `blastIsEven` is decidable on bits; show it agrees with `roundableIsEven_of_packedFloat` after applying `blastUpper`. Depends on T3.2. |
| T2.2 | `blastIsEvenLower_iff_smtLibIsEven_lower` (line 484) | Same as T2.1 with `blastLower`. Depends on T3.3. |
| T2.3 | `blastTieBreak_iff_smtLibTieBreak` (line 451) | Show `guardBit ∧ ¬stickyBit` ↔ "lower-extra and upper-extra are equidistant in `s+1`". Mostly an unfolding-and-`bv_decide` exercise once `lower`/`upper` are tied to bit operations. |
| T2.4 | `UnpackedFloat.truncateFittingExponent_Rel_of_Rel` (line 544) | After Issue 3 fix: with the new hypothesis, prove `ex.truncate` is value-preserving for in-range exponents. |
| T2.5 | `EUnpackedFloat.truncateFittingExponent_Rel_of_Rel` (line 552) | Case-split; `Number` reduces to T2.4. |

### Tier 3 — hard, ties our circuit to non-computable spec (≈1+ days each)

| # | Location | What |
|---|---|---|
| T3.1 | line 585 | Overflow case for RNE returns `mkInfinity x.sign`. SMT-LIB `roundRNE` for `r > maxNormal` selects `upper r = +∞` (and analogously for negatives). Need the `lower`/`upper` characterizations for out-of-range rationals; depends on T3.2 + T3.3 in their out-of-range form, plus reasoning about `lowerHalf`/`tieBreak` of an out-of-range rational (probably `lowerHalf = false`, so RNE picks `upper`). |
| T3.2 | `UnpackedFloat.blastUpper_Rel_smtLibUpper` (line 461) | Connect the bit-blasted greatest-PF-≤-r-or-+∞ circuit to `epsilon (IsLawfulUpper r)`. Plan: prove uniqueness of `IsLawfulUpper`, then show `blastUpper` satisfies it. |
| T3.3 | `UnpackedFloat.blastLower_Rel_smtLibLower` (line 469) | Symmetric to T3.2. |
| T3.4 | `UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero` (line 510) | Two branches, each by `blastUpper_Rel_smtLibUpper` / `blastLower_Rel_smtLibLower` applied at `r = 0`. Trivial **once** T3.2/T3.3 are proven. |

### Dependency DAG

```
                         (main proof, line 568)
                                  │
        ┌─────────────────┬───────┼─────────────┬──────────────┐
        ▼                 ▼       ▼             ▼              ▼
     T0.*            T1.1 (617)  T1.3        Issue 1+2      Issue 3
   (hsu fillers)        │      (E-normalize)  (blanket)        │
                        ▼         │                            │
                      T1.3        ▼                            ▼
                        │       T1.2 (UF-normalize)         T2.5
                        │                                   (E-truncate)
                        ▼                                       │
                  T3.2 / T3.3                                   ▼
                        │                                  T2.4 (UF-truncate)
                        ├──> T3.4
                        ├──> T2.1, T2.2
                        ├──> T2.3
                        └──> T3.1 (overflow)
```

## Execution order

1. **Pre-work (today):**
   - Fix Issue 1 (`↔ → ∧` in `EUnpackedFloat.Rel`). Re-check the 3 `Rel_of_...`
     constructors still close.
   - Fix Issue 2 (drop `hsu` on the four `*_Rel_of_Rel` lemmas; leave the
     proofs as `sorry` for now).
   - This kills T0.1–T0.14 wholesale.
2. **Day 1:** T1.2, T1.3 (normalize lemmas). T1.1 (line 617).
3. **Day 2:** Issue 3 fix on `truncateFittingExponent_Rel_of_Rel`, then T2.4,
   T2.5.
4. **Day 3-4:** T3.2, T3.3 (the hard core: connect blast to `epsilon`-lower/upper).
   Once these land, T3.4, T2.1, T2.2, T2.3 follow quickly.
5. **Day 5:** T3.1 (overflow). Likely needs lemmas about `IsLawfulUpper r` for
   `r > maxNormal`.
6. **Cleanup:** extract the duplicated 7-branch chain (Issue 4).

## Quick wins to unblock the user right now

- Apply Issue 1 (5 min).
- Apply Issue 2 (10 min): drop `hsu`. All 14 `(by sorry)`s in the main theorem
  shrink to a single chain of `apply`s discharged by `grind`.
- Tackle T1.2 + T1.3 next; they are the only "real" lemmas in the easy tier and
  unblock every non-overflow branch from terminating cleanly.
