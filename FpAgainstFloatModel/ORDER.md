# Proof order for `AgainstFloatModel` (easiest → hardest)

18 `sorry`s across the folder, grouped into tiers. Later tiers depend on earlier ones, and
within a tier items are ordered by increasing difficulty. Each item is a self-contained unit
suitable for **goal mode**: set the goal to *"remove the `sorry` for `<theorem>` in
`<file>` and keep `lake build` green"*, then work only that leaf.

The design is deliberately **circuit/bit-level and `Rat`-free**: relate the two libraries'
`unpack → op → round → pack` pipelines structurally, never through a rational value.

---

## Tier 0 — Foundation (`Basic.lean`) — do these first, they unblock everything

1. **`toModelUnpacked_eq_unpack`** — *medium.* The field interpretation (`toNat`/`toInt` of
   sign/ex/sig) equals `Float.Model.UnpackedFloat.unpack .binary64 pf.toBits`. Pure bit
   arithmetic: `unfold` both, case-split `isNaN / isInfinite / isZero / ex=0 / normal`,
   discharge each with `simp`/`omega` on `extractLsb`/`toNat`. Already validated by `#eval`,
   so the statement is known true — this is just the general proof. *No dependencies.*

2. **`unpack_unpackRel`** — *medium.* `PackedFloat.unpack` (project `EUnpackedFloat`) is
   `UnpackedRel`-related to the model's `unpack`. Case-split on classification; the finite
   case matches `sig.toNat` and `ex.toInt − 52` to the model's mantissa/exponent. Shares the
   bit-arithmetic lemmas from item 1. *Depends on: definitions only.*

3. **`pack_modelEquiv`** — *medium/hard.* `UnpackedRel euf u → (euf.pack).ModelEquiv
   (Float.Model.pack u)`. Both `pack`s are bit-level; show they emit the same 64 bits per
   class (canonical NaN coincides). *Depends on: 1.*

4. **`modelEquiv_iff_unpack`** — *easy once 1–3 exist.* `pf.ModelEquiv fm ↔ toModelUnpacked
   pf = fm.unpack`. Combine item 1 with injectivity of `unpack` up to NaN. *Depends on: 1.*

5. **`ofBits_modelEquiv`** — *easy.* `ofBits` round-trip. Direct from item 4 + `toBits∘ofBits`
   round-trip lemmas. *Depends on: 1, 4.*

## Tier 1 — Sign-only operations (`Neg.lean`, `Abs.lean`) — simplest agreements

6. **`neg_agree`** (`Neg.lean`) — *easy.* Both flip the sign bit; NaN stays canonical.
   Via `pack_modelEquiv` + "`unpack.neg` only flips sign". *Depends on: Tier 0.*

7. **`abs_agree`** (`Abs.lean`) — *easy.* Both clear the sign bit. Same shape as item 6.
   *Depends on: Tier 0.*

## Tier 2 — Comparisons (`Compare.lean`, `MinMax.lean`) — structural, no rounding

8. **`beq_agree`** (`Compare.lean`) — *medium.* `ieeeBeq a b = fa.beq fb`. Both are
   "compare unpacked forms, `NaN ≠ everything`, `±0` equal". Reduce via `unpack_unpackRel`
   to the model's `UnpackedFloat.beq`. *Depends on: 2.*

9. **`lt_agree`** (`Compare.lean`) — *medium.* Same, for strict order. *Depends on: 2.*

10. **`le_agree`** (`Compare.lean`) — *medium.* Same, for `≤`. *Depends on: 2.*

11. **`compare_agree`** (`Compare.lean`) — *easy once 8–10.* `compareOpt` is defined from
    `ieeeBeq`/`smtBlt`; unfold and assemble from items 8–10. *Depends on: 8, 9, 10.*

12. **`min_agree`** (`MinMax.lean`) — *medium/hard.* `smtMin false` vs left-leaning `Min.min`.
    Depends on `le_agree`; **watch the differing-signed-zero convention** — this is the item
    most likely to need the `xOnDiffZeros` flag adjusted. *Depends on: 10.*

13. **`max_agree`** (`MinMax.lean`) — *medium/hard.* Mirror of item 12. *Depends on: 10.*

## Tier 3 — Arithmetic (`Mul.lean`, `Add.lean`, `Sub.lean`, `Div.lean`)

Each factors as `unpack agree (2) → op-on-unpacked agree → RNE round agree → pack agree (3)`.
The hard leaf is always "the project's bit-blasted circuit and the model's `Nat`/`Int`
arithmetic compute the same rounded result", proved structurally (no `Rat`).

14. **`mul_agree`** (`Mul.lean`) — *hard, but the easiest arithmetic:* the product is exact
    pre-rounding on both sides, so only one RNE-round correspondence is needed.
    *Depends on: Tier 0.*

15. **`add_agree`** (`Add.lean`) — *hard:* exponent alignment + cancellation + sticky bit;
    the round input is a sticky-compression, not exact. *Depends on: Tier 0.*

16. **`sub_agree`** (`Sub.lean`) — *easy once 15:* both reduce to `add`+`neg`.
    *Depends on: 15, 6.*

17. **`div_agree`** (`Div.lean`) — *hard:* truncated quotient + remainder-derived sticky,
    then RNE round. Structurally similar to add's inexact rounding. *Depends on: Tier 0.*

## Tier 4 — Hardest

18. **`sqrt_agree`** (`Sqrt.lean`) — *hardest:* unlike +,−,×,÷ there is **no** existing
    project↔spec `sqrt` theorem to lean on, so both the inner `Nat.sqrt`/remainder-accuracy
    correspondence and its RNE round must be established from scratch. *Depends on: Tier 0.*

---

### Suggested goal-mode session order
`1 → 2 → 3 → 4 → 5` (foundation) → `6, 7` (warm-up) → `8 → 9 → 10 → 11 → 12 → 13`
(comparisons) → `14 → 15 → 16 → 17` (arithmetic) → `18` (sqrt).

### Reusable levers (all `Rat`-free where possible)
- Bit lemmas: `BitVec.extractLsb'`, `BitVec.toNat_*`, `BitVec.eq_of_toNat_eq`, `omega`.
- Project unpack/pack: `PackedFloat.unpack`, `EUnpackedFloat.pack`/`pack'`, `pack_eq_pack'`.
- Comparisons already characterized: `Fp/Theorems/PackedFloat/Comparison.lean`
  (`bltAux_*`, `bleAux_*`) — usable structurally.
- If a structural bridge proves impractical `Rat`-free for `add`/`div`, the *fallback* is to
  route through the existing rational agreement (`Fp.add_eq_add`, `Fp.div_eq_div`) — but this
  is explicitly the last resort per the design.
