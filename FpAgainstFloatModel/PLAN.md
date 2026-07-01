# Plan: `PackedFloat ⇄ Float.Model` agreement via three relations

Goal: prove that `PackedFloat 11 52`'s operations compute **bit-identical** results (up to the
single canonical NaN) to Lean's reference `Float.Model` (IEEE `binary64`).

The clean way to establish *"the packed-float bits are equal"* is to route through one of two
value-level relations and transfer back to bits. We therefore build **three relations** and
the bridges between them.

```
        (C)  a.toExtRat = modelToExtRat fa          ExtRat value equality
         │  ▲                                        (NaN ↦ .NaN, ±0 ↦ Number 0;
   bridge│  │bridge                                   normalization collapses in Rat)
         ▼  │
        (B)  UnpackedRel a.unpack fa.unpack         unpacked dyadic value equality
         │  ▲                                        (DyadicEqNat, Rat-free; carries sign)
   bridge│  │bridge
         ▼  │
        (A)  a.ModelEquiv fa                         bit equality up to NaN   ◀── the goal
```

## Relation A — bits equal up to NaN  (`Basic.lean`)
`PackedFloat.ModelEquiv pf fm := toBits64 pf = fm.toBits.toBitVec ∨ (pf.isNaN ∧ fm.isNaN)`.
- ✅ `modelEquiv_iff_unpack : a.ModelEquiv fa ↔ toModelUnpacked a = fa.unpack`
- ✅ `modelEquiv_of_toBits_eq`, `ofBits_modelEquiv`, `toModelUnpacked_eq_unpack`.

## Relation B — unpacked values equal  (`Basic.lean`)
`UnpackedRel` compares classification + sign + `DyadicEqNat` (value `M₁·2^E₁ = M₂·2^E₂`
compared by shifting to the common floor exponent — pure `Nat`/`Int`, tolerant of the
normal/subnormal normalization difference). **B is the relation that still sees the sign of
zero**, so it is what fixes the ±0 gap that C cannot.
- ✅ `unpack_unpackRel`: NaN / infinity / zero cases.
- ☐ `unpack_unpackRel` finite case: `(cons true).toNat`, and the `clz`-shift value identity for
  subnormals — reuse `Fp/Theorems/PackedFloat/Packing.lean`'s `cons`/`clz`/`toNat` machinery.

## Relation C — ExtRat values equal  (`ExtRat.lean`)  ← the clean route
`modelToExtRat : Float.Model → ExtRat` (the model has no rational semantics of its own).
- ✅ **crux:** `modelUnpackedToExtRat (toModelUnpacked pf) = pf.toExtRat`. At the `Rat` level
  the subnormal normalization difference vanishes and NaN collapses; proven with the zpow
  helper `sign_div_pow_mul_zpow`.
- ✅ forward bridge `toExtRat_eq_modelToExtRat_of_modelEquiv : A → C` (always holds).
- ✅ reverse anchors `modelToExtRat_eq_ofBits` (reduces C to the project's own
  `eq_of_toExtRat'_eq` determinism) and `modelToExtRat_eq_NaN_iff`.
- ✅ **reverse bridge `modelEquiv_of_toExtRat_eq : C → A`** — NaN via `modelToExtRat_eq_NaN_iff`,
  non-zero via `PackedFloat.eq_of_toExtRat'_eq` (`a = modelBits fa`), and the ±0 case via a
  `hzsign : a.isZero → a.sign = (modelBits fa).sign` witness (which **relation B** supplies).
- ✅ supporting: `isZero_of_toExtRat'_eq_zero` (`¬isNaN → toExtRat = Number 0 → isZero`, from
  the project's `toExtRat' ≤/< Number 0` iffs), `modelBits`, `toBits64_modelBits`.

## Bridging to the operations (the payoff)
Each arithmetic agreement `(a ∘ b).ModelEquiv (fa ∘ fb)` then goes:
1. inputs `A → C` (`toExtRat_eq_modelToExtRat_of_modelEquiv`);
2. **project side** — reuse the project's proven `Fp.mul_eq_mul` / `add_eq_add` / `div_eq_div`
   (packed op `= EquivUptoNaN` the SMT-LIB spec: *round of the exact `ExtRat` arithmetic*);
3. **model side** — prove `modelToExtRat (fa ∘ fb) = <same SMT-LIB round> (modelToExtRat fa ∘
   modelToExtRat fb)`, i.e. the model's `roundWithAccuracy` implements the same round on
   `ExtRat`. This is the one genuinely new, reusable **round-agreement** lemma;
4. combine to `(a∘b).toExtRat = modelToExtRat (fa∘fb)`, then `C → A` (+ B for ±0 sign).

Comparisons/min/max: the model's `UnpackedFloat.compare` is a value comparison on canonical
forms, and the project has `smtBle/smtBlt/ieeeBeq ↔ toExtRat` order lemmas — so `le`/`lt`/`beq`/
`min`/`max` agreement also factors through C's value equality (+ B for ±0).

## Status snapshot
Closed sorry-free: `unpack_inj`, `unpack_pack` (+ `ModelCanonical` theory), `neg_agree`,
`abs_agree`, `ofBits_modelEquiv`, all of relation C above. Remaining scaffold sorries:
`unpack_unpackRel` (finite), `pack_modelEquiv`, `Add/Sub/Mul/Div/Sqrt`, `Compare` (×4),
`MinMax` (×2) — all now reducible to the round-agreement lemma + the two small bridge leaves.
