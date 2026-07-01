# Proof checklists for `FpAgainstFloatModel` sorries

Goal: **eliminate all 18 `sorry`s.** Ordered easiest→hardest (see `ORDER.md` for the tier
rationale). Each box is a discrete, committable step.

Key upstream shapes:
- `Float.Model.UnpackedFloat.unpack spec b`: extracts sign/exp/mantissa via `extractLsb`;
  `exponent := expField.toNat - (bias + 52)`; all-ones exp → inf/NaN, exp 0 → zero/subnormal
  (`exp+1`), else normal (mantissa `= 2^52 + trailing`).
- `Float.Model.pack spec`: `notANumber → packedNaN`, `infinity/zero → packed…`, `finite s m e`
  → `biasedExponent := (e + bias + 52).toNat`, overflow→inf, `m.log2+1 = 53`→normal else subnormal.
- `packedNaN = positive, allOnes exp, top mantissa bit`. Project `getNaN = sign false, ex allOnes,
  sig intMin` — **identical 64-bit pattern**.
- Model `neg`: flips `Sign` in every constructor (NaN stays NaN). `abs`: sets `.positive`.
- Model `le/lt/beq := compare …`; `compare` returns `none` on any NaN, `some .eq` on `zero,zero`.
- Sign: `positive.toBitVec = 0#1`; `ofBitVec b = if b=0 then positive else negative`.

## Tier 0 — Foundation (`Basic.lean`)

- [ ] **`toModelUnpacked_eq_unpack`**
  - [ ] `unfold toModelUnpacked; unfold UnpackedFloat.unpack`.
  - [ ] Establish extraction identities on `toBits64 pf = (sign ++ ex ++ sig).cast`:
        `unpackSign = ofBool pf.sign`, `unpackExponent = pf.ex`, `unpackMantissa = pf.sig`
        (via `BitVec.extractLsb'`/`getElem` `simp`, or `bv_normalize`).
  - [ ] Match `isNaN/isInfinite/isZero` (project) to the model's `exp=allOnes / exp=0` branches
        (unfold `PackedFloat.isNaN` etc.; `pf.ex = allOnes 11 ↔ unpackExponent = -1#11`).
  - [ ] Normal branch: `signToModel pf.sign = Sign.ofBitVec (ofBool pf.sign)` (2-case `decide`);
        mantissa `2^52 + sig.toNat = (1#1 ++ sig).toNat` (`BitVec.toNat_append`); exponent
        `ex.toNat - 1075 = ex.toNat - (bias+52)` (`bias 11 = 1023`, `omega`).
  - [ ] Subnormal branch: exponent `-1074 = (0 - 1075) + 1`; mantissa `sig.toNat`.

- [ ] **`unpack_unpackRel`** — same extraction facts; case-split classification; `UnpackedRel`
      finite case is `sig.toNat = m ∧ ex.toInt - 52 = e` (Nat/Int eq). Reuse the project
      `unpackNum` normal/subnormal encoding + the bit facts above.

- [ ] **`pack_modelEquiv`** — case on `u`. For NaN/inf/zero: both packers emit the identical
      canonical pattern (`getNaN=packedNaN`, etc.) → `toBits64` eq. For finite: `EUnpackedFloat.pack'`
      `packNumber'` vs model `pack` `packComponents`; show equal bits from `UnpackedRel`'s
      `sig.toNat=m`, `ex.toInt-52=e`. Use `pack_eq_pack'` to switch to the clean packer.

- [ ] **`modelEquiv_iff_unpack`** — `→`: bit-eq ⇒ `unpack` eq (both = `unpack toBits`), close with
      `toModelUnpacked_eq_unpack`. `←`: `unpack` eq ⇒ bit-eq-or-both-NaN (unpack is injective off
      NaN; NaN collapses). 

- [ ] **`ofBits_modelEquiv`** — `toBits (ofBits b) = b` (`bv_normalize`), `Float.Model.ofBits`
      canonicalizes; conclude via `modelEquiv_iff_unpack` + `toModelUnpacked_eq_unpack`.

## Tier 1 — sign ops

- [ ] **`neg_agree`** (`Neg.lean`) — `PackedFloat.neg` flips `sign` bit; `Float.Model.neg =
      pack unpack.neg` flips the `Sign` in each constructor. Two routes: (a) direct bit: show
      `toBits64 (-a) = (toBits (-fa))` from `ha` (sign bit flip commutes with the shared layout),
      handling NaN via the `∨`; (b) via `pack_modelEquiv` + `toModelUnpacked (-a) = (toModelUnpacked a).neg`.
      Prefer (a) for a short proof; NaN case uses canonical-NaN-stays-NaN.
- [ ] **`abs_agree`** (`Abs.lean`) — identical, sign bit cleared to `false`/`.positive`.

## Tier 2 — comparisons

- [ ] **`beq_agree`** (`Compare.lean`) — reduce both to comparing unpacked forms.
      `Float.Model.beq = (unpack.compare == some .eq)`. Relate `ieeeBeq` (project, on
      `EUnpackedFloat`) to the model `compare` via `unpack_unpackRel`: both are "not-NaN ∧ equal
      value/sign, ±0 equal". Likely needs a `UnpackedRel`-respects-compare bridge lemma (add it).
- [ ] **`lt_agree`** — `compare == some .lt`; `smtBlt false` = strict order, NaN false.
- [ ] **`le_agree`** — `compare.any (·.isLE)`; `smtBle false`.
- [ ] **`compare_agree`** — unfold `compareOpt`; assemble from `beq/lt` + NaN case.
- [ ] **`min_agree` / `max_agree`** (`MinMax.lean`) — `Min.min` is left-leaning
      (`if b ≤ a then b else a` style); `smtMin false`. Depends on `le_agree`; **verify the
      ±0 convention** (`xOnDiffZeros`) matches — adjust the flag if not.

## Tier 3 — arithmetic (hard: relate the two `unpack→op→round→pack` pipelines)

- [ ] **`mul_agree`** (`Mul.lean`) — factor `unpack_unpackRel → mul-on-unpacked agree → RNE
      round agree → pack_modelEquiv`. The inner obligation: project `UnpackedFloat.mul` +
      `blastSmtLibRound .RNE` computes the same bits as model `UnpackedFloat.mul` (`m₁·m₂`,
      `e₁+e₂`, `roundWithAccuracy .exact`). *Fallback if a pure-circuit bridge is intractable:*
      route through `Fp.mul_eq_mul` (project = SMT-LIB spec) by proving `Float.Model.mul` also
      equals that spec — a new but self-contained bridge; the `ModelEquiv` relation stays bit-level.
- [ ] **`add_agree`** (`Add.lean`) — same skeleton; inexact (sticky). Relate project's
      `blastSmtLibRound` (via `StickyEquiv`) to model's `normalize`/`roundToNearestEven`.
- [ ] **`sub_agree`** (`Sub.lean`) — reduce both to `add`+`neg`; then `add_agree` + `neg_agree`.
- [ ] **`div_agree`** (`Div.lean`) — same as add (quotient + remainder sticky).

## Tier 4

- [ ] **`sqrt_agree`** (`Sqrt.lean`) — hardest; no existing project↔spec sqrt lemma. Relate
      project `UnpackedFloat.sqrt` + round to model `sqrtCore` (`Nat.sqrt` + accuracy) + round.

---

### Method
Prove strictly in the order above; each closed sorry → build the file → commit. Add small
reusable bridge lemmas to `Basic.lean` as needed (e.g. `UnpackedRel`-respects-`neg`/`compare`).
Never fake a proof: if a leaf is genuinely out of reach this session, leave it `sorry` with a
note and move on rather than introduce an unsound tactic.
