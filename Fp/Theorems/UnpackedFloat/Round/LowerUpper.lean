import Fp.Theorems.UnpackedFloat.Round.TruncateFittingExponent

namespace Fp


/-# `blastLowerNonneg` matches `lower` -/



/--
Helper: Reduce `result.Rel (smtLibLower.lower (Number r))` to producing a
witness `pf` that is a lawful lower with matching `toRat'` and `sign`.
-/
theorem EUnpackedFloat.Rel_smtLibLower_of_witness
    (he : 0 < ep) (hs : 0 < sp)
    (r : Rat)
    (result : EUnpackedFloat eu su)
    (hres : result.state = .Number)
    (pf : PackedFloat ep sp)
    (hpfNotNaN : ¬ pf.isNaN)
    (hpfLower : SmtLibSemantics.IsLawfulLower (ExtRat.Number r) pf)
    (hToRat : result.num.toRat' sp = pf.toRat)
    (hSign  : result.num.sign  = pf.sign) :
    result.Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp) := by
  -- The smtLib lower is also a lawful lower; by uniqueness it equals `pf`.
  have hSmtLower : SmtLibSemantics.IsLawfulLower (ExtRat.Number r)
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp) :=
    lsLawfulLower_smtLibLower ep sp he hs _
  have hSmtNotNaN : ¬ (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp).isNaN := by
    have := not_isNaN_lower_of_ne_NaN ep sp he hs (ExtRat.Number r) (by simp)
    grind only
  have hpf_eq : pf = SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) := by
    apply eq_of_IsLawfulLower_of_IsLawfulLower
    · exact hpfNotNaN
    · exact hSmtNotNaN
    · exact hpfLower
    · exact hSmtLower
  apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number
  · simp [hres]
  · refine UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign _ _ ?_ ?_
    · rw [hToRat, hpf_eq]
    · rw [hSign, hpf_eq]

  /--
info: 'Fp.EUnpackedFloat.Rel_smtLibLower_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EUnpackedFloat.Rel_smtLibLower_of_witness

/-! ## Branch (1): underflow

When `x` is positive but smaller in magnitude than the smallest representable
subnormal (i.e. `blastIsUnderflowNonneg`), the greatest representable PF ≤ x
is `+0`. -/

/--
Spec-side: when `x` underflows the target format, `+0` is a lawful lower
for `Number x.toRat'`.

This is hard: it requires knowing `x.toRat' < (minSubnormal target).toRat`
and that no negative PF can be `> x`'s value (since `x ≥ 0`).
-/
theorem isLawfulLower_Number_getZero_of_underflowNonneg
    (he : 0 < ep) (hs : 0 < sp)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hunder : x.blastIsUnderflowNonneg ep sp = true) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat')
      (PackedFloat.getZero ep sp false) := by
  sorry

theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_underflow
    (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hunder : x.blastIsUnderflowNonneg ep sp = true) :
    (EUnpackedFloat.mkNumber (UnpackedFloat.mkZero false) :
      EUnpackedFloat eu (sp+1)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := PackedFloat.getZero ep sp false)
      (he := by grind) (hs := hs)
  · simp
  · simp; grind only
  · exact isLawfulLower_Number_getZero_of_underflowNonneg (by grind) hs x hxsign hunder
  · -- `(mkZero false).num.toRat' = 0 = (getZero ep sp false).toRat`
    simp only [EUnpackedFloat.num_mkNumber]
    rw [UnpackedFloat.toRat'_mkZero,
        PackedFloat.toRat_eq_Zero_of_isZero _ (by simp [PackedFloat.isZero_getZero]; grind)]
  · -- `(mkZero false).num.sign = false = (getZero ep sp false).sign`
    simp [UnpackedFloat.mkZero, PackedFloat.sign_getZero]

/-! ## Branch (2): overflow

When `x.toRat'` exceeds `maxNormalNumber`, the greatest representable PF ≤ x
is `maxNormalNumber ep sp false` (since +∞ would be > x in the embedding,
and there is no PF strictly between maxNormal and +∞). -/

/--
Spec-side: when `x` overflows the target format positively, `maxNormalNumber`
is a lawful lower for `Number x.toRat'`.
-/
theorem isLawfulLower_Number_maxNormalNumber_of_overflowNonneg
    (he : 0 < ep) (hs : 0 < sp)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hover  : x.blastIsEarlyOverflowNonneg ep sp = true) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat')
      (PackedFloat.maxNormalNumber ep sp false) := by
  sorry

/-- `maxNormalNumber` is not NaN: its exponent is `allOnes - 1`, never `allOnes`
    (when `0 < ep`). -/
theorem PackedFloat.not_isNaN_maxNormalNumber (ep sp : Nat) (sign : Bool) (hep : 0 < ep) :
    ¬ (PackedFloat.maxNormalNumber ep sp sign).isNaN := by
  -- The exponent of `maxNormalNumber` is `allOnes - 1`, which differs from `allOnes`
  -- whenever `0 < ep`. `isNaN` requires `ex = allOnes`, so this case is excluded.
  simp [PackedFloat.maxNormalNumber, PackedFloat.isNaN]
  intros hcontra
  rw [BitVec.sub_eq_iff_eq_add] at hcontra
  simp at hcontra
  grind

/--
The unpacked `maxNormal` and packed `maxNormalNumber` agree under `toRat`.
-/
theorem UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber
    {eu su ep sp : Nat}
    {sign : Bool}
    (hsp : 0 < sp)
    (hsu : sp + 1 ≤ su)
    (hep : 2 < ep)
    (heu : exponentWidth ep sp ≤ eu) :
    (UnpackedFloat.maxNormal eu su ep sp sign).toRat' (sp)
      = (PackedFloat.maxNormalNumber ep sp sign).toRat := by
  rw [UnpackedFloat.maxNormal, UnpackedFloat.toRat']
  simp [UnpackedFloat.toExpInt]
  rw [PackedFloat.toRat]
  rw [PackedFloat.toRatSig_maxNormalNumber]
  rw [PackedFloat.toRatExp_maxNormalNumber]
  rw [Nat.mod_eq_of_lt]
  · rw [Int.bmod_eq_of_le]
    · simp
      rw [Int.neg_sub]
      rw [Rat.zpow_sub_eq_zpow_mul_zpow (by grind)]
      rw [Rat.natCast_sub_of_le (by grind)]
      push_cast
      have : ((2 : Rat) ^ (sp + 1) - 1) * (2 : Rat) ^ (-sp : Int) = (2 - (2 : Rat) ^ (-sp : Int)) := by
        rw [Rat.sub_mul]
        simp only [Rat.one_mul]
        norm_cast
        rw [Nat.pow_succ]
        simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat]
        have := Rat.zpow_mul_zpow (show 2 ≠ 0 by grind) sp (-sp)
        simp only [Rat.zpow_natCast] at this
        grind only
      rw [← this]
      grind
    · simp [maxNormalExp]
      grind
    · simp [maxNormalExp]
      norm_cast
      apply Nat.lt_trans <| bias_lt_two_pow_exponent_sub_one ep
      apply Nat.pow_lt_pow_of_lt
      · grind
      · have := self_lt_exponentWidth ep sp (by grind) (by grind)
        grind
  · rw [Nat.pow_add]
    have : 2 ^ (sp + 1) ≤ 2 ^ su := by
      apply Nat.pow_le_pow_of_le
      · grind
      · grind
    have : 2 * 2 ^ sp ≤ 2 ^ su := by
      grind
    grind
  · grind
  · grind

/--
info: 'Fp.UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber

theorem UnpackedFloat.mkNumber_maxNormal_Rel_smtLibLower_of_overflow
    (hep : 2 < ep)
    (hsp : 0 < sp)
    (x : UnpackedFloat eu su)
    (hsu : sp + 1 ≤ sm)
    (heu : exponentWidth ep sp ≤ em)
    (hxsign : x.sign = false)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (EUnpackedFloat.mkNumber (UnpackedFloat.maxNormal em sm ep sp false)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := PackedFloat.maxNormalNumber ep sp false)
      (by grind) (by grind)
  · simp
  · exact PackedFloat.not_isNaN_maxNormalNumber ep sp false (by grind)
  · exact isLawfulLower_Number_maxNormalNumber_of_overflowNonneg (by grind) (by grind) x hxsign hover
  · -- `num.toRat'` of the unpacked `maxNormal` equals `toRat` of the packed `maxNormalNumber`.
    simp only [EUnpackedFloat.num_mkNumber]
    apply UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber
    · grind
    · grind
    · grind
    · grind
  · -- sign is `false` on both sides
    simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]

/--
info: 'Fp.UnpackedFloat.mkNumber_maxNormal_Rel_smtLibLower_of_overflow' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.mkNumber_maxNormal_Rel_smtLibLower_of_overflow

/-! ## Branch (3): normal range — `blastRoundTowardZero` is a lawful lower

When `x` is in the normal range (no under/overflow), the bit-blasted
round-toward-zero `next := blastRoundTowardZero x ep sp` produces an
`UnpackedFloat (exponentWidth ep sp) (sp+1)` whose value is the greatest PF representable
in `(ep, sp)` that is ≤ `x.toRat'`.

To use the helper we need *some* `PackedFloat ep sp` `pf` such that
  • `IsLawfulLower (Number x.toRat') pf`
  • `next.toRat' = pf.toRat`
  • `next.sign  = pf.sign`

Such a `pf` exists because `next` is by construction representable in the
target format (its exponent and significand are within `(ep, sp)` bounds in
this branch); we don't have a single named constructor for it, so we
existentially extract one. -/

/-
Key facts:

- the packed float will be the one given by 'blastLowerNonneg.pack'
- pack preserves the toRat, nor does it change the sign
- we need a lemma that says that it's a lawful lower if the 'toRat' is equal, and then distance
  btween 'pf.toRat' and 'x.toRat' is less than 1 ulp of 'pf' (which is the same as 1 ulp of 'blastRoundTowardZero x').
  This needs a separate lemma or two.
- These key facts establish the existence of the 'pf'.
- TODO: maybe worth it to replace the existential with the concrete pf we know.
-/
/-- (M) Full not-underflow ⇒ early not-underflow.

`blastIsEarlyUnderflowNonneg` is the coarser test (exponent strictly below the
subnormal range), so it is subsumed by `blastIsUnderflowNonneg`. This lets the
`truncateFittingExponent` invariance lemmas — which are stated with the `Early`
form — apply under the hypothesis the keystone is actually given.

Proof: discharge via `blastUnderflowNonneg_eq_decide` and
`blastIsEarlyUnderflowNonneg_eq_decide` + `grind` on the exponent bounds. -/
theorem UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false) :
    x.blastIsEarlyUnderflowNonneg ep sp = false := by
  -- `not-underflow` says `minSubnormalExp ≤ x.ex.toInt`; since `minSubnormalExp - 1`
  -- is strictly smaller, `early-underflow` (testing `< minSubnormalExp - 1`) is false.
  rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu]
  rw [UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu] at hnotunder
  simp only [decide_eq_false_iff_not] at hnotunder ⊢
  grind

/--
info: 'Fp.UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg

/-- (U) The sub-ulp gap — the heart of round-toward-zero correctness.

The bits discarded by `blastRoundTowardZero` are worth strictly less than one ulp
of the *target* grid, so the rounded value plus one ulp strictly overshoots `x`.
The ulp exponent is `x.ex.toInt - sp + off` where `off = (minNormalExp ep - x.ex.toInt).toNat`
is the subnormal shift: in the normal range `off = 0` (ulp `2^(ex-sp)`), in the
subnormal range `off = minNormalExp - ex` (ulp `2^(minNormalExp-sp)`, the subnormal
quantum). The inequality is strict even when `x` is already representable.

Proof: factor out the common weight `2^(ex-(su-1))`; the goal reduces to
`x.sig.toNat < cleared.sig.toNat + 2^L` with `L = lsbIndex.toNat = (su-(sp+1))+off`,
which holds because `blastClearSignificand` zeroes exactly the low `L` bits and
`extractMsb'` then re-reads `cleared / 2^(su-(sp+1))`. -/
theorem UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    x.toRat' <
      (x.blastRoundTowardZero ep sp).toRat'
        + (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int)) := by
  -- Exponent / guard-index bounds from "no early over/underflow".
  have hoverE : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x; grind
  have hunderE : minSubnormalExp ep sp ≤ x.ex.toInt := by
    have := UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x; grind
  have hminrel : minNormalExp ep - minSubnormalExp ep sp = (sp : Int) := by
    simp only [minSubnormalExp, maxSubnormalExp]; grind
  have hdNat : (minNormalExp ep - x.ex.toInt).toNat ≤ sp := by grind
  obtain ⟨hdL, hdU⟩ := shift_range he hs heu (exInt := x.ex.toInt) (by grind) hoverE
  have hG := UnpackedFloat.toNat_guardBitIndex_eq he hs heu hsu x hdL hdU hdNat
  -- `L = guardBitIndex + 1 = (su-(sp+1)) + off`, `m = su-(sp+1) ≤ L`.
  have hLeq : (x.guardBitIndex ep sp).toNat + 1
      = (minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)) := by rw [hG]; grind
  -- Clearing rounds the significand down to a multiple of `2^L`; `extractMsb'` re-reads
  -- `cleared / 2^m`, and since `m ≤ L` this recovers `cleared` exactly.
  have hcl := UnpackedFloat.blastClearSignificand_sig_toNat_eq x ep sp
  have hdvd : 2 ^ (su - (sp + 1)) ∣ (x.blastClearSignificand ep sp).sig.toNat := by
    rw [hcl]; exact Nat.two_pow_dvd_div_mul_two_pow x.sig.toNat (by grind)
  have hrm : (x.blastRoundTowardZero ep sp).sig.toNat * 2 ^ (su - (sp + 1))
      = (x.blastClearSignificand ep sp).sig.toNat := by
    rw [sig_blastRoundTowardZero, BitVec.toNat_extractMsb'_zero _ (by grind)]
    exact Nat.div_mul_cancel hdvd
  -- The core Nat gap: `x.sig.toNat < cleared.sig.toNat + 2^L`.
  have hnatN : x.sig.toNat
      < (x.blastClearSignificand ep sp).sig.toNat
          + 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) := by
    rw [hcl, hLeq]
    have hk : 0 < 2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) :=
      Nat.two_pow_pos _
    have h1 := Nat.div_add_mod x.sig.toNat
      (2 ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))))
    have h2 := Nat.mod_lt x.sig.toNat hk
    grind
  have hnat : (x.sig.toNat : Rat)
      < (x.blastClearSignificand ep sp).sig.toNat
          + (2 : Rat) ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))) := by
    exact_mod_cast hnatN
  -- Expand both `toRat'` and factor the common weight `C = 2^(ex - (su-1))`.
  rw [UnpackedFloat.toRat', UnpackedFloat.toRat', sign_blastRoundTowardZero, hxsign,
    UnpackedFloat.toExpInt, UnpackedFloat.toExpInt, ex_blastRoundTowardZero,
    UnpackedFloat.toNat_toSigNat_eq, UnpackedFloat.toNat_toSigNat_eq]
  have hCpos : (0 : Rat) < 2 ^ (x.ex.toInt - ((su : Int) - 1)) := Rat.two_pow_pos _
  have hsg : (Bool.toSign false : Rat) = 1 := by simp [Bool.toSign]
  -- rewrite the three scaled terms onto the base weight `C = 2^(ex-(su-1))`.
  have hround : (Bool.toSign false : Rat) * (x.blastRoundTowardZero ep sp).sig.toNat
        * 2 ^ (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
      = (x.blastClearSignificand ep sp).sig.toNat * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    have hrmR : (↑(x.blastRoundTowardZero ep sp).sig.toNat : Rat) * 2 ^ (su - (sp + 1))
        = ↑(x.blastClearSignificand ep sp).sig.toNat := by exact_mod_cast hrm
    have hexp : (-((↑((sp + 1) - 1) : Int) - x.ex.toInt))
        = (↑(su - (sp + 1)) : Int) + (x.ex.toInt - ((su : Int) - 1)) := by
      rw [Int.natCast_sub (show sp + 1 ≤ su by grind)]
      have e1 : ((sp + 1) - 1 : Nat) = sp := by grind
      rw [e1]; push_cast; grind
    rw [hexp, ← Rat.zpow_mul_zpow (by grind), Rat.zpow_natCast, hsg, ← hrmR]
    grind
  have hulp : (2 : Rat) ^ (x.ex.toInt - (sp : Int) + ((minNormalExp ep - x.ex.toInt).toNat : Int))
      = (2 : Rat) ^ ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1)))
          * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    rw [← Rat.zpow_natCast (2 : Rat) ((minNormalExp ep - x.ex.toInt).toNat + (su - (sp + 1))),
      Rat.zpow_mul_zpow (by grind)]
    congr 1
    push_cast [Int.natCast_sub (show sp + 1 ≤ su by grind)]; grind
  have hx : (Bool.toSign false : Rat) * x.sig.toNat * 2 ^ (-((↑(su - 1) : Int) - x.ex.toInt))
      = (x.sig.toNat : Rat) * 2 ^ (x.ex.toInt - ((su : Int) - 1)) := by
    have hexp : (-((↑(su - 1) : Int) - x.ex.toInt)) = x.ex.toInt - ((su : Int) - 1) := by
      rw [Int.natCast_sub (show 1 ≤ su by grind)]; push_cast; grind
    rw [hexp, hsg]; grind
  rw [hround, hulp, hx]
  -- `x.sig.toNat * C < cleared.sig.toNat * C + (2^L) * C`, cancel `C > 0`.
  have hmul := (Rat.mul_lt_mul_cancel_right_of_lt hCpos).mpr hnat
  grind

/--
info: 'Fp.UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp

/-- (GLB) A non-NaN nonnegative packed float that is `≤ R` and lies within one ulp
below `R` is the greatest lower bound of `R`.

Reusable spec-side lemma. Proof: `constructor`.
  * clause 1 (`embed pf ≤ R`): from `hle` via `toExtRat'_eq_toRat_of` + `num_le_num_iff`.
  * clause 2 (`∀ pf', embed pf' ≤ R → pf' ≤ pf`): case-split `pf'` with
    `PackedFloat.kindCasesNaNInfZeroNum`; NaN and `+∞` are excluded by `embed ≤ R`,
    the negative kinds are `≤` the nonnegative `pf`, and for the positive-finite case
    a `pf < pf'` would force `pf.toRat + ulp ≤ pf'.toRat ≤ R` (via
    `toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false`), contradicting `hlt`.
Mirror the body of `lower_Number_eq_maxNormalNumber_of_toRat_le`. -/
theorem PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp
    (he : 1 < ep) (hs : 0 < sp)
    (R : Rat) (pf : PackedFloat ep sp)
    (hsign : pf.sign = false)
    (hfin : pf.isNormOrNonzeroSubnorm)
    (hle : pf.toRat ≤ R)
    (hlt : R < pf.toRat + (2 : Rat) ^ (-(sp : Int)) * 2 ^ pf.toRatExp) :
    SmtLibSemantics.IsLawfulLower (ExtRat.Number R) pf := by
  have hpfNaN : ¬ pf.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hfin
  constructor
  · -- `pf ≤ R` in the embedding.
    show pf.toExtRat ≤ ExtRat.Number R
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfin]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
    exact hle
  · -- Any representable `y` with embedded value `≤ R` is at most `pf`.
    intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number R := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']; exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'
      simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        -- `+∞` cannot be `≤ Number R`.
        exfalso
        rw [PackedFloat.toExtRat'_getInfinity hs] at hy'
        simp at hy'
      case true =>
        -- `-∞ ≤` the nonnegative `pf`.
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp) hsign (by simp [hs]) hpfNaN
    | zeroCase sign =>
      -- `±0 ≤` the nonnegative `pf`.
      exact PackedFloat.getZero_le_of_nonneg (by grind) hs pf hsign hpfNaN
    | numCase n hn =>
      have hnNaN : ¬ n.isNaN := by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn
      by_cases hnsign : n.sign
      · -- `n` negative, `pf` nonnegative.
        exact PackedFloat.le_of_nonneg_of_neg n pf hnsign hsign hnNaN hpfNaN
      · -- `n` nonnegative: the one-ulp gap above `pf` rules out `pf < n ≤ R`.
        simp only [Bool.not_eq_true] at hnsign
        apply Classical.byContradiction
        intro hcon
        have hltn : pf < n := PackedFloat.lt_of_not_le n pf (by grind) hcon
        have hulp := PackedFloat.toRat_le_plus_toRat_of_toRat_le_toRat_of_sign_eq_false
          (by grind) hs pf n hsign hnsign
          (by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hfin)
          (by simpa using PackedFloat.not_isZero_of_isNormOrSubnorm hn)
          hpfNaN hnNaN
          (by simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hfin)
          (by simpa using PackedFloat.not_isInfinite_of_isNormOrNonzeroSubnorm hn)
          hltn
        have hnR : n.toRat ≤ R := by
          rw [PackedFloat.toExtRat'_eq_toRat_of hn] at hy'
          simpa only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq] using hy'
        grind

/--
info: 'Fp.PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp

theorem UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)   -- ADDED (needed by `truncateFittingExponent`)
    (x : UnpackedFloat eu su)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    ∃ pf : PackedFloat ep sp,
      ¬ pf.isNaN ∧
      SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat') pf ∧
      (x.blastRoundTowardZero ep sp).toRat' = pf.toRat ∧
      (x.blastRoundTowardZero ep sp).sign  = pf.sign := by
  -- (M) Full not-underflow ⇒ early not-underflow, so the `truncateFittingExponent`
  -- invariance lemmas (stated with the `Early` form) apply.
  have hnotearlyunder : x.blastIsEarlyUnderflowNonneg ep sp = false :=
    UnpackedFloat.not_blastIsEarlyUnderflowNonneg_of_not_blastIsUnderflowNonneg
      he hs heu x hnotunder
  -- Width-adjust into the packable exponent width `exponentWidth ep sp`, then round.
  -- (`blastRoundTowardZero` keeps the input exponent width, so we adjust first.)
  let r : UnpackedFloat (exponentWidth ep sp) (sp + 1) :=
    (x.truncateFittingExponent ep sp).blastRoundTowardZero ep sp
  -- (P) `r` is `Packable`: (1) normalized (rounding keeps the top significand bit),
  -- (2) `ex ≤ maxNormalExp` (from `hnotover`), (3) subnormal divisibility — the bits
  -- `blastClearSignificand` zeroes are exactly the divisibility witness.
  have hPack : r.Packable := by
    sorry
  refine ⟨(EUnpackedFloat.mkNumber r).pack, ?_, ?_, ?_, ?_⟩
  · -- ¬ isNaN: `pack` of a `Number` whose exponent is `≤ maxNormalExp` is never NaN.
    --   `EUnpackedFloat.not_isNaN_packNumber'` (needs `hPack.2.1`) / `sign_pack`.
    sorry
  · -- IsLawfulLower — the crux. With `pf := pack r`, apply
    --   `PackedFloat.isLawfulLower_of_toRat_le_of_lt_add_ulp`, feeding:
    --     • `hle : pf.toRat ≤ x.toRat'` from round-toward-zero lowering the value
    --       (`blastClearSignificand_toRat_le_of_nonneg` + the truncation step);
    --     • `hlt : x.toRat' < pf.toRat + ulp` from
    --       `UnpackedFloat.toRat'_lt_blastRoundTowardZero_toRat'_add_ulp` (U) after the
    --       ulp bridge `2^(-sp)·2^(pf.toRatExp) = 2^(x.ex.toInt - sp)`.
    sorry
  · -- value: `pf.toRat = r.toRat = r.toRat' sp = (x.blastRoundTowardZero ep sp).toRat'`.
    --   `toRat_pack_mkNumber_eq_toRat he hs r hPack`, then the `truncateFittingExponent`
    --   invariance (`toRat'_eq_toRat'_of_parts`, as in `…_PartsEq`, Round.lean:2091).
    sorry
  · -- sign: LHS `= x.sign = false` (`sign_blastRoundTowardZero`); RHS `= r.sign = false`
    --   (`sign_pack` + ¬isNaN, `sign_blastRoundTowardZero`, `sign_truncateFittingExponent`).
    sorry

theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ e) (hsu : sp + 2 ≤ s)   -- ADDED (forwarded to the keystone)
    (x : UnpackedFloat e s)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (EUnpackedFloat.mkNumber (x.blastRoundTowardZero ep sp) :
      EUnpackedFloat e (sp+1)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      he hs heu hsu x hxsign hxnorm hnotunder hnotover
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := pf) (he := by grind) (hs := hs)
  · simp
  · exact hpfNotNaN
  · exact hpfLower
  · simpa using hToRat
  · simpa using hSign

/-- Main theorem: the bit-blasted lower-rounding circuit for nonnegative floats
    matches the SMT-LIB greatest lower bound. The proof unfolds
    `blastLowerNonneg` and dispatches to one of the three branch lemmas.

    Requires `x.normalize = x` (i.e. `x` is already in normalized form) so that
    the normal-range branch can identify `blastRoundTowardZero x` with a packed
    float — without normalization, multiple unpacked representations share the
    same value and the bit-level "extract top sp+1 bits" step does not commute
    with `toRat'`. -/
theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower (he : 2 < ep) (hsp : 0 < sp)
  (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
  (x : UnpackedFloat eu su)
  (hxsign : x.sign = false)
  (hxnorm : x.normalize = x) :
  (x.blastLowerNonneg ep sp).Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  unfold UnpackedFloat.blastLowerNonneg
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · simp [hunder]
    exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_underflow (by grind only) hsp x hxsign hunder
  · simp only [Bool.not_eq_true] at hunder
    simp [hunder]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
    · simp [hover]
      -- The witness lemma must be instantiated at `em := eu` (not `exponentWidth ep sp`):
      -- `blastLowerNonneg` returns an `EUnpackedFloat eu (sp+1)`, so the goal mentions
      -- `UnpackedFloat.maxNormal eu (sp+1) ep sp false`.
      have := mkNumber_maxNormal_Rel_smtLibLower_of_overflow (x := x) (ep := ep) (sp := sp) (sm := sp + 1) (em := eu)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
          (by grind)
      exact this
    · simp only [Bool.not_eq_true] at hover
      simp [hover]
      exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal (by grind only) hsp heu hsu x hxsign hxnorm hunder hover

/-# `blastUpperNonneg` matches `upper` -/

theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper (he : 1 < ep) (hs : 0 < sp)
  (x : UnpackedFloat eu su)
  (hxsign : x.sign = false) :
  (x.blastUpperNonneg ep sp).Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastUpperNonneg]
  sorry


/-# `blastLower` matches `lower` -/

theorem UnpackedFloat.blastLower_Rel_smtLibLower (hep : 2 < ep)
  (hsp : 0 < sp)
  (hsu : sp + 2 ≤ su)
  (heu : exponentWidth ep sp ≤ eu)
  (x : UnpackedFloat eu su)
  (hxnorm : x.normalize = x) :
  (x.blastLower ep sp).Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastLower]
  by_cases hsign : x.sign
  · simp [hsign]
    simp [UnpackedFloat.blastLowerNeg]
    rw [smtLibLower_eq_neg_smtLibUpper_neg]
    · apply EUnpackedFloat.neg_Rel_neg
      simp
      rw [show - x.toRat' = (-x).toRat' by simp]
      apply UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper
      · grind
      · grind
      · simp [hsign]
    · grind only
    · grind only
    · grind only
  · simp [hsign]
    apply UnpackedFloat.blastLowerNonneg_Rel_smtLibLower
    · grind only
    · grind only
    · grind
    · grind
    · grind only
    · grind only

/-# `blastUpper` matches `upper` -/


theorem UnpackedFloat.blastUpper_Rel_smtLibUpper (hep : 2 < ep) (hsp : 0 < sp)
    (hsu : sp + 2 ≤ su)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x) :
    (x.blastUpper ep sp).Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastUpper]
  by_cases hsign : x.sign
  · simp [hsign]
    simp [UnpackedFloat.blastUpperNeg]
    rw [smtLibUpper_eq_neg_smtLibLower_neg]
    · apply EUnpackedFloat.neg_Rel_neg
      simp
      rw [show - x.toRat' = (-x).toRat' by simp]
      apply UnpackedFloat.blastLowerNonneg_Rel_smtLibLower
      · grind
      · grind
      · grind
      · grind
      · simp; grind only
      · exact normalize_neg_eq_neg_of_normalize_eq x hxnorm
    · grind only
    · grind only
    · grind only
  · simp [hsign]
    apply UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper
    · grind only
    · grind only
    · simp [hsign]

/-- `maxNormalNumber` is a normal number when `1 < e`. -/
theorem PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber'
    {e s : Nat} (he : 1 < e) (sign : Bool) :
    (PackedFloat.maxNormalNumber e s sign).isNormOrNonzeroSubnorm := by
  have h := PackedFloat.isNorm_maxNormalNumber_of_lt_e e s he sign
  simp only [PackedFloat.isNormOrNonzeroSubnorm]
  simp only [PackedFloat.isNorm] at h
  grind

/-- Negating the positive `maxNormalNumber` gives the negative one. -/
theorem PackedFloat.neg_maxNormalNumber_false' {ep sp : Nat} :
    - PackedFloat.maxNormalNumber ep sp false = PackedFloat.maxNormalNumber ep sp true := rfl

/-- The value of `maxNormalNumber` is strictly below `2 ^ (maxNormalExp + 1)`. -/
theorem PackedFloat.toRat_maxNormalNumber_lt_two_pow
    {ep sp : Nat} (hep : 2 < ep) (hs : 0 < sp) :
    (PackedFloat.maxNormalNumber ep sp false).toRat < (2 : Rat) ^ (maxNormalExp ep + 1) := by
  rw [PackedFloat.toRat, PackedFloat.toRatSig_maxNormalNumber ep sp hep,
    PackedFloat.toRatExp_maxNormalNumber ep sp hep]
  simp [Bool.toSign]
  have h2 : (2 : Rat) * (2 : Rat) ^ maxNormalExp ep = (2 : Rat) ^ (maxNormalExp ep + 1) :=
    Rat.mul_self_zpow_eq_zpow_succ (by grind)
  rw [← h2, Rat.sub_mul]
  have hpos : (0 : Rat) < 2 ^ maxNormalExp ep := Rat.two_pow_pos _
  have hsub : (0 : Rat) < 2 ^ (-(sp : Int)) := Rat.two_pow_pos _
  have : (0 : Rat) < 2 ^ (-(sp : Int)) * 2 ^ maxNormalExp ep := Rat.mul_positive hsub hpos
  grind

/-- The value of the positive `maxNormalNumber` is nonnegative. -/
theorem PackedFloat.toRat_maxNormalNumber_nonneg
    {ep sp : Nat} (he : 1 < ep) :
    (0 : Rat) ≤ (PackedFloat.maxNormalNumber ep sp false).toRat := by
  have h := PackedFloat.sign_iff_toRat_neg
    (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp) he false)
  rw [PackedFloat.sign_maxNormalNumber] at h
  have h3 : ¬ ((PackedFloat.maxNormalNumber ep sp false).toRat < 0) := by
    simpa using h.symm
  grind

/-- The max normal value strictly increases with the significand width. -/
theorem PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ
    {ep sp : Nat} (hep : 2 < ep) (hs : 0 < sp) :
    (PackedFloat.maxNormalNumber ep sp false).toRat
      < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat := by
  rw [PackedFloat.toRat, PackedFloat.toRat,
    PackedFloat.toRatSig_maxNormalNumber ep sp hep,
    PackedFloat.toRatExp_maxNormalNumber ep sp hep,
    PackedFloat.toRatSig_maxNormalNumber ep (sp + 1) hep,
    PackedFloat.toRatExp_maxNormalNumber ep (sp + 1) hep]
  simp [Bool.toSign]
  have hpos : (0 : Rat) < 2 ^ maxNormalExp ep := Rat.two_pow_pos _
  rw [Rat.sub_mul, Rat.sub_mul]
  have hppos : (0 : Rat) < 2 ^ (-((sp : Int) + 1)) := Rat.two_pow_pos _
  have hstep : (2 : Rat) * (2 : Rat) ^ (-((sp : Int) + 1)) = 2 ^ (-((sp : Int) + 1) + 1) :=
    Rat.mul_self_zpow_eq_zpow_succ (by grind)
  have hexp : (-((sp : Int) + 1) + 1) = -(sp : Int) := by omega
  rw [hexp] at hstep
  have hlt : (2 : Rat) ^ (-((sp : Int) + 1)) < 2 ^ (-(sp : Int)) := by
    rw [← hstep]
    grind
  have h1 : (2 : Rat) ^ (-((sp : Int) + 1)) * 2 ^ maxNormalExp ep
      < 2 ^ (-(sp : Int)) * 2 ^ maxNormalExp ep := by
    rw [Rat.mul_lt_mul_cancel_right_of_lt hpos]
    exact hlt
  grind

/-- For `R` at or above `maxNormalNumber`, the greatest float `≤ R` is
`maxNormalNumber` itself. -/
theorem lower_Number_eq_maxNormalNumber_of_toRat_le
    {ep sp : Nat} (hep : 1 < ep) (hep0 : 0 < ep) (hsp : 0 < sp) (R : Rat)
    (hmax : (PackedFloat.maxNormalNumber ep sp false).toRat ≤ R) :
    lower ep sp hep0 hsp (ExtRat.Number R) = PackedFloat.maxNormalNumber ep sp false := by
  have hfin := PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp) hep false
  have hnan := PackedFloat.not_isNaN_maxNormalNumber ep sp false hep0
  symm
  apply eq_lower_of_IsLawfulLower ep sp hep0 hsp _ _ (by simp)
  constructor
  · -- `maxNormalNumber ≤ R` in the embedding
    show (PackedFloat.maxNormalNumber ep sp false).toExtRat ≤ ExtRat.Number R
    rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat'_eq_toRat_of hfin]
    simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
    exact hmax
  · -- anything `≤ R` is at most `maxNormalNumber`
    intro y hy
    have hy' : y.toExtRat' ≤ ExtRat.Number R := by
      rw [← PackedFloat.toExtRat_eq_toExtRat']
      exact hy
    clear hy
    induction y using PackedFloat.kindCasesNaNInfZeroNum with
    | nanCase n hn =>
      exfalso
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN n hn] at hy'
      simp at hy'
    | infCase sign =>
      cases sign
      case false =>
        exfalso
        rw [PackedFloat.toExtRat'_getInfinity hsp] at hy'
        simp at hy'
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp)
          (by simp [PackedFloat.sign_maxNormalNumber]) (by simp [hsp]) hnan
    | zeroCase sign =>
      cases sign
      case true =>
        exact PackedFloat.le_of_nonneg_of_neg _ _ (by simp [PackedFloat.sign_getZero])
          (by simp [PackedFloat.sign_maxNormalNumber]) (by simp [hsp] <;> omega) hnan
      case false =>
        apply PackedFloat.le_of_toExtRat'_le_toExtRat' hep0 hsp
          (PackedFloat.getZero ep sp false) (PackedFloat.maxNormalNumber ep sp false)
          (by simp [hsp] <;> omega) hnan
        · intro h1 h2 h3
          simp [PackedFloat.sign_getZero] at h3
        · intro h1 _ _
          exfalso
          have h2 := PackedFloat.not_isZero_of_isNormOrSubnorm hfin
          simp at h2
          simp [h2] at h1
        · rw [PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [hsp] <;> omega),
            PackedFloat.toExtRat'_eq_toRat_of hfin]
          simp only [ExtRat.ExtRat.num_le_num_iff, decide_eq_true_eq]
          exact PackedFloat.toRat_maxNormalNumber_nonneg hep
    | numCase n hn =>
      by_cases hsign : n.sign
      · exact PackedFloat.le_of_nonneg_of_neg _ _ hsign
          (by simp [PackedFloat.sign_maxNormalNumber])
          (by simpa using PackedFloat.not_isNaN_of_isNormOrSubnorm hn) hnan
      · apply PackedFloat.le_maxNormalNumber_of_isNormOrNonzeroSubnorm_of_nonneg _ hep hn
        simpa using hsign

end Fp
