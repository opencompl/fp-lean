import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.PackedFloat.Packing
import Fp.Theorems.PackedFloat.Negation
import Fp.Theorems.PackedFloat.Ordering
import Fp.Theorems.LowerUpperRound
import Fp.Theorems.PackedUnpackedRel

namespace Fp

@[grind <=]
theorem PackedFloat.eq_of_unpack_eq_unpack_of_isInfinity {x y : PackedFloat e s}
    (hs : 0 < s) (he : 0 < e)
    (hx : x.isInfinite) (hy : y.isInfinite) (h : x.unpack = y.unpack) :
    x = y := by
  cases x using PackedFloat.kindCasesNaNInfZeroNum <;> try grind


@[simp]
theorem clearSignificand_sign (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).sign = uf.sign := by
  simp [UnpackedFloat.blastClearSignificand]

@[simp]
theorem clearSignificand_ex (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).ex = uf.ex := by
  simp [UnpackedFloat.blastClearSignificand]

/-- Clearing guard/sticky bits can only decrease the significand value. -/
theorem UnpackedFloat.blastClearSignificand_sig_toNat_le (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).sig.toNat ≤ uf.sig.toNat := by
  rw [UnpackedFloat.blastClearSignificand]
  simp only [BitVec.toNat_and]
  apply Nat.and_le_left


/-- For a nonnegative unpacked float, clearing guard/sticky bits yields a nonnegative result. -/
theorem UnpackedFloat.blastClearSignificand_toRat_nonneg_of_sign_eq_false (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : uf.sign = false) :
    0 ≤ (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).toRat := by
  simp [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat']
  generalize hcleared : uf.blastClearSignificand targetExponentWidth targetSignificandWidth = cleared
  have : 0 < (2 : Rat) ^ cleared.toExpInt := by grind only [Rat.two_pow_pos]
  have hsign : cleared.sign = false := by
    simp [← hcleared, UnpackedFloat.blastClearSignificand, h]
  simp [hsign]
  grind only [Rat.mul_nonneg]



/-- For a nonnegative unpacked float, clearing guard/sticky bits rounds toward zero:
    the cleared value is at most the original value. -/
theorem UnpackedFloat.blastClearSignificand_toRat_le_of_nonneg (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (hufsign : uf.sign = false) :
    (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).toRat ≤ uf.toRat := by
  simp only [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat' , UnpackedFloat.toRat']
  generalize hcleared : uf.blastClearSignificand targetExponentWidth targetSignificandWidth = cleared
  have hsign : cleared.sign = false := by
    simp only [← hcleared, UnpackedFloat.blastClearSignificand, hufsign,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp [hsign, hufsign]
  have hexp : cleared.toExpInt = uf.toExpInt := by
    simp only [UnpackedFloat.toExpInt, ← hcleared, UnpackedFloat.blastClearSignificand,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp only [hexp, ge_iff_le]
  have : cleared.sig.toNat ≤ uf.sig.toNat := by
    rw [← hcleared]
    apply UnpackedFloat.blastClearSignificand_sig_toNat_le
  suffices (cleared.sig.toNat : Rat) ≤ (uf.sig.toNat : Rat) by
    apply Rat.mul_le_mul_of_nonneg_right
    · simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]; grind only
    · grind only [Rat.le_of_lt, Rat.two_pow_pos]
  simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]
  grind only [UnpackedFloat.blastClearSignificand]



/-! # guardBitIndex -/

/--
The guard bit index when interpreted as a natural number
gives us the location of the guard bit inside the unpaked float.

The `hdiff*` hypotheses say that the exponent shift
`minNormalExp ep - x.ex.toInt` is representable at unpacked exponent width `eu`
and that the shifted guard position still lies inside the unpacked significand.
-/
theorem UnpackedFloat.toNat_guardBitIndex_eq (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    -- (heusu : eu ≤ su)
    :
    (x.guardBitIndex ep sp).toNat =
    (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat) := by
  have := @one_lt_exponentWidth ep sp
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)]
    · grind only
    · grind only
    · grind only

  rw [UnpackedFloat.guardBitIndex]
  rw [BitVec.toNat_add]
  simp
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      simp
      rw [Int.sub_toNat_eq_zero_of_le]
      · simp
        rw [Nat.mod_eq_of_lt]
        · have : su < 2 ^ su := by exact Nat.lt_two_pow_self
          grind only
      · grind only
    case isFalse h =>
      simp at h
      rw [Nat.mod_eq_of_lt]
      have : su < 2 ^ su := by exact Nat.lt_two_pow_self
      omega
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    exact hdiffLower
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    exact hdiffUpper

theorem BitVec.eq_iff_getLsbD_eq (a b : BitVec w) : a = b ↔
    (∀ (i : Nat), a.getLsbD i = b.getLsbD i) := by
  constructor
  · intros h
    subst h
    grind only
  · intros h
    ext i hi
    simp only [← BitVec.getLsbD_eq_getElem]
    grind only [#0a30]


/--
`p iff q` iff `not p iff not q`.
-/
theorem iff_iff_not_iff_not {p q : Prop} :
    (p ↔ q) ↔ (¬ p ↔ ¬ q) := by
  grind

/-! # extractIsEven -/

@[simp]
theorem UnpackedFloat.blastSuccessorAwayFromZerotIsEven_eq_isEven_lower_of_nonneg (x : UnpackedFloat e s)
    (hx : x.sign = false) :
    x.blastExtractIsEven e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat)) := by
  simp [UnpackedFloat.blastExtractIsEven]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem UnpackedFloat.blastExtractIsEven_eq_isEven_upper_of_neg (x : UnpackedFloat e s)
    (hx : x.sign = true) :
    x.blastExtractIsEven e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat)) := by
  simp [UnpackedFloat.blastExtractIsEven]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

/-! # extractGuardBit -/
theorem UnpackedFloat.blastExtractGuardBit_eq_true_iff
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.blastExtractGuardBit ep sp = true ↔
    x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat) := by
  simp [UnpackedFloat.blastExtractGuardBit]
  constructor
  · intros h
    obtain h := BitVec.ne_iff_getLsbD_ne .. |>.mp h
    obtain ⟨i, hi⟩ := h
    simp at hi
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at hi
    grind only
  · intros h
    intros hcontra
    obtain hcontra := BitVec.eq_iff_getLsbD_eq .. |>.mp hcontra
    simp at hcontra
    specialize hcontra _ h (by grind)
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at hcontra
    grind only
/--
The guard bit is the bit at the lower index at '2' (when `su = sp + 2`),
plus the offset from the exponent difference, which accounts for shifts when we are subnormal.
-/
theorem UnpackedFloat.extractGuardBit_eq_getLsbD
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.blastExtractGuardBit ep sp =  x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat)  := by
  have := UnpackedFloat.blastExtractGuardBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  grind only [#65b0223044fbdd80]

-- TODO: 'toRatSig' lemma about what the guardBit tracks.

@[simp]
theorem BitVec.and_allOnes_eq_self (bv : BitVec n) :
    bv &&& (BitVec.allOnes n) = bv := by
  ext UnpackedFloat.blastExtractGuardBit
  simp

@[simp]
theorem BitVec.allOnes_and_eq_self (bv : BitVec n) :
    (BitVec.allOnes n) &&& bv = bv := by
  ext i hi
  simp
/--
Zero extension to a larger width does not change the value.
-/
theorem BitVec.toNat_zeroExtend_of_le {n m : Nat} (bv : BitVec n) (h : n ≤ m) :
    (bv.zeroExtend m).toNat = bv.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le]
  grind only

/--
Zero extension to a smaller width does not change the value
if the value fits in the smaller size.
-/
theorem BitVec.toNat_zeroExtend_of_lt {n m : Nat} (bv : BitVec n) (h : bv.toNat  < 2 ^ m) :
    (bv.zeroExtend m).toNat = bv.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth]
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt]
  grind only

/--
Reducing a bitvector modulo `2^v` can be computed from either `toNat` or `toInt`,
provided `v` is no larger than the original width.
-/
theorem BitVec.toNat_mod_two_pow_of_toInt_of_le {w v : Nat} (x : BitVec w) (hle : v ≤ w) :
    (x.toInt % (2 ^ v : Nat)).toNat = x.toNat % 2 ^ v := by
  simp [BitVec.toInt]
  split
  · rw [Int.toNat_emod]
    · rw [show (2 ^ v : Int).toNat = 2 ^ v by exact Int.toNat_natCast _]
      rw [show ((x.toNat : Int).toNat) = x.toNat by exact Int.toNat_natCast _]
    · exact Int.natCast_nonneg _
    · exact Int.natCast_nonneg _
  · have hpowdvd : (2 ^ v : Int) ∣ (2 ^ w : Int) := by
      norm_cast
      exact Nat.pow_dvd_pow 2 hle
    have hmod :
        ((x.toNat : Int) - (2 ^ w : Int)) % (2 ^ v : Int) =
          (x.toNat : Int) % (2 ^ v : Int) := by
      rw [Int.sub_emod]
      have hzero : ((2 ^ w : Int) % (2 ^ v : Int)) = 0 := by
        exact Int.emod_eq_zero_of_dvd hpowdvd
      rw [hzero]
      simp
    change (((x.toNat : Int) - (2 ^ w : Int)) % (2 ^ v : Int)).toNat =
      x.toNat % 2 ^ v
    rw [hmod]
    rw [Int.toNat_emod]
    · rw [show (2 ^ v : Int).toNat = 2 ^ v by exact Int.toNat_natCast _]
      rw [show ((x.toNat : Int).toNat) = x.toNat by exact Int.toNat_natCast _]
    · exact Int.natCast_nonneg _
    · exact Int.natCast_nonneg _

/--
Truncating to a smaller width preserves `toInt` when the signed value already
fits in the target signed range.
-/
theorem BitVec.toInt_truncate_eq_of_toInt_range {w v : Nat} (x : BitVec w)
    (hv : 0 < v) (hle : v ≤ w)
    (hlo : -2 ^ (v - 1) ≤ x.toInt)
    (hhi : x.toInt < 2 ^ (v - 1)) :
    (x.truncate v).toInt = x.toInt := by
  rw [BitVec.truncate_eq_setWidth]
  have hset : x.setWidth v = BitVec.ofInt v x.toInt := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    exact (BitVec.toNat_mod_two_pow_of_toInt_of_le x hle).symm
  rw [hset]
  exact BitVec.toInt_ofInt_eq_self hv hlo hhi



theorem extractStickyBit_eq_true_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
  (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
  (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
  :
  x.blastExtractStickyBit ep sp = true ↔
    -- This makes sense,
    -- Consider when `su = sp + 2`.
    -- Then we're saying that some bit
    -- after the guard bit is nonzero.
     (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  simp [UnpackedFloat.blastExtractStickyBit]
  rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe]
  rw [show (su - 1 - (sp + 1)) = su - (sp + 2) by grind only]
  rw [show su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat =
       ((su + (minNormalExp ep - x.ex.toInt).toNat)) - (sp + 2) by grind only]
  · rw [show (su - (su + (minNormalExp ep - x.ex.toInt).toNat - (sp + 2))) =
        (sp + 2 - (minNormalExp ep - x.ex.toInt).toNat) by grind only]
    constructor
    · intros heq
      rw [BitVec.eq_iff_getLsbD_eq] at heq
      simp at heq
      obtain ⟨i, hi⟩ := heq
      exists i
      grind only
    · intros h
      simp at h
      intros hcontra
      rw [BitVec.eq_iff_getLsbD_eq] at hcontra
      simp at hcontra
      obtain ⟨i, hi⟩ := h
      specialize hcontra i (by grind)
      obtain ⟨hi1, hi2⟩ := hi
      grind
theorem extractStickyBit_eq_false_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
  (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
  (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
  :
  x.blastExtractStickyBit ep sp = false ↔
    -- This makes sense,
    -- This says that all the lower bits are false.
     (∀ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat →
      x.sig.getLsbD i = false) := by
  have htrue := extractStickyBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  rw [iff_iff_not_iff_not] at htrue
  grind only [#da50, #0b53, #b326]

/--
The sticky bit tracks whether there is a bit
below the guard bit that is 1.
This is equivalent to saying that there exists some bit below the guard bit that is 1.
-/
theorem UnpackedFloat.blastExtractStickyBit_eq_decide
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
  (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
  (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
  :
  x.blastExtractStickyBit ep sp = decide (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  by_cases hextract : x.blastExtractStickyBit ep sp = true
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
    grind only [#46e5, #0b53]
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
    simp at this
    grind only [#46e5, #0b53]


/-! # Normalization commutes with negation -/

/-- Negating an `UnpackedFloat` commutes with `normalize` (passing the negated sign). -/
@[simp]
theorem UnpackedFloat.neg_normalize_eq_neg_normalize (x : UnpackedFloat e s) :
    (-x).normalize = -(x.normalize) := by
  simp only [UnpackedFloat.neg_def, UnpackedFloat.normalize, UnpackedFloat.neg,
    UnpackedFloat.mkZero]
  by_cases h : x.sig = 0#s
  · simp only [h, beq_self_eq_true, cond_true]
  · have : (x.sig == 0#s) = false := by simp [h]
    simp only [this, cond_false]

/-- If `x` is already normalized, so is `-x`. -/
theorem UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq (x : UnpackedFloat e s)
    (hxnorm : x.normalize = x) :
    (-x).normalize = -x := by
  rw [UnpackedFloat.neg_normalize_eq_neg_normalize, hxnorm]

/-# `blastLowerNonneg` matches `lower`

## Plan

The goal is to show that the bit-blasted greatest-PF-≤-x circuit
(`blastLowerNonneg`) produces a value `Rel`-equivalent to the
non-computable spec `smtLibLower.lower (Number x.toRat')`.

Strategy: `smtLibLower.lower r` is defined via `Classical.epsilon`, so we
cannot reason about it directly. Instead we use uniqueness
(`eq_of_IsLawfulLower_of_IsLawfulLower`): any two non-NaN lawful lowers are
equal. Concretely, to show `result.Rel (smtLibLower.lower r)`, it suffices to
exhibit *some* `pf : PackedFloat ep sp` such that
  (a) `IsLawfulLower r pf`,
  (b) `result.num.toRat' = pf.toRat`,
  (c) `result.num.sign  = pf.sign`.
Together with `lsLawfulLower_smtLibLower` and `pf` not being NaN, uniqueness
forces `pf = smtLibLower.lower r`, giving the `Rel`.

This reduces the proof to three case-splits matching the structure of
`blastLowerNonneg`:
  • underflow branch — witness is `getZero ep sp false`
  • overflow  branch — witness is `maxNormalNumber ep sp false`
  • normal    branch — witness is the packed form of `blastRoundTowardZero`

Each case factors into:
  (i)  `IsLawfulLower (Number x.toRat') witness` (the hard, spec-side
       characterization), and
  (ii) `Rel`-matching of `toRat'`/`sign` (mostly bit-level rewriting).

The three (i)-style lemmas are the genuinely hard core; they are stated
below with clear specifications and left as `sorry` (matching the existing
PLAN_RNE.md "Tier 3" classification of these properties). -/

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
    (hToRat : result.num.toRat' = pf.toRat)
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
  sorry

/--
The unpacked `maxNormal` and packed `maxNormalNumber` agree under `toRat`.
-/
theorem UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber
    (eu su ep sp : Nat) (sign : Bool) :
    (UnpackedFloat.maxNormal eu su ep sp sign).toRat'
      = (PackedFloat.maxNormalNumber ep sp sign).toRat := by
  sorry

theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_overflow
    (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat ex sx)
    (hxsign : x.sign = false)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (EUnpackedFloat.mkNumber (UnpackedFloat.maxNormal eu su ep sp false)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  apply EUnpackedFloat.Rel_smtLibLower_of_witness
      (pf := PackedFloat.maxNormalNumber ep sp false)
      (he := by grind) (hs := hs)
  · simp
  · exact PackedFloat.not_isNaN_maxNormalNumber ep sp false (by grind)
  · exact isLawfulLower_Number_maxNormalNumber_of_overflowNonneg (by grind) hs x hxsign hover
  · -- `num.toRat'` of the unpacked `maxNormal` equals `toRat` of the packed `maxNormalNumber`.
    simp only [EUnpackedFloat.num_mkNumber]
    exact UnpackedFloat.toRat'_maxNormal_eq_toRat_maxNormalNumber _ _ _ _ false
  · -- sign is `false` on both sides
    simp [UnpackedFloat.maxNormal, PackedFloat.sign_maxNormalNumber]

/--
info: 'Fp.UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_overflow' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_overflow

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

/--
Key facts:

- the packed float will be the one given by 'blastLowerNonneg.pack'
- pack preserves the toRat, nor does it change the sign
- we need a lemma that says that it's a lawful lower if the 'toRat' is equal, and then distance
  btween 'pf.toRat' and 'x.toRat' is less than 1 ulp of 'pf' (which is the same as 1 ulp of 'blastRoundTowardZero x').
  This needs a separate lemma or two.
- These key facts establish the existence of the 'pf'.
- TODO: maybe worth it to replace the existential with the concrete pf we know.
-/
theorem UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
    (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    ∃ pf : PackedFloat ep sp,
      ¬ pf.isNaN ∧
      SmtLibSemantics.IsLawfulLower (ExtRat.Number x.toRat') pf ∧
      (x.blastRoundTowardZero ep sp).toRat' = pf.toRat ∧
      (x.blastRoundTowardZero ep sp).sign  = pf.sign := by
  sorry

theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal
    (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s)
    (hxsign : x.sign = false)
    (hxnorm : x.normalize = x)
    (hnotunder : x.blastIsUnderflowNonneg ep sp = false)
    (hnotover  : x.blastIsEarlyOverflowNonneg ep sp = false) :
    (EUnpackedFloat.mkNumber (x.blastRoundTowardZero ep sp) :
      EUnpackedFloat e (sp+1)).Rel
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  obtain ⟨pf, hpfNotNaN, hpfLower, hToRat, hSign⟩ :=
    UnpackedFloat.exists_packedFloat_isLawfulLower_of_blastRoundTowardZero
      he hs x hxsign hxnorm hnotunder hnotover
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
theorem UnpackedFloat.blastLowerNonneg_Rel_smtLibLower (he : 1 < ep) (hs : 0 < sp)
  (x : UnpackedFloat eu su)
  (hxsign : x.sign = false)
  (hxnorm : x.normalize = x) :
  (x.blastLowerNonneg ep sp).Rel (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  unfold UnpackedFloat.blastLowerNonneg
  by_cases hunder : x.blastIsUnderflowNonneg ep sp = true
  · simp [hunder]
    exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_underflow he hs x hxsign hunder
  · simp only [Bool.not_eq_true] at hunder
    simp [hunder]
    by_cases hover : x.blastIsEarlyOverflowNonneg ep sp = true
    · simp [hover]
      -- apply UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_overflow
      apply blastLowerNonneg_Rel_smtLibLower_overflow he hs x
      · grind only
      · grind only
      · grind only
    · simp only [Bool.not_eq_true] at hover
      simp [hover]
      exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal he hs x hxsign hxnorm hunder hover

/-# `blastUpperNonneg` matches `upper` -/

theorem UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper (he : 1 < ep) (hs : 0 < sp)
  (x : UnpackedFloat eu su)
  (hxsign : x.sign = false) :
  (x.blastUpperNonneg ep sp).Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat') : PackedFloat ep sp) := by
  simp [UnpackedFloat.blastUpperNonneg]
  sorry


/-# `blastLower` matches `lower` -/

theorem UnpackedFloat.blastLower_Rel_smtLibLower (he : 1 < ep) (hs : 0 < sp)
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
    · simp [hsign]
    · exact hxnorm


/-# `blastUpper` matches `upper` -/


theorem UnpackedFloat.blastUpper_Rel_smtLibUpper (he : 1 < ep) (hs : 0 < sp)
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
      · simp [hsign]
      · exact UnpackedFloat.normalize_neg_eq_neg_of_normalize_eq x hxnorm
    · grind only
    · grind only
    · grind only
  · simp [hsign]
    apply UnpackedFloat.blastUpperNonneg_Rel_smtLibUpper
    · grind only
    · grind only
    · simp [hsign]

/-# blastIsEvenUpper, blastIsEvenLower -/

theorem blastIsEvenUpper_iff_smtLibIsEven_upper (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenUpper ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat')) = true := by
  simp [UnpackedFloat.blastIsEvenUpper]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

theorem blastIsEvenLower_iff_smtLibIsEven_lower (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenLower ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')) = true := by
  simp [UnpackedFloat.blastIsEvenLower]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

/-# blastIsOverflowNonneg -/

@[simp]
theorem UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide  (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) :
    x.blastIsEarlyOverflowNonneg ep sp = decide (maxNormalExp ep < x.ex.toInt) := by
  simp [UnpackedFloat.blastIsEarlyOverflowNonneg]
  rw [BitVec.slt_eq_decide]
  rw [toInt_ofInt_maxNormalExp_eq_maxNormalExp_of_le (w := eu) he hs]
  · grind only

/-# blastIsUnderflowNonneg -/

@[simp]
theorem UnpackedFloat.blastUnderflowNonneg_eq_decide (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) :
    x.blastIsUnderflowNonneg ep sp = decide (x.ex.toInt < minSubnormalExp ep sp) := by
  simp [UnpackedFloat.blastIsUnderflowNonneg]
  rw [BitVec.slt_eq_decide]
  rw [toInt_ofInt_minSubnormalExp_eq_minSubnormalExp_of_le (w := eu) he hs]
  · grind only

/-# blastIsEarlyUnderflowNonneg -/

@[simp]
theorem UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) :
    x.blastIsEarlyUnderflowNonneg ep sp = decide (x.ex.toInt < minSubnormalExp ep sp - 1) := by
  simp [UnpackedFloat.blastIsEarlyUnderflowNonneg]
  rw [BitVec.slt_eq_decide]
  rw [toInt_ofInt_minSubnormalExp_sub_one_eq_minSubnormalExp_sub_one_of_le (w := eu) he hs]
  · grind only

/-# blastIsLowerHalf -/

@[simp]
theorem blastIsLowerHalf_iff_smtLibLowerHalf  (he : 1 < ep) (hs : 0 < sp)  (x : UnpackedFloat e s)  :
    (x.blastIsLowerHalf ep sp = true) ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')
    := by
  simp [UnpackedFloat.blastIsLowerHalf]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem blastTieBreak_iff_smtLibTieBreak (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') := by
  simp [UnpackedFloat.blastIsTieBreak]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry



/-# `blastRounderForSign` matches `rounderForSign`-/


@[simp]
theorem UnpackedFloat.blastRounderForSign_of_sign_eq_true_eq
    (x : UnpackedFloat eu su)
    (hsign : x.sign = true) :
    x.blastRounderForSign ep sp = x.blastUpper ep sp := by
  simp [UnpackedFloat.blastRounderForSign, hsign]

theorem UnpackedFloat.blastRounderForSign_of_sign_eq_false_eq
    (x : UnpackedFloat eu su)
    (hsign : x.sign = false) :
    x.blastRounderForSign ep sp = x.blastLower ep sp := by
  simp [UnpackedFloat.blastRounderForSign, hsign]


theorem UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero (he : 1 < ep) (hs : 0 < sp)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hx0 : x.isZero) :
  (x.blastRounderForSign ep sp).Rel
    ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).rounderForSign x.sign
        (ExtRat.Number 0)) := by
  by_cases hsign : x.sign
  · simp [hsign]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact (UnpackedFloat.blastUpper_Rel_smtLibUpper he hs x hxnorm)
  · simp [hsign]
    rw [UnpackedFloat.blastRounderForSign_of_sign_eq_false_eq x (by grind)]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact
      (UnpackedFloat.blastLower_Rel_smtLibLower he hs x hxnorm)

/--
info: 'Fp.UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero

/-# normalize -/

/--
`normalize` preserves `Rel`, provided normalizing does not underflow the
exponent. The precondition `hssub` is "the BitVec subtraction `ex - clz` does
not signed-underflow at width `eu`"; semantically this is the "no underflow at
normalize" condition. At the call sites this should follow from being in the
`¬ blastIsOverflowNonneg` branch combined with the value fitting in the
destination `(ep, sp)` format — but discharging that derivation is a separate
sorry to fill.
-/
theorem UnpackedFloat.normalize_Rel_of_Rel (_he : 1 < ep) (_hs : 0 < sp)
    (_heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su) (pf : PackedFloat ep sp)
    (hse : su - 1 < 2 ^ (eu - 1))
    (hssub : !x.ex.ssubOverflow (BitVec.setWidth eu x.sig.clz))
    (h : x.Rel pf) :
    x.normalize.Rel pf := by
  obtain ⟨hToRat, hSign⟩ := h
  apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
  · rw [← UnpackedFloat.toRat_eq_toRat',
        UnpackedFloat.toRat_normalize_eq_toRat hse hssub,
        UnpackedFloat.toRat_eq_toRat']
    exact hToRat
  · simp only [UnpackedFloat.sign_normalize, beq_iff_eq, ite_self]
    exact hSign

/--
info: 'Fp.UnpackedFloat.normalize_Rel_of_Rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.normalize_Rel_of_Rel

theorem EUnpackedFloat.normalize_Rel_of_Rel (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : EUnpackedFloat eu su) (pf : PackedFloat ep sp)
    (hse : su - 1 < 2 ^ (eu - 1))
    (hssub : !x.num.ex.ssubOverflow (BitVec.setWidth eu x.num.sig.clz))
    (h : x.Rel pf) :
    x.normalize.Rel pf := by
  unfold EUnpackedFloat.normalize
  rcases hstate : x.state with rfl | rfl | rfl
  · simp [hstate, h]
  · simp [hstate, h]
  · simp [hstate]
    have hnumNorm :=
      UnpackedFloat.normalize_Rel_of_Rel he hs heu x.num pf hse hssub (by
        grind only [EUnpackeDFloat.num_Rel_of_Rel_of_eq_Number]
      )
    exact
      EUnpackedFloat.Rel_of_Rel_of_state_eq_Number x.num.normalize.toEUnpackedFloat pf rfl hnumNorm
/--
info: 'Fp.EUnpackedFloat.normalize_Rel_of_Rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms EUnpackedFloat.normalize_Rel_of_Rel


/-# truncateFittingExponent -/


/--
truncateFittingExponent does not change the sign.
-/
@[simp]
theorem sign_truncateFittingExponent
  (x : UnpackedFloat eu su) :
  (x.truncateFittingExponent ep sp).sign = x.sign := by
  simp [UnpackedFloat.truncateFittingExponent]

/--
truncateFittingExponent does not change the significand.
-/
@[simp]
theorem sig_truncateFittingExponent (x : UnpackedFloat eu su) :
    (x.truncateFittingExponent ep sp).sig = x.sig := by
  simp [UnpackedFloat.truncateFittingExponent]


/--
truncateFittingExponent doesn't change the value of the exponent
when we don't have early over and underflow.
-/
theorem toExpInt_truncateFittingExponent_of_not_blastIsOverflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).toExpInt = x.toExpInt := by
  simp [UnpackedFloat.truncateFittingExponent, UnpackedFloat.toExpInt]
  have hnotover' := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
  simp [hnotover] at hnotover'
  have hnotunder' := UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x
  simp [hnotunder] at hnotunder'

  rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le]
  · rw [Int.bmod_eq_of_le]
    · simp
      -- TODO: also need to check for underflow?
      have := x.ex.le_toInt
      have : 2 ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) := by
        apply Nat.two_pow_le_two_pow_of_le (by grind)
      apply Int.le_trans (b := minSubnormalExp ep sp - 1)
      · have := neg_two_pow_exponentWidth_lt_minSubnormalExp he hs
        grind only
      · grind only
    · simp; sorry
  · grind only

/--
If we have not overflowed, then `truncateFittingExponent` does not change the value of `toRat`.
-/
@[simp]
theorem UnpackedFloat.toRat_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (notunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).toRat = x.toRat := by
  simp [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat']
  rw [toExpInt_truncateFittingExponent_of_not_blastIsOverflowNonneg] <;> grind only


/--
info: 'Fp.UnpackedFloat.toRat_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg

/-
Round g anumber that's larger than max normal exp gives maxNormalExp as the result.
-/
theorem roundRNE_eq_infinity_of_lt_maxNormalExp
  {ep sp eu su : Nat}
  (he : 1 < ep)
  (hs : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hxnorm : x.normalize = x)
  (hover : maxNormalExp ep < x.ex.toInt) :
    (EUnpackedFloat.mkInfinity x.sign : EUnpackedFloat eu su).Rel
      ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE x.sign
        (ExtRat.Number x.toRat)) := by
  simp only [SmtLibSemantics.RoundMethod.roundRNE, SmtLibSemantics.instExtendedRat.isNaN_eq,
    ExtRat.isNaN_iff, ExtRat.ExtRat.NaN_le_iff, decide_eq_true_eq, ExtRat.ExtRat.le_refl,
    reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte,
    SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number.injEq,
    SmtLibSemantics.smtLibRoundMethod, SmtLibSemantics.smtLibV_lower_eq,
    SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', Nat.zero_lt_succ,
    SmtLibSemantics.instExtendedRat.smtLibEq, SmtLibSemantics.smtLibV_upper_eq, eq_iff_iff,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.decide_iff_dist,
    beq_eq_false_iff_ne, ne_eq, decide_eq_decide,
    SmtLibSemantics.isEven_roundableIsEven_of_packedFloat, beq_iff_eq,
    EUnpackedFloat.state_mkInfinity]
  -- TODO: this needs to argue that the sig is nonzero in this case.
  sorry

/--
Since 'truncateFittingExponent' does not change the significand,
it preserves being normalized.
-/
theorem normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
  (he : 1 < ep) (hs : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hxnorm : x.normalize = x) :
    (x.truncateFittingExponent ep sp).normalize = x.truncateFittingExponent ep sp := by
  apply UnpackedFloat.normalize_eq_self_of_msb_eq_true
  simp only [sig_truncateFittingExponent]
  sorry

/--
since truncateFittingExponent does not change the significand, it preserves being zero.
-/
theorem isZero_truncateFittingExponent_eq_isZero
    (x : UnpackedFloat eu su) :
    (x.truncateFittingExponent ep sp).isZero = x.isZero := by
  simp [UnpackedFloat.isZero, UnpackedFloat.truncateFittingExponent]


/-# `blastSmtLibRound` matches `smtLibRound` for RNE rounding mode. -/

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.

This is what I'm working on right now.

TODO: Refactor proof to case split on x.isZero, and then derive that y.isZero from this.
-/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (hsign : sign = x.sign)
    (r : Rat) (hr : r = x.toRat)
    (hxnorm : x.normalize = x) :
    (x.blastSmtLibRound ep sp .RNE  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE
        sign (ExtRat.Number r)) := by
  sorry
/-
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
  · simp [hover]
    rw [blastIsEarlyOverflowNonneg_eq_decide he hs heu x] at hover
    simp at hover
    simp [blastRounderSpecialCaseOverflow]
    sorry
  · simp [hover]
    rw [blastIsEarlyOverflowNonneg_eq_decide he hs heu x] at hover
    simp at hover
    simp only [UnpackedFloat.blastSmtLibRoundAux]
    simp only [SmtLibSemantics.RoundMethod.roundRNE, SmtLibSemantics.instExtendedRat.isNaN_eq,
      ExtRat.isNaN_iff,
      reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number.injEq,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq,
      SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
    rw [UnpackedFloat.blastSmtLibRoundRNE]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      UnpackedFloat.toRat_eq_toRat']
    simp
    by_cases hunder : x.blastIsEarlyOverflowNonneg ep
    generalize hy : x.truncateFittingExponent ep sp = y
    by_cases hy0 : y.isZero
    · simp [hy0, ↓reduceIte, UnpackedFloat.toRat'_eq_zero_of_isZero, not_true_eq_false,
      false_and]
      have hx0 :  x.isZero = true := by sorry
      simp [hx0]
-- Fixup the proof in 'toExtRat_round_Rel_smtLibRound_of_RNE' where you correctly write a lemma that says that in the case where there's no overflow, 'truncateFittingExponent' does not
--   change the toRat nor does it change the sign, and thus continues to be a Rel. This enables the rest of the place to go through, substituting x for y in Fp/UnpackedRound.lean in proof
--   theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
      apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
      have hy0' : y.toRat' = 0 := by grind only [=> UnpackedFloat.toRat'_eq_zero_of_isZero]
      have hx0' : x.toRat' = 0 := by sorry
      have hxsign : x.sign = y.sign := by sorry
      rw [hxsign]
      -- apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
      apply UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero (x := y) (by grind) (by grind)
      · subst y
        apply normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
        · exact he
        · exact hs
        · grind only
        · grind only
        · grind only
      · grind only
    · simp [hy0]
      have hx0 : x.isZero = true := by sorry
      simp [hx0]
      have hx0' : x.toRat' ≠ 0 := by sorry
      by_cases hlowerhalf : x.blastIsLowerHalf ep sp
      · have hlowerHalf' := blastIsLowerHalf_iff_smtLibLowerHalf he hs x |>.mp hlowerhalf
        simp [hlowerhalf, hlowerHalf']
        by_cases htiebreak : x.blastIsTieBreak ep sp
        · have htiebreak' := blastTieBreak_iff_smtLibTieBreak he hs x |>.mp htiebreak
          simp [htiebreak, htiebreak']
          by_cases hevenupper : x.blastIsEvenUpper ep sp
          · have hevenupper' := blastIsEvenUpper_iff_smtLibIsEven_upper he hs x |>.mp hevenupper
            simp [hevenupper, hevenupper']
            apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
            apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
            exact UnpackedFloat.blastUpper_Rel_smtLibUpper (by grind) (by grind) _ hxnorm
          · have hevenupper' := blastIsEvenUpper_iff_smtLibIsEven_upper he hs x
            simp [hevenupper] at hevenupper'
            simp [hevenupper, hevenupper']
            apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
            apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
            exact UnpackedFloat.blastLower_Rel_smtLibLower (by grind) (by grind) _ hxnorm
        · have htiebreak' := blastTieBreak_iff_smtLibTieBreak he hs x
          simp [htiebreak] at htiebreak'
          simp [htiebreak, htiebreak']
          apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
          apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
          exact UnpackedFloat.blastLower_Rel_smtLibLower (by grind) (by grind) _ hxnorm
      · have hlowerHalf' := blastIsLowerHalf_iff_smtLibLowerHalf he hs x
        simp [hlowerhalf] at hlowerHalf'
        simp [hlowerhalf, hlowerHalf']
        by_cases htiebreak : x.blastIsTieBreak ep sp
        · have htiebreak' := blastTieBreak_iff_smtLibTieBreak he hs x |>.mp htiebreak
          simp [htiebreak, htiebreak']
          by_cases hevenupper : x.blastIsEvenUpper ep sp
          · have hevenupper' := blastIsEvenUpper_iff_smtLibIsEven_upper he hs x |>.mp hevenupper
            simp [hevenupper, hevenupper']
            apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
            apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
            exact UnpackedFloat.blastUpper_Rel_smtLibUpper (by grind) (by grind) _ hxnorm
          · have hevenupper' := blastIsEvenUpper_iff_smtLibIsEven_upper he hs x
            simp [hevenupper] at hevenupper'
            simp [hevenupper, hevenupper']
            by_cases hevenlower : x.blastIsEvenLower ep sp
            · have hevenlower' := blastIsEvenLower_iff_smtLibIsEven_lower he hs x |>.mp hevenlower
              simp [hevenlower, hevenlower']
              apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
              apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
              exact UnpackedFloat.blastLower_Rel_smtLibLower (by grind) (by grind) _ hxnorm
            · have hevenlower' := blastIsEvenLower_iff_smtLibIsEven_lower he hs x
              simp [hevenlower] at hevenlower'
              simp [hevenlower, hevenlower']
              apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
              apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
              apply EUnpackedFloat.Rel_of_isNaN_of_isNaN
              · simp
              · simp
        · have htiebreak' := blastTieBreak_iff_smtLibTieBreak he hs x
          simp [htiebreak] at htiebreak'
          simp [htiebreak, htiebreak']
          apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by sorry) (by sorry)
          apply EUnpackedFloat.truncateFittingExponent_Rel_of_Rel_of_toInt_trunc_eq (by grind) (by grind) (by grind) _ _ (by sorry)
          exact UnpackedFloat.blastUpper_Rel_smtLibUpper (by grind) (by grind) _ hxnorm
-/
end Fp
