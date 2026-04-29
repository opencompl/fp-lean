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

def EquivUptoNaN {e s : Nat} (x y : PackedFloat e s) : Prop :=
  x = y ∨ (x.isNaN ∧ y.isNaN)

theorem EquivUptoNaN.of_isNaN_isNaN (x y : PackedFloat e s) (hx : x.isNaN) (hy : y.isNaN) : EquivUptoNaN x y :=
  by simp [EquivUptoNaN, hx, hy]

theorem EquivUptoNaN.of_eq (x y : PackedFloat e s) (h : x = y) : EquivUptoNaN x y := by simp [EquivUptoNaN, h]

@[simp]
theorem EquivUptoNaN.of_mkNaN_iff (x : PackedFloat e s) : EquivUptoNaN x (PackedFloat.getNaN e s) ↔ x.isNaN := by
  simp [EquivUptoNaN]
  grind only [!PackedFloat.isNaN_mkNaN]


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

/-- For a nonnegative unpacked float, the error from clearing guard/sticky bits is bounded by
    2^(guardBitIdx + 1) ULPs at the significand level, i.e.,
    `x.toRat - cleared.toRat < 2^(guardBitIdx + 1) UnpackedFloat.blastClearSignificand
    This is the ULP of the target precision. -/
theorem clearSignificand_toRat_sub_lt (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : 0 ≤ uf.toRat) :
    uf.toRat - (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).toRat <
      (2 : Rat) ^ ((uf.guardBitIndex targetExponentWidth targetSignificandWidth).toNat + 1) *
      (2 : Rat) ^ uf.toExpInt := by
  sorry

/--
The result of 'clearSignificand' results in an unpacked float
that can be represented in the target format, and has the same rational value as some `PackedFloat`.
-/
theorem exists_packedFloat_toRat_eq_clearSignificand_toRat (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    ∃ (pf : PackedFloat targetExponentWidth targetSignificandWidth),
      pf.toRat = (uf.blastClearSignificand targetExponentWidth targetSignificandWidth).toRat := by
  sorry


/-! # guardBitIndex -/

/--
The guard bit index when interpreted as a natural number
gives us the location of the guard bit inside the unpaked float.
sorry
-/
theorem UnpackedFloat.toNat_guardBitIndex_eq (hep : 1 < ep) (hsp : 0 < sp)
    -- TODO: I need a bound on `x.ex` to be at most `maxNormalExp`.
    -- TODO: I need a bound on `x.ex` to be at least `minSubnormalExp`.
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    -- (heusu : eu ≤ su)
    (x : UnpackedFloat eu su) :
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
      sorry
  · grind only
  · have := neg_two_pow_le_minNormalExp hep hsp heu
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    -- | This needs bounds on `minSubnormalExp ≤ x.ex.toInt` to prove this.
    -- ⊢ -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt
    sorry
  · have := minNormalExp_lt_two_pow hep hsp heu
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    --  This needs bounds on `x.ex.toInt ≤ maxNormalExp` to prove this.
    -- ⊢ minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1)
    sorry

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


/-! # roundTowardZero -/

theorem toRat_blastRoundTowardZero_eq_smtLibLower_of_nonneg (x : UnpackedFloat e s)
    (hx : 0 ≤ x.toRat) :
    (x.blastRoundTowardZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

theorem toRat_blastRoundTowardZero_eq_smtLibUpper_of_neg (x : UnpackedFloat e s)
    (hx : x.toRat < 0) :
    (x.blastRoundTowardZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry


/-# successorAwayFromZero -/

theorem UnpackedFloat.blastRoundTowardZerorAwayFromZero_eq_smtLibUpper_of_nonneg (x : UnpackedFloat e s)
    (hx : 0 ≤ x.toRat) :
    (x.blastSuccessorAwayFromZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

theorem UnpackedFloat.blastRoundTowardZerorAwayFromZero_eq_smtLibLower_of_neg (x : UnpackedFloat e s)
    (hx : x.toRat < 0) :
    (x.blastSuccessorAwayFromZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

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
    (x : UnpackedFloat eu su) :
    x.blastExtractGuardBit ep sp = true ↔
    x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat) := by
  simp [UnpackedFloat.blastExtractGuardBit]
  constructor
  · intros h
    obtain h := BitVec.ne_iff_getLsbD_ne .. |>.mp h
    obtain ⟨i, hi⟩ := h
    simp at hi
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu] at hi
    grind only
  · intros h
    intros hcontra
    obtain hcontra := BitVec.eq_iff_getLsbD_eq .. |>.mp hcontra
    simp at hcontra
    specialize hcontra _ h (by grind)
    rw [UnpackedFloat.toNat_guardBitIndex_eq hep hsp heu hsu] at hcontra
    grind only
/--
The guard bit is the bit at the lower index at '2' (when `su = sp + 2`),
plus the offset from the exponent difference, which accounts for shifts when we are subnormal.
-/
theorem UnpackedFloat.extractGuardBit_eq_getLsbD
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) :
    x.blastExtractGuardBit ep sp =  x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat)  := by
  have := UnpackedFloat.blastExtractGuardBit_eq_true_iff hep hsp heu hsu x
  grind only [#65b0223044fbdd80]

-- TODO: 'toRatSig' lemma about what the guardBit tracks.

theorem SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq_decide (r : Rat) :
    (smtLibRoundMethod e s smtLibV smtLibV).lowerHalf (ExtRat.Number r) =
    (r - ((smtLibRoundMethod e s smtLibV smtLibV).lower (ExtRat.Number r)).toRat ≤ 2^e) := by
  -- TODO: this is what I need to prove now.
  sorry

-- theorem le_toRatSig_of_extractGuardBit

@[simp]
theorem UnpackedFloat.blastExtractGuardBit_eq_not_lowerHalf_of_nonneg (x : UnpackedFloat e s)
    (hx : x.sign = false) :
    x.blastExtractGuardBit e s = ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat) := by
  -- simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem UnpackedFloat.blastExtractGuardBit_eq_smtLibLowerHalf_of_neg (x : UnpackedFloat e s)
    (hx : x.sign = true) :
    x.blastExtractGuardBit e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat) := by
  simp [UnpackedFloat.blastExtractGuardBit]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

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



theorem extractStickyBit_eq_true_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su) :
  x.blastExtractStickyBit ep sp = true ↔
    -- This makes sense,
    -- Consider when `su = sp + 2`.
    -- Then we're saying that some bit
    -- after the guard bit is nonzero.
     (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  simp [UnpackedFloat.blastExtractStickyBit]
  rw [UnpackedFloat.toNat_guardBitIndex_eq]
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
  · grind only
  · grind only
  · grind only
  · grind only

theorem extractStickyBit_eq_false_iff
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su) :
  x.blastExtractStickyBit ep sp = false ↔
    -- This makes sense,
    -- This says that all the lower bits are false.
     (∀ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat →
      x.sig.getLsbD i = false) := by
  have htrue := extractStickyBit_eq_true_iff hep hsp heu hsu x
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
  (x : UnpackedFloat eu su) :
  x.blastExtractStickyBit ep sp = decide (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  by_cases hextract : x.blastExtractStickyBit ep sp = true
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x
    grind only [#46e5, #0b53]
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x
    simp at this
    grind only [#46e5, #0b53]

@[simp]
theorem UnpackedFloat.blastExtractStickyBit_eq_not_tieBreak_of_nonneg_of_guardBit
    (he : 1 < ep)
    (hs : 0 < sp)
    (hsu : sp + 2 ≤ su)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hx : x.sign = false)
    (hguard : x.blastExtractGuardBit ep sp = true) :
    x.blastExtractStickyBit ep sp = ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat) := by
  simp [SmtLibSemantics.smtLibRoundMethod]
  rw [blastExtractStickyBit_eq_decide]
  · sorry
  · grind only
  · grind only
  · grind only
  · grind only

/-# IsEven and IsOdd -/


/--UnpackedFloat.blastExtractGuardBit
isEvenUnpackedFloat.blastExtractStickyBiteen numbers.
-/
theorem isEven_lower_eq_not_isEven_upper (eout sout : Nat) (r : Rat) :
  (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r)) =
  ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)) := by
  simp [SmtLibSemantics.smtLibRoundMethod]

  -- ned a precondition that lower != upper
  sorry

theorem isEven_upper_eq_not_isEven_lower (eout sout : Nat) (r : Rat) :
  (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)) =
  ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r)) := by
  have := isEven_lower_eq_not_isEven_upper eout sout r
  grind only [#9ad2]


/-# Rounding decision in terms of computable definitions -/


-- TDOO: add a 'computableRoundingDecision.

theorem round_eq_ite_roundingDecision_of_Number_of_nonneg {eout sout : Nat} (rm : RoundingMode)
    (sign : Bool)
    (isEven : Bool)
    (guard : Bool)
    (sticky : Bool)
    (_exact : Bool)
    (r : Rat)
    (hguardsticky : guard = false → sticky = false →
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout) = SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)
    )
    (hguard : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) = (guard = false))
    (htiebreak : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) = (guard = true ∧ sticky = false))
    (heven : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r)) = isEven)
    (hz : r ≠ 0)
    (hsign : sign = (r < 0))
    (hr : 0 ≤ r)
    :
    ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
    (ExtRat.Number r) : PackedFloat eout sout) =
    if roundingDecision rm sign isEven guard sticky _exact then
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper (ExtRat.Number r)
    else
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower  (ExtRat.Number r) := by
  simp [show ¬ r < 0 by grind only] at hsign
  subst hsign
  cases rm <;> simp [roundingDecision]
  case RNE =>
    simp only [SmtLibSemantics.RoundMethod.roundRNE]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · -- guard = false
      simp only [↓reduceIte, Bool.false_eq_true, false_and]
      simp at htiebreak
      simp [htiebreak]
    · -- guard = true
      simp only [Bool.true_eq_false, ↓reduceIte, true_and, ite_not]
      rcases sticky with rfl | rfl
      · -- tiebreak = false
        simp [htiebreak]
        simp [heven]
        rcases isEven with rfl | rfl
        · simp
          -- I need a theorem that says that if lower is not even then upper is.
          intros hupper
          -- isEven cannot be both true and false.
          have hcontra := isEven_upper_eq_not_isEven_lower eout sout r
          grind only
        · simp
          intros heven
          have hcontra := isEven_upper_eq_not_isEven_lower eout sout r
          grind only
      · -- tiebreak = true
        simp [htiebreak]
  case RNA =>
    -- This rounding mode is broken, I seem to have confused lower and upper!
    simp only [SmtLibSemantics.RoundMethod.roundRNA]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · -- guard = false
      simp
      intros hr
      have hrlt : r < 0 := by grind only
      grind only
    · -- guard = true
      simp
      intros hrle
      grind only
  case RTP =>
    simp only [SmtLibSemantics.RoundMethod.roundRTP]
    simp [hz]
    intros hguard hsticky
    rw [hguardsticky]
    · grind only
    · grind only
  case RTN =>
    simp only [SmtLibSemantics.RoundMethod.roundRTN]
    simp [hz]
  case RTZ =>
    simp only [SmtLibSemantics.RoundMethod.roundRTZ]
    simp [hz]
    intros hrlezero
    have hcontra : r = 0 := by grind only
    grind only

/--
When negative, the guard, stick, and isEven interpretations change.
- isEven tells us when the upper is even.
- guard bit tells us when we are in the lower half, since it is 'more negative'.
-/
theorem round_eq_ite_roundingDecision_of_Number_of_neg {eout sout : Nat} (rm : RoundingMode)
    (sign : Bool)
    (isEven : Bool)
    (guard : Bool)
    (sticky : Bool)
    (_exact : Bool)
    (r : Rat)
    (hguardsticky : guard = false → sticky = false →
      (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat eout sout) = SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)
    )
    -- | in the negative case, we are in the lower half when guard is true,
    -- since we are closer to lower than upp.er
    (hguard :
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r) =
      (guard = true))
    (htiebreak : (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r) = (guard = true ∧ sticky = false))
    (heven : (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r)) = isEven)
    (hz : r ≠ 0)
    (hsign : sign = (r < 0))
    (hr : r < 0)
    :
    ((SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign
    (ExtRat.Number r) : PackedFloat eout sout) =
    if roundingDecision rm sign isEven guard sticky _exact then
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower (ExtRat.Number r)
    else
      (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper  (ExtRat.Number r) := by
  simp [show r < 0 by grind only] at hsign
  subst hsign
  cases rm <;> simp [roundingDecision]
  case RNE =>
    simp only [SmtLibSemantics.RoundMethod.roundRNE]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · simp
      intros htiebreak'
      simp at htiebreak
      grind only
    · simp
      rcases sticky with rfl | rfl
      · -- tiebreak = false
        simp [htiebreak]
        simp at htiebreak
        simp at hguard
        simp at hguardsticky
        rcases isEven with rfl | rfl
        · simp
          intros isEven
          grind only
        · simp
          intros hevenUpper
          grind only
      · -- tiebreak = true
        simp [htiebreak]
  case RNA =>
    -- This rounding mode is broken, I seem to have confused lower and upper!
    simp only [SmtLibSemantics.RoundMethod.roundRNA]
    simp [hz]
    simp [hguard]
    rcases guard with rfl | rfl
    · simp [show ¬ 0 < r by grind only]
      simp [hr]
      intros htiebreak
      simp [htiebreak]
      grind only
    · simp [show ¬ 0 < r by grind only]
      intros hr
      grind only
  case RTP =>
    simp only [SmtLibSemantics.RoundMethod.roundRTP]
    simp [hz]
  case RTN =>
    simp only [SmtLibSemantics.RoundMethod.roundRTN]
    simp [hz]
    intros hguard hsticky
    apply hguardsticky
    · grind only
    · grind only
  case RTZ =>
    simp only [SmtLibSemantics.RoundMethod.roundRTZ]
    simp [hr]
    intros hr
    grind only

theorem isBlastOverflowNonneg_iff (x : UnpackedFloat e s) :
  x.blastIsOverflowNonneg ep sp = true ↔ (PackedFloat.maxNormalNumber ep sp false).toRat < x.toRat := by sorry


/-# `blastUpper` matches `upper` -/

/--
This tells us that `blastUpper` gives an unpacked float
which represents the same packed float as the SMT-LIB `upper` function on zero.
-/
theorem UnpackedFloat.blastUpper_zero_Rel
    (x : UnpackedFloat e s)
    (hep : 1 < ep) (hsp : 0 < sp)
    (hx : x.isZero) :
    (x.blastUpper ep sp).Rel (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number 0) : PackedFloat ep sp) := by
  rw [upper_zero_eq (by grind only)]
  sorry


/-# `blastLower` matches `lower` -/


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


theorem blastRounderForSign_eq_smtLibRounderForSign (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) :
  (x.blastRounderForSign ep sp).truncateFittingExponent.normalize =
    ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).rounderForSign x.sign
        (ExtRat.Number 0)).unpack := by
  by_cases hsign : x.sign
  · simp [hsign]
    sorry
  · simp [hsign]
    sorry


/-# `blastSmtLibRound` matches `smtLibRound` for RNE rounding mode. -/

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.

This is what I'm working on right now.
-/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (rstar : Rat) -- rational number we are modelling.
    (hx : (rstar - hx).abs < (2 : Rat) ^ (-((sp + 1) : Int))) -- the rational is within 0.5 ulp of the unpacked float.
    -- | The sticky bitt tracks whether 'r' is exactly representable.
    -- (hsticky : (∃ (pf : PackedFloat ep sp), pf.toRat = rstar)  x.extractStickyBit ep sp = false)
      :
    (x.blastSmtLibRound ep sp .RNE  : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE x.sign (ExtRat.Number x.toRat)) := by
  rw [UnpackedFloat.blastSmtLibRound]
  by_cases hover : x.blastIsOverflowNonneg ep sp
  · simp [hover]
    have := isBlastOverflowNonneg_iff x |>.mp hover
    simp [blastRounderSpecialCaseOverflow]
    sorry
  · simp [hover]
    simp only [UnpackedFloat.blastSmtLibRoundAux]
    simp only [SmtLibSemantics.RoundMethod.roundRNE, SmtLibSemantics.instExtendedRat.isNaN_eq,
      ExtRat.isNaN_iff, ExtRat.ExtRat.NaN_le_iff, decide_eq_true_eq, ExtRat.ExtRat.le_refl,
      reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def, ExtRat.Number.injEq,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, hs,
      SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq,
      SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
    rw [UnpackedFloat.blastSmtLibRoundRNE]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      UnpackedFloat.toRat_eq_toRat']
    by_cases hx0 : x.isZero
    · simp only [hx0, ↓reduceIte, UnpackedFloat.toRat'_eq_zero_of_isZero, not_true_eq_false,
      false_and]
      sorry
      -- simp [blastRounderForSign_eq_smtLibRounderForSign he hs heu hsu x]
    · simp [hx0]
      have hx0' : x.toRat' ≠ 0 := by sorry
      simp [hx0']
      sorry
end Fp
