import Fp.UnpackedRound
import Fp.SmtLibSemantics
import Fp.Theorems.SmtLibSemanticsQ
import Fp.Theorems.Packing
import Fp.Theorems.Negation
import Fp.Theorems.Ordering
import Fp.Theorems.LowerUpperRound

namespace Fp

/--
Find the right theorem statement here,
we should talk about guard and sticky bits and whatnot.
-/
theorem SmtLibSemantics_round_eq_pack_UnpackedFloat_round {rm : RoundingMode}
    {ein sin eout sout : Nat} {sign : Bool}
    (er : ExtRat) {r : Rat} (uf : UnpackedFloat ein sin)
    (hnorm : uf.sig.msb = true)
    (hr : er = ExtRat.Number r)
    -- | round works correctly as long as our number is close enough.
    (hApprox : (uf.toRat = r)) :
    (SmtLibSemantics.smtLibRoundMethod eout sout SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm sign er =
    (UnpackedFloat.round uf rm).pack := by
  sorry

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
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).sign = uf.sign := by
  simp [UnpackedFloat.clearSignificand]

@[simp]
theorem clearSignificand_ex (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).ex = uf.ex := by
  simp [UnpackedFloat.clearSignificand]

/-- Clearing guard/sticky bits can only decrease the significand value. -/
theorem UnpackedFloat.clearSignificand_sig_toNat_le (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).sig.toNat ≤ uf.sig.toNat := by
  rw [UnpackedFloat.clearSignificand]
  simp only [BitVec.toNat_and]
  grind only [Nat.and_le_left]



/-- For a nonnegative unpacked float, clearing guard/sticky bits yields a nonnegative result. -/
theorem UnpackedFloat.clearSignificand_toRat_nonneg_of_sign_eq_false (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : uf.sign = false) :
    0 ≤ (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat := by
  simp [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat']
  generalize hcleared : uf.clearSignificand targetExponentWidth targetSignificandWidth = cleared
  have : 0 < (2 : Rat) ^ cleared.toExpInt := by grind only [Rat.two_pow_pos]
  have hsign : cleared.sign = false := by
    simp [← hcleared, UnpackedFloat.clearSignificand, h]
  simp [hsign]
  grind only [Rat.mul_nonneg]




/-- For a nonnegative unpacked float, clearing guard/sticky bits rounds toward zero:
    the cleared value is at most the original value. -/
theorem UnpackedFloat.clearSignificand_toRat_le_of_nonneg (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (hufsign : uf.sign = false) :
    (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat ≤ uf.toRat := by
  simp only [UnpackedFloat.toRat_eq_toRat']
  rw [UnpackedFloat.toRat' , UnpackedFloat.toRat']
  generalize hcleared : uf.clearSignificand targetExponentWidth targetSignificandWidth = cleared
  have hsign : cleared.sign = false := by
    simp only [← hcleared, UnpackedFloat.clearSignificand, hufsign,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp [hsign, hufsign]
  have hexp : cleared.toExpInt = uf.toExpInt := by
    simp only [UnpackedFloat.toExpInt, ← hcleared, UnpackedFloat.clearSignificand,
      BitVec.orderEncode_eq_shiftRight_allOnes]
  simp only [hexp, ge_iff_le]
  have : cleared.sig.toNat ≤ uf.sig.toNat := by
    rw [← hcleared]
    apply UnpackedFloat.clearSignificand_sig_toNat_le
  suffices (cleared.sig.toNat : Rat) ≤ (uf.sig.toNat : Rat) by
    apply Rat.mul_le_mul_of_nonneg_right
    · simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]; grind only
    · grind only [Rat.le_of_lt, Rat.two_pow_pos]
  simp only [PackedFloat.Rat.natCast_le_natCast_iff_le]
  grind only

/-- For a nonnegative unpacked float, the error from clearing guard/sticky bits is bounded by
    2^(guardBitIdx + 1) ULPs at the significand level, i.e.,
    `x.toRat - cleared.toRat < 2^(guardBitIdx + 1) * 2^(x.toExpInt)`.
    This is the ULP of the target precision. -/
theorem clearSignificand_toRat_sub_lt (uf : UnpackedFloat e s)
    (targetExponentWidth targetSignificandWidth : Nat)
    (h : 0 ≤ uf.toRat) :
    uf.toRat - (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat <
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
      pf.toRat = (uf.clearSignificand targetExponentWidth targetSignificandWidth).toRat := by
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

theorem toRat_roundTowardZero_eq_smtLibLower_of_nonneg (x : UnpackedFloat e s)
    (hx : 0 ≤ x.toRat) :
    (x.roundTowardZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

theorem toRat_roundTowardZero_eq_smtLibUpper_of_neg (x : UnpackedFloat e s)
    (hx : x.toRat < 0) :
    (x.roundTowardZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry


/-# successorAwayFromZero -/

theorem toRat_successorAwayFromZero_eq_smtLibUpper_of_nonneg (x : UnpackedFloat e s)
    (hx : 0 ≤ x.toRat) :
    (x.successorAwayFromZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

theorem toRat_successorAwayFromZero_eq_smtLibLower_of_neg (x : UnpackedFloat e s)
    (hx : x.toRat < 0) :
    (x.successorAwayFromZero targetExponentWidth targetSignificandWidth).toRat =
    (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat) : PackedFloat targetExponentWidth targetSignificandWidth).toRat
      := by
  sorry

/-! # extractIsEven -/

@[simp]
theorem UnpackedFloat.extractIsEven_eq_isEven_lower_of_nonneg (x : UnpackedFloat e s)
    (hx : x.sign = false) :
    x.extractIsEven e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat)) := by
  simp [UnpackedFloat.extractIsEven]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem UnpackedFloat.extractIsEven_eq_isEven_upper_of_neg (x : UnpackedFloat e s)
    (hx : x.sign = true) :
    x.extractIsEven e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat)) := by
  simp [UnpackedFloat.extractIsEven]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry


/-! # extractGuardBit -/

theorem UnpackedFloat.extractGuardBit_eq_true_iff
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su) :
    x.extractGuardBit ep sp = true ↔ x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat) := by
  simp [UnpackedFloat.extractGuardBit]
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
    x.extractGuardBit ep sp =  x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat)  := by
  have := UnpackedFloat.extractGuardBit_eq_true_iff hep hsp heu hsu x
  grind only [#0e2e4e0bb1f1e395]

-- TODO: 'toRatSig' lemma about what the guardBit tracks.

theorem SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq_decide (r : Rat) :
    (smtLibRoundMethod e s smtLibV smtLibV).lowerHalf (ExtRat.Number r) =
    (r - ((smtLibRoundMethod e s smtLibV smtLibV).lower (ExtRat.Number r)).toRat ≤ 2^e) := by
  -- TODO: this is what I need to prove now.
  sorry

-- theorem le_toRatSig_of_extractGuardBit

@[simp]
theorem UnpackedFloat.extractGuardBit_eq_not_lowerHalf_of_nonneg (x : UnpackedFloat e s)
    (hx : x.sign = false) :
    x.extractGuardBit e s = ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat) := by
  -- simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem UnpackedFloat.extractGuardBit_eq_smtLibLowerHalf_of_neg (x : UnpackedFloat e s)
    (hx : x.sign = true) :
    x.extractGuardBit e s = (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat) := by
  simp [UnpackedFloat.extractGuardBit]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem BitVec.and_allOnes_eq_self (bv : BitVec n) :
    bv &&& (BitVec.allOnes n) = bv := by
  ext i hi
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
  x.extractStickyBit ep sp = true ↔
    -- This makes sense,
    -- Consider when `su = sp + 2`.
    -- Then we're saying that some bit
    -- after the guard bit is nonzero.
     (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  simp [UnpackedFloat.extractStickyBit]
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
  x.extractStickyBit ep sp = false ↔
    -- This makes sense,
    -- This says that all the lower bits are false.
     (∀ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat →
      x.sig.getLsbD i = false) := by
  have htrue := extractStickyBit_eq_true_iff hep hsp heu hsu x
  rw [iff_iff_not_iff_not] at htrue
  grind only [#c179, #0b53, #b326]

/--
The sticky bit tracks whether there is a bit
below the guard bit that is 1.
This is equivalent to saying that there exists some bit below the guard bit that is 1.
-/
theorem extractStickyBit_eq_decide
  (hep : 1 < ep) (hsp : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su) :
  x.extractStickyBit ep sp = decide (∃ (i : Nat),
      i < su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat ∧
      x.sig.getLsbD i = true) := by
  by_cases hextract : x.extractStickyBit ep sp = true
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x
    grind only [#46e5, #0b53]
  · have := extractStickyBit_eq_true_iff hep hsp heu hsu x
    simp at this
    grind only [#46e5, #0b53]

@[simp]
theorem UnpackedFloat.extractStickyBit_eq_not_tieBreak_of_nonneg_of_guardBit
    (he : 1 < ep)
    (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hx : x.sign = false)
    (hguard : x.extractGuardBit ep sp = true) :
    x.extractStickyBit ep sp = ! (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat) := by
  simp [SmtLibSemantics.smtLibRoundMethod]
  rw [extractStickyBit_eq_decide]
  · sorry
  · grind only
  · grind only
  · grind only
  · grind only

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.
-/
theorem UnpackedFloat.toExtRat_round_eq_smtLibRound
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
    (x.round rm (tep := ep) (tsp := sp) : EUnpackedFloat (exponentWidth ep sp) (sp + 1)) =
    ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round rm x.sign (ExtRat.Number x.toRat)).unpack := by
  rw [UnpackedFloat.round]
  by_cases hzero : x.isZero
  · simp [hzero, he, hs]
    rw [UnpackedFloat.toRat_eq_toRat']
    have : x.toRat' = 0 := by sorry
    sorry
  · simp [hzero]
    rw [round_eq_ite_roundingDecision_of_Number_of_nonneg]
    repeat sorry
    -- TODO: can we change the definition of 'lower' so that we fold the over/underflow cases into the 'lower' and 'upper'?

end Fp
