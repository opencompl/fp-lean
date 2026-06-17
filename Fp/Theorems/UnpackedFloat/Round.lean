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
  have : su < 2 ^ su := by exact Nat.lt_two_pow_self
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)]
    · grind only
    · grind only
    · grind only

  rw [UnpackedFloat.guardBitIndex]
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.add_mod_mod, Nat.mod_add_mod]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      rw [Int.sub_toNat_eq_zero_of_le]
      · grind only [= Nat.mod_eq_of_lt]
      · grind only
    case isFalse h =>
      grind only [= Nat.mod_eq_of_lt]
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    exact hdiffLower
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    exact hdiffUpper

theorem UnpackedFloat.toNat_lsbIndex_eq (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    -- (heusu : eu ≤ su)
    :
    (x.lsbIndex ep sp).toNat =
    (su - 1 - (sp + 1) + (minNormalExp ep - x.ex.toInt).toNat + 1) := by
  have := @one_lt_exponentWidth ep sp
  have hsu : su < 2 ^ su := by exact Nat.lt_two_pow_self
  have hminNormal : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep := by
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le (s := sp)]
    · grind only
    · grind only
    · grind only
  rw [UnpackedFloat.lsbIndex, UnpackedFloat.guardBitIndex]
  rw [BitVec.toNat_add]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat]
  · simp only [hminNormal]
    split
    case isTrue h =>
      grind only [= Int.toNat_neg_eq_zero_of_nonpos, = Nat.mod_eq_of_lt, #37a5855c772b74a3]
    case isFalse h =>
      grind only [= Nat.mod_eq_of_lt]
  · grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    grind only
  · rw [toInt_ofInt_minNormalExp_eq_minNormalExp_of_le hep hsp heu]
    grind only

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

theorem and_oneHotBV_eq_zero_iff (x i : BitVec w)  :
    x &&& (BitVec.oneHotBV i) = 0#w ↔ x.getLsbD i.toNat = false := by
  constructor
  · intros h
    rw [BitVec.eq_iff_getLsbD_eq] at h
    simp at h
    specialize h i.toNat
    grind only [= BitVec.getLsbD_of_ge]
  · intros h
    ext k hk
    simp
    intros hk
    have := i.getElem_oneHotBV ⟨k, by omega⟩
    grind only [= BitVec.getLsbD_eq_getElem, = Fin.getElem_fin]


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
    simp only [BitVec.getLsbD_and, BitVec.getlsbD_oneHotBV, BitVec.getLsbD_zero, ne_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, not_imp,
      Decidable.not_not] at hi
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


@[simp]
theorem UnpackedFloat.blastExtractIsEven_eq_true_iff
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    x.blastExtractIsEven ep sp = true ↔
    (x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1) = false):= by
  simp [UnpackedFloat.blastExtractIsEven]
  constructor
  · intros h
    simp only at h
    rw [BitVec.eq_iff_getLsbD_eq] at h
    simp only [BitVec.getLsbD_and, BitVec.getlsbD_oneHotBV, BitVec.getLsbD_zero, Bool.and_eq_false_imp, decide_eq_true_eq,
      decide_eq_false_iff_not] at h
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    specialize h _ hcontra
    rw [UnpackedFloat.toNat_lsbIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at h
    grind only
  · intros h
    simp only at h
    rw [BitVec.eq_iff_getLsbD_eq]
    intros i
    simp
    intros hx hi
    intros hcontra
    rw [UnpackedFloat.toNat_lsbIndex_eq hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe] at hcontra
    grind only


theorem blastExtractIsEven_eq_not_getLsbD
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.blastExtractIsEven ep sp = !x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1)  := by
  have := UnpackedFloat.blastExtractIsEven_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  grind only [#93deeaa3fa8dd789]

theorem getLsbD_eq_not_blastExtractIsEven
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (hsu : sp + 2 ≤ su)
    (x : UnpackedFloat eu su)
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp)
    :
    x.sig.getLsbD (su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat + 1) = !x.blastExtractIsEven ep sp := by
  have := UnpackedFloat.blastExtractIsEven_eq_true_iff hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe
  grind only [#ad239b3c63600307]

/--
info: 'Fp.UnpackedFloat.blastExtractIsEven_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.blastExtractIsEven_eq_true_iff


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
      exact UnpackedFloat.blastLowerNonneg_Rel_smtLibLower_normal (by grind only) hsp x hxsign hxnorm hunder hover

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

/-# blastIsEvenUpper, blastIsEvenLower -/

theorem blastIsEvenUpper_iff_smtLibIsEven_upper (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenUpper ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat')) = true := by
  simp [UnpackedFloat.blastIsEvenUpper]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

theorem blastIsEvenUpper_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenUpper ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number x.toRat'))) := by
  have := blastIsEvenUpper_iff_smtLibIsEven_upper he hs x
  grind

theorem blastIsEvenLower_iff_smtLibIsEven_lower (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenLower ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat')) = true := by
  simp [UnpackedFloat.blastIsEvenLower]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

theorem blastIsEvenLower_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsEvenLower ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).isEven
          (SmtLibSemantics.smtLibLower.lower (ExtRat.Number x.toRat'))) := by
  have := blastIsEvenLower_iff_smtLibIsEven_lower he hs x
  grind

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
theorem blastIsLowerHalf_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsLowerHalf ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number x.toRat')) := by
  have := blastIsLowerHalf_iff_smtLibLowerHalf he hs x
  grind


@[simp]
theorem blastTieBreak_iff_smtLibTieBreak (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = true ↔
    (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat') := by
  simp [UnpackedFloat.blastIsTieBreak]
  simp [SmtLibSemantics.smtLibRoundMethod]
  sorry

@[simp]
theorem blastIsTieBreak_eq (he : 1 < ep) (hs : 0 < sp) (x : UnpackedFloat e s) :
  x.blastIsTieBreak ep sp = (decide <| (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number x.toRat')) := by
  have := blastTieBreak_iff_smtLibTieBreak he hs x
  grind



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


theorem UnpackedFloat.blastRounderForSign_Rel_rounderForSign_zero (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (hsu : sp + 2 ≤ su) (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hx0 : x.isZero) :
  (x.blastRounderForSign ep sp).Rel
    ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).rounderForSign x.sign
        (ExtRat.Number 0)) := by
  by_cases hsign : x.sign
  · simp [hsign]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact (UnpackedFloat.blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm)
  · simp [hsign]
    rw [UnpackedFloat.blastRounderForSign_of_sign_eq_false_eq x (by grind)]
    rw [← UnpackedFloat.toRat'_eq_zero_of_isZero x hx0]
    exact
      (UnpackedFloat.blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm)

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
  · rw [UnpackedFloat.toRat'_normalize_eq_toRat' hse hssub]
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
    · simp
      have hbias := bias_plus_one_lt_two_pow_exponentWidth_minus_one ep sp he hs
      rw [maxNormalExp] at hnotover'
      have hcast : ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int) = (2 : Int) ^ (exponentWidth ep sp - 1) := by
        push_cast
        rfl
      omega
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
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms UnpackedFloat.toRat_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg

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

/--
Rounding (RNE) any number of magnitude at least `2 ^ (maxNormalExp ep + 1)`
produces the infinity whose sign is the sign of the number.

NOTE (statement corrected): the original hypothesis was
`2 ^ maxNormalExp ep < r.abs`, which does NOT force rounding to infinity
(counterexample `(ep, sp) = (3, 2)`, `r = 9`: `lower = 8`, `upper = 10`,
RNE returns `8`). The hypothesis was strengthened to
`2 ^ (maxNormalExp ep + 1) ≤ r.abs` (dischargeable at the call site from
`maxNormalExp ep < x.ex.toInt` and a normalized significand). Additionally
`hsign : sign = decide (r < 0)` and `hep : 2 < ep` were ADDED: without
`hsign` the conclusion is false for, e.g., positive `r` and `sign = true`
(the result `+∞` does not depend on `sign` for nonzero `r`).
-/
theorem roundRNE_eq_infinity_of_maxNormalExp_lt
  (he : 1 < ep)
  (hep : 2 < ep)
  (hs : 0 < sp)
  (r : Rat)
  (hsign : sign = decide (r < 0))
  (hr : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ r.abs) :
  ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
        (ExtRat.Number r)) = PackedFloat.getInfinity ep sp sign := by
  have hep0 : 0 < ep := by omega
  have hsp1 : 0 < sp + 1 := by omega
  have hpow_pos : (0 : Rat) < 2 ^ (maxNormalExp ep + 1) := Rat.two_pow_pos _
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    simp [Rat.abs] at hr
    grind
  have hfinN := PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp) he false
  have hfinN1 := PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' (e := ep) (s := sp + 1) he false
  have hmaxlt : (PackedFloat.maxNormalNumber ep sp false).toRat < 2 ^ (maxNormalExp ep + 1) :=
    PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hs
  have hmaxlt1 : (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat < 2 ^ (maxNormalExp ep + 1) :=
    PackedFloat.toRat_maxNormalNumber_lt_two_pow hep hsp1
  have hmono : (PackedFloat.maxNormalNumber ep sp false).toRat
      < (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat :=
    PackedFloat.toRat_maxNormalNumber_lt_toRat_maxNormalNumber_succ hep hs
  have hnotnan : ¬ (SmtLibSemantics.ExtendedNumber.isNaN (ExtRat.Number r)) := by
    simp
  have hnotzero : ¬ (SmtLibSemantics.ExtendedNumber.isZero (ExtRat.Number r)) := by
    simp only [SmtLibSemantics.instExtendedRat.isZero, ← ExtRat.ExtRat.zero_def]
    simp [hr0]
  by_cases hneg : r < 0
  case neg =>
    -- positive case: `2 ^ (maxNormalExp + 1) ≤ r`
    have habs : r.abs = r := by
      simp [Rat.abs, hneg]
    rw [habs] at hr
    have hsignF : sign = false := by simp [hsign, hneg]
    -- evaluations of the four bounds
    have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp false := by
      rw [smtLibLower_eq_lower ep sp hep0 hs _ (by simp),
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hs r (by grind)]
    have hL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.maxNormalNumber ep (sp + 1) false := by
      rw [smtLibLower_eq_lower ep (sp + 1) hep0 hsp1 _ (by simp),
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hsp1 r (by grind)]
    have hU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.getInfinity ep sp false := by
      rw [smtLibUpper_eq_upper ep sp hep0 hs _ (by simp),
        upper_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hs r (by grind)]
    have hU1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.getInfinity ep (sp + 1) false := by
      rw [smtLibUpper_eq_upper ep (sp + 1) hep0 hsp1 _ (by simp),
        upper_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hsp1 r (by grind)]
    -- conditions
    have hLH : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq, hL, hL1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_toRat_of hfinN, PackedFloat.toExtRat'_eq_toRat_of hfinN1]
      simp only [ExtRat.Number.injEq]
      grind
    have hTB : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq,
        SmtLibSemantics.smtLibV_upper_eq, hL, hL1, hU, hU1]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_eq_toRat_of hfinN, PackedFloat.toExtRat'_eq_toRat_of hfinN1,
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1]
      have h1 : (ExtRat.Number (PackedFloat.maxNormalNumber ep sp false).toRat
          < ExtRat.Number (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat) := by
        simp [hmono]
      have h2 : ¬ ((ExtRat.Infinity false : ExtRat) < ExtRat.Infinity false) := by
        simp
      intro hcontra
      rw [hcontra] at h1
      exact h2 h1
    have hRU : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).upper (ExtRat.Number r) = PackedFloat.getInfinity ep sp false := by
      rw [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq, hU]
    rw [SmtLibSemantics.RoundMethod.roundRNE]
    rw [if_neg hnotnan, if_pos ⟨hnotzero, by simp [hLH], by simp [hTB]⟩, hRU, hsignF]
  case pos =>
    -- negative case: `r ≤ -2 ^ (maxNormalExp + 1)`
    have habs : r.abs = -r := by
      simp [Rat.abs, hneg]
    rw [habs] at hr
    have hsignT : sign = true := by simp [hsign, hneg]
    have hflip : (PackedFloat.maxNormalNumber ep sp true).toRat
        = - (PackedFloat.maxNormalNumber ep sp false).toRat := by
      rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
    have hflip1 : (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat
        = - (PackedFloat.maxNormalNumber ep (sp + 1) false).toRat := by
      rw [← PackedFloat.neg_maxNormalNumber_false', PackedFloat.toRat_neg]
    -- evaluations of the four bounds
    have hL : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.getInfinity ep sp true := by
      rw [smtLibLower_eq_lower ep sp hep0 hs _ (by simp),
        lower_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hs r (by grind)]
    have hL1 : (SmtLibSemantics.smtLibLower.lower (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.getInfinity ep (sp + 1) true := by
      rw [smtLibLower_eq_lower ep (sp + 1) hep0 hsp1 _ (by simp),
        lower_Number_eq_getInfinity_of_maxNormalNumber_lt hep0 hsp1 r (by grind)]
    have hU : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep sp)
        = PackedFloat.maxNormalNumber ep sp true := by
      rw [smtLibUpper_eq_upper ep sp hep0 hs _ (by simp), upper, ExtRat.ExtRat.neg_number,
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hs (-r) (by grind),
        PackedFloat.neg_maxNormalNumber_false']
    have hU1 : (SmtLibSemantics.smtLibUpper.upper (ExtRat.Number r) : PackedFloat ep (sp + 1))
        = PackedFloat.maxNormalNumber ep (sp + 1) true := by
      rw [smtLibUpper_eq_upper ep (sp + 1) hep0 hsp1 _ (by simp), upper, ExtRat.ExtRat.neg_number,
        lower_Number_eq_maxNormalNumber_of_toRat_le he hep0 hsp1 (-r) (by grind),
        PackedFloat.neg_maxNormalNumber_false']
    -- conditions
    have hLH : ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lowerHalf (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq, hL, hL1,
        SmtLibSemantics.instExtendedRat.smtLibEq]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1]
    have hTB : ¬ ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).tieBreak (ExtRat.Number r)) := by
      rw [SmtLibSemantics.smtLibRoundMethod.tieBreak_eq]
      simp only [SmtLibSemantics.smtLibV_embed_eq, SmtLibSemantics.smtLibV_lower_eq,
        SmtLibSemantics.smtLibV_upper_eq, hL, hL1, hU, hU1]
      rw [PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat_eq_toExtRat', PackedFloat.toExtRat_eq_toExtRat',
        PackedFloat.toExtRat'_getInfinity hs, PackedFloat.toExtRat'_getInfinity hsp1,
        PackedFloat.toExtRat'_eq_toRat_of (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he true),
        PackedFloat.toExtRat'_eq_toRat_of (PackedFloat.isNormOrNonzeroSubnorm_maxNormalNumber' he true)]
      have h1 : ¬ ((ExtRat.Infinity true : ExtRat) < ExtRat.Infinity true) := by
        simp
      have h2 : (ExtRat.Number (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat
          < ExtRat.Number (PackedFloat.maxNormalNumber ep sp true).toRat) := by
        have : (PackedFloat.maxNormalNumber ep (sp + 1) true).toRat
            < (PackedFloat.maxNormalNumber ep sp true).toRat := by
          rw [hflip, hflip1]
          grind
        simp [this]
      intro hcontra
      rw [← hcontra] at h2
      exact h1 h2
    have hRL : (SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV
        SmtLibSemantics.smtLibV).lower (ExtRat.Number r) = PackedFloat.getInfinity ep sp true := by
      rw [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq, hL]
    rw [SmtLibSemantics.RoundMethod.roundRNE]
    rw [if_neg hnotnan,
      if_neg (by intro h; exact absurd hLH (by simpa using h.2.1)),
      if_neg (by intro h; exact hTB h.2.1),
      if_neg (by intro h; exact hTB h.2.1),
      if_pos ⟨hnotzero, hLH⟩, hRL, hsignT]

/--
An overflowing, normalized, nonzero float has magnitude strictly above `2 ^ maxNormalExp ep`.
-/
theorem UnpackedFloat.two_pow_maxNormalExp_lt_abs_toRat'
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hzero : ¬ x.isZero)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (2 : Rat) ^ maxNormalExp ep < (x.toRat').abs := by
  -- exponent strictly above maxNormalExp
  have hover' : maxNormalExp ep < x.ex.toInt := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
    grind
  -- the significand is nonzero and normalized, so its msb is set
  have hsig : x.sig ≠ 0#su := by
    simp [UnpackedFloat.isZero] at hzero
    exact hzero
  have hmsb : x.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hle : 2 ^ (su - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hmsb
  -- |toRat'| = sig.toNat * 2 ^ toExpInt
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsignat : (0 : Rat) < (x.sig.toNat : Rat) := by
    have : 0 < x.sig.toNat := by
      have : 0 < 2 ^ (su - 1) := Nat.two_pow_pos _
      omega
    exact_mod_cast this
  have habs : (x.toRat').abs = (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [UnpackedFloat.toRat', Rat.abs]
    cases hsgn : x.sign
    · simp [Bool.toSign]
      intros hlt
      exfalso
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
    · simp [Bool.toSign]
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
  rw [habs]
  -- 2 ^ (su-1) * 2 ^ toExpInt = 2 ^ ex.toInt
  have hexp : x.toExpInt = x.ex.toInt - ((su - 1 : Nat) : Int) := by
    simp [UnpackedFloat.toExpInt]
    omega
  have h1 : ((2 : Rat) ^ ((su - 1 : Nat) : Int)) * (2 : Rat) ^ x.toExpInt = (2 : Rat) ^ x.ex.toInt := by
    rw [Rat.zpow_mul_zpow (by grind)]
    have heq : ((su - 1 : Nat) : Int) + x.toExpInt = x.ex.toInt := by
      rw [hexp]; omega
    rw [heq]
  have key : (2 : Rat) ^ x.ex.toInt ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [← h1]
    apply Rat.mul_le_mul_of_nonneg_right
    · rw [Rat.zpow_natCast]
      have : ((2 ^ (su - 1) : Nat) : Rat) ≤ (x.sig.toNat : Rat) := by
        exact_mod_cast hle
      simpa [Rat.natCast_pow] using this
    · exact Rat.le_of_lt hpos
  have hstrict : (2 : Rat) ^ maxNormalExp ep < (2 : Rat) ^ x.ex.toInt := by
    have h2 : (2 : Rat) * (2 : Rat) ^ maxNormalExp ep = (2 : Rat) ^ (maxNormalExp ep + 1) :=
      Rat.mul_self_zpow_eq_zpow_succ (by grind)
    have h3 : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (2 : Rat) ^ x.ex.toInt :=
      Rat.two_pow_le_two_pow_of_le (by omega)
    have h4 : (0 : Rat) < (2 : Rat) ^ maxNormalExp ep := Rat.two_pow_pos _
    grind
  grind

/--
An overflowing, normalized, nonzero float has magnitude at least `2 ^ (maxNormalExp ep + 1)`.
Strengthened form of `two_pow_maxNormalExp_lt_abs_toRat'`, used to discharge the
corrected hypothesis of `roundRNE_eq_infinity_of_maxNormalExp_lt`.
-/
theorem UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat'
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hxnorm : x.normalize = x)
    (hzero : ¬ x.isZero)
    (hover : x.blastIsEarlyOverflowNonneg ep sp = true) :
    (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (x.toRat').abs := by
  -- exponent strictly above maxNormalExp
  have hover' : maxNormalExp ep < x.ex.toInt := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
    grind
  -- the significand is nonzero and normalized, so its msb is set
  have hsig : x.sig ≠ 0#su := by
    simp [UnpackedFloat.isZero] at hzero
    exact hzero
  have hmsb : x.sig.msb = true := (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hle : 2 ^ (su - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hmsb
  -- |toRat'| = sig.toNat * 2 ^ toExpInt
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsignat : (0 : Rat) < (x.sig.toNat : Rat) := by
    have : 0 < x.sig.toNat := by
      have : 0 < 2 ^ (su - 1) := Nat.two_pow_pos _
      omega
    exact_mod_cast this
  have habs : (x.toRat').abs = (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [UnpackedFloat.toRat', Rat.abs]
    cases hsgn : x.sign
    · simp [Bool.toSign]
      intros hlt
      exfalso
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
    · simp [Bool.toSign]
      have : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
        exact Rat.mul_positive hsignat hpos
      grind
  rw [habs]
  -- 2 ^ (su-1) * 2 ^ toExpInt = 2 ^ ex.toInt
  have hexp : x.toExpInt = x.ex.toInt - ((su - 1 : Nat) : Int) := by
    simp [UnpackedFloat.toExpInt]
    omega
  have h1 : ((2 : Rat) ^ ((su - 1 : Nat) : Int)) * (2 : Rat) ^ x.toExpInt = (2 : Rat) ^ x.ex.toInt := by
    rw [Rat.zpow_mul_zpow (by grind)]
    have heq : ((su - 1 : Nat) : Int) + x.toExpInt = x.ex.toInt := by
      rw [hexp]; omega
    rw [heq]
  have key : (2 : Rat) ^ x.ex.toInt ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt := by
    rw [← h1]
    apply Rat.mul_le_mul_of_nonneg_right
    · rw [Rat.zpow_natCast]
      have : ((2 ^ (su - 1) : Nat) : Rat) ≤ (x.sig.toNat : Rat) := by
        exact_mod_cast hle
      simpa [Rat.natCast_pow] using this
    · exact Rat.le_of_lt hpos
  have h3 : (2 : Rat) ^ (maxNormalExp ep + 1) ≤ (2 : Rat) ^ x.ex.toInt :=
    Rat.two_pow_le_two_pow_of_le (by omega)
  grind

/-- The absolute value of an unpacked float is its significand value times its scaled exponent. -/
theorem UnpackedFloat.abs_toRat'_eq (x : UnpackedFloat eu su) :
    (x.toRat' prec).abs = (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt prec := by
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt prec := Rat.two_pow_pos _
  have hsignn : (0 : Rat) ≤ (x.sig.toNat : Rat) := by exact_mod_cast Nat.zero_le _
  have hnonneg : (0 : Rat) ≤ (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt prec :=
    Rat.mul_nonneg hsignn (Rat.le_of_lt hpos)
  rw [UnpackedFloat.toRat', Rat.abs]
  cases hsgn : x.sign
  · simp [Bool.toSign]
    intros hlt
    grind
  · simp [Bool.toSign]
    grind

/-- For a nonzero unpacked float, the sign bit records whether the value is negative. -/
theorem UnpackedFloat.sign_eq_decide_toRat'_lt_zero (x : UnpackedFloat eu su)
    (hx0 : x.toRat' ≠ 0) :
    x.sign = decide (x.toRat' < 0) := by
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsig : x.sig.toNat ≠ 0 := by
    intro h
    apply hx0
    simp [UnpackedFloat.toRat', UnpackedFloat.toSigNat, h]
  have hsignat : (0 : Rat) < (x.sig.toNat : Rat) := by
    exact_mod_cast Nat.pos_of_ne_zero hsig
  have hprod : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt :=
    Rat.mul_positive hsignat hpos
  rw [UnpackedFloat.toRat']
  cases hsgn : x.sign
  · simp [Bool.toSign]
    grind
  · simp [Bool.toSign]
    grind

/-- An early-underflowing float is strictly smaller in magnitude than
half the minimum subnormal of the target format. -/
theorem UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hunder : x.blastIsEarlyUnderflowNonneg ep sp = true) :
    (x.toRat').abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1) := by
  have hunder' : x.ex.toInt < minSubnormalExp ep sp - 1 := by
    have := UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x
    grind
  rw [UnpackedFloat.abs_toRat'_eq]
  have hpos : (0 : Rat) < (2 : Rat) ^ x.toExpInt := Rat.two_pow_pos _
  have hsiglt : x.sig.toNat < 2 ^ su := x.sig.isLt
  have h1 : (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt
      < ((2 : Rat) ^ ((su : Nat) : Int)) * (2 : Rat) ^ x.toExpInt := by
    rw [Rat.mul_lt_mul_cancel_right_of_lt hpos]
    rw [Rat.zpow_natCast]
    have : ((x.sig.toNat : Nat) : Rat) < ((2 ^ su : Nat) : Rat) := by exact_mod_cast hsiglt
    simpa [Rat.natCast_pow] using this
  have h2 : ((2 : Rat) ^ ((su : Nat) : Int)) * (2 : Rat) ^ x.toExpInt
      = (2 : Rat) ^ (((su : Nat) : Int) + x.toExpInt) :=
    Rat.zpow_mul_zpow (by grind) _ _
  have h3 : ((su : Nat) : Int) + x.toExpInt ≤ minSubnormalExp ep sp - 1 := by
    simp [UnpackedFloat.toExpInt]
    omega
  have h4 : (2 : Rat) ^ (((su : Nat) : Int) + x.toExpInt) ≤ (2 : Rat) ^ (minSubnormalExp ep sp - 1) :=
    Rat.two_pow_le_two_pow_of_le h3
  grind

/--
Rounding any number whose absolute value is strictly smaller than *half the
minimum subnormal* of the target format produces a zero, whose sign is the
sign of the number itself.

NOTE (statement corrected): the original statement assumed only
`r.abs < 2 ^ minNormalExp ep` and an arbitrary `sign`, which is FALSE:
* any representable subnormal `r` (e.g. `r = 2 ^ minSubnormalExp ep sp`)
  satisfies that bound but rounds to itself (nonzero);
* for nonzero `r` the sign of the resulting zero is forced by the sign of
  `r` (e.g. positive tiny `r` rounds to `+0` even when `sign = true`).
The corrected hypotheses require `|r| < 2 ^ (minSubnormalExp ep sp - 1)`
(strictly below half the smallest subnormal, so RNE rounds to zero) and
`sign = decide (r < 0)`.
-/
theorem roundRNE_eq_zero_of_lt_minNormalExp
  (he : 1 < ep)
  (hs : 0 < sp)
  (r : Rat)
  (hsign : sign = decide (r < 0))
  (hr : r.abs < (2 : Rat) ^ (minSubnormalExp ep sp - 1)) :
  ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE sign
        (ExtRat.Number r)) = PackedFloat.getZero ep sp sign := by
  sorry


/--
Since 'truncateFittingExponent' does not change the significand,
it preserves being normalized.

NOTE (statement corrected): the hypothesis `¬ x.isZero` was added. The
original statement (without it) is FALSE when `exponentWidth ep sp < eu`:
for the canonical zero (`sig = 0`, `ex = intMin eu`), `truncateFittingExponent`
truncates `intMin eu` to `0`, while re-normalizing the result produces the
canonical zero of the *narrower* width, whose exponent is
`intMin (exponentWidth ep sp) ≠ 0`. (Counterexamples found by exhaustive
enumeration at `ep = 3, sp = 2, eu = 5, su = 4`; the nonzero case has no
counterexamples there.) The lemma was unused at the time of the change.
-/
theorem normalize_truncateFittingExponent_eq_self_of_normalize_eq_self
  (he : 1 < ep) (hs : 0 < sp)
  (heu : exponentWidth ep sp ≤ eu)
  (hsu : sp + 2 ≤ su)
  (x : UnpackedFloat eu su)
  (hzero : ¬ x.isZero)
  (hxnorm : x.normalize = x) :
    (x.truncateFittingExponent ep sp).normalize = x.truncateFittingExponent ep sp := by
  apply UnpackedFloat.normalize_eq_self_of_msb_eq_true
  simp only [sig_truncateFittingExponent]
  have hsig : x.sig ≠ 0#su := by
    simp [UnpackedFloat.isZero] at hzero
    exact hzero
  exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm

/--
since truncateFittingExponent does not change the significand, it preserves being zero.
-/
theorem isZero_truncateFittingExponent_eq_isZero
    (x : UnpackedFloat eu su) :
    (x.truncateFittingExponent ep sp).isZero = x.isZero := by
  simp [UnpackedFloat.isZero, UnpackedFloat.truncateFittingExponent]


@[simp]
theorem UnpackedFloat.toRat'_isZero
    (x : UnpackedFloat eu su) :
    x.isZero = true ↔ x.toRat' = 0 := by
  simp [UnpackedFloat.isZero, UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat']
  grind only [= BitVec.toNat_zero, = BitVec.ofNat_toNat, = BitVec.getElem_zero,
    = BitVec.getElem_setWidth, = BitVec.getLsbD_eq_getElem, #a38c, #742d]

@[simp]
theorem toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    {x : UnpackedFloat eu su}
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).toRat' = x.toRat' := by
  simp [UnpackedFloat.toRat']
  rw [toExpInt_truncateFittingExponent_of_not_blastIsOverflowNonneg] <;> grind only

/-! ### Invariance of the lower/upper circuits under `truncateFittingExponent`

The lemmas below show that (in the no-early-over/underflow window) the
`blastLower*`/`blastUpper*` circuits produce `Rel`-equivalent results before
and after `truncateFittingExponent`. The proofs go through `PartsEq`
(agreement on state, sign and rational value at every precision). -/

/-- Under no early over/underflow, `truncateFittingExponent` preserves the
*value* of the exponent field. -/
theorem toInt_ex_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).ex.toInt = x.ex.toInt := by
  have h := toExpInt_truncateFittingExponent_of_not_blastIsOverflowNonneg he hs heu x hnotover hnotunder
  simp [UnpackedFloat.toExpInt] at h
  omega

/-- `s + 1` is strictly below `2 ^ (exponentWidth e s - 1)` when `1 < e`. -/
theorem sigWidth_add_one_lt_two_pow_exponentWidth_sub_one (he : 1 < e) :
    s + 1 < 2 ^ (exponentWidth e s - 1) := by
  rw [exponentWidth]
  have hpow : 2 ≤ 2 ^ (e - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h0 : 2 ^ (e - 1) + s - 1 ≠ 0 := by omega
  obtain ⟨k, hk, hle, hlt⟩ := Nat.log2_eq_exists _ h0
  rw [hk]
  show s + 1 < 2 ^ (k + 1)
  omega

/-- The shift amount `minNormalExp ep - exInt` fits in the signed range of any
width `w ≥ exponentWidth ep sp`, provided the exponent is between
`minSubnormalExp - 1` and `maxNormalExp`. -/
theorem shift_range
    (he : 1 < ep) (hs : 0 < sp) (hw : exponentWidth ep sp ≤ w)
    {exInt : Int}
    (hlo : minSubnormalExp ep sp - 1 ≤ exInt) (hhi : exInt ≤ maxNormalExp ep) :
    -2 ^ (w - 1) ≤ minNormalExp ep - exInt ∧ minNormalExp ep - exInt < 2 ^ (w - 1) := by
  have hbias : 0 < bias ep := bias_pos_of_one_lt ep he
  have hminN : minNormalExp ep = 1 - (bias ep : Int) := by
    rw [minNormalExp]
    omega
  have hminS : minSubnormalExp ep sp = -(bias ep : Int) - ((sp : Int) - 1) :=
    minSubnormalExp_eq_neg_bias_minus_s_minus_one he
  have hmaxN : maxNormalExp ep = (bias ep : Int) := rfl
  have hsp1 : sp + 1 < 2 ^ (exponentWidth ep sp - 1) :=
    sigWidth_add_one_lt_two_pow_exponentWidth_sub_one he
  have h2b : 2 * bias ep = 2 ^ ep - 2 := two_mul_bias_eq_twoPow_minus_two ep he
  have hpow1 : (2 : Nat) ^ ep ≤ 2 ^ (exponentWidth ep sp - 1) := by
    apply Nat.pow_le_pow_right (by omega)
    have := self_lt_exponentWidth ep sp he hs
    omega
  have hpow2 : (2 : Nat) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (w - 1) := by
    apply Nat.pow_le_pow_right (by omega)
    have := @one_lt_exponentWidth ep sp
    omega
  have hcast : ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) := by push_cast; rfl
  omega

/-- `blastIsUnderflowNonneg` is invariant under `truncateFittingExponent`
(no early over/underflow). -/
theorem blastIsUnderflowNonneg_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).blastIsUnderflowNonneg ep sp
      = x.blastIsUnderflowNonneg ep sp := by
  rw [UnpackedFloat.blastUnderflowNonneg_eq_decide he hs (Nat.le_refl _),
      UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu,
      toInt_ex_truncateFittingExponent he hs heu x hnotover hnotunder]

/-- `blastIsEarlyOverflowNonneg` is invariant under `truncateFittingExponent`
(no early over/underflow). -/
theorem blastIsEarlyOverflowNonneg_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).blastIsEarlyOverflowNonneg ep sp
      = x.blastIsEarlyOverflowNonneg ep sp := by
  rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs (Nat.le_refl _),
      UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu,
      toInt_ex_truncateFittingExponent he hs heu x hnotover hnotunder]

/-- The guard bit index is invariant under `truncateFittingExponent`
(no early over/underflow). -/
theorem guardBitIndex_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).guardBitIndex ep sp = x.guardBitIndex ep sp := by
  have hover' : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
    grind
  have hunder' : minSubnormalExp ep sp - 1 ≤ x.ex.toInt := by
    have := UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x
    grind
  have hext := toInt_ex_truncateFittingExponent he hs heu x hnotover hnotunder
  have hofIntT : (BitVec.ofInt (exponentWidth ep sp) (minNormalExp ep)).toInt = minNormalExp ep :=
    toInt_ofInt_minNormalExp_eq_minNormalExp_of_le he hs (Nat.le_refl _)
  have hofIntX : (BitVec.ofInt eu (minNormalExp ep)).toInt = minNormalExp ep :=
    toInt_ofInt_minNormalExp_eq_minNormalExp_of_le he hs heu
  have hewpos : 0 < exponentWidth ep sp := zero_lt_exponentWidth
  have heupos : 0 < eu := by omega
  obtain ⟨hrt1, hrt2⟩ := shift_range he hs (Nat.le_refl _) (exInt := x.ex.toInt) hunder' hover'
  obtain ⟨hrx1, hrx2⟩ := shift_range he hs heu (exInt := x.ex.toInt) hunder' hover'
  unfold UnpackedFloat.guardBitIndex
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  rw [BitVec.toNat_subSaturatingZero_eq_ite_toNat hewpos _ _
        (by rw [hofIntT, hext]; exact hrt1) (by rw [hofIntT, hext]; exact hrt2),
      BitVec.toNat_subSaturatingZero_eq_ite_toNat heupos _ _
        (by rw [hofIntX]; exact hrx1) (by rw [hofIntX]; exact hrx2)]
  rw [hofIntT, hofIntX, hext]

/-- The cleared significand is invariant under `truncateFittingExponent`. -/
theorem sig_blastClearSignificand_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastClearSignificand ep sp).sig
      = (x.blastClearSignificand ep sp).sig := by
  unfold UnpackedFloat.blastClearSignificand
  simp only [sig_truncateFittingExponent]
  rw [guardBitIndex_truncateFittingExponent he hs heu x hnotover hnotunder]

@[simp]
theorem sign_blastRoundTowardZero (uf : UnpackedFloat eu su) :
    (uf.blastRoundTowardZero tep tsp).sign = uf.sign := by
  simp [UnpackedFloat.blastRoundTowardZero]

theorem sig_blastRoundTowardZero (uf : UnpackedFloat eu su) :
    (uf.blastRoundTowardZero tep tsp).sig
      = (uf.blastClearSignificand tep tsp).sig.extractMsb' 0 (tsp + 1) := rfl

@[simp]
theorem ex_blastRoundTowardZero (uf : UnpackedFloat eu su) :
    (uf.blastRoundTowardZero tep tsp).ex = uf.ex := by
  simp [UnpackedFloat.blastRoundTowardZero, UnpackedFloat.blastClearSignificand]

/-- `needsRounding` is invariant under `truncateFittingExponent`
(no early over/underflow). -/
theorem needsRounding_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    (x.truncateFittingExponent ep sp).needsRounding ep sp = x.needsRounding ep sp := by
  unfold UnpackedFloat.needsRounding UnpackedFloat.blastExtractGuardBit
    UnpackedFloat.blastExtractStickyBit
  rw [guardBitIndex_truncateFittingExponent he hs heu x hnotover hnotunder]
  simp only [sig_truncateFittingExponent]

@[simp]
theorem sign_blastSuccessorAwayFromZero (uf : UnpackedFloat eu su) :
    (uf.blastSuccessorAwayFromZero tep tsp).sign = uf.sign := by
  simp [UnpackedFloat.blastSuccessorAwayFromZero, UnpackedFloat.blastClearSignificand]

@[simp]
theorem sign_blastSuccessorAwayFromZeroNonnegAux (uf : UnpackedFloat eu su) :
    (uf.blastSuccessorAwayFromZeroNonnegAux tep tsp).sign = uf.sign := by
  unfold UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux
  split <;> simp

/-- The significand produced by `blastSuccessorAwayFromZero` is invariant under
`truncateFittingExponent` (no early over/underflow). -/
theorem sig_blastSuccessorAwayFromZero_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastSuccessorAwayFromZero ep sp).sig
      = (x.blastSuccessorAwayFromZero ep sp).sig := by
  unfold UnpackedFloat.blastSuccessorAwayFromZero
  simp only [guardBitIndex_truncateFittingExponent he hs heu x hnotover hnotunder,
    sig_blastClearSignificand_truncateFittingExponent he hs heu x hnotover hnotunder]

/-- The exponent *value* produced by `blastSuccessorAwayFromZero` is invariant
under `truncateFittingExponent` (no early over/underflow). -/
theorem toInt_ex_blastSuccessorAwayFromZero_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastSuccessorAwayFromZero ep sp).ex.toInt
      = (x.blastSuccessorAwayFromZero ep sp).ex.toInt := by
  have hexhi : x.ex.toInt ≤ maxNormalExp ep := by
    have := UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x
    grind
  have hexlo : minSubnormalExp ep sp - 1 ≤ x.ex.toInt := by
    have := UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x
    grind
  have hext := toInt_ex_truncateFittingExponent he hs heu x hnotover hnotunder
  have hew1 : 1 < exponentWidth ep sp := one_lt_exponentWidth
  have heu1 : 1 < eu := by omega
  have hbias : bias ep + 1 < 2 ^ (exponentWidth ep sp - 1) :=
    bias_plus_one_lt_two_pow_exponentWidth_minus_one ep sp he hs
  have hminS := neg_two_pow_exponentWidth_lt_minSubnormalExp (e := ep) (s := sp) he hs
  have hmaxN : maxNormalExp ep = (bias ep : Int) := rfl
  have hpowle : (2 : Int) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) := by
    have h1 : (2 : Nat) ^ (exponentWidth ep sp - 1) ≤ 2 ^ (eu - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hc1 : ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int)
        = (2 : Int) ^ (exponentWidth ep sp - 1) := by push_cast; rfl
    have hc2 : ((2 ^ (eu - 1) : Nat) : Int) = (2 : Int) ^ (eu - 1) := by push_cast; rfl
    omega
  have hcastBias : ((bias ep : Nat) : Int) + 1 < (2 : Int) ^ (exponentWidth ep sp - 1) := by
    have : ((bias ep + 1 : Nat) : Int) < ((2 ^ (exponentWidth ep sp - 1) : Nat) : Int) := by
      exact_mod_cast hbias
    push_cast at this
    omega
  have h2pow : ∀ n : Nat, 0 < n → (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    rw [Int.pow_succ]
    simp
    omega
  have h2eu : (2 : Int) ^ eu = 2 * 2 ^ (eu - 1) := h2pow eu (by omega)
  have h2ew : (2 : Int) ^ (exponentWidth ep sp) = 2 * 2 ^ (exponentWidth ep sp - 1) :=
    h2pow _ (by omega)
  unfold UnpackedFloat.blastSuccessorAwayFromZero
  simp only [guardBitIndex_truncateFittingExponent he hs heu x hnotover hnotunder,
    sig_blastClearSignificand_truncateFittingExponent he hs heu x hnotover hnotunder,
    clearSignificand_ex]
  split
  · -- carry: both exponents incremented by one
    rw [BitVec.toInt_add, BitVec.toInt_add, hext]
    have h1t : (1#(exponentWidth ep sp)).toInt = 1 := by
      rw [BitVec.toInt_one_of_lt hew1]
    have h1x : (1#eu).toInt = 1 := by
      rw [BitVec.toInt_one_of_lt heu1]
    rw [h1t, h1x]
    rw [Int.bmod_eq_of_le, Int.bmod_eq_of_le] <;> push_cast <;> omega
  · exact hext

/-- The significand of `blastSuccessorAwayFromZeroNonnegAux` is invariant under
`truncateFittingExponent`. -/
theorem sig_blastSuccessorAwayFromZeroNonnegAux_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastSuccessorAwayFromZeroNonnegAux ep sp).sig
      = (x.blastSuccessorAwayFromZeroNonnegAux ep sp).sig := by
  unfold UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux
  rw [needsRounding_truncateFittingExponent he hs heu x hnotover hnotunder]
  split
  · exact sig_blastSuccessorAwayFromZero_truncateFittingExponent he hs heu x hnotover hnotunder
  · rw [sig_blastRoundTowardZero, sig_blastRoundTowardZero,
      sig_blastClearSignificand_truncateFittingExponent he hs heu x hnotover hnotunder]

/-- The exponent value of `blastSuccessorAwayFromZeroNonnegAux` is invariant
under `truncateFittingExponent`. -/
theorem toInt_ex_blastSuccessorAwayFromZeroNonnegAux_truncateFittingExponent
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt
      = (x.blastSuccessorAwayFromZeroNonnegAux ep sp).ex.toInt := by
  unfold UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux
  rw [needsRounding_truncateFittingExponent he hs heu x hnotover hnotunder]
  split
  · exact toInt_ex_blastSuccessorAwayFromZero_truncateFittingExponent he hs heu x hnotover hnotunder
  · rw [ex_blastRoundTowardZero, ex_blastRoundTowardZero]
    exact toInt_ex_truncateFittingExponent he hs heu x hnotover hnotunder

/-- Two extended unpacked floats (possibly of different widths) that agree on
state, sign, and rational value at every precision are `Rel`-related to
exactly the same packed floats. -/
def EUnpackedFloat.PartsEq (a : EUnpackedFloat e1 s1) (b : EUnpackedFloat e2 s2) : Prop :=
  a.state = b.state ∧ a.num.sign = b.num.sign ∧ ∀ w, a.num.toRat' w = b.num.toRat' w

theorem EUnpackedFloat.Rel_iff_Rel_of_PartsEq
    {a : EUnpackedFloat e1 s1} {b : EUnpackedFloat e2 s2}
    {z : PackedFloat zep zsp}
    (h : EUnpackedFloat.PartsEq a b) :
    a.Rel z ↔ b.Rel z := by
  obtain ⟨hstate, hsign, htoRat⟩ := h
  unfold EUnpackedFloat.Rel UnpackedFloat.Rel EUnpackedFloat.sign
  rw [hstate, htoRat zsp, hsign]

theorem EUnpackedFloat.PartsEq.neg
    {a : EUnpackedFloat e1 s1} {b : EUnpackedFloat e2 s2}
    (h : EUnpackedFloat.PartsEq a b) :
    EUnpackedFloat.PartsEq (-a) (-b) := by
  obtain ⟨hstate, hsign, htoRat⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa using hstate
  · rw [← EUnpackedFloat.neg_def, ← EUnpackedFloat.neg_def]
    simp [EUnpackedFloat.neg]
    grind
  · intro w
    rw [← EUnpackedFloat.neg_def, ← EUnpackedFloat.neg_def]
    simp only [EUnpackedFloat.neg]
    simp only [UnpackedFloat.toRat'_neg]
    rw [htoRat w]

/-- Two unpacked floats with equal sign, significand and exponent *value*
have equal rational values at every precision. -/
theorem UnpackedFloat.toRat'_eq_toRat'_of_parts
    {a : UnpackedFloat e1 s} {b : UnpackedFloat e2 s}
    (hsign : a.sign = b.sign) (hsig : a.sig = b.sig) (hex : a.ex.toInt = b.ex.toInt)
    (w : Nat) :
    a.toRat' w = b.toRat' w := by
  simp [UnpackedFloat.toRat', UnpackedFloat.toExpInt, UnpackedFloat.toSigNat, hsig, hsign, hex]

/-- `blastLowerNonneg` commutes with `truncateFittingExponent` up to `PartsEq`. -/
theorem blastLowerNonneg_truncateFittingExponent_PartsEq
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    EUnpackedFloat.PartsEq
      ((x.truncateFittingExponent ep sp).blastLowerNonneg ep sp)
      (x.blastLowerNonneg ep sp) := by
  have hcondU := blastIsUnderflowNonneg_truncateFittingExponent he hs heu x hnotover hnotunder
  have hcondO := blastIsEarlyOverflowNonneg_truncateFittingExponent he hs heu x hnotover hnotunder
  unfold UnpackedFloat.blastLowerNonneg
  rw [hcondU, hcondO]
  by_cases h1 : x.blastIsUnderflowNonneg ep sp
  · simp only [h1, if_true]
    exact ⟨rfl, by simp, fun w => by simp⟩
  · simp only [h1, Bool.false_eq_true, if_false, hnotover]
    refine ⟨rfl, ?_, ?_⟩
    · simp only [EUnpackedFloat.num_mkNumber, sign_blastRoundTowardZero,
        sign_truncateFittingExponent]
    · intro w
      simp only [EUnpackedFloat.num_mkNumber]
      apply UnpackedFloat.toRat'_eq_toRat'_of_parts
      · simp only [sign_blastRoundTowardZero, sign_truncateFittingExponent]
      · rw [sig_blastRoundTowardZero, sig_blastRoundTowardZero,
          sig_blastClearSignificand_truncateFittingExponent he hs heu x hnotover hnotunder]
      · simp only [ex_blastRoundTowardZero]
        exact toInt_ex_truncateFittingExponent he hs heu x hnotover hnotunder

/-- `blastUpperNonneg` commutes with `truncateFittingExponent` up to `PartsEq`. -/
theorem blastUpperNonneg_truncateFittingExponent_PartsEq
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    (x : UnpackedFloat eu su)
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    EUnpackedFloat.PartsEq
      ((x.truncateFittingExponent ep sp).blastUpperNonneg ep sp)
      (x.blastUpperNonneg ep sp) := by
  have hsig := sig_blastSuccessorAwayFromZeroNonnegAux_truncateFittingExponent
    he hs heu x hnotover hnotunder
  have hexI := toInt_ex_blastSuccessorAwayFromZeroNonnegAux_truncateFittingExponent
    he hs heu x hnotover hnotunder
  have hcondU :
      ((x.truncateFittingExponent ep sp).blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp
        = (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp := by
    rw [UnpackedFloat.blastUnderflowNonneg_eq_decide he hs (Nat.le_refl _),
        UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu, hexI]
  have hcondO :
      ((x.truncateFittingExponent ep sp).blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp
        = (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp := by
    rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs (Nat.le_refl _),
        UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu, hexI]
  simp only [UnpackedFloat.blastUpperNonneg]
  rw [hcondU, hcondO]
  by_cases h1 : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsUnderflowNonneg ep sp
  · simp only [h1, if_true]
    refine ⟨rfl, by simp [UnpackedFloat.minSubnormalForPackedFloat], fun w => ?_⟩
    simp only [EUnpackedFloat.num_mkNumber]
    apply UnpackedFloat.toRat'_eq_toRat'_of_parts
    · simp [UnpackedFloat.minSubnormalForPackedFloat]
    · simp [UnpackedFloat.minSubnormalForPackedFloat]
    · simp only [UnpackedFloat.minSubnormalForPackedFloat]
      rw [toInt_ofInt_minSubnormalExp_eq_minSubnormalExp_of_le he hs (Nat.le_refl _),
          toInt_ofInt_minSubnormalExp_eq_minSubnormalExp_of_le he hs heu]
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : (x.blastSuccessorAwayFromZeroNonnegAux ep sp).blastIsEarlyOverflowNonneg ep sp
    · simp only [h2, if_true]
      exact ⟨rfl, by simp [EUnpackedFloat.mkInfinity],
        fun w => by simp [EUnpackedFloat.mkInfinity, UnpackedFloat.toRat']⟩
    · simp only [h2, Bool.false_eq_true, if_false]
      refine ⟨rfl, ?_, fun w => ?_⟩
      · simp only [EUnpackedFloat.num_mkNumber, sign_blastSuccessorAwayFromZeroNonnegAux,
          sign_truncateFittingExponent]
      · simp only [EUnpackedFloat.num_mkNumber]
        exact UnpackedFloat.toRat'_eq_toRat'_of_parts (by simp) hsig hexI w

/-- Negation commutes with `truncateFittingExponent`. -/
theorem neg_truncateFittingExponent (x : UnpackedFloat eu su) :
    -(x.truncateFittingExponent ep sp) = (-x).truncateFittingExponent ep sp := by
  simp [UnpackedFloat.truncateFittingExponent, UnpackedFloat.neg_def, UnpackedFloat.neg]

@[simp]
theorem blastIsEarlyOverflowNonneg_neg (x : UnpackedFloat eu su) :
    (-x).blastIsEarlyOverflowNonneg tep tsp = x.blastIsEarlyOverflowNonneg tep tsp := rfl

@[simp]
theorem blastIsEarlyUnderflowNonneg_neg (x : UnpackedFloat eu su) :
    (-x).blastIsEarlyUnderflowNonneg tep tsp = x.blastIsEarlyUnderflowNonneg tep tsp := rfl

/--
NOTE (statement corrected): the hypothesis `heu : exponentWidth ep sp ≤ eu`
was ADDED. Without it the statement is FALSE: for `eu < exponentWidth ep sp`
the constants `BitVec.ofInt eu (minSubnormalExp ep sp)` etc. wrap around, so
`x.blastIsUnderflowNonneg` can disagree with the (faithful) condition computed
at width `exponentWidth ep sp` after `truncateFittingExponent` (which *widens*
losslessly in that case). E.g. at `(ep, sp) = (3, 2)`, `eu = 2`:
`hnotover`/`hnotunder` force `x.ex.toInt = -1`, then `x` takes the underflow
branch (`lower = +0`) while `truncateFittingExponent x` takes the normal
branch (nonzero result). All call sites have `heu` in scope.
-/
@[simp]
theorem blastLowerNonneg_truncateFittingExponent_Rel_eq_blastLower_Rel
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    {x : UnpackedFloat eu su}
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastLowerNonneg ep sp).Rel z ↔
    (x.blastLowerNonneg ep sp).Rel z :=
  EUnpackedFloat.Rel_iff_Rel_of_PartsEq
    (blastLowerNonneg_truncateFittingExponent_PartsEq he hs heu x hnotover hnotunder)

/--
NOTE (statement corrected): the hypothesis `heu : exponentWidth ep sp ≤ eu`
was ADDED (see `blastLowerNonneg_truncateFittingExponent_Rel_eq_blastLower_Rel`
for why the statement is FALSE without it). All call sites have `heu` in scope.
-/
@[simp]
theorem blastUpperNeg_truncateFittingExponent_Rel_eq_blastUpper_Rel
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    {x : UnpackedFloat eu su}
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastUpperNeg ep sp).Rel z ↔
    (x.blastUpperNeg ep sp).Rel z := by
  rw [UnpackedFloat.blastUpperNeg, UnpackedFloat.blastUpperNeg]
  rw [neg_truncateFittingExponent]
  exact EUnpackedFloat.Rel_iff_Rel_of_PartsEq
    (EUnpackedFloat.PartsEq.neg
      (blastLowerNonneg_truncateFittingExponent_PartsEq he hs heu (-x)
        (by simpa using hnotover) (by simpa using hnotunder)))


/--
NOTE (statement corrected): the hypothesis `heu : exponentWidth ep sp ≤ eu`
was ADDED (see `blastLowerNonneg_truncateFittingExponent_Rel_eq_blastLower_Rel`
for why the statement is FALSE without it). All call sites have `heu` in scope.
-/
@[simp]
theorem blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    {x : UnpackedFloat eu su}
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastUpper ep sp).Rel z ↔
    (x.blastUpper ep sp).Rel z := by
  rw [UnpackedFloat.blastUpper, UnpackedFloat.blastUpper]
  simp only [sign_truncateFittingExponent]
  by_cases hsign : x.sign
  · simp only [hsign, if_true]
    exact blastUpperNeg_truncateFittingExponent_Rel_eq_blastUpper_Rel he hs heu hnotover hnotunder
  · simp only [hsign, Bool.false_eq_true, if_false]
    exact EUnpackedFloat.Rel_iff_Rel_of_PartsEq
      (blastUpperNonneg_truncateFittingExponent_PartsEq he hs heu x hnotover hnotunder)

/--
NOTE (statement corrected): the hypothesis `heu : exponentWidth ep sp ≤ eu`
was ADDED (see `blastLowerNonneg_truncateFittingExponent_Rel_eq_blastLower_Rel`
for why the statement is FALSE without it). All call sites have `heu` in scope.
-/
@[simp]
theorem blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu)
    {x : UnpackedFloat eu su}
    (hnotover : x.blastIsEarlyOverflowNonneg ep sp = false)
    (hnotunder : x.blastIsEarlyUnderflowNonneg ep sp = false) :
    ((x.truncateFittingExponent ep sp).blastLower ep sp).Rel z ↔
    (x.blastLower ep sp).Rel z := by
  rw [UnpackedFloat.blastLower, UnpackedFloat.blastLower]
  simp only [sign_truncateFittingExponent]
  by_cases hsign : x.sign
  · simp only [hsign, if_true]
    rw [UnpackedFloat.blastLowerNeg, UnpackedFloat.blastLowerNeg, neg_truncateFittingExponent]
    exact EUnpackedFloat.Rel_iff_Rel_of_PartsEq
      (EUnpackedFloat.PartsEq.neg
        (blastUpperNonneg_truncateFittingExponent_PartsEq he hs heu (-x)
          (by simpa using hnotover) (by simpa using hnotunder)))
  · simp only [hsign, Bool.false_eq_true, if_false]
    exact EUnpackedFloat.Rel_iff_Rel_of_PartsEq
      (blastLowerNonneg_truncateFittingExponent_PartsEq he hs heu x hnotover hnotunder)



/-- The significand width is below `2 ^ (exponentWidth e s - 1)`:
`exponentWidth` reserves enough room for subnormal exponent stealing.
Used to discharge the `hse` hypothesis of `EUnpackedFloat.normalize_Rel_of_Rel`
at `(eu, su) = (exponentWidth ep sp, sp + 1)`. -/
theorem sigWidth_lt_two_pow_exponentWidth_sub_one (e s : Nat) :
    s < 2 ^ (exponentWidth e s - 1) := by
  rw [exponentWidth]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    exact Nat.two_pow_pos _
  · have hpow : 0 < 2 ^ (e - 1) := Nat.two_pow_pos _
    have h0 : 2 ^ (e - 1) + s - 1 ≠ 0 := by omega
    obtain ⟨k, hk, hle, hlt⟩ := Nat.log2_eq_exists _ h0
    rw [hk]
    show s < 2 ^ (k + 1)
    omega

/-# `blastSmtLibRound` matches `smtLibRound` for RNE rounding mode. -/

/--
The final theorem: That our implementation of 'round' matches the SMT-LIB
definition of rounding. But this should be defined carefully.

This is what I'm working on right now.

TODO: Refactor proof to case split on x.isZero, and then derive that y.isZero from this.
-/
theorem UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE
    (he : 1 < ep)
    (hep : 2 < ep)
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
  subst r sign
  rw [UnpackedFloat.blastSmtLibRound]
  simp [UnpackedFloat.toRat_eq_toRat']
  by_cases hzero : x.isZero
  · simp [hzero, hs]
    rw [roundRNE_zero]
    · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
      · grind only
    · grind only
  · by_cases hover : x.blastIsEarlyOverflowNonneg ep sp
    · simp [hover]
      -- rw [blastIsEarlyOverflowNonneg_eq_decide he hs heu x] at hover
      -- simp at hover
      simp [blastRounderSpecialCaseOverflow]
      have hx0 : x.toRat' ≠ 0 := by grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
      simp [hx0]
      rw [roundRNE_eq_infinity_of_maxNormalExp_lt]
      · apply EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign
        · simp
        · grind
        · simp
      · simp [he]
      · simp [hep]
      · simp [hs]
      · -- the sign argument matches the sign of the rational value
        exact UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
      · -- from hover
        exact UnpackedFloat.two_pow_maxNormalExp_succ_le_abs_toRat' he hs heu x hxnorm hzero hover
    · simp [hover]
      -- rw [blastIsEarlyOverflowNonneg_eq_decide he hs heu x] at hover
      -- simp at hover
      by_cases hx0 : x.toRat' = 0
      · simp [hx0]
        rw [roundRNE_zero]
        · apply EUnpackedFloat.Rel_of_Rel_of_isZero_of_isZero_of_eq_sign
          · simp
          · simp; grind only
          · simp
        · grind
      · simp [hx0]
        by_cases hunder : x.blastIsEarlyUnderflowNonneg ep sp
        · simp [hunder]
          -- rw [blastIsEarlyUnderflowNonneg_eq_decide he hs heu x] at hunder
          simp [blastRounderSpecialCaseUnderflow]
          -- need a lemma that says that 'round' on smaller than minSubnormal values gives zero.
          rw [roundRNE_eq_zero_of_lt_minNormalExp]
          · apply EUnpackedFloat.mkZero_Rel_of_isZero ep sp (exponentWidth ep sp) (sp + 1) he
            · grind only
          · simp [he]
          · simp [hs]
          · -- the sign argument matches the sign of the rational value
            exact UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hx0
          · -- from hunder
            exact UnpackedFloat.abs_toRat'_lt_two_pow_of_blastIsEarlyUnderflowNonneg he hs heu x hunder
        · simp [hunder]
          -- rw [blastIsEarlyUnderflowNonneg_eq_decide he hs heu x] at hunder
          -- -- simp at hunder
          rw [UnpackedFloat.blastSmtLibRoundAux, UnpackedFloat.blastSmtLibRoundRNE]
          simp
          rw [blastIsLowerHalf_eq (by grind only) (by grind only)]
          simp only [decide_eq_false_iff_not, decide_eq_true_eq]
          rw [blastIsTieBreak_eq (by grind only) (by grind only)]
          simp only [decide_eq_false_iff_not, decide_eq_true_eq]
          rw [blastIsEvenUpper_eq (by grind only) (by grind only)]
          simp only [Bool.decide_eq_true]
          rw [blastIsEvenLower_eq (by grind only) (by grind only)]
          simp only [Bool.decide_eq_true]
          rw [SmtLibSemantics.RoundMethod.roundRNE]
          simp [hx0]
          rw [toRat'_truncateFittingExponent_of_not_blastIsOverflowNonneg_of_not_blastIsEarlyUnderflowNonneg he hs heu (by grind only) (by grind only)]
          -- use that blastUpper rel smtLiBupper, blastLower rel smtLibLower.
          -- this should just be pure proof automation!
          split
          case neg.isTrue h1 =>
            apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by have := sigWidth_lt_two_pow_exponentWidth_sub_one ep sp; omega) (by sorry)
            rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
            exact blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm
          case neg.isFalse h1 =>
            split
            case isTrue h2 =>
              apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by have := sigWidth_lt_two_pow_exponentWidth_sub_one ep sp; omega) (by sorry)
              rw [blastUpper_truncateFittingExponent_Rel_eq_blastUpper_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
              exact blastUpper_Rel_smtLibUpper hep hs hsu heu x hxnorm
            case isFalse h2 =>
              split
              case isTrue h3 =>
                apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by have := sigWidth_lt_two_pow_exponentWidth_sub_one ep sp; omega) (by sorry)
                rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                exact blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm
              case isFalse h3 =>
                split
                case isTrue h4 =>
                  apply EUnpackedFloat.normalize_Rel_of_Rel (by grind) (by grind) (by grind) _ _ (by have := sigWidth_lt_two_pow_exponentWidth_sub_one ep sp; omega) (by sorry)
                  rw [blastLower_truncateFittingExponent_Rel_eq_blastLower_Rel (by grind) (by grind) (by grind) (by grind) (by grind)]
                  exact blastLower_Rel_smtLibLower hep hs hsu heu x hxnorm
                case isFalse h4 =>
                  apply EUnpackedFloat.Rel_of_state_eq_NaN_of_isNaN
                  · simp
                  · grind

end Fp
