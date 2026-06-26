import Fp.Theorems.UnpackedFloat.Round.OverflowUnderflow

namespace Fp



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
  rw [isZero_truncateFittingExponent_eq_isZero]
  by_cases hz : x.isZero
  · simp [hz, EUnpackedFloat.PartsEq]
  simp only [hz, Bool.false_eq_true, if_false]
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

end Fp
