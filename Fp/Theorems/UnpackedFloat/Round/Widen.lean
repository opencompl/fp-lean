import Fp.Theorems.UnpackedFloat.Round.GuardBitIndex
import Fp.Theorems.UnpackedFloat.Round.ExtractGuardBit
import Fp.Theorems.UnpackedFloat.Round.ExtractStickyBit
import Fp.Theorems.UnpackedFloat.Round.OverflowUnderflow

/- # Widening an `UnpackedFloat`

`widen x eu' su'` re-types `x : UnpackedFloat eu su` to `UnpackedFloat eu' su'` (for `eu ≤ eu'`,
`su ≤ su'`) by sign-extending the exponent and appending `su' − su` low zero bits to the significand.
This preserves the value (`toRat'`), the sign, the MSB (normalization), the exponent's over/underflow
classification, and — crucially — the guard and sticky bits (their index shifts by `su' − su`, exactly
matching the significand shift). It lets a proof needing `sp+1`-precision width (`exponentWidth ep (sp+1) ≤ eu`,
`sp+3 ≤ su`) apply to a too-narrow float by widening first.

The body is built from bitblastable `BitVec` primitives (`signExtend`, `setWidth`, `<<<`) so it is
tagged `@[bv_normalize]` and reduces cleanly under `bv_decide`. -/
@[bv_normalize]
def UnpackedFloat.widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat) : UnpackedFloat eu' su' :=
  { sign := x.sign
    ex := x.ex.signExtend eu'
    sig := x.sig.setWidth su' <<< (su' - su) }

namespace Fp

-- `widen` bitblasts: `bv_decide` reduces it via `@[bv_normalize]` with no manual unfolding.
example (x : UnpackedFloat 3 4) (h : x.sig = 5#4) : (x.widen 5 6).sig = 20#6 := by bv_decide
example (x : UnpackedFloat 3 4) : (x.widen 5 6).ex = x.ex.signExtend 5 := by bv_decide

@[simp] theorem sign_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat) :
    (x.widen eu' su').sign = x.sign := rfl

theorem ex_toInt_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat) (heu : eu ≤ eu') :
    (x.widen eu' su').ex.toInt = x.ex.toInt := by
  simp only [UnpackedFloat.widen, BitVec.toInt_signExtend_of_le heu]

theorem sig_toNat_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat) (hsu : su ≤ su') :
    (x.widen eu' su').sig.toNat = x.sig.toNat * 2 ^ (su' - su) := by
  simp only [UnpackedFloat.widen, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth_of_le hsu,
    Nat.shiftLeft_eq]
  have hlt : x.sig.toNat * 2 ^ (su' - su) < 2 ^ su' := by
    have h1 : x.sig.toNat < 2 ^ su := x.sig.isLt
    calc x.sig.toNat * 2 ^ (su' - su) < 2 ^ su * 2 ^ (su' - su) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
      _ = 2 ^ (su + (su' - su)) := by rw [Nat.pow_add]
      _ = 2 ^ su' := by congr 1; omega
  exact Nat.mod_eq_of_lt hlt

/-- The significand bit at index `i` of the widened float is the bit at `i − (su'−su)` of the original
(and `0` below `su'−su`). -/
theorem getLsbD_sig_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat) (i : Nat) :
    (x.widen eu' su').sig.getLsbD i
      = (decide (su' - su ≤ i) && decide (i < su') && x.sig.getLsbD (i - (su' - su))) := by
  simp only [UnpackedFloat.widen, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : su' - su ≤ i <;> by_cases h2 : i < su' <;> simp_all <;> grind

/-- Widening preserves the value. -/
theorem toRat'_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (heu : eu ≤ eu') (hsu : su ≤ su') (hsupos : 0 < su) :
    (x.widen eu' su').toRat' = x.toRat' := by
  simp only [UnpackedFloat.toRat', UnpackedFloat.toSigNat, UnpackedFloat.toExpInt, sign_widen,
    sig_toNat_widen x eu' su' hsu, ex_toInt_widen x eu' su' heu]
  rw [Rat.mul_assoc, Rat.mul_assoc]
  congr 1
  -- ↑(x.sig.toNat * 2^(su'-su)) * 2^(-(↑(su'-1) - x.ex.toInt))
  --   = ↑x.sig.toNat * 2^(-(↑(su-1) - x.ex.toInt))
  rw [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_assoc]
  congr 1
  rw [← Rat.zpow_natCast (2 : Rat) (su' - su), Rat.zpow_mul_zpow (by decide)]
  congr 1
  rw [Int.natCast_sub hsu, Int.natCast_sub (show 1 ≤ su' by omega),
    Int.natCast_sub (show 1 ≤ su by omega)]
  grind

/-- The exponent-difference bounds at width `eu` carry to the wider width `eu'`. -/
private theorem widen_diff_bounds {eu eu' : Nat} (heu : eu ≤ eu') (hge : 1 ≤ eu)
    (d : Int) (hlo : -2 ^ (eu - 1) ≤ d) (hhi : d < 2 ^ (eu - 1)) :
    -2 ^ (eu' - 1) ≤ d ∧ d < 2 ^ (eu' - 1) := by
  have hnat : (2 : Nat) ^ (eu - 1) ≤ 2 ^ (eu' - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcast : ((2 : Int)) ^ (eu - 1) ≤ (2 : Int) ^ (eu' - 1) := by
    have e1 : ((2 : Int)) ^ (eu - 1) = (((2 ^ (eu - 1) : Nat)) : Int) := by rw [Int.natCast_pow]; norm_cast
    have e2 : ((2 : Int)) ^ (eu' - 1) = (((2 ^ (eu' - 1) : Nat)) : Int) := by rw [Int.natCast_pow]; norm_cast
    rw [e1, e2]; exact_mod_cast hnat
  omega

/-- Widening preserves the guard bit (the guard index and the significand shift cancel). -/
theorem blastExtractGuardBit_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (heu' : exponentWidth ep sp ≤ eu') (hsu' : sp + 2 ≤ su')
    (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    (x.widen eu' su').blastExtractGuardBit ep sp = x.blastExtractGuardBit ep sp := by
  have hge : 1 ≤ eu := by
    have : 0 < exponentWidth ep sp := zero_lt_exponentWidth
    omega
  have hb := widen_diff_bounds hwideu hge (minNormalExp ep - x.ex.toInt) hdiffLower hdiffUpper
  rw [UnpackedFloat.extractGuardBit_eq_getLsbD hep hsp heu' hsu' (x.widen eu' su')
        (by rw [ex_toInt_widen x eu' su' hwideu]; exact hb.1)
        (by rw [ex_toInt_widen x eu' su' hwideu]; exact hb.2)
        (by rw [ex_toInt_widen x eu' su' hwideu]; exact hdiffNatLe),
      UnpackedFloat.extractGuardBit_eq_getLsbD hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe,
      ex_toInt_widen x eu' su' hwideu, getLsbD_sig_widen x eu' su']
  have hA : su' - su ≤ su' - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat := by omega
  have hB : su' - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat < su' := by omega
  have hIdx : su' - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat - (su' - su)
            = su - (sp + 2) + (minNormalExp ep - x.ex.toInt).toNat := by omega
  rw [hIdx]
  simp only [hA, hB, decide_true, Bool.true_and, Bool.and_true]

/-- Widening preserves the sticky bit (the discarded low bits are unchanged up to the shift). -/
theorem blastExtractStickyBit_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (heu' : exponentWidth ep sp ≤ eu') (hsu' : sp + 2 ≤ su')
    (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    (x.widen eu' su').blastExtractStickyBit ep sp = x.blastExtractStickyBit ep sp := by
  have hge : 1 ≤ eu := by
    have : 0 < exponentWidth ep sp := zero_lt_exponentWidth
    omega
  have hb := widen_diff_bounds hwideu hge (minNormalExp ep - x.ex.toInt) hdiffLower hdiffUpper
  rw [UnpackedFloat.blastExtractStickyBit_eq_decide hep hsp heu' hsu' (x.widen eu' su')
        (by rw [ex_toInt_widen x eu' su' hwideu]; exact hb.1)
        (by rw [ex_toInt_widen x eu' su' hwideu]; exact hb.2)
        (by rw [ex_toInt_widen x eu' su' hwideu]; exact hdiffNatLe),
      UnpackedFloat.blastExtractStickyBit_eq_decide hep hsp heu hsu x hdiffLower hdiffUpper hdiffNatLe,
      ex_toInt_widen x eu' su' hwideu]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨i, hi, hbit⟩
    rw [getLsbD_sig_widen x eu' su'] at hbit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbit
    obtain ⟨⟨hge', hlt'⟩, hbit⟩ := hbit
    exact ⟨i - (su' - su), by omega, hbit⟩
  · rintro ⟨j, hj, hbit⟩
    refine ⟨j + (su' - su), by omega, ?_⟩
    rw [getLsbD_sig_widen x eu' su']
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show j + (su' - su) - (su' - su) = j by omega]
    exact hbit

/-- Widening preserves the significand MSB (the leading bit moves from `su-1` to `su'-1`). -/
theorem sig_msb_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hsu : su ≤ su') (hsupos : 0 < su) :
    (x.widen eu' su').sig.msb = x.sig.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, getLsbD_sig_widen x eu' su']
  have h1 : su' - su ≤ su' - 1 := by omega
  have h2 : su' - 1 < su' := by omega
  have h3 : su' - 1 - (su' - su) = su - 1 := by omega
  rw [h3]
  simp only [h1, h2, decide_true, Bool.true_and, Bool.and_true]

/-- Widening preserves normalization: if `x` is already normalized then so is its widening. -/
theorem normalize_widen {eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hsu : su ≤ su') (hsupos : 0 < su) (hmsb : x.sig.msb = true) :
    (x.widen eu' su').normalize = x.widen eu' su' :=
  UnpackedFloat.normalize_eq_self_of_msb_eq_true _ (by rw [sig_msb_widen x eu' su' hsu hsupos, hmsb])

/-- Widening preserves the early-overflow flag (it depends only on `ex.toInt`). -/
theorem blastIsEarlyOverflowNonneg_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (heu' : exponentWidth ep sp ≤ eu') (hwideu : eu ≤ eu') :
    (x.widen eu' su').blastIsEarlyOverflowNonneg ep sp = x.blastIsEarlyOverflowNonneg ep sp := by
  rw [UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu' (x.widen eu' su'),
      UnpackedFloat.blastIsEarlyOverflowNonneg_eq_decide he hs heu x,
      ex_toInt_widen x eu' su' hwideu]

/-- Widening preserves the early-underflow flag (it depends only on `ex.toInt`). -/
theorem blastIsEarlyUnderflowNonneg_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (heu' : exponentWidth ep sp ≤ eu') (hwideu : eu ≤ eu') :
    (x.widen eu' su').blastIsEarlyUnderflowNonneg ep sp = x.blastIsEarlyUnderflowNonneg ep sp := by
  rw [UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu' (x.widen eu' su'),
      UnpackedFloat.blastIsEarlyUnderflowNonneg_eq_decide he hs heu x,
      ex_toInt_widen x eu' su' hwideu]

/-- Widening preserves the underflow flag (it depends only on `ex.toInt`). -/
theorem blastIsUnderflowNonneg_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (he : 1 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (heu' : exponentWidth ep sp ≤ eu') (hwideu : eu ≤ eu') :
    (x.widen eu' su').blastIsUnderflowNonneg ep sp = x.blastIsUnderflowNonneg ep sp := by
  rw [UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu' (x.widen eu' su'),
      UnpackedFloat.blastUnderflowNonneg_eq_decide he hs heu x,
      ex_toInt_widen x eu' su' hwideu]

/-- Widening preserves `blastIsLowerHalf` (both branches are functions of guard/sticky/sign). -/
theorem blastIsLowerHalf_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (heu' : exponentWidth ep sp ≤ eu') (hsu' : sp + 2 ≤ su')
    (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    (x.widen eu' su').blastIsLowerHalf ep sp = x.blastIsLowerHalf ep sp := by
  simp only [UnpackedFloat.blastIsLowerHalf, UnpackedFloat.blastIsLowerHalfNonneg,
    UnpackedFloat.blastIsLowerHalfNeg, sign_widen,
    blastExtractGuardBit_widen x eu' su' hep hsp heu hsu heu' hsu' hwideu hwidesu
      hdiffLower hdiffUpper hdiffNatLe,
    blastExtractStickyBit_widen x eu' su' hep hsp heu hsu heu' hsu' hwideu hwidesu
      hdiffLower hdiffUpper hdiffNatLe]

/-- Widening preserves `blastIsTieBreak` (= `guard && !sticky`). -/
theorem blastIsTieBreak_widen {ep sp eu su : Nat} (x : UnpackedFloat eu su) (eu' su' : Nat)
    (hep : 1 < ep) (hsp : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 2 ≤ su)
    (heu' : exponentWidth ep sp ≤ eu') (hsu' : sp + 2 ≤ su')
    (hwideu : eu ≤ eu') (hwidesu : su ≤ su')
    (hdiffLower : -2 ^ (eu - 1) ≤ minNormalExp ep - x.ex.toInt)
    (hdiffUpper : minNormalExp ep - x.ex.toInt < 2 ^ (eu - 1))
    (hdiffNatLe : (minNormalExp ep - x.ex.toInt).toNat ≤ sp) :
    (x.widen eu' su').blastIsTieBreak ep sp = x.blastIsTieBreak ep sp := by
  simp only [UnpackedFloat.blastIsTieBreak, UnpackedFloat.blastIsTieBreakNonneg,
    UnpackedFloat.blastIsTieBreakNeg, sign_widen,
    blastExtractGuardBit_widen x eu' su' hep hsp heu hsu heu' hsu' hwideu hwidesu
      hdiffLower hdiffUpper hdiffNatLe,
    blastExtractStickyBit_widen x eu' su' hep hsp heu hsu heu' hsu' hwideu hwidesu
      hdiffLower hdiffUpper hdiffNatLe]

/-- info: 'Fp.toRat'_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toRat'_widen
/-- info: 'Fp.blastExtractGuardBit_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blastExtractGuardBit_widen
/-- info: 'Fp.blastExtractStickyBit_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blastExtractStickyBit_widen
/-- info: 'Fp.blastIsLowerHalf_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blastIsLowerHalf_widen
/-- info: 'Fp.blastIsTieBreak_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blastIsTieBreak_widen

end Fp
