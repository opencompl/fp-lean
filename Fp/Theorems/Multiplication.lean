import Fp.Multiplication
import Fp.Theorems.UnpackedRound


/--
The result of raw multiplication, which has an un-normalized
significand and exponent. The interpretation of this bitpattern is given by
MulUnnormalized.toRat.
-/
structure MulUnnormalized (e s : Nat) where
  sig : BitVec (2 * s)
  ex : BitVec (e + 1)
  sign : Bool

@[bv_normalize]
def MulUnnormalized.mul (x y : UnpackedFloat e s) : MulUnnormalized e s :=
  {
    sign := sign
    -- Exponent guaranteed to fit in e+1 bits (no overflow):
    -- max: (2^(e-1) - 1) + (2^(e-1) - 1) + 1 = 2^e - 1 < 2^e
    -- min: -2^(e-1) + -2^(e-1) + 0 = -2^e
    -- Optimization: consider using `Bitvec.adc`
    ex := ex
    -- If product in range [2,4) (i.e., 1x...x), then it is already normalized.
    -- If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
    sig := sig
  }
  where
    -- use 'where' blocks since they create auxiliary defs which can be neatly unfolded.
    sig := x.sig.setWidth' (by omega) * y.sig.setWidth' (by omega)
    ex := x.ex.signExtend (e + 1) + y.ex.signExtend (e + 1)
    sign := x.sign ^^ y.sign

/--
The rational interpretation of this number. See that it has
two bits to the left of the decimal point, since 'sig' is '2s' long,
but the precisoin is `-2(s-1) = 2s - 2`.
This is normalized away in the next step, and this intermediate
computation is 'manually' normalized.
-/
def MulUnnormalized.toRat (m : MulUnnormalized e s) : Rat :=
  m.sign.toSign * m.sig.toNat * (2 : Rat) ^ (- ((2 * (s - 1) : Int) - m.ex.toInt))

/--
Perform the normalization step.
If product in range [2,4) (i.e., 1x...x), then it is already normalized.
If product in range [1,2) (i.e., 01x..x), then normalize by shifting left once.
-/
def MulUnnormalized.mulAdjustMsb (u : MulUnnormalized e s) :
  UnpackedFloat (e + 1) (2 * s) := {
      sign := u.sign
      sig := sig
      ex := ex
    }
  where
    sig := u.sig <<< (BitVec.ofBool (!u.sig.msb))
    ex := u.ex + (BitVec.ofBool u.sig.msb).setWidth' (by omega)

/--
The multiplication circuit can be conceptualized as first

- computing the multiplication as unadjusted, that results in a number that two digits
  to the left of the dot, followed by digits of precision.
- normalizing the unadjusted number to push the msb up.
-/
theorem UnpackedFloat.mul_eq_mulAdjustMsb_mulUnadjustedMsb (x y : UnpackedFloat e s) :
    x.mul y = (MulUnnormalized.mul x y).mulAdjustMsb := by rfl

private theorem Nat.pow_two_eq_mul_self (a : Nat) : a ^ 2 = a * a := by grind

/--
The unadjusted result has the correct rational interpretation.
-/
theorem UnpackedFloat.toRat_mulUnadjustedMsb_eq_toRat_mul_toRat {a b : UnpackedFloat e s}
    (hs : 0 < s) :
    (MulUnnormalized.mul a b).toRat = (a.toRat * b.toRat) := by
  simp [MulUnnormalized.mul, MulUnnormalized.toRat]
  simp [UnpackedFloat.toRat_eq_toRat']
  simp [UnpackedFloat.toRat']
  simp [UnpackedFloat.toExpInt]
  symm
  calc
    _ = ↑a.sign.toSign * ↑a.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - a.ex.toInt)) *
        (↑b.sign.toSign * ↑b.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - b.ex.toInt))) := by grind
    _ = (↑a.sign.toSign * ↑b.sign.toSign) * ↑a.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - a.ex.toInt)) *
        (↑b.sig.toNat * (2 : Rat) ^ (-(↑(s - 1) - b.ex.toInt))) := by grind
    _ = (↑a.sign.toSign * ↑b.sign.toSign) * (↑a.sig.toNat * ↑b.sig.toNat) *
          ((2 : Rat) ^ (-(↑(s - 1) - a.ex.toInt)) * (2 : Rat) ^ (-(↑(s - 1) - b.ex.toInt))) := by grind
  congr 2
  · simp [MulUnnormalized.mul.sign]
  · simp [MulUnnormalized.mul.sig]
    rw [Nat.mod_eq_of_lt]
    · simp
    · have : a.sig.toNat < 2 ^ s := by grind
      have : b.sig.toNat < 2 ^ s := by grind
      rw [Nat.pow_mul']
      rw [Nat.pow_two_eq_mul_self]
      apply Nat.mul_lt_mul'' <;> assumption
  · rw [MulUnnormalized.mul.ex]
    rw [← Rat.zpow_add (show 2 ≠ 0 by decide)]
    rw [BitVec.toInt_add]
    rw [BitVec.toInt_signExtend_of_le (by lia)]
    rw [BitVec.toInt_signExtend_of_le (by lia)]
    rw [Int.bmod_eq_of_le]
    · apply congrArg
      simp [Int.neg_sub]
      norm_cast
      grind
    · grind
    · grind

/--
When multiplying two numbers, if both of them have `msb` true,
then in the result, then either 'msb' or the bit one below the msb is 1.
This shows that to normalize, we only need to shift the msb by one.
-/
theorem BitVec.getMsbD_mul_eq_true_of_msb_eq_true_of_msb_eq_true (x y : BitVec w)
    (hx : x.msb = true) (hy : y.msb = true)
    {z : BitVec (2 * w)}
    (hz : z = (x.zeroExtend (2 * w)) * (y.zeroExtend (2 * w))) :
    z.getMsbD 0 = true ∨ (z.getMsbD 0 = false ∧ z.getMsbD 1 = true) := by
  subst hz
  by_cases hw : w = 0
  · grind only [= msb_eq_getMsbD_zero, = getMsbD_eq_getLsbD]
  · by_cases hw : w = 1
    · subst hw
      simp only [Nat.reduceMul, truncate_eq_setWidth]
      have : x = 1#1 := by grind
      subst this
      have : y = 1#1 := by grind
      subst this
      grind only
    · have : x.toNat ≥ 2 ^ (w - 1) := by
          simp
          exact le_toNat_of_msb_true hx
      have : y.toNat ≥ 2 ^ (w - 1) := by
        simp
        exact le_toNat_of_msb_true hy
      generalize hz : setWidth (2 * w) x *  (setWidth (2 * w) y) = z
      apply Classical.byContradiction
      intros hcontra
      simp at hcontra
      -- TODO: peel this non-overflw proof out
      have hznat : z.toNat = x.toNat * y.toNat := by
        simp [← hz]
        apply Nat.mod_eq_of_lt
        have : x.toNat < 2 ^ w := by grind
        have : y.toNat < 2 ^ w := by grind
        rw [Nat.pow_mul']
        rw [Nat.pow_two_eq_mul_self]
        apply Nat.mul_lt_mul'' <;> grind
      have hcontraGt : z.toNat ≥ 2 ^ (w - 1) * 2 ^ (w - 1) := by
        rw [hznat]
        simp
        apply Nat.mul_le_mul <;> grind
      -- TODO: use this lemma to get the fact that
      -- we will have either msb or one below msb to be true.
      have hcontra' : z.toNat < 2 ^ (2 * w - 2) := by
        apply (BitVec.toNat_lt_iff_getLsbD_eq_false (x := z) (i := 2 * w - 2) (by grind)).mpr
        intros k
        have hk : k = 0 ∨ k = 1 ∨ k ≥ 2 := by grind
        rcases hk with rfl | rfl | hk
        · grind only [= getMsbD_eq_getLsbD]
        · grind only [= msb_eq_getMsbD_zero, = getMsbD_eq_getLsbD, = getLsbD_of_ge]
        · grind only [= msb_eq_getMsbD_zero, = getLsbD_of_ge, = getMsbD_eq_getLsbD]
      have : 2 ^ (w - 1) * 2 ^ (w - 1) = 2 ^(2 * w - 2) := by
        rw [← Nat.pow_add]
        apply congrArg
        grind only [= msb_eq_getMsbD_zero, = getMsbD_eq_getLsbD]
      grind only

/--
The exponent of the unadjusted multiplication result is at most `2^e - 2`,
which allows one to add *one* more bit to be `2^e - 1` and still be in range.
This is important, because we need to add one more bit to the exponent when we adjust the msb.
-/
theorem MulUnnormalized.toInt_ex_le (x y : UnpackedFloat e s) (he : 0 < e):
    (MulUnnormalized.mul x y).ex.toInt ≤ 2 ^ e - 2 := by
  have : ∃ e', e = e' + 1 := by exact Nat.exists_eq_add_one.mpr he
  obtain ⟨e', he'⟩ := this
  subst he'
  simp [MulUnnormalized.mul, mul.ex]
  rw [BitVec.toInt_signExtend_of_le (by lia)]
  rw [BitVec.toInt_signExtend_of_le (by lia)]
  have := x.ex.toInt_le
  have := y.ex.toInt_le
  rw [Int.bmod_eq_of_le]
  · grind
  · grind
  · grind

/--
The result of adjusting the MSB returns the same 'toRat' value.
-/
def MulUnnormalized.mulAdjustMsb_toRat_eq
    (u : MulUnnormalized e s)
    (hs : 0 < s)
    (he : 0 < e)
    -- | Since the exponent comes by adding two sign extended value,
    -- it will be at most 2^(e-1) - 1 + 2^(e-1) - 1 + 1 = 2^e - 1, and at least -2^e.
    (hex : u.ex.toInt ≤ 2 ^ e - 2) :
    u.mulAdjustMsb.toRat = u.toRat := by
  simp [toRat, mulAdjustMsb, UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat', UnpackedFloat.toExpInt]
  rw [Rat.mul_assoc u.sign.toSign]
  rw [Rat.mul_assoc u.sign.toSign]
  rw [Rat.mul_cancel_left (by simp)]
  rw [mulAdjustMsb.sig]
  rcases hmsb : u.sig.msb
  · simp
    rw [Nat.mod_eq_of_lt]
    · simp [Nat.shiftLeft_eq]
      simp [mulAdjustMsb.ex, hmsb]
      rw [Rat.mul_assoc u.sig.toNat]
      by_cases hsig : u.sig = 0#_
      · simp [hsig]
      · rw [Rat.mul_cancel_left (by simp; grind)]
        rw [Rat.mul_self_zpow_eq_zpow_succ]
        grind
    · simp [Nat.shiftLeft_eq]
      grind only [usr BitVec.msb_eq_false_iff_two_mul_lt]
  · simp
    rw [Rat.mul_cancel_left]
    · simp only [mulAdjustMsb.ex, hmsb, BitVec.ofBool_true, BitVec.ofNat_eq_ofNat,
      BitVec.setWidth'_eq, Nat.le_add_left, Nat.pow_one, Nat.lt_add_one,
      BitVec.setWidth_ofNat_of_le_of_lt, BitVec.toInt_add, Nat.lt_add_left_iff_pos, he,
      BitVec.toInt_one_of_lt]
      rw [Int.mul_sub]
      rw [Int.bmod_eq_of_le]
      · grind
      · grind
      · grind
    · grind only [Rat.natCast_eq_zero_iff, usr BitVec.msb_eq_false_iff_two_mul_lt, usr BitVec.isLt]

/--
The result of `MulUnormalized.mulAdjustMsb` is normalized if the inputs are normalized.
i.e, the msb is `true`.
-/
def MulUnnormalized.mulAdjustMsb_msb_eq_true
    (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true)
    (hy : y.sig.msb = true) :
    (MulUnnormalized.mul x y).mulAdjustMsb.sig.msb = true := by
  simp only [mulAdjustMsb, mulAdjustMsb.sig, BitVec.shiftLeft_eq', BitVec.toNat_ofBool,
    BitVec.msb_shiftLeft]
  generalize hz : (mul x y).sig = z
  have : z.getMsbD 0 = true ∨ (z.getMsbD 0 = false ∧ z.getMsbD 1 = true) := by
    apply BitVec.getMsbD_mul_eq_true_of_msb_eq_true_of_msb_eq_true
    · exact hx
    · exact hy
    · rw [← hz]
      simp [mul, mul.sig]
  rcases this with this0 | this1
  · simp [BitVec.msb_eq_getMsbD_zero, this0]
  · simp [BitVec.msb_eq_getMsbD_zero, this1]


/--
The result of `x.mul y` is exact.
-/
theorem toRat_mul_eq_toRat_mul_toRat {a b : UnpackedFloat e s}
    (hs : 0 < s) (he : 0 < e) :
    (a.mul b).toRat = a.toRat * b.toRat := by
  rw [UnpackedFloat.mul_eq_mulAdjustMsb_mulUnadjustedMsb]
  rw [MulUnnormalized.mulAdjustMsb_toRat_eq]
  · rw [UnpackedFloat.toRat_mulUnadjustedMsb_eq_toRat_mul_toRat]
    · grind only
  · grind only
  · grind only
  · have : (MulUnnormalized.mul a b).ex.toInt ≤ 2 ^ e - 2 := by
      apply MulUnnormalized.toInt_ex_le <;> grind only
    grind only
/--
The result of `x.mul y` is normalized.
-/
theorem msb_mul_eq_true_of_msb_eq_true {x y : UnpackedFloat e s}
    (hx : x.sig.msb = true)
    (hy : y.sig.msb = true) :
    (x.mul y).sig.msb = true := by
  rw [UnpackedFloat.mul_eq_mulAdjustMsb_mulUnadjustedMsb]
  apply MulUnnormalized.mulAdjustMsb_msb_eq_true <;> grind only

namespace Fp

theorem unpackNum_mul_unpackNum_toRat_eq_mul_toRat
    {a b : PackedFloat e s}
    (ha : a.isNormOrNonzeroSubnorm := by solve | grind | simp)
    (hb : b.isNormOrNonzeroSubnorm := by solve | grind | simp) :
    -- (hamsb : a.unpackNum.sig.msb = true := by solve | grind | simp)
    -- (hbmsb : b.unpackNum.sig.msb = true := by solve | grind | simp) :
    ((a.unpackNum.mul b.unpackNum).toRat = a.toRat * b.toRat) := by
  have ha : a.toRat = a.unpackNum.toRat := by grind
  rw [ha]
  have hb : b.toRat = b.unpackNum.toRat := by grind
  rw [hb]
  apply toRat_mul_eq_toRat_mul_toRat
  · grind
  · simp [exponentWidth]

set_option trace.Meta.Tactic.simp.all true
set_option diagnostics true
/--
Example theorem we will prove, using our proof strategy of proving against the SMT-Lib semantics.
-/
theorem mul_eq_mul {ein sin : Nat} (hsin : 0 < sin) (he : 0 < ein)
    (rm : RoundingMode) (a b : PackedFloat ein sin) :
    EquivUptoNaN
      (Fp.SmtLibSemantics.SmtLibFunctions.mul (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b)
    (PackedFloat.mul rm a b) := by
  simp [SmtLibSemantics.SmtLibFunctions.mul]
  rw [PackedFloat.mul, EUnpackedFloat.mul]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    simp [hnan]
  case infCase signa =>
    simp [hsin]
    rw [← ExtRat.mul_def]
    unfold ExtRat.mul
    simp
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
    case infCase signb =>
      simp [hsin]
      apply EquivUptoNaN.of_eq
      simp [hsin, he]
    case zeroCase signb =>
      simp [he]
    case numCase hb =>
      -- TODO: prove a theorem that says that 'isNumber -> ∃ r such that b.toExtRat' = Number r'.
      -- Use that to simplify the value.
      -- simp [he, hsin]
      -- | I want this to automatically apply with simp?
      -- rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      -- rw [<- PackedFloat.toExtRat_eq_toExtRat']
      -- rw [← PackedFloat.toExtRat_unpack_eq_toExtRat]
      rw [b.toExtRat'_eq_toRat_of hb]
      simp [b.toRat_ne_zero hb]
      simp [show ¬ b.isNaN by grind]
      simp [show ¬ b.isZero by grind]
      apply EquivUptoNaN.of_eq
      have : b.unpack.num.sign = decide (b.toRat < 0) := by
        rw [b.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
        simp only [EUnpackedFloat.num_mkNumber, PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign]
        grind only [→ PackedFloat.sign_iff_toRat_neg]
      simp [this, hsin, he]
  case zeroCase sign =>
    simp [he]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
    case infCase signb =>
      simp [hsin]
    case zeroCase signb =>
      simp [he]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign, hsin]
      simp [show decide (ein = 0) = false by grind]
      apply EquivUptoNaN.of_eq
      grind only
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      simp
      rw [b.toExtRat'_eq_toRat_of hb]
      simp only [ExtRat.number_mul_number_eq, Rat.zero_mul, round_eq_mkZero_of_mkZero, he, hsin]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign]
      simp [show ¬ b.isNaN by grind]
      simp [show ¬ b.isInfinite by grind]
      apply EquivUptoNaN.of_eq
      grind only
      -- TODO: prove a theorem that says that 'isNumber -> ∃ r such that b.toExtRat' = Number r'.
      -- Use that to simplify the value.
  case numCase ha =>
    rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha]
    rw [a.toExtRat'_eq_toRat_of ha]
    -- interesting case, when a is a number.
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp [hb]
    case infCase signb =>
      simp [hsin]
      have : ¬ a.isZero := by grind
      simp [this]
      rw [← ExtRat.mul_def, ExtRat.mul]
      simp only [SmtLibSemantics.instExtendedRat, SmtLibSemantics.instExtendedRat.eq_1, roundQ_eq]
      simp [show a.toRat < 0 ↔ a.sign = true by grind]
      simp [show a.toRat = 0 ↔ a.isZero by grind]
      simp [show ¬ a.isZero by grind]
      apply EquivUptoNaN.of_eq
      simp [hsin, he]
      rw [show (signb ^^ a.sign) = (a.sign ^^ signb) by grind]
    case zeroCase signb =>
      simp [he]
      simp [SmtLibSemantics.SmtLibFunctions.xorSign, hsin]
      apply EquivUptoNaN.of_eq
      grind only
    case numCase hb =>
      simp [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb]
      rw [b.toExtRat'_eq_toRat_of hb]
      have : ¬ a.isZero := by grind
      simp [this]
      have : ¬ b.isZero := by grind
      apply EquivUptoNaN.of_eq
      simp [this, -BitVec.toNat, -PackedFloat.eq_getInfinity_of_getInfinity_le, - ExtRat.ExtRat.eq_of_le_of_le]
      rw [SmtLibSemantics_round_eq_pack_UnpackedFloat_round (r := a.toRat * b.toRat)]
      · apply msb_mul_eq_true_of_msb_eq_true
        · exact PackedFloat.msb_unpackNum_eq_true ha
        · exact PackedFloat.msb_unpackNum_eq_true hb
      · simp [this]
      · apply unpackNum_mul_unpackNum_toRat_eq_mul_toRat
        · grind
        · grind
end Fp
