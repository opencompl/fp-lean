import Fp.FMA
import Fp.Theorems.Addition
import Fp.Theorems.Multiplication

/-!
# Correctness of `fma`

`UnpackedFloat.fma x y z = add (mul x y) (z.extendWidths …)`.  The intermediate
product `mul x y` is *exact* (`toRat_mul_eq_toRat_mul_toRat`), so the addition's
sticky-error analysis applies to the true value `x·y + z`, and the single final
`blastSmtLibRound` is covered by the shared rounding bridge.

This file first establishes value/normalization lemmas for `UnpackedFloat.extendWidths`
(which previously had no lemmas), then the fma sticky bound, then the top-level
`fma_eq_fma`.
-/

open Fp

namespace UnpackedFloat

/-- Extending widths scales the significand by `2 ^ (s' - s)` (the left shift). -/
theorem toNat_sig_extendWidths {e s e' s' : Nat} (uf : UnpackedFloat e s)
    (he : e ≤ e') (hs : s ≤ s') :
    (uf.extendWidths he hs).sig.toNat = uf.sig.toNat * 2 ^ (s' - s) := by
  simp only [UnpackedFloat.extendWidths, BitVec.setWidth'_eq, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth]
  have hlt : uf.sig.toNat < 2 ^ s := uf.sig.isLt
  have h1 : uf.sig.toNat % 2 ^ s' = uf.sig.toNat := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hs)
  rw [h1, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc uf.sig.toNat * 2 ^ (s' - s) < 2 ^ s * 2 ^ (s' - s) :=
        Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
    _ = 2 ^ s' := by rw [← Nat.pow_add]; congr 1; omega

/-- Extending widths preserves the exponent value. -/
theorem toInt_ex_extendWidths {e s e' s' : Nat} (uf : UnpackedFloat e s)
    (he : e ≤ e') (hs : s ≤ s') :
    (uf.extendWidths he hs).ex.toInt = uf.ex.toInt := by
  simp only [UnpackedFloat.extendWidths]
  exact BitVec.toInt_signExtend_of_le he

/-- Extending widths preserves the sign. -/
@[simp] theorem sign_extendWidths {e s e' s' : Nat} (uf : UnpackedFloat e s)
    (he : e ≤ e') (hs : s ≤ s') :
    (uf.extendWidths he hs).sign = uf.sign := rfl

/-- Extending widths preserves the value. -/
theorem toRat_extendWidths {e s e' s' : Nat} (uf : UnpackedFloat e s)
    (he : e ≤ e') (hs : s ≤ s') (hs0 : 0 < s) :
    (uf.extendWidths he hs).toRat = uf.toRat := by
  rw [toRat_eq_sign_sig_exp, toRat_eq_sign_sig_exp,
    sign_extendWidths, toNat_sig_extendWidths uf he hs]
  simp only [toExpInt, toInt_ex_extendWidths uf he hs]
  push_cast
  have key : (2 : Rat) ^ (s' - s) * (2 : Rat) ^ (-(((s' - 1 : Nat) : Int) - uf.ex.toInt))
      = (2 : Rat) ^ (-(((s - 1 : Nat) : Int) - uf.ex.toInt)) := by
    rw [show ((2 : Rat) ^ (s' - s)) = (2 : Rat) ^ (((s' - s : Nat)) : Int) from
        (Rat.zpow_natCast 2 _).symm]
    rw [← Rat.zpow_add (by decide)]
    congr 1
    omega
  -- goal: sign * (↑sig * 2^(s'-s)) * 2^E' = sign * ↑sig * 2^E
  grind

/-- Extending widths preserves the significand's msb. -/
theorem msb_extendWidths {e s e' s' : Nat} (uf : UnpackedFloat e s)
    (he : e ≤ e') (hs : s ≤ s') (hs0 : 0 < s) :
    (uf.extendWidths he hs).sig.msb = uf.sig.msb := by
  rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, toNat_sig_extendWidths uf he hs]
  congr 1
  rw [show (2 ^ (s' - 1)) = 2 ^ (s - 1) * 2 ^ (s' - s) by rw [← Nat.pow_add]; congr 1; omega]
  rw [Nat.mul_le_mul_right_iff (Nat.two_pow_pos _)]

/-- Negation commutes with width extension (both only touch the sign / zero-extend). -/
theorem neg_extendWidths {e s e' s' : Nat} (uf : UnpackedFloat e s)
    (he : e ≤ e') (hs : s ≤ s') :
    (uf.neg).extendWidths he hs = (uf.extendWidths he hs).neg := rfl

/-- The fma circuit value is a sticky compression of the exact value `x·y + z`.
The intermediate product is exact, so this is just the addition sticky bound applied
to `(mul x y) + (extend z)`. -/
theorem stickyEquiv_fma {e s : Nat} (x y z : UnpackedFloat e s)
    (hs : 0 < s) (he : 0 < e)
    (hes : 2 * s + 3 < 2 ^ (e + 2)) (hbnd : 2 * s + 1 ≤ 2 ^ e)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) (hz : z.sig.msb = true)
    (hne : x.toRat * y.toRat + z.toRat ≠ 0) :
    StickyEquiv ((UnpackedFloat.fma x y z).toExpInt) ((UnpackedFloat.fma x y z).toRat)
      (x.toRat * y.toRat + z.toRat) := by
  simp only [UnpackedFloat.fma]
  have hA : (x.mul y).toRat = x.toRat * y.toRat :=
    UnpackedFloat.toRat_mul_eq_toRat_mul_toRat hs he
  have hB : (z.extendWidths (e' := e + 1) (s' := 2 * s) (by omega) (by omega)).toRat = z.toRat :=
    UnpackedFloat.toRat_extendWidths z (by omega) (by omega) hs
  have hxmsb : (x.mul y).sig.msb = true :=
    UnpackedFloat.msb_mul_eq_true_of_msb_eq_true hx hy
  have hzmsb : (z.extendWidths (e' := e + 1) (s' := 2 * s) (by omega) (by omega)).sig.msb = true := by
    rw [UnpackedFloat.msb_extendWidths z (by omega) (by omega) hs]; exact hz
  have hmain := UnpackedFloat.stickyEquiv_add (x.mul y) (z.extendWidths (e' := e + 1) (s' := 2 * s) (by omega) (by omega))
    (by omega) (by omega) hes hbnd hxmsb hzmsb (by rw [hA, hB]; exact hne)
  rw [hA, hB] at hmain
  exact hmain

/-- fma sticky bound lifted to the unpacked numbers of packed inputs, with the
exponent-range side-conditions discharged from `1 < e` / `2 < e`
(mirrors `unpackNum_add_unpackNum_stickyEquiv`). -/
theorem unpackNum_fma_stickyEquiv
    {e s : Nat} {a b c : PackedFloat e s} (hs : 0 < s) (he : 1 < e) (hep : 2 < e)
    (ha : a.isNormOrNonzeroSubnorm) (hb : b.isNormOrNonzeroSubnorm)
    (hc : c.isNormOrNonzeroSubnorm)
    (hne : a.toRat * b.toRat + c.toRat ≠ 0) :
    StickyEquiv ((UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum).toExpInt)
      ((UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum).toRat)
      (a.toRat * b.toRat + c.toRat) := by
  have hra := PackedFloat.unpackNum_toRat_eq_toRat (pf := a) ha
  have hrb := PackedFloat.unpackNum_toRat_eq_toRat (pf := b) hb
  have hrc := PackedFloat.unpackNum_toRat_eq_toRat (pf := c) hc
  rw [← hra, ← hrb, ← hrc] at hne ⊢
  have h2e : 2 ≤ 2 ^ (e - 1) := by
    calc (2 : Nat) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlog : 2 ^ (e - 1) + s - 1 < 2 ^ ((2 ^ (e - 1) + s - 1).log2 + 1) := Nat.lt_log2_self
  have hew : exponentWidth e s = (2 ^ (e - 1) + s - 1).log2 + 2 := by rw [exponentWidth]
  have hbnd' : 2 * (s + 1) + 1 ≤ 2 ^ (exponentWidth e s) := by
    rw [hew, show (2 ^ (e - 1) + s - 1).log2 + 2 = ((2 ^ (e - 1) + s - 1).log2 + 1) + 1 by omega,
      Nat.pow_succ]
    omega
  have hes' : 2 * (s + 1) + 3 < 2 ^ (exponentWidth e s + 2) := by
    rw [hew, show (2 ^ (e - 1) + s - 1).log2 + 2 + 2 = ((2 ^ (e - 1) + s - 1).log2 + 1) + 3 by omega,
      Nat.pow_add]
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    omega
  exact stickyEquiv_fma a.unpackNum b.unpackNum c.unpackNum (by omega)
    zero_lt_exponentWidth hes' hbnd'
    (PackedFloat.msb_unpackNum_eq_true ha) (PackedFloat.msb_unpackNum_eq_true hb)
    (PackedFloat.msb_unpackNum_eq_true hc) hne

end UnpackedFloat

namespace Fp

/-- `Number r * Infinity s = Infinity (r.sign ^^ s)` for a nonzero, representable `r`. -/
theorem number_mul_inf_eq {ein sin : Nat} {a : PackedFloat ein sin}
    (ha : a.isNormOrNonzeroSubnorm) (s : Bool) :
    ExtRat.Number a.toRat * ExtRat.Infinity s = ExtRat.Infinity (a.sign ^^ s) := by
  have hne : a.toRat ≠ 0 := PackedFloat.toRat_ne_zero ha
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  simp only [hne, ↓reduceIte]
  rw [PackedFloat.sign_iff_toRat_neg ha, Bool.xor_comm]

/-- `Infinity s * Number r = Infinity (s ^^ r.sign)` for a nonzero, representable `r`. -/
theorem inf_mul_number_eq {ein sin : Nat} {a : PackedFloat ein sin}
    (ha : a.isNormOrNonzeroSubnorm) (s : Bool) :
    ExtRat.Infinity s * ExtRat.Number a.toRat = ExtRat.Infinity (s ^^ a.sign) := by
  have hne : a.toRat ≠ 0 := PackedFloat.toRat_ne_zero ha
  rw [← ExtRat.mul_def]
  unfold ExtRat.mul
  simp only [hne, ↓reduceIte]
  rw [PackedFloat.sign_iff_toRat_neg ha]

open SmtLibSemantics in
/-- Passthrough helper when the fma value is a genuine infinity `Infinity xy` (the product
is infinite and the addend cannot cancel it, except an opposite-signed infinite addend which
yields NaN). Used by the `infCase` special-value leaves. -/
theorem fmaInfAddPassthrough {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (he0 : 0 < ein) (rm : RoundingMode) (hrm : rm = .RNE) (sgn xy : Bool) (c : PackedFloat ein sin) :
    ((smtLibRoundMethod ein sin smtLibV smtLibV).round rm sgn
        (ExtRat.Infinity xy + c.toExtRat')).EquivUptoNaN
      ((bif c.unpack.isNaN || c.unpack.isInfinite && (xy != c.unpack.sign) then EUnpackedFloat.mkNaN
        else EUnpackedFloat.mkInfinity (bif c.unpack.isInfinite then c.unpack.sign else xy)).pack) := by
  cases c using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hc =>
    simp only [hc, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
      EUnpackedFloat.isNaN_mkNaN, Bool.true_or, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
      PackedFloat.EquivUptoNaN.of_mkNaN_iff]
    rw [ExtRat.ExtRat.add_NaN]
    exact isNaN_round_of_nan
  case infCase signc =>
    simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true, PackedFloat.unpack_getInfinity,
      ↓reduceIte, PackedFloat.sign_getInfinity, EUnpackedFloat.isNaN_mkInfinity,
      EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.sign_mkInfinity, Bool.false_or,
      cond_true]
    have hcinf : (PackedFloat.getInfinity ein sin signc).toExtRat' = ExtRat.Infinity signc :=
      PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _
        (by simp [PackedFloat.isInfinite_getInfinity, hsin])
    rw [hcinf]
    by_cases hxy : xy = signc
    · subst hxy
      have hval : ExtRat.Infinity xy + ExtRat.Infinity xy = ExtRat.Infinity xy := by
        rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; grind [ExtRat]
      simp only [hval, bne_self_eq_false, cond_false, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp [roundQ_eq_round_of_Infinity he0 hsin]
    · have hval : ExtRat.Infinity xy + ExtRat.Infinity signc = ExtRat.NaN := by
        rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; grind [ExtRat]
      have hbne : (xy != signc) = true := by grind
      simp only [hval, hbne, Bool.and_self, Bool.true_and, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      exact isNaN_round_of_nan
  case zeroCase signc =>
    simp only [PackedFloat.isZero_getZero, he0, PackedFloat.unpack_getZero, ↓reduceIte,
      PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero,
      Bool.and_false, Bool.or_false, cond_false, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
    have hc0 : (PackedFloat.getZero ein sin signc).toExtRat' = ExtRat.Number 0 :=
      PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
    have hval : ExtRat.Infinity xy + ExtRat.Number 0 = ExtRat.Infinity xy := by
      rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; grind [ExtRat]
    rw [hc0, hval]
    apply PackedFloat.EquivUptoNaN.of_eq
    simp [roundQ_eq_round_of_Infinity he0 hsin]
  case numCase hc =>
    have hcz : c.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false c hc
    rw [c.toExtRat'_eq_toRat_of hc,
      PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hc]
    simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
      Bool.and_false, Bool.or_false, cond_false, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
    have hval : ExtRat.Infinity xy + ExtRat.Number c.toRat = ExtRat.Infinity xy := by
      rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; grind [ExtRat]
    rw [hval]
    apply PackedFloat.EquivUptoNaN.of_eq
    simp [roundQ_eq_round_of_Infinity he0 hsin]

open SmtLibSemantics in
/-- Passthrough helper: when the fma value collapses to `Number 0 + c` (one factor is a
zero, so the exact product is `0`), the circuit returns `z = c.unpack` (branching only on
`c`'s kind) and the spec rounds `c`'s value. Used by the `zeroCase` special-value leaves. -/
theorem fmaZeroAddPassthrough {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (he0 : 0 < ein) (rm : RoundingMode) (hrm : rm = .RNE) (xy : Bool) (c : PackedFloat ein sin) :
    ((smtLibRoundMethod ein sin smtLibV smtLibV).round rm
        (if rm = .RTN then xy || c.sign else xy && c.sign) (ExtRat.Number 0 + c.toExtRat')).EquivUptoNaN
      ((bif c.unpack.isNaN then EUnpackedFloat.mkNaN
        else bif c.unpack.isInfinite then
          EUnpackedFloat.mkInfinity (bif c.unpack.isInfinite then c.unpack.sign else xy)
        else bif c.unpack.isZero then
          EUnpackedFloat.mkZero (bif xy == c.unpack.sign then c.unpack.sign else rm == .RTN)
        else c.unpack).pack) := by
  cases c using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hc =>
    simp only [hc, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
      EUnpackedFloat.isNaN_mkNaN, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
      PackedFloat.EquivUptoNaN.of_mkNaN_iff]
    rw [ExtRat.ExtRat.add_NaN]
    exact isNaN_round_of_nan
  case infCase signc =>
    simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
      PackedFloat.unpack_getInfinity, ↓reduceIte, PackedFloat.sign_getInfinity,
      EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkInfinity,
      EUnpackedFloat.sign_mkInfinity, cond_true, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
    have hvinf : (PackedFloat.getInfinity ein sin signc).toExtRat' = ExtRat.Infinity signc :=
      PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _
        (by simp [PackedFloat.isInfinite_getInfinity, hsin])
    have hval : ExtRat.Number 0 + ExtRat.Infinity signc = ExtRat.Infinity signc := by
      rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; grind [ExtRat]
    rw [hvinf, hval]
    apply PackedFloat.EquivUptoNaN.of_eq
    simp [roundQ_eq_round_of_Infinity he0 hsin]
  case zeroCase signc =>
    simp only [PackedFloat.isZero_getZero, he0, PackedFloat.unpack_getZero, ↓reduceIte,
      PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero,
      EUnpackedFloat.isZero_mkZero, cond_false, cond_true]
    have hv0 : (PackedFloat.getZero ein sin signc).toExtRat' = ExtRat.Number 0 :=
      PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
    rw [hv0, ExtRat.ExtRat.add_Number, Rat.add_zero, round_eq_mkZero_of_mkZero he0,
      EUnpackedFloat.mkZero_pack_eq_getZero]
    apply PackedFloat.EquivUptoNaN.of_eq
    subst hrm
    grind
  case numCase hc =>
    have hcz : c.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false c hc
    rw [c.toExtRat'_eq_toRat_of hc, ExtRat.ExtRat.add_Number, Rat.zero_add,
      round_number_toRat_eq_self he0 hsin rm _ c hc,
      PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hc]
    simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
      EUnpackedFloat.isZero_mkNumber, hcz, Bool.false_eq_true, cond_false]
    apply PackedFloat.EquivUptoNaN.of_eq
    rw [← PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hc]
    exact (PackedFloat.unpack_pack_eq_self_of_isNormOrNonzeroSubnorm he hsin c hc).symm

set_option maxHeartbeats 1000000 in
theorem fma_eq_fma {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (rm : RoundingMode) (hrm : rm = .RNE) (a b c : PackedFloat ein sin) :
    (Fp.SmtLibSemantics.SmtLibFunctions.fma (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b c).EquivUptoNaN
      (PackedFloat.fma rm a b c) := by
  have he0 : 0 < ein := by grind
  simp only [SmtLibSemantics.SmtLibFunctions.fma, SmtLibSemantics.SmtLibFunctions.fmaSign,
    SmtLibSemantics.SmtLibFunctions.xorSign,
    SmtLibSemantics.smtLibRoundMethod.embed_eq, SmtLibSemantics.smtLibV_embed_eq,
    SmtLibSemantics.RoundableEmbed.embed_packedFloat_eq,
    PackedFloat.toExtRat_eq_toExtRat', roundQ_eq]
  rw [PackedFloat.fma, EUnpackedFloat.fma]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    simp only [hnan, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
      EUnpackedFloat.isNaN_mkNaN, Bool.true_or, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
      PackedFloat.EquivUptoNaN.of_mkNaN_iff]
    rw [ExtRat.NaN_mul, ExtRat.ExtRat.NaN_add]
    exact isNaN_round_of_nan
  case infCase signa => sorry
  case zeroCase signa =>
    simp only [PackedFloat.isZero_getZero, he0, PackedFloat.unpack_getZero, ↓reduceIte,
      PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero,
      EUnpackedFloat.isZero_mkZero, EUnpackedFloat.mkZero_num_sign,
      Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_false, Bool.false_and, Bool.true_or,
      cond_false]
    have ha0 : (PackedFloat.getZero ein sin signa).toExtRat' = ExtRat.Number 0 :=
      PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
    rw [ha0]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
        EUnpackedFloat.isNaN_mkNaN, Bool.true_or, Bool.or_true, cond_true,
        EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [ExtRat.mul_NaN, ExtRat.ExtRat.NaN_add]
      exact isNaN_round_of_nan
    case infCase signb =>
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true, PackedFloat.unpack_getInfinity,
        ↓reduceIte, EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.isNaN_mkInfinity,
        Bool.and_true, Bool.or_true, Bool.true_or, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
        PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      have hbinf : (PackedFloat.getInfinity ein sin signb).toExtRat' = ExtRat.Infinity signb :=
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _
          (by simp [PackedFloat.isInfinite_getInfinity, hsin])
      rw [hbinf, ExtRat.zero_mul_inf_eq, ExtRat.ExtRat.NaN_add]
      exact isNaN_round_of_nan
    case zeroCase signb =>
      have hbz0 : (PackedFloat.getZero ein sin signb).toExtRat' = ExtRat.Number 0 :=
        PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
      simp only [PackedFloat.isZero_getZero, he0, PackedFloat.unpack_getZero, ↓reduceIte,
        PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero,
        EUnpackedFloat.isZero_mkZero, EUnpackedFloat.mkZero_num_sign, Bool.or_self, Bool.false_and,
        Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
        Bool.false_eq_true, cond_false, cond_true]
      rw [hbz0, ExtRat.number_mul_number_eq, Rat.mul_zero]
      exact fmaZeroAddPassthrough hsin he hep he0 rm hrm (signa ^^ signb) c
    case numCase hb =>
      have hbz : b.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false b hb
      simp only [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.num_mkNumber, hbz, Bool.or_self,
        Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
        Bool.false_eq_true, cond_false, cond_true,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign]
      rw [b.toExtRat'_eq_toRat_of hb, ExtRat.number_mul_number_eq, Rat.zero_mul]
      exact fmaZeroAddPassthrough hsin he hep he0 rm hrm (signa ^^ b.sign) c
  case numCase ha =>
    rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha, a.toExtRat'_eq_toRat_of ha]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
        EUnpackedFloat.isNaN_mkNaN, EUnpackedFloat.isNaN_mkNumber, Bool.or_true, Bool.true_or,
        cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [ExtRat.mul_NaN, ExtRat.ExtRat.NaN_add]
      exact isNaN_round_of_nan
    case infCase signb =>
      have haz : a.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false a ha
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true, PackedFloat.unpack_getInfinity,
        ↓reduceIte, EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkInfinity,
        EUnpackedFloat.sign_num_mkInfinity, EUnpackedFloat.isZero_mkInfinity,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.num_mkNumber, haz,
        PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign, Bool.or_self, Bool.false_and,
        Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.true_or,
        Bool.false_eq_true, cond_false]
      have hbinf : (PackedFloat.getInfinity ein sin signb).toExtRat' = ExtRat.Infinity signb :=
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _
          (by simp [PackedFloat.isInfinite_getInfinity, hsin])
      rw [hbinf, number_mul_inf_eq ha signb]
      exact fmaInfAddPassthrough hsin he hep he0 rm hrm _ (a.sign ^^ signb) c
    case zeroCase signb =>
      have haz : a.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false a ha
      simp only [PackedFloat.isZero_getZero, he0,
        PackedFloat.unpack_getZero, ↓reduceIte, PackedFloat.sign_getZero,
        EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isZero_mkZero,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.num_mkNumber, haz, Bool.or_self,
        Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
        Bool.false_eq_true, cond_false, cond_true]
      -- value `a·0 + c = c`
      have hb0 : (PackedFloat.getZero ein sin signb).toExtRat' = ExtRat.Number 0 :=
        PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
      rw [hb0, ExtRat.number_mul_number_eq, Rat.mul_zero]
      cases c using PackedFloat.kindCasesNaNInfZeroNum
      case nanCase hc =>
        simp only [hc, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
          EUnpackedFloat.isNaN_mkNaN, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
          PackedFloat.EquivUptoNaN.of_mkNaN_iff]
        rw [ExtRat.ExtRat.add_NaN]
        exact isNaN_round_of_nan
      case infCase signc =>
        simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
          PackedFloat.unpack_getInfinity, ↓reduceIte, PackedFloat.sign_getInfinity,
          EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkInfinity,
          EUnpackedFloat.sign_mkInfinity, cond_true, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
        have hvinf : (PackedFloat.getInfinity ein sin signc).toExtRat' = ExtRat.Infinity signc :=
          PackedFloat.toExtRat'_eq_Infinity_of_isInfinite _
            (by simp [PackedFloat.isInfinite_getInfinity, hsin])
        have hval : ExtRat.Number 0 + ExtRat.Infinity signc = ExtRat.Infinity signc := by
          rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; grind [ExtRat]
        rw [hvinf, hval]
        apply PackedFloat.EquivUptoNaN.of_eq
        simp [roundQ_eq_round_of_Infinity he0 hsin]
      case zeroCase signc =>
        simp only [PackedFloat.isZero_getZero, he0, PackedFloat.toExtRat'_eq_zero_of_isZero,
          PackedFloat.unpack_getZero, ↓reduceIte, PackedFloat.sign_getZero,
          EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isZero_mkZero,
          cond_false, cond_true]
        have hv0 : (PackedFloat.getZero ein sin signc).toExtRat' = ExtRat.Number 0 :=
          PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
        rw [hv0, ExtRat.ExtRat.add_Number, Rat.add_zero, round_eq_mkZero_of_mkZero he0,
          EUnpackedFloat.mkZero_pack_eq_getZero]
        apply PackedFloat.EquivUptoNaN.of_eq
        subst hrm
        have h1 := PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign a
        grind
      case numCase hc =>
        have hcz : c.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false c hc
        rw [c.toExtRat'_eq_toRat_of hc, ExtRat.ExtRat.add_Number, Rat.zero_add,
          round_number_toRat_eq_self he0 hsin rm _ c hc,
          PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hc]
        simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
          EUnpackedFloat.isZero_mkNumber, hcz, Bool.false_eq_true, cond_false]
        apply PackedFloat.EquivUptoNaN.of_eq
        rw [← PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hc]
        exact (PackedFloat.unpack_pack_eq_self_of_isNormOrNonzeroSubnorm he hsin c hc).symm
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb, b.toExtRat'_eq_toRat_of hb]
      cases c using PackedFloat.kindCasesNaNInfZeroNum
      case nanCase hc =>
        simp only [hc, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
          EUnpackedFloat.isNaN_mkNaN, EUnpackedFloat.isNaN_mkNumber, Bool.or_true, Bool.true_or,
          cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
        rw [ExtRat.number_mul_number_eq, ExtRat.ExtRat.add_NaN]
        exact isNaN_round_of_nan
      case infCase signc =>
        simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true, ↓reduceIte,
          PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.unpack_getInfinity,
          PackedFloat.sign_getInfinity, EUnpackedFloat.isInfinite_mkInfinity,
          EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isZero_mkInfinity,
          EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
          EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.sign_mkInfinity, EUnpackedFloat.num_mkNumber,
          Bool.or_self, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.or_true,
          Bool.and_true, cond_true, cond_false, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
        rw [ExtRat.number_mul_number_eq]
        have hval : ExtRat.Number (a.toRat * b.toRat) + ExtRat.Infinity signc
            = ExtRat.Infinity signc := by
          rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp
        rw [hval]
        apply PackedFloat.EquivUptoNaN.of_eq
        simp [roundQ_eq_round_of_Infinity he0 hsin]
      case zeroCase signc =>
        have haz : a.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false a ha
        have hbz : b.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false b hb
        simp only [PackedFloat.isZero_getZero, PackedFloat.toExtRat'_eq_zero_of_isZero,
          PackedFloat.unpack_getZero, he0, ↓reduceIte,
          PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero,
          EUnpackedFloat.isZero_mkZero, EUnpackedFloat.isNaN_mkNumber,
          EUnpackedFloat.isInfinite_mkNumber, EUnpackedFloat.isZero_mkNumber,
          EUnpackedFloat.num_mkNumber, haz, hbz, Bool.or_self, Bool.false_and, Bool.and_false,
          Bool.false_or, Bool.or_false, Bool.false_eq_true, cond_false, cond_true]
        have hv0 : (PackedFloat.getZero ein sin signc).toExtRat' = ExtRat.Number 0 :=
          PackedFloat.toExtRat'_eq_zero_of_isZero _ (by simp [PackedFloat.isZero_getZero, he0])
        rw [hv0, ExtRat.number_mul_number_eq, ExtRat.ExtRat.add_Number, Rat.add_zero]
        have hmsb : (a.unpackNum.mul b.unpackNum).sig.msb = true :=
          UnpackedFloat.msb_mul_eq_true_of_msb_eq_true
            (PackedFloat.msb_unpackNum_eq_true ha) (PackedFloat.msb_unpackNum_eq_true hb)
        have hxnorm : (a.unpackNum.mul b.unpackNum).normalize = a.unpackNum.mul b.unpackNum :=
          UnpackedFloat.normalize_eq_self_of_msb_eq_true _ hmsb
        have hmulrat : (a.unpackNum.mul b.unpackNum).toRat = a.toRat * b.toRat :=
          UnpackedFloat.unpackNum_mul_unpackNum_toRat_eq_mul_toRat ha hb
        have hne : a.toRat * b.toRat ≠ 0 :=
          Rat.mul_ne_zero_iff.mpr ⟨PackedFloat.toRat_ne_zero ha, PackedFloat.toRat_ne_zero hb⟩
        have hsticky : StickyEquiv ((a.unpackNum.mul b.unpackNum).toExpInt)
            ((a.unpackNum.mul b.unpackNum).toRat) (a.toRat * b.toRat) := by
          rw [hmulrat]; exact StickyEquiv.rfl
        rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
        subst hrm
        refine EUnpackedFloat.pack'_EquivUptoNaN_of_Rel he hsin _ _ ?hrel ?hpack ?hpf
        case hrel =>
          exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv he hep hsin
            (eu := exponentWidth ein sin + 1) (su := 2 * (sin + 1)) (by omega) (by omega)
            (a.unpackNum.mul b.unpackNum) _ _ hne hxnorm hsticky
        case hpack =>
          exact UnpackedFloat.blastSmtLibRound_Packable_of_RNE hep hsin (by omega) (by omega)
            (a.unpackNum.mul b.unpackNum) hxnorm
        case hpf =>
          exact UnpackedFloat.blastSmtLibRound_finite_of_RNE_of_stickyEquiv he hep hsin
            (by omega) (by omega) (a.unpackNum.mul b.unpackNum) _ _ hne hxnorm hsticky
      case numCase hc =>
        rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hc, c.toExtRat'_eq_toRat_of hc]
        rw [ExtRat.number_mul_number_eq, ExtRat.ExtRat.add_Number]
        have hamsb := PackedFloat.msb_unpackNum_eq_true ha
        have hbmsb := PackedFloat.msb_unpackNum_eq_true hb
        have hcmsb := PackedFloat.msb_unpackNum_eq_true hc
        have hABmsb : (a.unpackNum.mul b.unpackNum).sig.msb = true :=
          UnpackedFloat.msb_mul_eq_true_of_msb_eq_true hamsb hbmsb
        have hCextmsb : (c.unpackNum.extendWidths (e' := exponentWidth ein sin + 1)
            (s' := 2 * (sin + 1)) (by omega) (by omega)).sig.msb = true := by
          rw [UnpackedFloat.msb_extendWidths (e' := exponentWidth ein sin + 1)
            (s' := 2 * (sin + 1)) c.unpackNum (by omega) (by omega) (by omega)]
          exact hcmsb
        -- exact value of the two `add` operands
        have hAB : (a.unpackNum.mul b.unpackNum).toRat = a.toRat * b.toRat :=
          UnpackedFloat.unpackNum_mul_unpackNum_toRat_eq_mul_toRat ha hb
        have hCext : (c.unpackNum.extendWidths (e' := exponentWidth ein sin + 1)
            (s' := 2 * (sin + 1)) (by omega) (by omega)).toRat = c.toRat := by
          rw [UnpackedFloat.toRat_extendWidths (e' := exponentWidth ein sin + 1)
            (s' := 2 * (sin + 1)) c.unpackNum (by omega) (by omega) (by omega)]
          exact PackedFloat.unpackNum_toRat_eq_toRat hc
        have haz : a.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false a ha
        have hbz : b.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false b hb
        have hcz : c.unpackNum.isZero = false := PackedFloat.isZero_unpackNum_eq_false c hc
        -- simplify the special-value guards of the `bif` cascade (all false for numbers)
        simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
          EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.num_mkNumber, haz, hbz, hcz, Bool.or_self,
          Bool.false_and, Bool.and_false, Bool.false_eq_true,
          cond_false]
        by_cases hcancel : (a.unpackNum.mul b.unpackNum).structBeq
            ((c.unpackNum.neg).extendWidths (e' := exponentWidth ein sin + 1)
              (s' := 2 * (sin + 1)) (by omega) (by omega))
        · -- exact cancellation: `a*b + c = 0`
          have hsum0 : a.toRat * b.toRat + c.toRat = 0 := by
            have h := UnpackedFloat.toRat_add_toRat_eq_zero_of_structBeq_neg
              (a.unpackNum.mul b.unpackNum)
              (c.unpackNum.extendWidths (e' := exponentWidth ein sin + 1)
                (s' := 2 * (sin + 1)) (by omega) (by omega))
              (by rw [← UnpackedFloat.neg_extendWidths]; exact hcancel)
            rw [hAB, hCext] at h
            exact h
          rw [hsum0, round_eq_mkZero_of_mkZero he0]
          simp only [hcancel, cond_true, EUnpackedFloat.mkZero_pack_eq_getZero]
          apply PackedFloat.EquivUptoNaN.of_eq
          subst hrm
          have hsg := hcancel
          simp only [UnpackedFloat.structBeq, Bool.and_eq_true, beq_iff_eq,
            UnpackedFloat.mul_sign, UnpackedFloat.sign_extendWidths, UnpackedFloat.neg] at hsg
          have h1 := PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign a
          have h2 := PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign b
          have h3 := PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign c
          grind
        · -- genuine nonzero fma, rounded by the circuit
          have hsumne : a.toRat * b.toRat + c.toRat ≠ 0 := by
            have h := UnpackedFloat.toRat_add_toRat_ne_zero_of_not_structBeq_neg
              (a.unpackNum.mul b.unpackNum)
              (c.unpackNum.extendWidths (e' := exponentWidth ein sin + 1)
                (s' := 2 * (sin + 1)) (by omega) (by omega))
              hABmsb hCextmsb (by rw [← UnpackedFloat.neg_extendWidths]; exact hcancel)
            rw [hAB, hCext] at h
            exact h
          have hfmamsb : (UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum).sig.msb = true := by
            simp only [UnpackedFloat.fma]
            exact UnpackedFloat.msb_add_eq_true _ _ (by omega) hABmsb hCextmsb
              (by rw [hAB, hCext]; exact hsumne)
          have hxnorm : (UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum).normalize
              = UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum :=
            UnpackedFloat.normalize_eq_self_of_msb_eq_true _ hfmamsb
          have hsticky := UnpackedFloat.unpackNum_fma_stickyEquiv hsin he hep ha hb hc hsumne
          rw [Bool.not_eq_true] at hcancel
          rw [hcancel, cond_false]
          rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
          subst hrm
          refine EUnpackedFloat.pack'_EquivUptoNaN_of_Rel he hsin _ _ ?hrel ?hpack ?hpf
          case hrel =>
            exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv he hep hsin
              (eu := exponentWidth ein sin + 2) (su := 2 * (sin + 1) + 2) (by omega) (by omega)
              (UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum) _ _ hsumne hxnorm hsticky
          case hpack =>
            exact UnpackedFloat.blastSmtLibRound_Packable_of_RNE hep hsin (by omega) (by omega)
              (UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum) hxnorm
          case hpf =>
            exact UnpackedFloat.blastSmtLibRound_finite_of_RNE_of_stickyEquiv he hep hsin
              (by omega) (by omega) (UnpackedFloat.fma a.unpackNum b.unpackNum c.unpackNum) _ _
              hsumne hxnorm hsticky

end Fp
