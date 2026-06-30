import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Grind
import Fp.Utils.Nat

@[bv_normalize]
def BitVec.leadingOne (w : Nat) : BitVec w :=
  1#w <<< (w - 1)

@[simp]
def BitVec.getElem_leadingOne (w : Nat) (i : Nat) (hi : i < w ) : (BitVec.leadingOne w)[i] = decide (i = w - 1) := by
  simp [leadingOne]
  grind

@[bv_normalize]
def BitVec.decrement (x : BitVec w) : BitVec w := x - 1#w

@[bv_normalize]
def BitVec.extendAtMsb (x : BitVec w) (δ : Nat) : BitVec (δ + w) :=
  x.zeroExtend _

/-- Extract from the MSB, starting at msb lo, going downward for 'len' bits.
0<----------------------->(w-1)
----------->loMsb----|len
           |
            <-----------------loLsb

-/
@[bv_normalize]
def BitVec.extractMsb' (x : BitVec w) (loMsb : Nat) (len : Nat) :
    BitVec len :=
  (x.reverse.extractLsb' loMsb len).reverse

theorem BitVec.getLsbD_extractMsb' {w lo len : Nat} (x : BitVec w)
    (i : Nat):
    (extractMsb' x lo len).getMsbD i =
    (x.getMsbD (lo + i) && decide (i < len) && decide (lo + i < w)) := by
  simp [extractMsb', BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_reverse]
  by_cases h1 : i < len
  · simp [h1]
    simp [show len - 1 - i < len by omega]
    simp [show len - 1 - (len - 1 - i) < len by omega]
    simp [show len - 1 - (len - 1 - i) = i by omega]
    intros h2 h3
    have := BitVec.lt_of_getLsbD h3
    omega
  · simp [h1]

/-- Taking the top `len` bits (`extractMsb' _ 0 len`) reads off the high part of the
value: it equals `x >>> (w - len)` truncated to `len` bits. -/
theorem BitVec.extractMsb'_zero_eq_setWidth_ushiftRight {w len : Nat} (x : BitVec w)
    (h : len ≤ w) :
    BitVec.extractMsb' x 0 len = (x >>> (w - len)).setWidth len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < len
  · have lhs : (BitVec.extractMsb' x 0 len).getLsbD i
        = (BitVec.extractMsb' x 0 len).getMsbD (len - 1 - i) := by
      rw [BitVec.getMsbD_eq_getLsbD]
      have h1 : len - 1 - i < len := by grind
      simp only [h1, decide_true, Bool.true_and]
      congr 1
      grind
    rw [lhs, BitVec.getLsbD_extractMsb']
    have h1 : len - 1 - i < len := by grind
    have h2 : (0 : Nat) + (len - 1 - i) < w := by grind
    simp only [Nat.zero_add, h1, h2, decide_true, Bool.and_true, Bool.true_and]
    rw [BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    have h3 : len - 1 - i < w := by grind
    simp only [h3, hi, decide_true, Bool.true_and]
    congr 1
    grind
  · rw [BitVec.getLsbD_setWidth,
        BitVec.getLsbD_of_ge (BitVec.extractMsb' x 0 len) i (Nat.le_of_not_lt hi)]
    simp [hi]

/-- `toNat` of the top `len` bits is the high quotient `x.toNat / 2 ^ (w - len)`. -/
theorem BitVec.toNat_extractMsb'_zero {w len : Nat} (x : BitVec w) (h : len ≤ w) :
    (BitVec.extractMsb' x 0 len).toNat = x.toNat / 2 ^ (w - len) := by
  rw [BitVec.extractMsb'_zero_eq_setWidth_ushiftRight x h, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add]
  have : w - len + len = w := by grind
  rw [this]
  exact x.isLt

@[bv_normalize]
def BitVec.expandingSubtract {w} (a b : BitVec w) : BitVec (w + 1) :=
  let a' : BitVec (w + 1) := a.signExtend (w + 1)
  let b' : BitVec (w + 1) := b.signExtend (w + 1)
  a' - b'


@[simp]
theorem BitVec.toInt_expandingSubtract {w} (a b : BitVec w) :
  (expandingSubtract a b).toInt = a.toInt - b.toInt := by
  simp [expandingSubtract, toInt_signExtend]
  have : 2 ^ (w + 1) / 2 = 2^w := by grind
  apply Int.bmod_eq_of_le <;> grind


@[bv_normalize]
def BitVec.width {w : Nat} (_x : BitVec w) : Nat := w

/-- bitvector that has 1 at index i and 0 everywhere else. -/
@[bv_normalize]
def BitVec.oneHotBV (i : BitVec w) : BitVec w :=
    1#w <<< i

@[simp]
theorem BitVec.getlsbD_oneHotBV (i : BitVec w) :
    (oneHotBV i).getLsbD j =
    (decide (j < w) && decide (i.toNat = j)) := by
  simp [oneHotBV]
  by_cases h1 : j < w
  · simp [h1]
    grind
  · simp [h1]

@[simp]
theorem BitVec.getElem_oneHotBV (i : BitVec w) (j : Fin w) :
    (oneHotBV i)[j] = decide (i.toNat = j) := by
  simp [← BitVec.getLsbD_eq_getElem]

/-- `oneHotBV i` (a single bit set at position `i.toNat`) has value `2 ^ i.toNat`,
provided that position is in range. -/
theorem BitVec.toNat_oneHotBV {w : Nat} (i : BitVec w) (hi : i.toNat < w) :
    (BitVec.oneHotBV i).toNat = 2 ^ i.toNat := by
  have hlt : 2 ^ i.toNat < 2 ^ w := Fp.Nat.two_pow_lt_two_pow_of_lt hi
  have heq : BitVec.oneHotBV i = BitVec.twoPow w i.toNat := rfl
  rw [heq, BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt]

/-- The single leading (top) bit `leadingOne w = 1 <<< (w-1)` has value `2 ^ (w-1)`. -/
theorem BitVec.toNat_leadingOne {w : Nat} (hw : 0 < w) :
    (BitVec.leadingOne w).toNat = 2 ^ (w - 1) := by
  have hlt : 2 ^ (w - 1) < 2 ^ w := Fp.Nat.two_pow_lt_two_pow_of_lt (by grind)
  have heq : BitVec.leadingOne w = BitVec.twoPow w (w - 1) := rfl
  rw [heq, BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt]

/-- Value of the `lsbMask` used by `blastSuccessorAwayFromZero`: the guard-bit one-hot
mask zero-extended by one bit and shifted left by one is `2 ^ (g.toNat + 1)`. -/
theorem BitVec.toNat_zeroExtend_oneHotBV_shiftLeft_one {su : Nat} (g : BitVec su)
    (hg : g.toNat + 1 < su) :
    (((BitVec.oneHotBV g).setWidth (su + 1)) <<< 1).toNat = 2 ^ (g.toNat + 1) := by
  have hone : (BitVec.oneHotBV g).toNat = 2 ^ g.toNat := BitVec.toNat_oneHotBV g (by grind)
  have hfit : 2 ^ g.toNat < 2 ^ (su + 1) := Fp.Nat.two_pow_lt_two_pow_of_lt (by grind)
  have hfit2 : 2 ^ (g.toNat + 1) < 2 ^ (su + 1) := Fp.Nat.two_pow_lt_two_pow_of_lt (by grind)
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, hone, Nat.mod_eq_of_lt hfit,
    Nat.shiftLeft_eq]
  have hpow : 2 ^ g.toNat * 2 ^ 1 = 2 ^ (g.toNat + 1) := by rw [← Nat.pow_add]
  rw [hpow, Nat.mod_eq_of_lt hfit2]


/-- Convert a binary number into a unary mask of that number. -/
@[bv_normalize]
def BitVec.orderEncode (x : BitVec w) : BitVec w :=
  (oneHotBV x) - 1

theorem BitVec.orderEncode_eq_oneHotBV_sub (x : BitVec w) :
    BitVec.orderEncode x = oneHotBV x - 1 := rfl

@[simp]
theorem BitVec.orderEncode_eq_allOnes_of_le {w : Nat} (x : BitVec w)
    (h : w ≤ x.toNat) :
    orderEncode x = allOnes w := by
  simp [orderEncode, oneHotBV]
  rw [BitVec.shiftLeft_eq_zero]
  · simp [BitVec.neg_one_eq_allOnes]
  · omega

theorem BitVec.getLsbD_orderEncode_of_lt (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x).getLsbD i = (decide (i < x.toNat)) := by
  by_cases hi : x.toNat < w
  · rw [orderEncode]
    · -- ⊢ (1#w <<< x - 1).getLsbD i = decide (i < x.toNat)
      have hw0 : 0 < w := by grind
      have h1mod : 1 % 2^w = 1 := by grind only [= Nat.mod_eq_of_lt, usr Nat.pow_pos, usr Nat.div_pow_of_pos]
      have hshiftx  : (1 <<< x.toNat) % 2^w = 2 ^x.toNat := by
        rw [Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt]
        · simp
        · simp only [Nat.one_mul]
          apply Nat.pow_lt_pow_of_lt
          · grind only
          · grind only
      by_cases hw : w = 1
      · subst hw 
        simp [oneHotBV, show x.toNat = 0 by grind]
      · simp [oneHotBV]
        rw [BitVec.getLsbD]
        rw [BitVec.toNat_sub_of_le]
        · simp [h1mod]
          rw [hshiftx]
          rw [Nat.testBit_two_pow_sub_one]
        · rw [BitVec.le_def]
          simp [h1mod]
          rw [Nat.mod_eq_of_lt]
          · grind only [= Nat.shiftLeft_eq, usr Nat.pow_pos]
          · rw [Nat.shiftLeft_eq]
            simp
            apply Nat.pow_lt_pow_of_lt
            · grind only
            · grind only
  · rw [BitVec.orderEncode_eq_allOnes_of_le]
    · simp; omega
    · omega

/--
info: 'BitVec.getLsbD_orderEncode_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms BitVec.getLsbD_orderEncode_of_lt

theorem BitVec.getElem_orderEncode_of_lt {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x)[i] = (decide (i < x.toNat)) := by
  rw [← getLsbD_eq_getElem]
  apply BitVec.getLsbD_orderEncode_of_lt x i hi

@[simp]
theorem BitVec.getLsbD_orderEncode {w : Nat} (x : BitVec w) (i : Nat) :
    (orderEncode x).getLsbD i = (decide (i < x.toNat) && decide (i < w)) := by
  by_cases hi : i < w
  · simp [hi]
    rw [BitVec.getElem_orderEncode_of_lt]
  · rw [BitVec.getLsbD_of_ge x.orderEncode i (by omega)]
    simp; omega

@[simp]
theorem BitVec.getElem_orderEncode {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x)[i] = (decide (i < x.toNat)) := by
  rw [← getLsbD_eq_getElem]
  rw [BitVec.getLsbD_orderEncode x i]
  simp [hi]

@[simp]
theorem BitVec.orderEncode_eq_shiftRight_allOnes {x : BitVec w} :
    orderEncode x = BitVec.allOnes w >>> (w - x.toNat) := by
  ext i hi
  simp
  omega


/-- Clearing the guard bit `g` together with all sticky bits below it (the mask
`~~~(oneHotBV g ||| orderEncode g)`) zeroes exactly the low `g.toNat + 1` bits:
the result is `v` shifted right then left by `g.toNat + 1`. -/
theorem BitVec.and_not_oneHotBV_or_orderEncode_eq {w : Nat} (v g : BitVec w) :
    v &&& ~~~(BitVec.oneHotBV g ||| BitVec.orderEncode g)
      = (v >>> (g.toNat + 1)) <<< (g.toNat + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hiw
  by_cases hL : g.toNat + 1 ≤ i
  · rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or,
        BitVec.getlsbD_oneHotBV, BitVec.getLsbD_orderEncode_of_lt g i hiw,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    have he : g.toNat + 1 + (i - (g.toNat + 1)) = i := by grind
    rw [he]
    grind
  · rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or,
        BitVec.getlsbD_oneHotBV, BitVec.getLsbD_orderEncode_of_lt g i hiw,
        BitVec.getLsbD_shiftLeft]
    grind

/--
info: 'BitVec.and_not_oneHotBV_or_orderEncode_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms BitVec.and_not_oneHotBV_or_orderEncode_eq

/-- `toNat` form of `and_not_oneHotBV_or_orderEncode_eq`: clearing the low
`g.toNat + 1` bits rounds the value down to a multiple of `2 ^ (g.toNat + 1)`. -/
theorem BitVec.toNat_and_not_oneHotBV_or_orderEncode {w : Nat} (v g : BitVec w) :
    (v &&& ~~~(BitVec.oneHotBV g ||| BitVec.orderEncode g)).toNat
      = v.toNat / 2 ^ (g.toNat + 1) * 2 ^ (g.toNat + 1) := by
  rw [BitVec.and_not_oneHotBV_or_orderEncode_eq, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self v.toNat _) v.isLt

/--
info: 'BitVec.toNat_and_not_oneHotBV_or_orderEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms BitVec.toNat_and_not_oneHotBV_or_orderEncode

/-- `orderEncode g` is the mask of the low `g.toNat` bits, so its value is `2^g.toNat − 1`. -/
theorem BitVec.toNat_orderEncode_of_le {w : Nat} (g : BitVec w) (hg : g.toNat ≤ w) :
    (BitVec.orderEncode g).toNat = 2 ^ g.toNat - 1 := by
  rcases Nat.lt_or_ge g.toNat w with h | h
  · have hw : 0 < w := by grind
    have hstrict : 2 ^ g.toNat < 2 ^ w := Nat.pow_lt_pow_right (by grind) h
    rw [BitVec.orderEncode_eq_oneHotBV_sub, BitVec.toNat_sub, BitVec.toNat_oneHotBV g h]
    have h1 : (1 : BitVec w).toNat = 1 := BitVec.toNat_one hw
    have hX1 : 1 ≤ 2 ^ g.toNat := Nat.one_le_two_pow
    rw [h1]
    have key : 2 ^ w - 1 + 2 ^ g.toNat = 2 ^ w + (2 ^ g.toNat - 1) := by grind
    rw [key, Nat.add_mod_left, Nat.mod_eq_of_lt (by grind)]
  · have hgw : g.toNat = w := by grind
    rw [BitVec.orderEncode_eq_allOnes_of_le _ (by grind), BitVec.toNat_allOnes, hgw]

/-- ANDing with `orderEncode g` keeps exactly the low `g.toNat` bits — i.e. the bits an arithmetic
right shift by `g.toNat` would discard. This is how the addition circuit detects its sticky bit. -/
theorem BitVec.toNat_and_orderEncode {w : Nat} (v g : BitVec w) (hg : g.toNat ≤ w) :
    (v &&& BitVec.orderEncode g).toNat = v.toNat % 2 ^ g.toNat := by
  rw [BitVec.toNat_and, BitVec.toNat_orderEncode_of_le g hg, Nat.and_two_pow_sub_one_eq_mod]

@[simp]
theorem BitVec.clz_zero (w : Nat) : (0#w : BitVec w).clz = w := by
  rw [BitVec.clz_eq_iff_eq_zero]


@[simp, grind =]
theorem toNat_clz_lt_iff_ne_zero (x : BitVec w) : x.clz.toNat < w ↔ x ≠ 0#w := by
  have := BitVec.clz_lt_iff_ne_zero (x := x)
  by_cases hx : x = 0#w
  · simp [hx]
  · simp [hx]
    have := this.mpr (by grind only)
    simp [BitVec.lt_def] at this
    grind only

/--
Shifting by the clz never overflows.
-/
theorem toNat_shiftLeft_clz_eq_toNat (x : BitVec w) :
    (x <<< x.clz.toNat).toNat = x.toNat <<< x.clz.toNat := by
  by_cases hs : w = 0
  · simp [hs]
    grind only [= Nat.shiftLeft_eq, = BitVec.toNat_zero_length]
  · by_cases hsig : x = 0#w
    · simp [hsig]
    · simp only [BitVec.toNat_shiftLeft]
      apply Nat.mod_eq_of_lt
      have : x.toNat < 2 ^ w := by grind
      have := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (x := x) (by grind only) (by grind only)
      have := BitVec.toNat_lt_two_pow_sub_clz (x := x) (w := w)
      have : x.clz.toNat < w := by
        grind only [#2867]
      rw [Nat.shiftLeft_eq]
      apply Nat.lt_of_lt_of_le (m := 2 ^ (w - x.clz.toNat) * (2 ^ x.clz.toNat))
      · apply Nat.mul_lt_mul_of_lt_of_le
        · grind only
        · apply Nat.pow_le_pow_of_le
          · grind only
          · grind only
        · grind only [usr Nat.pow_pos]
      · rw [← Nat.pow_add]
        apply Nat.pow_le_pow_of_le
        · grind only
        · grind only

@[simp, grind =]
theorem getMsbD_true_clz_of_ne_zero {x : BitVec w} :
    x.getMsbD ((x.clz).toNat) = (decide (x ≠ 0#w)) := by
  by_cases hw : w = 0
  · grind only [= BitVec.getMsbD_of_ge, = BitVec.toNat_zero_length]
  · by_cases hx : x = 0#w
    · simp [hx]
    · rw [BitVec.getMsbD_eq_getLsbD]
      rw [BitVec.getLsbD_true_clz_of_ne_zero]
      · grind only [= toNat_clz_lt_iff_ne_zero]
      · grind only
      · grind only

/-- The clz is zero iff the msb is true, or the width is zero. -/
@[simp]
theorem BitVec.clz_eq_zero_iff_msb_of_lt (x : BitVec w) : x.clz = 0#w ↔ (x.msb = true ∨ w = 0) := by
  by_cases hw : w = 0
  · subst hw
    grind only
  · constructor
    · intros h
      have h' : x.clz.toNat = 0 := by grind
      grind only [BitVec.msb_eq_decide, BitVec.clz_eq_zero_iff]
    · intros h
      rw [← BitVec.toNat_inj]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      grind only [!BitVec.clz_eq_zero_iff, !BitVec.le_toNat_of_msb_true]

/--
Shifting a nonzero bitvector left by its leading-zero count sets the msb.
(This is what `UnpackedFloat.normalize` relies on.)
-/
theorem BitVec.msb_shiftLeft_clz_of_ne_zero {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
    (x <<< x.clz).msb = true := by
  rw [show (x <<< x.clz) = x <<< x.clz.toNat from rfl, BitVec.msb_eq_getMsbD,
    BitVec.getMsbD_shiftLeft, Nat.zero_add, getMsbD_true_clz_of_ne_zero]
  simp [hx]

/--
If we shift left by 1 and we get the same bitvector, the bitvector must be zero.
-/
@[simp]
theorem BitVec.shiftLeft_one_eq_self_iff_eq_zero (x : BitVec w) :
    x <<< 1 = x ↔ x = 0#w := by
  by_cases hx : x = 0#w
  · simp [hx]
  · simp only [hx, iff_false]
    intros hcontra
    have : x.toNat ≠ 0 := by
      intros hcontra
      apply hx
      apply BitVec.eq_of_toNat_eq
      simp only [hcontra, BitVec.toNat_ofNat, Nat.zero_mod]
    have hcontra : (x <<< 1).toNat = x.toNat := by grind only
    simp only [BitVec.toNat_shiftLeft] at hcontra
    rw [Nat.shiftLeft_eq] at hcontra
    simp only [Nat.pow_one] at hcontra
    by_cases hval : x.toNat * 2 < 2 ^ w
    · rw [Nat.mod_eq_of_lt] at hcontra
      · grind only
      · grind only
    · have : x.toNat * 2 < 2 * 2^w := by grind only [usr BitVec.isLt]
      have : x.toNat * 2 - 2 ^ w < 2^w := by grind only
      rw [Nat.mod_eq_sub_mod] at hcontra
      · rw [Nat.mod_eq_of_lt] at hcontra
        · grind only
        · grind only
      · grind only

@[simp]
theorem BitVec.shiftLeft_one_ne_self_iff (x : BitVec w) :
    x <<< 1 ≠ x ↔ x ≠ 0#w := by
  have := BitVec.shiftLeft_one_eq_self_iff_eq_zero x
  grind

theorem BitVec.ne_iff_getLsbD_ne (x y : BitVec w) : x ≠ y ↔ (∃ (i : Nat), x.getLsbD i ≠ y.getLsbD i) := by
  constructor
  · intros hxy
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    apply hxy
    ext i
    apply hcontra i
  · intros h1 h2
    subst h2
    grind only

/--
Private lemma for establishing that 'x <<< n = x'
implies that the bits at positions 'n + i' and 'i' are the same.
-/
protected theorem BitVec.getLsbD_add_eq_getLsbD_of_shiftLeft_eq_self {w i} {x : BitVec w} {n : Nat} (hx : x <<< n = x) (hi : n + i < w) :
    x.getLsbD (n + i) = x.getLsbD i := by
  conv =>
    lhs
    rw [← hx]
  simp
  intros hi
  grind

/--
Private lemma for establishing that 'x <<< n = x'
implies that the bits at positions 'k*n + i' and 'i' are the same.
-/
protected theorem BitVec.getLsbD_mul_add_eq_getLsbD_of_shiftLeft_eq_self
    {x : BitVec w} {n : Nat} (hx : x <<< n = x) (hi : k * n + i < w) :
    x.getLsbD (k * n + i) = x.getLsbD i := by
  induction k generalizing i
  case zero => simp
  case succ k ih =>
    simp [Nat.add_mul]
    rw [Nat.add_assoc]
    rw [ih]
    · apply BitVec.getLsbD_add_eq_getLsbD_of_shiftLeft_eq_self <;> grind
    · rw [Nat.add_mul] at hi
      grind


/--
If x <<< n = x and n > 0, then x must be zero.
-/
protected theorem BitVec.eq_zero_of_shiftLeft_eq_self_of_lt
    {x : BitVec w} {n : Nat} (hx : x <<< n = x)  (hn : 0 < n) :
    x = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intros i hi
  have : i = (i / n) * n + (i % n) := by
    grind [Nat.div_add_mod]
  rw [this]
  rw [BitVec.getLsbD_mul_add_eq_getLsbD_of_shiftLeft_eq_self hx (by grind)]
  rw [← hx]
  have : i % n < n := by
    apply Nat.mod_lt
    grind
  simp [this]

/--
If we shift left by n and we get the same bitvector, then either `n = 0` or the bitvector is zero.
-/
theorem BitVec.shiftLeft_eq_self_iff_eq_zero {x : BitVec w} {n : Nat} :
      x <<< n = x ↔ (n = 0 ∨ x = 0#w) := by
  by_cases hx0 : x = 0#w
  · simp [hx0]
  · simp [hx0]
    constructor
    · intros hx
      by_cases hn : n = 0
      · simp [hn]
      · have := BitVec.eq_zero_of_shiftLeft_eq_self_of_lt hx (by grind)
        grind
    · intros hn
      subst hn
      simp

@[simp]
theorem BitVec.cons_false_eq_zero_iff_eq_zero {x : BitVec w} :
  (BitVec.cons false x = 0#(w + 1)) ↔ x = 0#w := by
  constructor
  · intros hcons
    ext i hi
    simp only [getElem_zero]
    have := congrFun (congrArg BitVec.getLsbD hcons) (i)
    simp only [getLsbD_zero] at this
    rw [BitVec.getLsbD_cons] at this
    simp only [show i ≠ w by grind only, ↓reduceIte] at this
    grind only [= getLsbD_eq_getElem]
  · intros hzero
    subst hzero
    simp
@[grind .]
protected theorem BitVec.eq_allOnes_iff_toNat_eq (x : BitVec w) :
    x = .allOnes w ↔ x.toNat = 2 ^ w - 1 := by
  constructor
  · intros h
    subst h
    simp
  · intros h
    apply BitVec.toNat_inj.mp
    simp [h]


@[grind .]
protected theorem BitVec.eq_zero_iff_toNat_eq (x : BitVec w) :
    x = .zero w ↔ x.toNat = 0 := by
  constructor
  · intros h
    subst h
    simp
  · intros h
    apply BitVec.toNat_inj.mp
    simp [h]

@[simp high]
theorem BitVec.toNat_allOnes_sub_one_eq_twoPow_sub_two (n : Nat) (hn : 0 < n) :
    BitVec.toNat (BitVec.allOnes n - 1#n) = 2 ^ n - 2 := by
  rw [BitVec.toNat_sub_of_le]
  · simp [hn]
    grind
  · rw [BitVec.le_def]
    simp [hn]
    grind

@[simp]
theorem BitVec.one_le_allOnes (n : Nat) : 1#n ≤ BitVec.allOnes n := by
  rw [BitVec.le_def]
  simp
  grind

@[simp]
theorem BitVec.sub_le_iff_le_add (a b c : BitVec n)
    (hle' : c ≤ a)
    (hbc : b.toNat + c.toNat < 2^n) : a - c ≤ b ↔ a ≤ b + c := by
  rw [BitVec.le_def]
  rw [BitVec.le_def]
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_add_of_lt]
    · grind
    · grind
  · grind


theorem BitVec.allOnes_ne_zero {e : Nat} :
    e = 0 ∨ BitVec.allOnes e ≠ BitVec.zero e := by
  match e with
  | 0     => left; rfl
  | e + 1 =>
    right
    simp only [BitVec.allOnes, BitVec.zero, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNatLT]
    grind only [!Nat.two_pow_pos]
attribute [grind .] BitVec.toNat_inj
attribute [grind .] BitVec.toInt_inj
@[simp]
theorem BitVec.allOnes_eq_one_iff (e : Nat) : BitVec.allOnes e = 1#e ↔ e ≤ 1 := by
  constructor
  · intros h
    have := BitVec.toNat_inj.mpr h
    simp at this
    apply Classical.byContradiction
    intros hcontra
    simp at hcontra
    rw [Nat.mod_eq_of_lt] at this
    · have : 4 ≤ 2^e := by simp [hcontra]
      grind only
    · have : 4 ≤ 2^e := by simp [hcontra]
      grind only
  · intros h
    rcases e with rfl | rfl | e
    · grind only
    · grind only
    · grind only
/--
The only way we can get 'x = x+1` is if the width is zero.
-/
theorem BitVec.add_one_eq_self_iff (x : BitVec w) : x = x + 1#w ↔ w = 0 := by
  constructor
  · intros h
    have hcontra := BitVec.toNat_inj.mpr h
    simp [BitVec.toNat_add] at hcontra
    have : x.toNat < 2^w := by grind
    by_cases hxlt : x.toNat + 1 < 2^w
    · rw [Nat.mod_eq_of_lt] at hcontra
      · grind only
      · grind only
    · have hx : x.toNat = 2^w - 1 := by grind
      rw [hx] at hcontra
      rw [show 2^w - 1 + 1 = 2^w by grind] at hcontra
      simp at hcontra
      rcases w with rfl | w
      · simp
      · simp [Nat.pow_succ] at hcontra
        have : 0 < 2^w := by grind only
        grind only
  · intros h
    simp [h]
@[simp]
theorem BitVec.ofInt_eq_zero_iff_of_width_1 :
    BitVec.ofInt 1 i = 0#1 ↔ i % 2 = 0 := by
  constructor
  · intros h
    have := BitVec.toInt_inj.mpr h
    simp only [BitVec.toInt_ofInt, BitVec.toInt_zero] at this
    simp at this
    grind only [#8803]
  · intros h
    apply BitVec.eq_of_toInt_eq
    simp
    grind only [#8803]


-- TODO: upstream
theorem BitVec.toNat_clz_le {x : BitVec w} : x.clz.toNat ≤ w := by
  suffices h : x.clz.toNat ≤ (BitVec.ofNat w w).toNat from by
    simpa using h
  simp only [← BitVec.ule_iff_toNat_le, BitVec.ule_iff_le]
  apply BitVec.clz_le
theorem BitVec.toNat_clz_lt_iff_ne_zero {x : BitVec w} : x.clz.toNat < w ↔ x.toNat ≠ 0 := by
  suffices h : x.clz.toNat < (BitVec.ofNat w w).toNat ↔ x.toNat ≠ (BitVec.ofNat w 0).toNat from by
    simpa using h
  simp only [← BitVec.ult_iff_toNat_lt, BitVec.ult_iff_lt, ne_eq, BitVec.toNat_inj]
  apply BitVec.clz_lt_iff_ne_zero
theorem BitVec.toNat_shiftLeft_clz (x : BitVec w)
  : (x <<< x.clz).toNat = x.toNat <<< x.clz.toNat := by
  simp
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := BitVec.toNat_lt_two_pow_sub_clz (x := x)
  have := BitVec.clz_le (x := x)
  have : x.clz.toNat ≤ w := BitVec.toNat_clz_le
  conv =>
    rhs
    rw [show w = (w - x.clz.toNat) + x.clz.toNat by grind]
  simp [Nat.pow_add]
  apply Nat.mul_lt_mul_of_pos_right
  · grind
  · exact Nat.two_pow_pos x.clz.toNat
theorem BitVec.add_one_eq_zero_iff_eq_allOnes (x : BitVec s) :
    x + 1#_ = 0#_ ↔ x = BitVec.allOnes s := by
  constructor
  · intro h
    have := BitVec.toNat_inj .. |>.mpr h
    simp at this
    have : x.toNat = 2^s - 1 := by grind
    apply BitVec.eq_of_toNat_eq
    simp
    rw [this]
  · intros h
    subst h
    apply BitVec.eq_of_toNat_eq
    simp
    have : 0 < 2^s := by grind only [!Nat.two_pow_pos]
    have : (2^s - 1) + 1 = 2^s := by grind
    rw [this]
    simp only [Nat.mod_self]
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

/-- Masking out `m` from `a` is a no-op iff `a` has no bits in common with `m`. -/
theorem BitVec.and_not_eq_self_iff {w : Nat} (a m : BitVec w) :
    a &&& ~~~m = a ↔ a &&& m = 0#w := by
  rw [BitVec.eq_iff_getLsbD_eq, BitVec.eq_iff_getLsbD_eq]
  constructor
  · intro h i
    have := h i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero] at this ⊢
    grind
  · intro h i
    have := h i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero] at this ⊢
    grind

/--
info: 'BitVec.and_not_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms BitVec.and_not_eq_self_iff

/-- `a` has no bits in common with `b ||| c` iff it has none with `b` and none with `c`. -/
theorem BitVec.and_or_eq_zero_iff {w : Nat} (a b c : BitVec w) :
    a &&& (b ||| c) = 0#w ↔ a &&& b = 0#w ∧ a &&& c = 0#w := by
  rw [BitVec.eq_iff_getLsbD_eq, BitVec.eq_iff_getLsbD_eq, BitVec.eq_iff_getLsbD_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    · have := h i
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      grind
  · intro ⟨h1, h2⟩ i
    have hb := h1 i
    have hc := h2 i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hb hc ⊢
    grind

/--
info: 'BitVec.and_or_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms BitVec.and_or_eq_zero_iff

/-- `toInt` of a sign-extended subtraction with a small (0/1) borrow, when no overflow occurs. -/
theorem signExtSubSub_toInt {e : Nat} (he : 0 < e) (A B : BitVec e) (c : BitVec (e + 1))
    (cval : Int) (hc : c.toInt = cval) (hc0 : 0 ≤ cval) (hc1 : cval ≤ 1) :
    ((A.signExtend (e + 1)) - (B.signExtend (e + 1)) - c).toInt
      = A.toInt - B.toInt - cval := by
  have hAr := BitVec.toInt_lt (x := A)
  have hAl := BitVec.le_toInt A
  have hBr := BitVec.toInt_lt (x := B)
  have hBl := BitVec.le_toInt B
  have he1 : (2:Int) ^ (e + 1) = 2 ^ e * 2 := by rw [Int.pow_succ]
  have he0 : (2:Int) ^ e = 2 ^ (e - 1) * 2 := by
    rw [show e = (e - 1) + 1 by omega, Int.pow_succ]; rw [show e-1+1 = e by omega]
  have hAse : (A.signExtend (e + 1)).toInt = A.toInt := BitVec.toInt_signExtend_of_le (by omega)
  have hBse : (B.signExtend (e + 1)).toInt = B.toInt := BitVec.toInt_signExtend_of_le (by omega)
  rw [BitVec.toInt_sub, BitVec.toInt_sub, hAse, hBse, hc]
  have hinner : (A.toInt - B.toInt).bmod (2 ^ (e + 1)) = A.toInt - B.toInt := by
    apply Int.bmod_eq_of_le <;> (push_cast; omega)
  rw [hinner]
  apply Int.bmod_eq_of_le <;> (push_cast; omega)

/-- `toInt` of a one-bit boolean widened by `setWidth'` is its `Nat` value. -/
theorem ofBool_setWidth_toInt {e : Nat} (he : 0 < e) (β : Bool) :
    ((BitVec.ofBool β).setWidth' (by omega : 1 ≤ e + 1)).toInt = (β.toNat : Int) := by
  have hn : ((BitVec.ofBool β).setWidth' (by omega : 1 ≤ e + 1)).toNat = β.toNat := by
    rw [BitVec.toNat_setWidth', BitVec.toNat_ofBool]
  rw [BitVec.toInt_eq_toNat_bmod, hn]
  have hbN : (β.toNat : Int) < 2 := by cases β <;> simp
  have h2eN : (2:Nat) ≤ 2 ^ e := by
    calc (2:Nat) = 2 ^ 1 := rfl
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) (by omega)
  have h2e : (2:Int) ≤ 2 ^ e := by exact_mod_cast h2eN
  have he1 : (2:Int) ^ (e + 1) = 2 ^ e * 2 := by rw [Int.pow_succ]
  have hb0 : (0:Int) ≤ (β.toNat : Int) := by exact_mod_cast Nat.zero_le _
  apply Int.bmod_eq_of_le <;> push_cast <;> omega

/-- A single boolean bit widened to `≥ 2` bits has a clear top bit: its value is `≤ 1 < 2^(w-1)`. -/
theorem BitVec.msb_setWidth'_ofBool_eq_false {w : Nat} (hw : 2 ≤ w) (b : Bool) (h : 1 ≤ w) :
    ((BitVec.ofBool b).setWidth' h : BitVec w).msb = false := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_setWidth', BitVec.toNat_ofBool]
  have h1 : b.toNat ≤ 1 := Bool.toNat_le b
  have h2 : 1 < 2 ^ (w - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by grind) (by grind)
    grind
  grind
