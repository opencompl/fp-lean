import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Grind

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

axiom AxOrderEncode {P : Prop} : P

theorem BitVec.getLsbD_orderEncode_of_lt (x : BitVec w) (i : Nat) (hi : i < w) :
    (orderEncode x).getLsbD i = (decide (i < x.toNat)) := by
  by_cases hi : x.toNat < w
  · rw [orderEncode]
    · -- ⊢ (1#w <<< x - 1).getLsbD i = decide (i < x.toNat)
      exact AxOrderEncode
  · rw [BitVec.orderEncode_eq_allOnes_of_le]
    · simp; omega
    · omega

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
