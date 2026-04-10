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



theorem Rat.mul_ne_zero_iff {x y : Rat} : (¬ (x * y = 0)) ↔ x ≠ 0 ∧ y ≠ 0 := by
  grind

theorem Rat.ne_zero_of_zero_lt {r : Rat} (h : 0 < r) : r ≠ 0 := by
  grind

attribute [simp] Rat.zero_add
attribute [simp] Rat.add_zero
attribute [simp] Rat.zero_mul
attribute [simp] Rat.mul_zero
attribute [simp] Rat.mul_one
attribute [simp] Rat.one_mul

attribute [simp] Rat.natCast_eq_zero_iff
attribute [simp] Rat.natCast_inj
attribute [simp] Rat.intCast_inj


@[simp]
theorem Rat.mul_le_mul_cancel_right_of_lt {a b c : Rat} (hc : 0 < c) :
    a * c ≤ b * c ↔ a ≤ b := by
  constructor
  · intros h
    exact Rat.le_of_mul_le_mul_right h hc
  · intros h
    apply Rat.mul_le_mul_of_nonneg_right h <;> grind

@[simp]
theorem Rat.mul_lt_mul_cancel_right_of_lt {a b c : Rat} (hc : 0 < c) :
    a * c < b * c ↔ a < b := by
  constructor
  · intros h
    exact Rat.lt_of_mul_lt_mul_right h (by grind)
  · intros h
    apply Rat.mul_lt_mul_of_pos_right h <;> grind


@[simp]
theorem Rat.div_le_div_self {a b c : Rat} (hc : 0 < c) :
    a / c ≤ b / c ↔ a ≤ b := by
  rw [Rat.div_def, Rat.div_def]
  apply Rat.mul_le_mul_cancel_right_of_lt
  apply Rat.inv_pos .. |>.mpr
  grind

@[simp]
theorem Rat.div_lt_div_self {a b c : Rat} (hc : 0 < c) :
    a / c < b / c ↔ a < b := by
  rw [Rat.div_def, Rat.div_def]
  apply Rat.mul_lt_mul_cancel_right_of_lt
  apply Rat.inv_pos .. |>.mpr
  grind

@[simp]
theorem Rat.add_le_iff_le {a b c : Rat} : a + c ≤ b + c ↔ a ≤ b := by
  grind

  @[simp]
theorem Rat.add_le_iff_le' {a b c : Rat} : c + a ≤  c + b ↔ a ≤ b := by
  grind


theorem Rat.lt_add_of_lt_of_nonneg {a b c : Rat} (hab : a < b) (hc : 0 ≤ c) :
  a < b + c := by grind

theorem Rat.le_add_of_le_of_nonneg {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) :
  a ≤ b + c := by grind



@[simp]
theorem Rat.mul_cancel_left {x y z : Rat} (hx : x ≠ 0) : x * y = x * z ↔ y = z := by
  grind


@[simp]
theorem Rat.mul_cancel_right {x y z : Rat} (hx : x ≠ 0) : y * x = z * x ↔ y = z := by
  grind

@[simp]
theorem Rat.natCast_ne_natCast_iff {r s : Nat} : (r : Rat) ≠ (s : Rat) ↔ r ≠ s := by
  apply not_congr; simp


@[simp]
theorem Rat.intCast_ne_intCast_iff {r s : Int} : (r : Rat) ≠ (s : Rat) ↔ r ≠ s := by
  apply not_congr; simp

/-- convert the sign bit to an integer value. Morally, this is (-1)^s -/
def signToInt (s : Bool) : Int :=
  if s then -1 else 1

/-- write the sign bit as two pow. -/
@[simp]
theorem signToInt_eq_negOne_pow_toNat (s : Bool) :
  signToInt s = (-1 : Int) ^ s.toNat := by
  cases s
  · simp [signToInt]
  · simp [signToInt]


@[simp, bv_normalize]
def lastPowerOfTwo_iter (m : Nat) (n : Nat) : Nat :=
  if m = 0 then
    1
  else if 2 ^ m < n then
    2 ^ m
  else
    lastPowerOfTwo_iter (m-1) n
  termination_by m

/--
Returns the largest power of two strictly less than `n`.

If no such number exists, returns `1` instead.
-/
@[simp, bv_normalize]
def lastPowerOfTwo (n : Nat) : Nat :=
  lastPowerOfTwo_iter ((n+1)/2) n

theorem sub_two_le { n : Nat } : n - 2 ≤ n := by
  omega

@[grind .]
theorem le_two_pow : n ≤ 2^n := by
  induction n
  case zero =>
    exact Nat.zero_le _
  case succ ih =>
    simp only [Nat.pow_add_one, Nat.mul_two]
    exact Nat.add_le_add ih Nat.one_le_two_pow

theorem two_pow_sub_one_le_two_pow (e : Nat) : 2^(e-1) ≤ 2^e :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem toEFixed_hPrec (e s : Nat) : 2 ^ (e - 1) + s - 2 < 2 ^ e + s := by
  have hexp0 : 0 < 2^e := Nat.two_pow_pos _
  have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
  omega



@[simp, grind .]
theorem Rat.div_cancel {p q d : Rat} (hd : d ≠ 0) :
    (p / d = q / d) <-> p = q := by
  rw [Rat.div_def, Rat.div_def]
  rw [Rat.mul_cancel_right]
  · grind

@[grind .]
theorem Rat.twoPowNeZero (n : Int) : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  grind only [Fp.Rat.two_pow_pos]

attribute [simp] Rat.zpow_natCast

theorem Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
    {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) (hac : 0 ≤ a) (hcc : 0 ≤ c) :
    a * c ≤ b * d := by
  apply (Rat.le_iff_sub_nonneg (a * c) (b * d)).mpr
  rw [show b = a + (b - a) by grind only]
  rw [Rat.add_mul]
  have : (b - a) ≥ 0 := by grind
  have : 0 ≤ a * d := by
    apply Rat.mul_nonneg <;> grind only
  rw [show a * d + (b - a) * d - a * c = (b - a) * d + a * (d - c) by grind only]
  have : 0 ≤ a * (d - c) := by
    apply Rat.mul_nonneg <;> grind only
  have : 0 ≤ (b - a) * d := by
    apply Rat.mul_nonneg <;> grind only
  grind only

theorem Rat.mul_lt_mul_of_lt_of_le_of_nonneg_of_nonneg
    {a b c d : Rat} (hab : a < b) (hcd : c ≤ d) (hac : 0 ≤ a) (hcc : 0 ≤ c) :
    a * c ≤ b * d := by
  apply (Rat.le_iff_sub_nonneg (a * c) (b * d)).mpr
  rw [show b = a + (b - a) by grind only]
  rw [Rat.add_mul]
  have : (b - a) ≥ 0 := by grind
  have : 0 ≤ a * d := by
    apply Rat.mul_nonneg <;> grind only
  rw [show a * d + (b - a) * d - a * c = (b - a) * d + a * (d - c) by grind only]
  have : 0 ≤ a * (d - c) := by
    apply Rat.mul_nonneg <;> grind only
  have : 0 ≤ (b - a) * d := by
    apply Rat.mul_nonneg <;> grind only
  grind only

theorem Rat.mul_lt_mul_of_le_of_lt_of_nonneg_of_nonneg
    {a b c d : Rat} (hab : a <=  b) (hcd : c < d) (hac : 0 ≤ a) (hcc : 0 ≤ c) :
    a * c ≤ b * d := by
  apply (Rat.le_iff_sub_nonneg (a * c) (b * d)).mpr
  rw [show b = a + (b - a) by grind only]
  rw [Rat.add_mul]
  have : (b - a) ≥ 0 := by grind
  have : 0 ≤ a * d := by
    apply Rat.mul_nonneg <;> grind only
  rw [show a * d + (b - a) * d - a * c = (b - a) * d + a * (d - c) by grind only]
  have : 0 ≤ a * (d - c) := by
    apply Rat.mul_nonneg <;> grind only
  have : 0 ≤ (b - a) * d := by
    apply Rat.mul_nonneg <;> grind only
  grind only

attribute [grind .] Rat.pow_pos

@[grind .]
theorem Rat.two_pow_int_ne_zero {n : Int} : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  apply Rat.zpow_pos
  grind only

@[grind .]
theorem Rat.two_pow_nat_ne_zero {n : Nat} : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  exact Nat.two_pow_pos n


@[grind ., simp]
theorem Rat.two_pow_ne_zero (n : Int) : (2 : Rat) ^ n ≠ 0 := by
  apply Rat.ne_zero_of_zero_lt
  norm_cast
  grind

theorem Rat.zpow_sub_eq_zpow_mul_zpow {b : Rat} (hb : b ≠ 0)
    (x y: Int) : b ^ (x - y) = b ^ x * b ^ (-y) := by
  rw [Int.sub_eq_add_neg]
  rw [Rat.zpow_add hb]

theorem Rat.mul_sub (b x y : Rat) : b * (x - y) = b * x - b * y := by
  grind only

@[simp, grind .]
theorem Rat.one_le_two_pow_nat {n : Nat} : 1 ≤ (2 : Rat) ^ n := by
  induction n with
  | zero => grind
  | succ n ih =>
    rw [Rat.pow_succ]
    grind

theorem Rat.two_pow_le_two_pow_of_le {x y : Int} (h : x ≤ y) : (2 : Rat) ^ x ≤ (2 : Rat) ^ y := by
  rw [Rat.le_iff_sub_nonneg]
  rw [show (2 : Rat) ^ x = (2 : Rat) ^ x * 1 by grind only]
  rw [show y = x + (y - x) by grind only]
  rw [Rat.zpow_add (by grind only)]
  rw [← Rat.mul_sub]
  have : 1 ≤ (2 : Rat) ^ (y - x) := by
    have : ∃ (k : Nat), y - x = k := by
      exact Int.nonneg_def.mp h
    obtain ⟨k, hk⟩ := this
    rw [hk]
    simp
  grind only [Rat.mul_nonneg, Rat.le_of_lt, Fp.Rat.two_pow_pos]

theorem Rat.le_mul_of_one_le_of_le  {x y y' : Rat} (hx1 : 1 ≤ x) (hy : 0 ≤ y) (hy' : y ≤ y')
    : y ≤ x * y' := by
  suffices 1 * y ≤ x * y' by grind only
  apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
  · grind only
  · grind only
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]


theorem Rat.le_mul_self_of_le_one_of_nonneg {y} {x : Rat} (hx0 : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y)
    : x * y ≤ y := by
  suffices x * y ≤ 1 * y by grind only
  apply Rat.mul_le_mul_of_le_of_le_of_nonneg_of_nonneg
  · grind only
  · grind only
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]
  · grind only [Rat.le_of_lt, Fp.Rat.two_pow_pos]

attribute [simp] Rat.le_refl

@[simp]
theorem Rat.mul_self_pow_eq_pow_succ (a : Rat) (n : Nat) :
  a * a ^ n = a ^ (n + 1) := by
  rw [Rat.mul_comm]
  rw [← Rat.pow_succ]

@[simp]
theorem Rat.mul_self_zpow_eq_zpow_succ {a : Rat} {n : Int}
  (ha : a ≠ 0 := by solve | simp | grind) :
  a * a ^ n = a ^ (n + 1) := by
  rw [Rat.mul_comm]
  rw [Rat.zpow_add]
  · simp
  · simp [ha]


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

theorem BitVec.ne_iff_getLsbD_ne (x y : BitVec w) : x ≠ y ↔ (x.getLsbD ≠ y.getLsbD) := by
  constructor
  · intros h1 h2
    apply h1
    apply BitVec.eq_of_getLsbD_eq
    intros i hi
    rw [h2]
  · intros h1 h2
    apply h1
    subst h2
    simp only


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

@[simp]
theorem Rat.ne_zero_of_one_le {a : Rat} (h : 1 ≤ a) : a ≠ 0 := by
  apply Classical.byContradiction
  intros hcontra
  simp at hcontra
  subst hcontra
  grind only

@[simp]
theorem Rat.ne_zero_of_one_lt {a : Rat} (h : 1 < a) : a ≠ 0 := by
  apply Classical.byContradiction
  intros hcontra
  simp at hcontra
  subst hcontra
  grind only

/--
Show that `n/d ≤ n` when `n` is nonnegative and `d` is at least 1.
-/
@[simp]
theorem Rat.div_le_self_of_nonneg_of_one_le (n d : Rat)
    (hn : 0 ≤ n) (hd : 1 ≤ d) :
    n / d ≤ n := by
  rw [Rat.div_def]
  suffices n * d⁻¹ ≤ n * 1 from by
    grind
  apply Rat.mul_le_mul_of_nonneg_left
  · suffices d⁻¹ * d ≤ 1 * d from by
      apply Rat.le_of_mul_le_mul_right (c := d)
      exact this
      grind only
    simp [Rat.inv_mul_cancel, hd]
  · grind only

theorem Rat.inv_mul_eq_div {a b : Rat}: a * b⁻¹ = a / b := by
  rw [Rat.div_def]

theorem Rat.mul_inv_eq_div {a b : Rat} : b⁻¹ * a = a / b := by
  rw [Rat.div_def]
  simp [Rat.mul_comm]

@[simp]
theorem Rat.inv_mul_mul_self_cancel {a b : Rat} (hb : b ≠ 0) : b⁻¹ * a * b = a := by
  grind

@[simp]
theorem Rat.inv_mul_mul_self_cancel' {a b : Rat} (hb : b ≠ 0) : b⁻¹ * (a * b) = a := by
  grind

@[simp]
theorem Rat.self_mul_mul_inv_cancel {a b : Rat} (hb : b ≠ 0) : b * a * b⁻¹ = a := by
  grind

@[simp]
theorem Rat.self_mul_mul_inv_cancel' {a b : Rat} (hb : b ≠ 0) : b * (a * b⁻¹) = a := by
  grind

@[simp]
theorem Rat.inv_mul_self_mul_cancel {a b : Rat} (hb : b ≠ 0) : b⁻¹ * (b * a) = a := by
  grind
@[simp]
theorem Rat.self_mul_inv_mul_cancel {a b : Rat} (hb : b ≠ 0) : b * (b⁻¹ * a) = a := by
  grind

/--
Multiplication is positive when both factors are positive.
-/
theorem Rat.mul_positive {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  apply Rat.lt_of_le_of_ne
  · apply Rat.mul_nonneg
    · grind only
    · grind only
  · intros hcontra
    have : a = 0 ∨ b = 0 := by grind
    rcases this with rfl | rfl <;> grind

/--
For positive numbers, the inverse is order-reversing.
-/
theorem Rat.inv_le_inv_of_le_of_positive {a b : Rat} (ha : 0 < a)
    (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  by_cases hb : b = 0
  · simp [hb]
    exact Fp.Rat.inv_nonneg (by grind)
  · by_cases ha : a = 0
    · simp [ha]
      subst ha
      grind
    · apply Rat.le_of_mul_le_mul_right (c := a * b)
      · simp [ha, hb, hab]
      · apply Rat.mul_positive
        · grind only
        · grind only

theorem Rat.inv_eq_div (a : Rat)  : a⁻¹ = 1 / a := by
  grind only

-- TODO: write a simp lemma
theorem Rat.zpow_neg_natCast_eq_one_div_zpow (a : Rat) (n : Nat)
    : a ^ (-n : Int) = 1 / a ^ n := by
  rw [Rat.zpow_neg]
  rw [Rat.inv_eq_div]
  rw [Rat.zpow_natCast]

theorem Rat.one_div_zpow_natCast_eq_zpow_neg (a : Rat) (n : Nat) : 1 / a ^ n = a ^ (- (n : Int)) := by
  rw [Rat.zpow_neg]
  rw [← inv_eq_div]
  simp

theorem Rat.one_div_zpow_eq_zpow_neg (a : Rat) (n : Int) : 1 / a ^ n = a ^ (-n) := by
  rw [Rat.zpow_neg]
  rw [← inv_eq_div]


@[simp]
theorem Rat.inv_zpow_eq_zpow_neg (a : Rat) (n : Int) : (a ^ n)⁻¹ = a ^ (-n) := by
  rw [Rat.inv_eq_div]
  rw [one_div_zpow_eq_zpow_neg]

@[simp]
theorem Rat.inv_zpow_natCast_eq_zpow_neg (a : Rat) (n : Nat) : (a ^ n)⁻¹ = a ^ (- (n : Int)) := by
  rw [Rat.inv_eq_div]
  rw [one_div_zpow_natCast_eq_zpow_neg]

theorem Rat.zpow_mul_zpow {a : Rat} (ha : a ≠ 0) (x y : Int) : a ^ x * a ^ y = a ^ (x + y) := by
  rw [Rat.zpow_add ha]

theorem Rat.zpow_div_zpow {a : Rat} (ha : a ≠ 0) (x y : Int) : a ^ x / a ^ y = a ^ (x - y) := by
  rw [zpow_sub_eq_zpow_mul_zpow ha x y]
  rw [Rat.div_def]
  rw [Rat.inv_zpow_eq_zpow_neg]

theorem Rat.div_zpow_eq_zpow_neg {n a : Rat} (i : Int) : n / a ^ i = n * a ^ (-i) := by
  rw [Rat.div_def]
  rw [Rat.inv_zpow_eq_zpow_neg]

theorem Rat.div_zpow_natCast_eq_zpow_neg {n a : Rat} (i : Nat) : n / a ^ i = n * a ^ (- (i : Int)) := by
  rw [Rat.div_def]
  rw [Rat.inv_zpow_natCast_eq_zpow_neg]

@[simp]
theorem Rat.natCast_sub_of_le {m n : Nat} (h : m ≤ n) :
  ((n - m : Nat) : Rat) = n - m := by
  have : ∃ k : Nat, n = m + k := by
    apply Nat.exists_eq_add_of_le
    exact h
  obtain ⟨k, hk⟩ := this
  subst hk
  simp
  grind only

theorem Rat.sub_div_eq_div_sub_div {a b c : Rat} :
  (a - b) / c = a / c - b / c := by
  grind only

theorem Rat.div_self_eq_one_of_ne_zero {a : Rat} (ha : a ≠ 0) : a / a = 1 := by
  grind

theorem Rat.div_self_eq_ite {a : Rat} : a / a = (if a = 0 then 0 else 1) := by
  grind

@[grind]
def Int.monus (a b : Int) : Int :=
  if a < b then 0 else a - b

@[simp]
theorem Int.zero_le_monus (a b : Int) : 0 ≤ a.monus b := by
  grind

@[simp]
theorem Int.add_monus_eq_self_of_le {a b : Int} (h : a ≤ b) : a + a.monus b = a := by
  grind

theorem natCast_monus_natCast_eq_natCast_sub {m n : Nat} : Int.monus m n = ((m - n : Nat) : Int) := by
  grind


@[simp, grind .]
theorem one_lt_two_pow_iff (x : Nat) : 1 < 2 ^ x ↔ 0 < x := by
  rw [show 1 = 2 ^ 0 by simp]
  rw [Nat.pow_lt_pow_iff_right]
  · grind only
