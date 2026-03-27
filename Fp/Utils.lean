import Std.Tactic.BVDecide
import Fp.Tactics
import Fp.Grind



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
