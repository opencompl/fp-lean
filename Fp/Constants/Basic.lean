import Fp.Utils
import Fp.Utils.Dyadic
import Fp.Grind
import Fp.Utils.Rat

/--
The "state" of an extended fixed-point number: either NaN, infinity, or a
number.
-/
@[grind]
inductive State : Type
| NaN : State
| Infinity : State
| Number : State
deriving DecidableEq

instance {P : State → Prop} [∀ (s : State), Decidable (P s)] :
    Decidable (∀ (s : State), P s) :=
  if hnan : P .NaN then
    if hinf : P .Infinity then
      if hnum : P .Number then
        isTrue (by grind only [#0000])
      else
        isFalse (by grind only [#b4e6])
    else
      isFalse (by grind only [#b4e6])
  else
    isFalse (by grind only [#b4e6])

instance {P : State → Prop} [∀ (s : State), Decidable (P s)] :
    Decidable (∃ (s : State), P s) :=
  if hnan : P .NaN then
    isTrue (by grind only [#5c30])
  else
    if hinf : P .Infinity then
      isTrue (by grind only [#5c30])
    else
      if hnum : P .Number then
        isTrue (by grind only [#5c30])
      else
        isFalse (by grind only [#0000])

attribute [bv_normalize] State.eq_iff_enumToBitVec_eq

@[bv_normalize]
theorem State.beq_iff_enumToBitVec_beq {x y : State}
  : (x == y) = (x.enumToBitVec == y.enumToBitVec) := by
  cases h : (x == y) <;> simp_all [eq_iff_enumToBitVec_eq]

@[bv_normalize]
theorem State.bne_to_beq {x y : State}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [eq_iff_enumToBitVec_eq]

@[bv_normalize]
theorem State.NaN_enumToBitVec_eq : enumToBitVec NaN = 0b00#2 := rfl
@[bv_normalize]
theorem State.Infinity_enumToBitVec_eq : enumToBitVec Infinity = 0b01#2 := rfl
@[bv_normalize]
theorem State.Number_enumToBitVec_eq : enumToBitVec Number = 0b10#2 := rfl

@[bv_normalize]
theorem State.eq_cond_enumToBitVec {x y : State} :
  (bif b then x else y).enumToBitVec = bif b then x.enumToBitVec else y.enumToBitVec := by
  cases b <;> rfl

instance : Repr State where
  reprPrec s _prec :=
    match s with
    | .NaN => "NaN"
    | .Infinity => "∞"
    | .Number => "num"


-- https://en.wikipedia.org/wiki/Single-precision_floating-point_format

/--
In 8 bit exponent, this value is 2^7 - 1 = 127.
The exponent's value is [e.toNat] - bias = [e.toNat] - 127.
-/
@[bv_normalize]
def bias (e : Nat) : Nat :=
  2 ^ (e - 1) - 1

/-- info: 127 -/
#guard_msgs in #eval bias 8

/--
Adding the bias to itself equals '2^e - 2', which is the
maximum normal exponent of a packed float.
-/
theorem bias_plus_bias_eq_twoPow_minus_two
  (e : Nat) (he : 1 < e) : bias e + bias e = 2 ^ e - 2 := by
  simp [bias]
  have : 2^e = 2 * 2^(e - 1) := by
    rw [show e = (e - 1) + 1 by grind only]
    rw [Nat.pow_succ]
    grind only
  have : 1 ≤ 2 ^ (e - 1) := by exact Nat.one_le_two_pow
  grind only [!Nat.two_pow_pos, #11341de38214aa15]

theorem two_mul_bias_eq_twoPow_minus_two (e : Nat) (he : 1 < e) : 2 * bias e = 2 ^ e - 2 := by
  have := bias_plus_bias_eq_twoPow_minus_two e he
  grind only

theorem mul_two_bias_eq_twoPow_minus_two (e : Nat) (he : 1 < e) : bias e * 2 = 2 ^ e - 2 := by
  have := bias_plus_bias_eq_twoPow_minus_two e he
  grind only

@[simp]
theorem bias_zero_eq : bias 0 = 0 := rfl
@[simp]
theorem bias_one_eq : bias 1 = 0 := rfl
@[simp]
theorem bias_two_eq : bias 2 = 1 := rfl

@[simp, grind .]
theorem bias_pos_of_one_lt (e : Nat) (he : 1 < e) : 0 < bias e := by
  simp [bias]
  rcases e with rfl | e
  · grind only
  · simp; grind only [!Nat.two_pow_pos, usr Nat.div_pow_of_pos]

/-- Bias is weakly monotone with respect to its argument. -/
@[simp]
theorem bias_le_of_le {e1 e2 : Nat} (he : e1 ≤ e2) : bias e1 ≤ bias e2 := by
  simp [bias]
  have : 0 < 2 ^ (e2 - 1) := by grind only [!Nat.two_pow_pos]
  suffices 2 ^ (e1 - 1) ≤ 2 ^ (e2 - 1) by grind only
  apply Nat.pow_le_pow_of_le (by decide)
  · grind only [#2ce3]

/-- Bias is strictly monotone for exponents over 0. -/
@[simp]
theorem bias_lt_of_lt {e1 e2 : Nat} (he' : 0 < e1) (he : e1 < e2) : bias e1 < bias e2 := by
  simp [bias]
  have : 0 < 2 ^ (e2 - 1) := by grind only [!Nat.two_pow_pos]
  have : 0 < 2 ^ (e1 - 1) := by grind only [!Nat.two_pow_pos]
  suffices 2 ^ (e1 - 1) < 2 ^ (e2 - 1) by grind only
  apply Nat.pow_lt_pow_of_lt (by decide)
  grind only

/--
The biases are equal if either the exponents are equal and at least 2,
or if both exponents are at most 1, in which case the bias is 0.
-/
@[simp]
theorem bias_eq_bias_iff {e1 e2 : Nat}  :
    bias e1 = bias e2 ↔ ((e1 = e2 ∧ e1 ≥ 2) ∨ (e1 ≤ 1 ∧ e2 ≤ 1)) := by
  simp [bias]
  have : 0 < 2 ^ (e2 - 1) := by grind only [!Nat.two_pow_pos]
  have : 0 < 2 ^ (e1 - 1) := by grind only [!Nat.two_pow_pos]
  by_cases he1 : e1 ≤ 1 <;> by_cases he2 : e2 ≤ 1
  · simp [he1, he2]
  · simp [he1, he2]
    grind => instantiate approx
  · simp [he1, he2]
    grind =>
      instantiate approx
      cases #70e3
  · simp [he1, he2]
    constructor
    · intros heq
      have : 2 ^ (e1 - 1) = 2 ^ (e2 - 1) := by grind only
      have : e1 - 1 = e2 - 1 := by grind only [Nat.pow_right_inj]
      grind only
    · grind only

@[bv_normalize]
def Nat.ceilLog2 (n : Nat) : Nat :=
  if n.log2 * 2 = n then n.log2 else n.log2 + 1

@[bv_normalize]
def minNormalExp (e : Nat) : Int :=
  -(bias e - 1 : Nat)

/-- info: -126 -/
#guard_msgs in #eval minNormalExp 8

/-- The max value the exponent can take when unbiased. -/
@[bv_normalize]
def maxNormalExp (e : Nat) : Int := (bias e)

/-- info: 127 -/
#guard_msgs in #eval maxNormalExp 8

/--
The value the subnormal exponent can take.
In 8 bits, this value is -127, because it's -126, but start with a `0.xxx`,
which makes it one smaller than the minimum normal exponent.
-/
@[bv_normalize]
def maxSubnormalExp (e : Nat) : Int :=
  minNormalExp e - 1

/-- info: -127 -/
#guard_msgs in #eval maxSubnormalExp 8

/-- maxSubnormalExp should be -127. -/
theorem maxSubnormalExp_eq_neg_bias_plus_one (he : 1 < e) :
    maxSubnormalExp e = - (bias e)  := by
  simp [maxSubnormalExp, minNormalExp, bias]
  grind


/-- For unpacked floats, the *minimum* the subnormal exponent can take,
which can "steal" bits from the significand to be smaller than minNormalExp.
We have (s - 1) bits, since we need one bit for the leading 1.
(i.e., we include the hidden bit.)

### `s = 1` (IEEE, so `s=1` is one bit after the decimal point.

With 2 significand bits [minimum for the concept to make sense]:

```
2^emin * 1.0 -> minNormalExp
2^emin * 0.1 -> maxSubnormalExp = minNormalExp - 1
2^emin * 0.1 -> also minSubnormalExp! = minNormalExp - 1
```

### `s = 2` (IEEE, so `s=1` is one bit after the decimal point.

```
2^emin * 1.00 -> minNormalExp
2^emin * 0.10 -> maxSubnormalExp = minNormalExp - 1
2^emin * 0.01 -> minSubnormalExp = minNormalExp - 2
```

### `s = 3` (IEEE, so `s=1` is one bit after the decimal point.

```
2^emin * 1.000 -> minNormalExp
2^emin * 0.100 -> maxSubnormalExp = minNormalExp - 1
2^emin * 0.010                    = minNormalExp - 2
2^emin * 0.001 -> minSubnormalExp = minNormalExp - 3
```

In general, we get `(s - 2)` values,
which are `minNormalExp - 1`, `minNormalExp - 2`, ..., `minNormalExp - (s - 1)`
-/
@[bv_normalize]
def minSubnormalExp (e : Nat) (s : Nat) : Int :=
  (maxSubnormalExp e) - (s - 1 : Int)

/--
The minimum subnormal exponent can have `(s - 1)`
extra negative values, taken from the significand.
-/
theorem minSubnormalExp_eq_neg_bias_minus_s_minus_one (he : 1 < e) :
    minSubnormalExp e s = - (bias e) - (s - 1) := by
  simp [minSubnormalExp, maxSubnormalExp, minNormalExp, bias]
  grind

/-#

The value is `-149` wrt [wikipedia](https://en.wikipedia.org/wiki/Single-precision_floating-point_format):
> ... the minimum positive (subnormal) value is 2^(-149).
-/
/-- info: -149 -/
#guard_msgs in #eval minSubnormalExp 8 23
/--
This is a simpler (but less tight) bound than `exponentWidth`.
It's logarithmically larger.
-/
@[bv_normalize, simp]
def exponentWidth' (e s : Nat) : Nat :=
  e + s.ceilLog2

/--
The required exponent width to represent all exponents of an `e`-bit
floating-point number with `s`-bit significand, including normalized
subnormals. Note that this slightly differs from symfpu's definition,
which uses `s - 2` instead of `s - 1`. The reason is that symfpu assumes
`e ≥ 2` while we want to support the degenerate case of `e = 1`,
mainly to minimize our proof assumptions. The correctness
proof of `unpack` relies on this difference which ensures that `uf.sig.clz`
does not overflow when its width is set to `exponentWidth 1 s` (where
`s = 2 ^ n` for some `n`).
-/
@[bv_normalize]
def exponentWidth (e s : Nat) : Nat :=
  (2 ^ (e - 1) + s - 1).log2 + 2

@[simp]
theorem zero_lt_exponentWidth : 0 < exponentWidth e s  := by
  simp [exponentWidth]

@[simp]
theorem one_lt_exponentWidth : 1 < exponentWidth e s  := by
  simp [exponentWidth]

/--
the exponentWidth is strictly larger than the exponent itself.
-/
theorem self_lt_exponentWidth (e s : Nat) (he : 1 < e) (hs : 0 < s) :
  e < exponentWidth e s := by
  simp [exponentWidth]
  have : 0 < 2 ^ (e - 1) + s - 1 := by grind only [!Nat.two_pow_pos, #5690]
  have : e - 1 = (2 ^ (e - 1)).log2 := by
    exact Eq.symm Nat.log2_two_pow
  have : (2 ^ (e - 1)).log2 ≤ (2 ^ (e - 1) + s - 1).log2 := by
    apply Nat.log2_le_log2_of_le
    grind only
  grind only

@[grind ., simp]
theorem two_pow_e_lt_two_pow_exponentWidth (he : 1 < e) (hs : 0 < s) :
    2 ^ e < 2 ^ exponentWidth e s := by
  apply Nat.pow_lt_pow_of_lt
  · decide
  · exact self_lt_exponentWidth e s he hs

/--
The bias is less than `2 ^ (e - 1)`.
-/
@[grind ., simp]
theorem bias_lt_two_pow_exponent_sub_one (e : Nat) :
    bias e < 2 ^ (e - 1) := by
  simp [bias]
  apply Nat.lt_of_lt_of_le (m := 2 ^ (e - 1))
  · grind
  · apply Nat.pow_le_pow_of_le
    · decide
    · grind only

/--
The bias, when converted to a BitVec of the exponent width fits properly.
-/
@[simp, grind =]
theorem toNat_ofNat_bias_eq_bias (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofNat (exponentWidth e s) (bias e)).toNat = bias e := by
  simp
  rw [Nat.mod_eq_of_lt]
  apply Nat.lt_of_lt_of_le (m := 2 ^ (e - 1))
  · have := bias_lt_two_pow_exponent_sub_one e
    grind only
  · apply Nat.pow_le_pow_of_le
    · decide
    · have := self_lt_exponentWidth e s he hs
      grind only

/-
The bias, when converted to a BitVec of the exponent width fits properly.
-/
@[simp, grind =]
theorem toNat_ofInt_bias_eq_bias (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofInt (exponentWidth e s) (bias e)).toNat = bias e := by
  simp
  rw [Nat.mod_eq_of_lt]
  apply Nat.lt_of_lt_of_le (m := 2 ^ (e - 1))
  · have := bias_lt_two_pow_exponent_sub_one e
    grind only
  · apply Nat.pow_le_pow_of_le
    · decide
    · have := self_lt_exponentWidth e s he hs
      grind only

@[simp, grind =]
theorem toInt_ofNat_bias_eq_bias (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofNat (exponentWidth e s) (bias e)).toInt = bias e := by
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rw [toNat_ofNat_bias_eq_bias he hs]
  · rw [toNat_ofNat_bias_eq_bias he hs]
    rw [bias, exponentWidth]
    have := Nat.log2_eq_exists (n := 2 ^ (e - 1) + s - 1) (by grind only [!Nat.two_pow_pos, #5690])
    obtain ⟨log, hlogeq, hloglt, hlogle⟩ := this
    grind only [!Nat.two_pow_pos, #569066451790c837]
/--
The bound between bias and the exponent width: `bias e + 1 < 2 ^ (exponentWidth e s - 1)`.
This is tight.
-/
theorem bias_plus_one_lt_two_pow_exponentWidth_minus_one (e s: Nat)
    (he : 1 < e) (hs : 0 < s) :
    bias e + 1 < 2 ^ (exponentWidth e s - 1) := by
  have := bias_lt_two_pow_exponent_sub_one e
  apply Nat.lt_of_le_of_lt (m := 2 ^ (e - 1))
  · grind only
  · apply Nat.pow_lt_pow_of_lt
    · decide
    · have := self_lt_exponentWidth e s he hs
      grind only

@[grind ., simp]
theorem neg_two_pow_exponentWidth_le_minNormalExp (he : 1 < e) (hs : 0 < s)
  : -2 ^ (exponentWidth e s - 1) ≤ minNormalExp e := by
  rw [minNormalExp]
  simp only [Int.neg_le_neg_iff]
  have : 0 < bias e := by exact bias_pos_of_one_lt e he
  rw [Int.natCast_sub (by grind only)]
  simp
  have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
  grind only

@[simp, grind .]
theorem minNormalExp_le_two_pow_exponentWidth (he : 1 < e) (hs : 0 < s)
  : minNormalExp e < 2 ^ (exponentWidth e s - 1) := by
  rw [minNormalExp]
  apply Int.le_of_neg_le_neg
  have : 0 < bias e := by exact bias_pos_of_one_lt e he
  rw [Int.natCast_sub (by grind only)]
  simp
  have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
  grind only

/--
minNormalExp, when converted to a BitVec of the exponent width, fits properly.
-/
@[simp, grind =]
theorem toInt_ofInt_minNormalExp_eq_minNormalExp (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofInt (exponentWidth e s) (minNormalExp e)).toInt = (minNormalExp e) := by
  simp only [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le]
  · simp only [Int.natCast_pow, Int.cast_ofNat_Int, zero_lt_exponentWidth,
    Int.two_pow_div_two_eq_sub_one_of_pos]
    apply neg_two_pow_exponentWidth_le_minNormalExp
    · grind only
    · grind only
  · simp
    apply minNormalExp_le_two_pow_exponentWidth
    · grind only
    · grind only

theorem neg_two_pow_le_minNormalExp
    (he : 1 < e) (hs : 0 < s) (hw : exponentWidth e s ≤ w) :
    -(2 ^ (w - 1)) ≤ minNormalExp e := by
  rw [minNormalExp]
  simp only [Int.neg_le_neg_iff]
  have : 0 < bias e := by exact bias_pos_of_one_lt e he
  rw [Int.natCast_sub (by grind only)]
  simp
  have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
  have : (2 : Int) ^ w / 2 = 2 ^ (w - 1) := by
    rw [Int.two_pow_div_two_eq_sub_one_of_pos]
    grind only
  have : 2 ^ (exponentWidth e s - 1) ≤ 2 ^ (w - 1) := by
    apply Nat.pow_le_pow_of_le
    · decide
    · grind only
  grind only

grind_pattern neg_two_pow_le_minNormalExp => exponentWidth e s ≤ w, minNormalExp e

theorem minNormalExp_lt_two_pow
    (he : 1 < e) (hs : 0 < s) (hw : exponentWidth e s ≤ w) :
    minNormalExp e < 2 ^ (w - 1):= by
  rw [minNormalExp]
  apply Int.lt_of_neg_lt_neg
  simp only [Int.neg_neg]
  have : 0 < bias e := by exact bias_pos_of_one_lt e he
  rw [Int.natCast_sub (by grind only)]
  simp only [Int.cast_ofNat_Int, gt_iff_lt]
  have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
  norm_cast
  simp only [Int.natCast_pow, Int.cast_ofNat_Int, gt_iff_lt]
  have : 2 ^ (exponentWidth e s - 1) ≤ 2 ^ (w - 1) := by
    apply Nat.pow_le_pow_of_le
    · decide
    · grind only
  grind only

grind_pattern minNormalExp_lt_two_pow => exponentWidth e s ≤ w, minNormalExp e

/--
Any bitvector that is at least as large as `exponentWidth e s`
can fit `minNormalExp`
-/
theorem toInt_ofInt_minNormalExp_eq_minNormalExp_of_le
    (he : 1 < e) (hs : 0 < s) (hw : exponentWidth e s ≤ w) :
    (BitVec.ofInt w (minNormalExp e)).toInt = (minNormalExp e) := by
  have : 0 < exponentWidth  e s := by exact zero_lt_exponentWidth
  have hwpos : 0 < w := by grind only
  simp only [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le]
  · simp only [Int.natCast_pow, Int.cast_ofNat_Int, hwpos, Int.two_pow_div_two_eq_sub_one_of_pos];
    apply neg_two_pow_le_minNormalExp he hs hw
  · simp; apply minNormalExp_lt_two_pow he hs hw

grind_pattern toInt_ofInt_minNormalExp_eq_minNormalExp_of_le => exponentWidth e s ≤ w, minNormalExp e


@[simp, grind =]
theorem toInt_ofInt_maxNormalExp_eq_maxNormalExp (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofInt (exponentWidth e s) (maxNormalExp e)).toInt = (maxNormalExp e) := by
  simp only [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le]
  · simp
    rw [maxNormalExp]
    have : 0 < bias e := by exact bias_pos_of_one_lt e he
    grind only
  · rw [maxNormalExp]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int, Int.two_pow_plus_one_div_two_eq_two_pow]
    have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
    norm_cast
    grind only

theorem toInt_ofInt_maxNormalExp_eq_maxNormalExp_of_le
    (he : 1 < e) (hs : 0 < s) (hw : exponentWidth e s ≤ w) :
    (BitVec.ofInt w (maxNormalExp e)).toInt = (maxNormalExp e) := by
  have : 0 < exponentWidth  e s := by exact zero_lt_exponentWidth
  have hwpos : 0 < w := by grind only
  simp only [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le]
  · simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    rw [maxNormalExp]
    have : 0 < bias e := by exact bias_pos_of_one_lt e he
    grind only
  · rw [maxNormalExp]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
    norm_cast
    apply Nat.lt_of_lt_of_le (m :=  2 ^ (exponentWidth e s - 1))
    · grind only
    · simp
      apply Nat.pow_le_pow_of_le
      · decide
      · grind only

@[simp, grind =]
theorem toInt_ofInt_maxSubnormalExp_eq_maxSubnormalExp (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofInt (exponentWidth e s) (maxSubnormalExp e)).toInt = (maxSubnormalExp e) := by
  simp only [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le]
  · simp
    rw [maxSubnormalExp, minNormalExp]
    have : 0 < bias e := by exact bias_pos_of_one_lt e he
    simp only [ge_iff_le]
    have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
    grind only
  · rw [maxSubnormalExp, minNormalExp]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int, Int.two_pow_plus_one_div_two_eq_two_pow]
    apply Int.lt_of_neg_lt_neg
    have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
    grind only

@[simp, grind =]
theorem toInt_ofInt_minSubnormalExp_eq_minSubnormalExp (he : 1 < e) (hs : 0 < s) :
    (BitVec.ofInt (exponentWidth e s) (minSubnormalExp e s)).toInt = (minSubnormalExp e s) := by
  simp only [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le]
  · simp
    rw [minSubnormalExp, maxSubnormalExp, minNormalExp]
    have : 0 < bias e := by exact bias_pos_of_one_lt e he
    rw [Int.natCast_sub (by grind only)]
    have hbias := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
    norm_cast
    rw [exponentWidth, bias] at hbias ⊢
    have hlog := Nat.log2_eq_exists ((2 ^ (e - 1) + s - 1)) (by grind only [!Nat.two_pow_pos,
      #569066451790c837])
    obtain ⟨log, hlogeq, hloglt, hlogle⟩ := hlog -- log2 value.
    grind only [!Nat.two_pow_pos, #569066451790c837]
  · rw [minSubnormalExp, maxSubnormalExp, minNormalExp]
    simp
    have := bias_plus_one_lt_two_pow_exponentWidth_minus_one e s he hs
    grind only

/--
The max normal exponent plus the bias fit into a bitvector of size 'exponentWidth'
-/
theorem maxNormalExp_plus_bias_lt_two_pow_exponentWidth (hs : 0 < s) :
    maxNormalExp e + bias e < 2 ^ exponentWidth e s := by
  simp [maxNormalExp, bias, exponentWidth]
  have : 0 < 2 ^ (e - 1) + s - 1 := by grind only [!Nat.two_pow_pos]
  have : 0 < s := hs
  have : 0 < 2 ^ (e - 1) + s - 1 := by grind only [!Nat.two_pow_pos, #5690]
  have hlog2 := Nat.log2_eq_exists (2 ^ (e - 1) + s - 1) (by grind only [!Nat.two_pow_pos, #569066451790c837])
  obtain ⟨log, hlogeq, hloglt, hlogle⟩ := hlog2
  simp [hlogeq]
  grind only [!Nat.two_pow_pos, #569066451790c837]
