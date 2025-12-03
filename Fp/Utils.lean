import Std.Tactic.BVDecide
import Fp.Tactics

@[simp, bv_float_normalize]
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
@[simp, bv_float_normalize]
def lastPowerOfTwo (n : Nat) : Nat :=
  lastPowerOfTwo_iter ((n+1)/2) n

theorem sub_two_le { n : Nat } : n - 2 ≤ n := by
  omega

theorem le_two_pow : n ≤ 2^n := by
  induction n
  case zero =>
    exact Nat.zero_le _
  case succ ih =>
    simp only [Nat.pow_add_one, Nat.mul_two]
    exact Nat.add_le_add ih Nat.one_le_two_pow

theorem two_pow_sub_one_le_two_pow (e : Nat) : 2^(e-1) ≤ 2^e :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem toEFixed_hExOffset (e s : Nat) : 2 ^ (e - 1) + s - 2 < 2 ^ e + s := by
  have hexp0 : 0 < 2^e := Nat.two_pow_pos _
  have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
  omega

@[simp, bv_float_normalize]
def fls' (m : Nat) (b : BitVec n) (hm : n ≤ m) : BitVec m := match n with
  | 0 => 0
  | n' + 1 =>
    if b.msb then n
    else fls' m (BitVec.truncate n' b) (by omega)

/-- If fls' returns an index 'i', then b.getLsbD at this index is true. -/
theorem getLsbD_eq_true_of_fls'_eq_of_ne_zero (m : Nat) (b : BitVec n) (hm : n ≤ m) (hi : i ≠ 0) (hi' : i ≤ m) :
    fls' m b hm = i → b.getLsbD (i - 1) = true := by
  induction n generalizing m i
  case zero =>
    simp [fls']
    intros h
    rw [← BitVec.toNat_inj] at h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h
    rw [Nat.mod_eq_of_lt] at h
    · omega
    · apply Nat.lt_of_le_of_lt hi'
      exact Nat.lt_two_pow_self
  case succ n ih =>
    simp only [fls']
    split
    case isTrue h =>
      simp
      · intros hfls
        rw [← BitVec.toNat_inj] at hfls
        simp only [BitVec.toNat_ofNat] at hfls
        rw [Nat.mod_eq_of_lt] at hfls
        · rw [Nat.mod_eq_of_lt] at hfls
          · rw [BitVec.msb_eq_getLsbD_last] at h
            rw [← hfls]
            simp at h
            simp [h]
          · apply Nat.lt_of_le_of_lt hi'
            exact Nat.lt_two_pow_self
        · apply Nat.lt_of_le_of_lt hm
          exact Nat.lt_two_pow_self
    case isFalse h =>
      intros h
      have := ih (b := b.truncate _) (i := i) (by omega) (by omega) (by omega) (by omega) h
      simp at this
      simp [this]

theorem getLsbD_eq_false_of_fls'_eq_of_ne_zero (m : Nat) (b : BitVec n) (hm : n ≤ m) (hi' : i ≤ m) :
      fls' m b hm = i → (∀ (j : Nat), i ≤ j → b.getLsbD j = false) := by
  induction n generalizing m i
  case zero =>
    simp [fls']
  case succ n ih =>
    simp only [fls']
    split
    case isTrue h =>
      simp
      · intros hfls
        rw [← BitVec.toNat_inj] at hfls
        simp only [BitVec.toNat_ofNat] at hfls
        rw [Nat.mod_eq_of_lt] at hfls
        · rw [Nat.mod_eq_of_lt] at hfls
          · rw [BitVec.msb_eq_getLsbD_last] at h
            rw [← hfls]
            simp at h
            intros j hj
            apply BitVec.getLsbD_of_ge
            omega
          · apply Nat.lt_of_le_of_lt hi'
            exact Nat.lt_two_pow_self
        · apply Nat.lt_of_le_of_lt hm
          exact Nat.lt_two_pow_self
    case isFalse hmsb =>
      intros h
      intros j hj
      have := ih (b := b.truncate _) (i := i) (m := m) (by omega) (by omega) h
      simp at this
      specialize this j (by omega)
      by_cases hj : j < n
      · apply this hj
      · simp at hj
        rw [BitVec.msb_eq_getLsbD_last] at hmsb
        simp at hmsb
        by_cases hj' : j = n
        · subst hj'
          simp [hmsb]
        · apply BitVec.getLsbD_of_ge
          omega

theorem fls'_eq_zero_iff (b : BitVec n) (m : Nat) (hm : n ≤ m) :
  fls' m b hm = 0 ↔ b = 0 := by
  induction n generalizing m with
  | zero =>
    simp [fls']
    exact BitVec.of_length_zero
  | succ n ih =>
    simp only [fls']
    split
    case succ.isTrue h =>
      constructor
      · intros contra
        simp at contra
        rw [← BitVec.toNat_inj] at contra
        simp at contra
        rw [Nat.mod_eq_of_lt] at contra
        · omega
        · apply Nat.lt_of_le_of_lt hm
          exact Nat.lt_two_pow_self
      · intros h
        subst h
        simp at h
    case succ.isFalse h =>
      constructor
      · intros hfls
        simp at hfls
        specialize ih (BitVec.setWidth n b) m (by omega)
        have ih := ih.mp hfls
        ext i hi
        by_cases hiEq : i = n
        · subst hiEq
          simp
          simp at h
          rw [BitVec.msb_eq_getLsbD_last] at h
          simpa using h
        · have : i < n := by
            omega
          have : (BitVec.setWidth n b)[i] = false := by
            rw [ih]
            simp
          simp at this
          rw [BitVec.getLsbD_eq_getElem] at this
          simpa using this
      · intros hb
        specialize ih (0#n) m (by omega)
        rw [hb]
        simp only [BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, Nat.le_add_right,
          BitVec.setWidth_ofNat_of_le]
        apply ih.mpr
        simp only [BitVec.ofNat_eq_ofNat]

@[simp, bv_float_normalize]
def fls_log (m : Nat) (b : BitVec n) : BitVec n :=
  if m = 0 then
    0
  else if b >>> m == 0 then
    fls_log (m/2) b
  else
    BitVec.ofNat _ m ||| fls_log (m/2) (b >>> m)
  termination_by m

/--
Find the position of the last (most significant) set bit in a BitVec.

Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.

Implemented naively using a fold with $O(n)$ steps.
-/
@[simp, bv_float_normalize]
def fls (b : BitVec n) : BitVec n :=
  fls' n b (n.le_refl)

@[simp]
theorem fls_eq_zero_iff (b : BitVec n) :
  fls b = 0 ↔ b = 0 := by
  simp [fls]
  apply fls'_eq_zero_iff

/--
Find the position of the last (most significant) set bit in a BitVec.

Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.
-/
@[simp, bv_float_normalize]
def flsLog (b : BitVec n) : BitVec n :=
  if b == 0 then 0 else 1#_ + fls_log (lastPowerOfTwo n) b

/--
`flsLog` and `fls` implement the same function.
-/
theorem flsIter_eq_fls (b : BitVec 8)
  : flsLog b = fls b := by
  simp
  bv_decide

/--
Gets the first `w` bits of the bitvector `v`.
-/
@[bv_float_normalize]
def truncateRight (w : Nat) (v : BitVec n) : BitVec w :=
  if hw : n ≤ w then
    -- Have to show that hw ⊢ n + (w - n) = w
    have h : (n+(w-n)) = w := by
      omega
    (v ++ 0#(w-n)).cast h
  else
    BitVec.truncate w (v >>> (n-w))


@[simp]
theorem toNat_truncateRight (x : BitVec w) :
  (truncateRight w' x).toNat =
  if w ≤ w' then
      x.toNat * (2 ^ (w' - w))
    else
      x.toNat / 2 ^ (w - w') := by
  by_cases hw : w ≤ w'
  · simp [truncateRight, hw]
    rw [Nat.shiftLeft_eq]
  · simp only [Nat.not_le] at hw
    simp only [truncateRight, BitVec.truncate_eq_setWidth]
    simp only [show ¬w ≤ w' by omega, ↓reduceDIte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      ↓reduceIte]
    have : x.toNat < 2^w := by omega
    rw [Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    simp [show w - w' + w' = w by omega, this]

theorem getMsbD_truncateRight (x : BitVec w)
  : (truncateRight w' x).getMsbD i = ((x.getMsbD i && (decide (i < w')))) := by
  by_cases hw : w ≤ w'
  · simp only [truncateRight, hw, ↓reduceDIte, BitVec.getMsbD_cast, BitVec.getMsbD_append,
    BitVec.getMsbD_zero, Bool.if_false_left]
    by_cases hi : i < w'
    · simp only [hi, decide_true, Bool.and_true, Bool.and_eq_right_iff_imp, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, Nat.not_le]
      apply BitVec.lt_of_getMsbD
    · simp only [hi, decide_false, Bool.and_false, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, Nat.not_le]
      omega
  · simp only [truncateRight, hw, ↓reduceDIte, BitVec.truncate_eq_setWidth,
    BitVec.getMsbD_setWidth, Nat.sub_le_iff_le_add, BitVec.getMsbD_ushiftRight]
    simp only [Nat.not_le] at hw
    simp only [show w' ≤ i + w by omega, decide_true, Bool.true_and]
    by_cases hi : i < w'
    · simp only [hi, decide_true, Bool.and_true]
      simp only [show i + w - w' < w by omega, decide_true, Bool.true_and]
      simp only [show ¬i + w - w' < w - w' by omega, decide_false, Bool.not_false, Bool.true_and]
      simp only [show i + w - w' - (w - w') = i by omega]
    · simp [hi]
      omega
