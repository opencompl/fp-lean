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
@[simp, bv_float_normalize]
def truncateRight (w : Nat) (v : BitVec n) : BitVec w :=
  if hw : n ≤ w then
    -- Have to show that hw ⊢ n + (w - n) = w
    have h : (n+(w-n)) = w := by
      omega
    (v ++ 0#(w-n)).cast h
  else
    BitVec.truncate w (v >>> (n-w))

theorem getMsbD_truncateRight (x : BitVec w)
  : (truncateRight w' x).getMsbD i = ((x.getMsbD i && (decide (i < w')))) := by
  by_cases hw : w ≤ w'
  · simp [truncateRight, hw]
    by_cases hi : i < w'
    · simp [hi]
      apply BitVec.lt_of_getMsbD
    · simp [hi]
      omega
  · simp [truncateRight, hw]
    simp at hw
    simp [show w' ≤ i + w by omega]
    by_cases hi : i < w'
    · simp [hi]
      simp [show i + w - w' < w by omega]
      simp [show ¬ i + w - w' < w - w' by omega]
      simp [show i + w - w' - (w - w') = i by omega]
    · simp [hi]
      omega
