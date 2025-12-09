import Std.Tactic.BVDecide
import Fp.Tactics

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
