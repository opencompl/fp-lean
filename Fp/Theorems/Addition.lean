import Fp.Addition
import Fp.Theorems.Multiplication
import Fp.Theorems.RoundEquiv

/-!
# Correctness of `PackedFloat.add` against the SMT-LIB semantics

The goal of this file is `Fp.add_eq_add`, the analogue of `Fp.mul_eq_mul`:
the bit-blasted addition circuit agrees (up to NaN bit patterns) with the
SMT-LIB semantics `SmtLibFunctions.add`, which adds the *exact* rational
values and rounds the result.

## Why addition is harder than multiplication

For multiplication, the unpacked circuit is **exact**: a product of two
`s`-bit significands fits in `2s` bits, so
`(a.mul b).toRat = a.toRat * b.toRat` on the nose
(`UnpackedFloat.toRat_mul_eq_toRat_mul_toRat`), and the rounding theorem
`UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE` can be applied directly
to the exact product.

For addition this is impossible: when the exponents of the operands differ by
`d`, the exact sum needs `s + d` bits of significand, and `d` can be as large
as the entire exponent range.  The circuit `UnpackedFloat.add` instead keeps
`s + 2` bits (one overflow bit, one guard bit) plus a **sticky bit** OR-ed
into the least significant position, which records "some nonzero bits were
shifted out".  The result is *not* the exact sum, but it is close enough that
**rounding cannot tell the difference**.

## Top-down proof plan

The proof is assembled from the following layers (top to bottom):

1. `add_eq_add` (the big theorem): case analysis on the kinds
   (NaN/∞/0/number) of both arguments, mirroring `mul_eq_mul`.
   * The NaN/∞ cases evaluate both sides by `simp`/`grind`.
   * The zero cases use that the sum is then exactly representable
     (layer 4) or exactly zero (layer 5).
   * The number/number case is layer 2.

2. `blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`: the rounding bridge.
   If the circuit value `q = z.toRat` is a *sticky compression* of the exact
   sum `r` (layer 3), then rounding `z` with the circuit agrees (`Rel`) with
   rounding `r` with the SMT-LIB rounder.  Internally:
   * `round_congr_of_RoundEquiv`: the SMT-LIB rounder only inspects a
     rational through the predicates "is it (weakly) above/below a
     representable value", so two rationals that agree on all those
     predicates round identically (`RoundEquiv`, `SameSideOfPacked`).
   * `roundEquiv_of_stickyEquiv`: a sticky compression of `r` agrees with
     `r` on all those predicates.  This is the "the error is small enough
     for rounding to take care of the rest" lemma: the circuit value is an
     odd multiple of a power of two that lies strictly below the
     representable grid (and below the midpoint grid), so no breakpoint of
     the rounding function separates `q` from `r`.
   * `round_eq_round_of_ne_zero`: the `sign` argument of the SMT-LIB
     rounder is only consulted for `r = 0`, so it is irrelevant here.

3. `UnpackedFloat.stickyEquiv_add` (+ `UnpackedFloat.msb_add_eq_true`):
   the circuit-level error bound.  For normalized inputs whose exact sum is
   nonzero, `(x.add y).toRat` is a sticky compression of
   `x.toRat + y.toRat` at the weight of the result's last significand bit,
   and the result is normalized.

4. `round_number_toRat_eq_self`: rounding is the identity on (the rational
   value of) a normal/nonzero-subnormal float.  Needed for the `x + 0 = x`
   branches, where the circuit returns the nonzero operand unchanged while
   the spec rounds its exact value.  Internally `smtLibLower`/`smtLibUpper`
   of a representable value are computed by `Classical.epsilon_elim` from
   uniqueness of lawful bounds (`IsLawfulLower`/`IsLawfulUpper`).

5. `structBeq` detection of exact cancellation: the circuit returns a signed
   zero exactly when `x = -y` *structurally*; for normalized significands
   this is *equivalent* to `x.toRat + y.toRat = 0`
   (`toRat_add_toRat_eq_zero_iff_structBeq_neg`), since the normalized
   representation of a nonzero value is unique.

## Definition: sticky compression

`StickyEquiv k q r` says: `q = r`, or `q` is an *odd* multiple of `2^k` and
`r` lies strictly within `2^k` of `q`.  This is exactly the contract of a
guard+sticky implementation: either no low bits were lost, or the kept value
has its bottom (weight `2^k`) bit forced to `1` and the true value is inside
the open interval `(q - 2^k, q + 2^k)`.

Note that `q` odd and `|r - q| < 2^k` force `q` and `r` to be nonzero with
the same sign: `|q| ≥ 2^k` since an odd integer is nonzero.
-/

namespace Fp

open SmtLibSemantics

/-! ## Layer 3: circuit-level error bound

These are the bit-level facts about `UnpackedFloat.add`.  Pen-and-paper
proofs are given in the docstrings; the Lean proofs are left as `sorry`
(they are bitvector/rational mixed arithmetic, analogous in spirit to —
but heavier than — `UnpackedFloat.toRat_mulUnadjustedMsb_eq_toRat_mul_toRat`).
-/

/--
**The addition circuit is correct up to a sticky-bit error.**

For normalized inputs (`msb = true`) with nonzero exact sum,
`(x.add y).toRat` is a sticky compression of the exact sum
`x.toRat + y.toRat` at the weight `2^((x.add y).toExpInt)` of the result's
last significand bit.

Pen-and-paper proof.  WLOG (the circuit swaps internally) `x` has the larger
exponent (or equal exponents and the larger significand), so the result is
computed as `±(X - Y)` or `±(X + Y)` at the grid `L₀ = 2^(x.ex - (s+1))`,
where `X = 4·x.sig` is exact on the grid and `Y` is `y`'s significand
aligned by an arithmetic right shift by `d = |x.ex - y.ex|` (capped at
`s+3`, which is harmless because then `y` contributes at most a sticky bit).

* The arithmetic shift computes `floor` over the *signed* value, so
  `sigSum = ⌊(exact aligned sum)/L₀⌋` and the lost bits
  (`ySig &&& orderEncode shift ≠ 0`) are nonzero iff the floor is strict.
  Hence `exact = (sigSum + f)·L₀` with `f ∈ [0, 1)`, `f > 0` iff sticky.
* If the (same-sign) sum overflows into the top bit, the circuit shifts
  right by one and folds the dropped bit into the sticky; the same
  invariant holds at grid `2·L₀`.
* If bits were lost (`sticky = true`) then `d ≥ 3` (the two appended low
  zero bits absorb shifts of `1` and `2`), so at most one leading bit
  cancels in `X - Y`; the post-cancellation `normalize` shifts left by at
  most one and the invariant holds at grid `L₀/2` with the kept value an
  *even* multiple of the new grid.
* Finally the sticky bit is OR-ed into the bottom bit: if the kept value
  `z₀` was even at the final grid `L`, the result becomes `z₀ + L`; in all
  cases the result is an odd multiple of `L` and the exact sum lies in
  `(z₀, z₀ + 2L') ⊆ (result - L, result + L)` strictly.
* If no bits were lost the result equals the exact sum (left disjunct).
-/
theorem UnpackedFloat.stickyEquiv_add {e s : Nat} (x y : UnpackedFloat e s)
    (hs : 0 < s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true)
    (hne : x.toRat + y.toRat ≠ 0) :
    StickyEquiv ((x.add y).toExpInt) ((x.add y).toRat) (x.toRat + y.toRat) := by
  -- L1 assembly: strip the shared sign `sd = (x.add y).sign.toSign` and grid `2^k`, reducing to the
  -- integer-significand disjunction `addCore` on `n = (x.add y).sig.toNat`, `t = sd·exact·2^(-k)`.
  rw [UnpackedFloat.toRat_eq_sign_sig_exp (x.add y)]
  have hsd : ((x.add y).sign.toSign : Rat) = 1 ∨ ((x.add y).sign.toSign : Rat) = -1 := by
    cases (x.add y).sign <;> simp [Bool.toSign]
  have hss : ((x.add y).sign.toSign : Rat) * (x.add y).sign.toSign = 1 := by
    rcases hsd with h | h <;> rw [h] <;> grind
  have hzz : (2 : Rat) ^ (-(x.add y).toExpInt) * 2 ^ ((x.add y).toExpInt) = 1 := by
    have hk0 : -(x.add y).toExpInt + (x.add y).toExpInt = 0 := by grind
    rw [← Rat.zpow_add (by grind), hk0]; simp
  have key : x.toRat + y.toRat
      = (x.add y).sign.toSign
        * ((x.add y).sign.toSign * (x.toRat + y.toRat) * (2 : Rat) ^ (-(x.add y).toExpInt))
        * 2 ^ ((x.add y).toExpInt) := by
    generalize x.toRat + y.toRat = E
    generalize ((x.add y).sign.toSign : Rat) = S at hss ⊢
    generalize (2 : Rat) ^ ((x.add y).toExpInt) = P at hzz ⊢
    generalize (2 : Rat) ^ (-(x.add y).toExpInt) = Q at hzz ⊢
    grind
  rw [key]
  refine StickyEquiv.of_sign_grid hsd ?_
  -- `addCore`: `t = n ∨ (n odd ∧ |t − n| < 1)`. Case split on `addSticky x y` (Phase C: lemmas A–G).
  sorry

/-- `bmod` is nonzero for a nonzero value lying strictly within one modulus of zero. -/
theorem bmod_ne_zero_of_lt (S : Int) (m : Nat) (hS0 : S ≠ 0) (hlo : -(m : Int) < S) (hhi : S < m) :
    S.bmod m ≠ 0 := by
  intro h
  have hdvd := Int.dvd_of_bmod_eq_zero h
  rcases (by omega : S < 0 ∨ S = 0 ∨ 0 < S) with hS | hS | hS
  · have : (m : Int) ≤ -S := Int.le_of_dvd (by omega) (Int.dvd_neg.mpr hdvd)
    omega
  · exact hS0 hS
  · have : (m : Int) ≤ S := Int.le_of_dvd hS hdvd
    omega

/-- **The aligned significand sum is nonzero.** For a larger significand `xS` and a smaller one `yS0`,
both normalized into the band `[2^(s+1), 2^(s+2))` (with `yS0` a multiple of four, so `≤ 2^(s+2) - 4`),
the aligned sum `xS ± (yS0 ≫ sh)` is nonzero — unless the operands cancel exactly (`sh = 0`, opposite
signs, equal significands), which `hcancel` rules out. Different signs: for `sh ≥ 1` the shifted smaller
operand has magnitude `< 2^(s+1) ≤ xS`, so the leading bit survives; for `sh = 0` it is exact
cancellation. Same sign: the sum is at least `xS ≥ 2^(s+1)`. This is the magnitude core shared by
`msb_add_eq_true` and (eventually) `stickyEquiv_add`. -/
theorem aligned_ne_zero {s : Nat} (xS yS0 sh : BitVec (s + 3)) (same : Bool)
    (hxlo : 2 ^ (s + 1) ≤ xS.toNat) (hxhi : xS.toNat < 2 ^ (s + 2))
    (hylo : 2 ^ (s + 1) ≤ yS0.toNat) (hyhi4 : yS0.toNat ≤ 2 ^ (s + 2) - 4)
    (hcancel : sh.toNat = 0 → same = false → xS.toNat = yS0.toNat → False) :
    xS + (bif same then yS0 else -yS0).sshiftRight' sh ≠ 0#(s + 3) := by
  have hp1 : 2 ^ (s + 1) * 2 = 2 ^ (s + 2) := by rw [← Nat.pow_succ]
  have hp2 : 2 ^ (s + 2) * 2 = 2 ^ (s + 3) := by rw [← Nat.pow_succ]
  have hxi : xS.toInt = (xS.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hyi : yS0.toInt = (yS0.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hdpos : (0 : Int) < ((2 ^ sh.toNat : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos _
  intro hzero
  have hz : (xS + (bif same then yS0 else -yS0).sshiftRight' sh).toInt = 0 := by
    rw [hzero]; exact BitVec.toInt_zero
  rw [BitVec.toInt_add, BitVec.toInt_sshiftRight'] at hz
  have hmod1 : -(((2 ^ (s + 3) : Nat) : Int) / 2) ≤ -(yS0.toNat : Int) := by omega
  have hmod2 : -(yS0.toNat : Int) < (((2 ^ (s + 3) : Nat) : Int) + 1) / 2 := by omega
  cases hsame : same
  · -- different sign
    simp only [hsame, cond_false] at hz
    have hnegi : (-yS0).toInt = -(yS0.toNat : Int) := by
      rw [BitVec.toInt_neg, hyi]; exact Int.bmod_eq_of_le hmod1 hmod2
    rw [hnegi, Int.shiftRight_eq_div_pow, hxi] at hz
    have hqle0 : (-(yS0.toNat : Int)) / ((2 ^ sh.toNat : Nat) : Int) ≤ 0 := by
      have h := Int.ediv_le_ediv hdpos (show (-(yS0.toNat : Int)) ≤ 0 by omega)
      simpa using h
    rcases Nat.eq_zero_or_pos sh.toNat with hsh | hsh
    · -- shift 0: exact cancellation
      have hq_eq : (-(yS0.toNat : Int)) / ((2 ^ sh.toNat : Nat) : Int) = -(yS0.toNat : Int) := by
        rw [hsh]; simp
      rw [hq_eq] at hz
      refine bmod_ne_zero_of_lt _ _ ?_ ?_ ?_ hz
      · intro h0; exact hcancel hsh hsame (by omega)
      · omega
      · omega
    · -- shift ≥ 1: the smaller operand cannot cancel the leading bit
      have h2sh : 2 ≤ 2 ^ sh.toNat := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ sh.toNat := Nat.pow_le_pow_right (by omega) hsh
      have h1le : (1 : Nat) ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
      have hqlb : -((2 ^ (s + 1) : Nat) : Int) + 1
          ≤ (-(yS0.toNat : Int)) / ((2 ^ sh.toNat : Nat) : Int) := by
        rw [Int.le_ediv_iff_mul_le hdpos]
        have hmul : (2 ^ (s + 1) - 1) * 2 ≤ (2 ^ (s + 1) - 1) * 2 ^ sh.toNat :=
          Nat.mul_le_mul_left _ h2sh
        have hdist : (2 ^ (s + 1) - 1) * 2 ^ sh.toNat
            = 2 ^ (s + 1) * 2 ^ sh.toNat - 2 ^ sh.toNat := by rw [Nat.sub_mul, Nat.one_mul]
        have key2 : yS0.toNat + 2 ^ sh.toNat ≤ 2 ^ (s + 1) * 2 ^ sh.toNat := by omega
        have key2I : (yS0.toNat : Int) + ((2 ^ sh.toNat : Nat) : Int)
            ≤ ((2 ^ (s + 1) * 2 ^ sh.toNat : Nat) : Int) := by exact_mod_cast key2
        have hexpand : (-((2 ^ (s + 1) : Nat) : Int) + 1) * ((2 ^ sh.toNat : Nat) : Int)
            = ((2 ^ sh.toNat : Nat) : Int)
              - ((2 ^ (s + 1) : Nat) : Int) * ((2 ^ sh.toNat : Nat) : Int) := by grind
        have hpm : ((2 ^ (s + 1) : Nat) : Int) * ((2 ^ sh.toNat : Nat) : Int)
            = ((2 ^ (s + 1) * 2 ^ sh.toNat : Nat) : Int) := by push_cast; grind
        rw [hexpand, hpm]; omega
      refine bmod_ne_zero_of_lt _ _ ?_ ?_ ?_ hz <;> omega
  · -- same sign
    simp only [hsame, cond_true] at hz
    rw [hyi, Int.shiftRight_eq_div_pow, hxi] at hz
    have hq0 : 0 ≤ (yS0.toNat : Int) / ((2 ^ sh.toNat : Nat) : Int) :=
      Int.ediv_nonneg (by exact_mod_cast Nat.zero_le _) (by omega)
    have hqle : (yS0.toNat : Int) / ((2 ^ sh.toNat : Nat) : Int) ≤ (yS0.toNat : Int) :=
      Int.ediv_le_self _ (by exact_mod_cast Nat.zero_le _)
    refine bmod_ne_zero_of_lt _ _ ?_ ?_ ?_ hz <;> omega

/-- **Lemma A (value form of `aligned_ne_zero`)** — the aligned signed sum `xS + (±yS0) >> sh` as a
`Nat` (big dominates ⇒ ≥ 0). Same sign ⇒ `xS + ⌊yS0/2^sh⌋` (logical shift, `yS0.msb = false`); diff
sign ⇒ `xS − ⌈yS0/2^sh⌉` (the signed shift floors the negated operand toward −∞, via
`Int.neg_natCast_ediv_eq`). `hdom` supplies the swap ordering needed only for the diff-sign `sh = 0`
(equal-exponent) case. -/
theorem aligned_toNat {s : Nat} (xS yS0 sh : BitVec (s + 3)) (same : Bool)
    (hxlo : 2 ^ (s + 1) ≤ xS.toNat) (hxhi : xS.toNat < 2 ^ (s + 2))
    (hylo : 2 ^ (s + 1) ≤ yS0.toNat) (hyhi4 : yS0.toNat ≤ 2 ^ (s + 2) - 4)
    (hdom : same = false → sh.toNat = 0 → yS0.toNat ≤ xS.toNat) :
    (xS + (bif same then yS0 else -yS0).sshiftRight' sh).toNat
      = if same = true then xS.toNat + yS0.toNat / 2 ^ sh.toNat
        else xS.toNat - (yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat := by
  have hp1 : 2 ^ (s + 1) * 2 = 2 ^ (s + 2) := by rw [← Nat.pow_succ]
  have hp2 : 2 ^ (s + 2) * 2 = 2 ^ (s + 3) := by rw [← Nat.pow_succ]
  have hyi : yS0.toInt = (yS0.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by grind)
  have hxi : xS.toInt = (xS.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by grind)
  have hdiv_le : yS0.toNat / 2 ^ sh.toNat ≤ yS0.toNat := Nat.div_le_self _ _
  have hd2pos : 0 < 2 ^ sh.toNat := Nat.two_pow_pos _
  cases hsame : same
  · -- different sign: the shift floors the negated operand toward −∞, giving a ceiling.
    simp only [cond_false, Bool.false_eq_true, if_false]
    -- shifted value = -⌈yS0/2^sh⌉
    have hnegi : (-yS0).toInt = -(yS0.toNat : Int) := by
      rw [BitVec.toInt_neg, hyi]; apply Int.bmod_eq_of_le <;> grind
    have hshiftI : ((-yS0).sshiftRight' sh).toInt
        = -(((yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat : Nat) : Int) := by
      rw [BitVec.toInt_sshiftRight', hnegi, Int.shiftRight_eq_div_pow]
      exact Int.neg_natCast_ediv_eq yS0.toNat (2 ^ sh.toNat) hd2pos
    -- big dominates: `xS.toNat ≥ ⌈yS0/2^sh⌉`
    have hCLle : (yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat ≤ xS.toNat := by
      rcases Nat.eq_zero_or_pos sh.toNat with hsh0 | hshp
      · rw [hsh0]; simpa using hdom hsame hsh0
      · have h2sh : 2 ≤ 2 ^ sh.toNat := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ sh.toNat := Nat.pow_le_pow_right (by grind) hshp
        have hdr : yS0.toNat / 2 ^ sh.toNat ≤ yS0.toNat / 2 := Nat.div_le_div_left h2sh (by grind)
        have hstep : (yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat ≤ yS0.toNat / 2 ^ sh.toNat + 1 := by
          rw [show yS0.toNat + 2 ^ sh.toNat - 1 = (yS0.toNat - 1) + 2 ^ sh.toNat by grind,
            Nat.add_div_right _ hd2pos]
          have hh : (yS0.toNat - 1) / 2 ^ sh.toNat ≤ yS0.toNat / 2 ^ sh.toNat :=
            Nat.div_le_div_right (Nat.sub_le _ _)
          grind
        grind
    -- the (nonneg) sum value
    have hsum : (xS + (-yS0).sshiftRight' sh).toInt
        = ((xS.toNat - (yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat : Nat) : Int) := by
      rw [BitVec.toInt_add, hshiftI, hxi,
        show (xS.toNat : Int) + -(((yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat : Nat) : Int)
          = ((xS.toNat - (yS0.toNat + 2 ^ sh.toNat - 1) / 2 ^ sh.toNat : Nat) : Int) by
          grind]
      apply Int.bmod_eq_of_le <;> grind
    have hsumnn : 0 ≤ (xS + (-yS0).sshiftRight' sh).toInt := by
      rw [hsum]; exact_mod_cast Nat.zero_le _
    have htoNat := BitVec.toInt_eq_toNat_of_toInt_nonneg _ hsumnn
    rw [hsum] at htoNat; exact_mod_cast htoNat.symm
  · -- same sign: `yS0 >> sh` is a logical shift (`yS0.msb = false`)
    simp only [cond_true]
    have hge : 0 ≤ (yS0.sshiftRight' sh).toInt := by
      rw [BitVec.toInt_sshiftRight', hyi, Int.shiftRight_eq_div_pow]
      exact Int.ediv_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)
    have heq : (yS0.sshiftRight' sh).toInt = ((yS0.toNat / 2 ^ sh.toNat : Nat) : Int) := by
      rw [BitVec.toInt_sshiftRight', hyi, Int.shiftRight_eq_div_pow, Int.natCast_ediv]
    have hshift : (yS0.sshiftRight' sh).toNat = yS0.toNat / 2 ^ sh.toNat := by
      have h := BitVec.toInt_eq_toNat_of_toInt_nonneg (yS0.sshiftRight' sh) hge
      rw [heq] at h; exact_mod_cast h.symm
    rw [BitVec.toNat_add, hshift, Nat.mod_eq_of_lt (by grind)]
    simp [hsame]

/-- A zero alignment shift forces equal exponents: the circuit's `shiftAmount` is `0` only via the
`ult` branch (the `↑s + 3` else-branch has `toNat = s + 3 ≠ 0`), which bounds `absExpDiff.toNat <
s + 3 < 2^(s+3)`, so the capping `setWidth` is exact and `absExpDiff = 0`, hence `expDiff = 0` and
(`signExtend` injective on `toInt`) `x.ex = y.ex`. -/
theorem UnpackedFloat.addShift_zero_imp_ex_eq {e s : Nat} (x y : UnpackedFloat e s)
    (expDiff : BitVec (e + 1)) (hed : expDiff = x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1))
    (absExpDiff : BitVec (e + 1)) (had : absExpDiff = bif expDiff.msb then -expDiff else expDiff)
    (shiftAmount : BitVec (s + 3))
    (hsa : shiftAmount = bif absExpDiff.ult (↑s + 3)
        then BitVec.setWidth (s + 3) absExpDiff else (↑s + 3))
    (hsh0 : shiftAmount.toNat = 0) : x.ex = y.ex := by
  have hlt : s + 3 < 2 ^ (s + 3) := Nat.lt_two_pow_self
  have hsM : s % 2 ^ (s + 3) = s := Nat.mod_eq_of_lt (by omega)
  have h3M : 3 % 2 ^ (s + 3) = 3 := Nat.mod_eq_of_lt (by omega)
  have hsumM : (s + 3) % 2 ^ (s + 3) = s + 3 := Nat.mod_eq_of_lt (by omega)
  have h3v : (3 : BitVec (s + 3)).toNat = 3 := by
    rw [show (3 : BitVec (s + 3)) = BitVec.ofNat (s + 3) 3 from rfl, BitVec.toNat_ofNat]; exact h3M
  have hsv : (↑s : BitVec (s + 3)).toNat = s := by
    rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]; exact hsM
  have helse : ((↑s + 3 : BitVec (s + 3))).toNat = s + 3 := by
    rw [BitVec.toNat_add, hsv, h3v, hsumM]
  rw [hsa] at hsh0
  have habs0 : absExpDiff = 0 := by
    cases hu : absExpDiff.ult (↑s + 3)
    · simp only [hu, cond_false] at hsh0
      rw [helse] at hsh0; exact absurd hsh0 (by omega)
    · simp only [hu, cond_true] at hsh0
      have hb1 : absExpDiff.toNat < ((↑s + 3 : BitVec (e + 1))).toNat := by
        have h := hu; rw [BitVec.ult, decide_eq_true_eq] at h; exact h
      have hb2 : ((↑s + 3 : BitVec (e + 1))).toNat ≤ s + 3 := by
        rw [BitVec.toNat_add]
        have h1 : (↑s : BitVec (e + 1)).toNat ≤ s := by
          rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]; exact Nat.mod_le _ _
        have h2 : (3 : BitVec (e + 1)).toNat ≤ 3 := by
          rw [show (3 : BitVec (e + 1)) = BitVec.ofNat (e + 1) 3 from rfl, BitVec.toNat_ofNat]
          exact Nat.mod_le _ _
        have h3 := Nat.mod_le ((↑s : BitVec (e + 1)).toNat + (3 : BitVec (e + 1)).toNat) (2 ^ (e + 1))
        omega
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at hsh0
      exact BitVec.eq_of_toNat_eq (by simpa using hsh0)
  have hed0 : expDiff = 0 := by
    rw [had] at habs0
    cases hm : expDiff.msb <;> simp only [hm, cond_true, cond_false] at habs0
    · exact habs0
    · exact BitVec.neg_inj.mp (habs0.trans (BitVec.neg_zero (e + 1)).symm)
  have hed0' : x.ex.signExtend (e + 1) - y.ex.signExtend (e + 1) = 0 := hed.symm.trans hed0
  have hAB : x.ex.signExtend (e + 1) = y.ex.signExtend (e + 1) := by
    have h2 := congrArg (· + y.ex.signExtend (e + 1)) hed0'
    simp only [BitVec.sub_add_cancel] at h2
    simpa using h2
  apply BitVec.toInt_inj.mp
  have ha : (x.ex.signExtend (e + 1)).toInt = x.ex.toInt :=
    BitVec.toInt_signExtend_of_le (by omega)
  have hb : (y.ex.signExtend (e + 1)).toInt = y.ex.toInt :=
    BitVec.toInt_signExtend_of_le (by omega)
  rw [← ha, ← hb, hAB]

/-- The cancellation-renormalisation step (`bif !uf.sig.msb then uf.normalize else uf`) yields a
result with msb set exactly when the input significand is nonzero: if the msb is already set there is
nothing to do, otherwise `normalize` sets it (`msb_normalize_eq_decide`). -/
theorem UnpackedFloat.msb_cond_normalize_of_sig_ne_zero {e s : Nat} (uf : UnpackedFloat e s)
    (zsign : Bool) (h : uf.sig ≠ 0#s) :
    (bif !uf.sig.msb then uf.normalize zsign else uf).sig.msb = true := by
  cases huf : uf.sig.msb
  · simp only [huf, Bool.not_false, cond_true]
    rw [UnpackedFloat.msb_normalize_eq_decide]
    simp [h]
  · simp [huf]

/-- `structBeq` is sound for cancellation detection: if `x` is structurally the negation of `y`, the
exact sum is zero. -/
theorem UnpackedFloat.toRat_add_toRat_eq_zero_of_structBeq_neg
    {e s : Nat} (x y : UnpackedFloat e s)
    (h : x.structBeq y.neg) : x.toRat + y.toRat = 0 := by
  have hx : x = y.neg := by
    simp only [UnpackedFloat.structBeq, Bool.and_eq_true, beq_iff_eq] at h
    rcases x with ⟨xsign, xex, xsig⟩
    rcases y with ⟨ysign, yex, ysig⟩
    simp_all [UnpackedFloat.neg]
  subst hx
  have : y.neg = -y := Eq.refl _
  rw [this, UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat_eq_toRat',
    UnpackedFloat.toRat'_neg]
  grind

/-- **Lemma A″** — the capped alignment shift is `min Δ (s+3)`, where `Δ = (addAbsExpDiff x y).toNat` is
the uncapped exponent difference. Needs `s + 3 < 2^(e+1)` so the `↑s + 3` cap literal doesn't wrap. -/
theorem UnpackedFloat.addShiftAmount_toNat_eq {e s : Nat} (x y : UnpackedFloat e s)
    (hes : s + 3 < 2 ^ (e + 1)) :
    (UnpackedFloat.addShiftAmount x y).toNat = min (UnpackedFloat.addAbsExpDiff x y).toNat (s + 3) := by
  unfold UnpackedFloat.addShiftAmount
  have hlt3 : s + 3 < 2 ^ (s + 3) := Nat.lt_two_pow_self
  have hcap : ((↑s + 3 : BitVec (e + 1))).toNat = s + 3 := BitVec.toNat_natCast_add_three s hes
  cases hu : (UnpackedFloat.addAbsExpDiff x y).ult (↑s + 3)
  · simp only [hu, cond_false]
    have hge : s + 3 ≤ (UnpackedFloat.addAbsExpDiff x y).toNat := by
      have h := hu; rw [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt, hcap] at h; exact h
    rw [BitVec.toNat_natCast_add_three s hlt3]; grind
  · simp only [hu, cond_true]
    have hlt : (UnpackedFloat.addAbsExpDiff x y).toNat < s + 3 := by
      have h := hu; rw [BitVec.ult, decide_eq_true_eq, hcap] at h; exact h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by grind)]; grind

/-- The extended significand `sig.setWidth' _ ++ 0#2` has `toNat = sig.toNat * 4` (one overflow bit on
the left, two round/sticky zero bits on the right). -/
theorem BitVec.setWidth'_append0_toNat {w : Nat} (h : w ≤ w + 1) (v : BitVec w) :
    (v.setWidth' h ++ (0#2)).toNat = v.toNat * 4 := by
  rw [BitVec.toNat_append, BitVec.toNat_setWidth', BitVec.toNat_ofNat]
  simp [Nat.shiftLeft_eq]

/-- The post-swap larger operand keeps a normalized significand. -/
theorem UnpackedFloat.msb_addBig {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (UnpackedFloat.addBig x y).sig.msb = true := by
  unfold UnpackedFloat.addBig
  cases UnpackedFloat.addSwapCond x y <;> simp [hx, hy]

/-- The post-swap smaller operand keeps a normalized significand. -/
theorem UnpackedFloat.msb_addSmall {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true) :
    (UnpackedFloat.addSmall x y).sig.msb = true := by
  unfold UnpackedFloat.addSmall
  cases UnpackedFloat.addSwapCond x y <;> simp [hx, hy]

/-- The operand swap preserves the exact sum. -/
theorem UnpackedFloat.toRat_addBig_add_addSmall {e s : Nat} (x y : UnpackedFloat e s) :
    (UnpackedFloat.addBig x y).toRat + (UnpackedFloat.addSmall x y).toRat = x.toRat + y.toRat := by
  unfold UnpackedFloat.addBig UnpackedFloat.addSmall
  cases UnpackedFloat.addSwapCond x y <;> simp [Rat.add_comm]

/--
**The addition circuit produces a normalized result** (for normalized inputs
with nonzero exact sum).

Pen-and-paper proof.  Three cases:
* Same signs: the aligned sum is at least the larger operand, whose
  significand has its msb set, so after the conditional 1-bit overflow
  shift the msb of the `s+2`-bit result is set.
* Different signs with sticky (`d ≥ 3`): at most one leading bit cancels
  (`X - Y > X·(1 - 2^{-2}) ≥ 2^s` at the result grid), so either the msb is
  already set or `normalize` shifts by exactly one and sets it.
* Different signs without sticky: the subtraction is exact; the result is
  nonzero by `hne`, and `normalize` establishes the msb
  (`UnpackedFloat.msb_normalize_eq_decide`).  OR-ing the (false) sticky bit
  changes nothing; OR-ing a true sticky never clears the msb.
-/
theorem UnpackedFloat.msb_add_eq_true {e s : Nat} (x y : UnpackedFloat e s)
    (hs : 0 < s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true)
    (hne : x.toRat + y.toRat ≠ 0) :
    (x.add y).sig.msb = true := by
  -- Gradual unfold of the named circuit pieces (no `extract_lets`/swap-casing): peel one layer
  -- at a time down to `addSigSum x y ≠ 0`, then discharge with `aligned_ne_zero`.
  unfold UnpackedFloat.add
  show ((UnpackedFloat.addNormSum x y).sig
      ||| (BitVec.ofBool (UnpackedFloat.addSticky x y)).setWidth' (by grind)).msb = true
  -- Strip the sticky OR (never clears the top bit), collapse the cancellation-normalize.
  rw [BitVec.msb_or, BitVec.msb_setWidth'_ofBool_eq_false (by grind), Bool.or_false]
  unfold UnpackedFloat.addNormSum
  apply UnpackedFloat.msb_cond_normalize_of_sig_ne_zero
  unfold UnpackedFloat.addSum
  -- Bridge `sum.sig = truncate(s+2)(sigSum >>> ofBool sigSum.msb) ≠ 0` to `sigSum ≠ 0`.
  show BitVec.truncate (s + 2)
      (UnpackedFloat.addSigSum x y >>> BitVec.ofBool (UnpackedFloat.addSigSum x y).msb) ≠ 0#(s + 2)
  suffices hss : UnpackedFloat.addSigSum x y ≠ 0#(s + 3) by
    generalize hgen : UnpackedFloat.addSigSum x y = sigSum at hss ⊢
    rw [show (sigSum >>> BitVec.ofBool sigSum.msb)
          = sigSum >>> (BitVec.ofBool sigSum.msb).toNat from rfl,
      Ne, BitVec.toNat_eq, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofBool, BitVec.toNat_ofNat, Nat.zero_mod]
    have hlt : sigSum.toNat < 2 ^ (s + 3) := sigSum.isLt
    have hne' : sigSum.toNat ≠ 0 := by rw [Ne, BitVec.toNat_eq] at hss; simpa using hss
    cases hm : sigSum.msb
    · have hlo : sigSum.toNat < 2 ^ (s + 2) := by
        have h := hm; rw [BitVec.msb_eq_decide] at h
        simp only [decide_eq_false_iff_not, Nat.not_le, show s + 3 - 1 = s + 2 from rfl] at h
        exact h
      simp only [hm, Bool.toNat_false, Nat.shiftRight_zero, Nat.mod_eq_of_lt hlo]
      exact hne'
    · have hge : 2 ^ (s + 2) ≤ sigSum.toNat := by
        have h := hm; rw [BitVec.msb_eq_decide] at h
        simp only [decide_eq_true_eq, show s + 3 - 1 = s + 2 from rfl] at h
        exact h
      simp only [hm, Bool.toNat_true, Nat.shiftRight_succ, Nat.shiftRight_zero]
      have h1 : 2 ^ (s + 1) ≤ sigSum.toNat / 2 := by
        rw [Nat.le_div_iff_mul_le (by decide)]; rw [Nat.pow_succ] at hge ⊢; grind
      have h2 : sigSum.toNat / 2 < 2 ^ (s + 2) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at hlt; grind
      rw [Nat.mod_eq_of_lt h2]
      have := Nat.two_pow_pos (s + 1); grind
  -- `addSigSum x y ≠ 0` via `aligned_ne_zero` on the named pieces (no swap-casing — `addBig`/`addSmall`
  -- encapsulate the swap; their msb / exact-sum lemmas do the rest).
  unfold UnpackedFloat.addSigSum UnpackedFloat.addYSig
  have hbig := UnpackedFloat.msb_addBig x y hx hy
  have hsmall := UnpackedFloat.msb_addSmall x y hx hy
  have hxval : (UnpackedFloat.addXSig x y).toNat = (UnpackedFloat.addBig x y).sig.toNat * 4 := by
    unfold UnpackedFloat.addXSig; exact BitVec.setWidth'_append0_toNat _ _
  have hyval : ((UnpackedFloat.addSmall x y).sig.setWidth' (Nat.le_succ s) ++ 0#2).toNat
      = (UnpackedFloat.addSmall x y).sig.toNat * 4 := BitVec.setWidth'_append0_toNat _ _
  have e1 : 2 ^ (s - 1) * 4 = 2 ^ (s + 1) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; grind
  have e2 : 2 ^ s * 4 = 2 ^ (s + 2) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hbiglo : 2 ^ (s - 1) ≤ (UnpackedFloat.addBig x y).sig.toNat := BitVec.le_toNat_of_msb_true hbig
  have hsmalllo : 2 ^ (s - 1) ≤ (UnpackedFloat.addSmall x y).sig.toNat :=
    BitVec.le_toNat_of_msb_true hsmall
  have hbighi : (UnpackedFloat.addBig x y).sig.toNat < 2 ^ s := (UnpackedFloat.addBig x y).sig.isLt
  have hsmallhi : (UnpackedFloat.addSmall x y).sig.toNat < 2 ^ s :=
    (UnpackedFloat.addSmall x y).sig.isLt
  refine aligned_ne_zero (UnpackedFloat.addXSig x y)
    ((UnpackedFloat.addSmall x y).sig.setWidth' (Nat.le_succ s) ++ 0#2) (UnpackedFloat.addShiftAmount x y)
    ((UnpackedFloat.addBig x y).sign == (UnpackedFloat.addSmall x y).sign)
    (by rw [hxval]; grind) (by rw [hxval]; grind) (by rw [hyval]; grind) (by rw [hyval]; grind) ?_
  -- `hcancel`: zero shift ⇒ equal exponents; equal significands + opposite signs ⇒ exact cancellation.
  intro hsh0 hsamef hxyeq
  have hexeq : x.ex = y.ex :=
    UnpackedFloat.addShift_zero_imp_ex_eq x y (UnpackedFloat.addExpDiff x y) rfl
      (UnpackedFloat.addAbsExpDiff x y) rfl (UnpackedFloat.addShiftAmount x y) rfl hsh0
  have hsigeq : (UnpackedFloat.addBig x y).sig = (UnpackedFloat.addSmall x y).sig := by
    apply BitVec.eq_of_toNat_eq; rw [hxval, hyval] at hxyeq; grind
  have hexeq2 : (UnpackedFloat.addBig x y).ex = (UnpackedFloat.addSmall x y).ex := by
    unfold UnpackedFloat.addBig UnpackedFloat.addSmall
    cases UnpackedFloat.addSwapCond x y <;> simp [hexeq]
  have hsignneq : (UnpackedFloat.addBig x y).sign = !(UnpackedFloat.addSmall x y).sign := by
    cases hbs : (UnpackedFloat.addBig x y).sign <;>
      cases hcs : (UnpackedFloat.addSmall x y).sign <;> simp_all
  have hzero : (UnpackedFloat.addBig x y).toRat + (UnpackedFloat.addSmall x y).toRat = 0 :=
    UnpackedFloat.toRat_add_toRat_eq_zero_of_structBeq_neg _ _ (by
      simp only [UnpackedFloat.structBeq, UnpackedFloat.neg, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hsignneq, hexeq2⟩, hsigeq⟩)
  exact hne (by rw [← UnpackedFloat.toRat_addBig_add_addSmall x y]; exact hzero)

/-! ## Layer 5: exact-cancellation detection -/

/--
The normalized representation of a nonzero value is unique: two
`UnpackedFloat`s with set msb and the same nonzero rational value are
structurally equal.

Proof: `|toRat| = sig · 2^(ex - (s-1))` with `sig ∈ [2^(s-1), 2^s)`, so the
binade of the value determines `ex.toInt` (hence `ex`), then `sig`, and the sign
of the value determines `sign` — discharged by `Rat.mul_two_zpow_inj`.
-/
theorem UnpackedFloat.eq_of_toRat_eq_toRat_of_msb {e s : Nat}
    (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true)
    (h : x.toRat = y.toRat) : x = y := by
  -- normalized significands sit in the band `[2^(s-1), 2^s)`
  have hxlo : 2 ^ (s - 1) ≤ x.sig.toNat := BitVec.le_toNat_of_msb_true hx
  have hylo : 2 ^ (s - 1) ≤ y.sig.toNat := BitVec.le_toNat_of_msb_true hy
  have hxhi : x.sig.toNat < 2 ^ s := x.sig.isLt
  have hyhi : y.sig.toNat < 2 ^ s := y.sig.isLt
  have hxpos : 0 < x.sig.toNat := by have := Nat.two_pow_pos (s - 1); omega
  have hypos : 0 < y.sig.toNat := by have := Nat.two_pow_pos (s - 1); omega
  -- equal values ⇒ equal magnitudes `a·2^p = b·2^q`
  rw [UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat_eq_toRat'] at h
  have habs : (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt
      = (y.sig.toNat : Rat) * (2 : Rat) ^ y.toExpInt := by
    have hx' := UnpackedFloat.abs_toRat'_eq x (prec := s - 1)
    have hy' := UnpackedFloat.abs_toRat'_eq y (prec := s - 1)
    rw [← hx', ← hy', h]
  -- binade uniqueness pins the significand and exponent
  obtain ⟨hsigeq, hexpeq⟩ := Rat.mul_two_zpow_inj hxlo hxhi hylo hyhi habs
  -- the sign bit is recovered from the (nonzero) value
  have hxnz : x.toRat' ≠ 0 := by
    intro hz
    have hpos : (0 : Rat) < (x.sig.toNat : Rat) * (2 : Rat) ^ x.toExpInt :=
      Rat.mul_positive (by exact_mod_cast hxpos) (Rat.two_pow_pos _)
    rw [← UnpackedFloat.abs_toRat'_eq, hz] at hpos
    simp [Rat.abs] at hpos
  have hynz : y.toRat' ≠ 0 := by
    intro hz
    have hpos : (0 : Rat) < (y.sig.toNat : Rat) * (2 : Rat) ^ y.toExpInt :=
      Rat.mul_positive (by exact_mod_cast hypos) (Rat.two_pow_pos _)
    rw [← UnpackedFloat.abs_toRat'_eq, hz] at hpos
    simp [Rat.abs] at hpos
  have hsign : x.sign = y.sign := by
    rw [UnpackedFloat.sign_eq_decide_toRat'_lt_zero x hxnz,
        UnpackedFloat.sign_eq_decide_toRat'_lt_zero y hynz, h]
  -- exponent equality ⇒ `ex` equality
  have hex : x.ex = y.ex := by
    apply BitVec.toInt_inj.mp
    simp only [UnpackedFloat.toExpInt] at hexpeq
    omega
  have hsig : x.sig = y.sig := BitVec.toNat_inj.mp hsigeq
  rw [UnpackedFloat.ext_iff]
  exact ⟨hsign, hex, hsig⟩

/--
`structBeq` is complete for cancellation detection on normalized inputs:
if `x` is *not* structurally the negation of `y`, the exact sum is nonzero.
Together with soundness this justifies the early-out `mkZero` branch of
`EUnpackedFloat.add`: it fires *exactly* when the exact sum is zero.
-/
theorem UnpackedFloat.toRat_add_toRat_ne_zero_of_not_structBeq_neg
    {e s : Nat} (x y : UnpackedFloat e s)
    (hx : x.sig.msb = true) (hy : y.sig.msb = true)
    (h : ¬ x.structBeq y.neg) : x.toRat + y.toRat ≠ 0 := by
  intro hcontra
  apply h
  have hyneg : y.neg.sig.msb = true := by
    simpa [UnpackedFloat.neg] using hy
  have : x.toRat = y.neg.toRat := by
    have : y.neg = -y := Eq.refl _
    rw [this, UnpackedFloat.toRat_eq_toRat', UnpackedFloat.toRat_eq_toRat',
      UnpackedFloat.toRat'_neg]
    have h1 := UnpackedFloat.toRat_eq_toRat' (uf := y)
    have h2 := UnpackedFloat.toRat_eq_toRat' (uf := x)
    grind
  have := UnpackedFloat.eq_of_toRat_eq_toRat_of_msb x y.neg hx hyneg this
  simp [this, UnpackedFloat.structBeq]

/-! ## Layer 2: the rounding bridge -/

/--
The bit-blasted rounder applied to the circuit result agrees with the
SMT-LIB rounder applied to the *exact* value, provided the circuit result is
a sticky compression of the exact value.  This generalizes
`UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE` (which requires
`r = x.toRat` on the nose, as is the case for multiplication).
-/
theorem UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RNE : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).Rel
      ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
          SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE sign (ExtRat.Number r)) := by
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RNE x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RNE sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.toExtRat_round_Rel_smtLibRound_of_RNE he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm

/--
**Finiteness companion of `blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv`.**

When the circuit is a finite `Number`, the SMT-LIB round of the exact value `r`
is neither NaN nor infinite.  Since the rounder cannot distinguish `r` from the
circuit's sticky-compressed value `x.toRat` (`roundEquiv_of_stickyEquiv`), the
round of `r` equals the round of `x.toRat`, so this reduces to the exact-value
finiteness lemma `blastSmtLibRound_finite_of_RNE`.
-/
theorem UnpackedFloat.blastSmtLibRound_finite_of_RNE_of_stickyEquiv
    {ep sp eu su : Nat}
    (he : 1 < ep) (hep : 2 < ep) (hs : 0 < sp)
    (heu : exponentWidth ep sp ≤ eu) (hsu : sp + 3 ≤ su)
    (x : UnpackedFloat eu su)
    (sign : Bool) (r : Rat) (hrne : r ≠ 0)
    (hxnorm : x.normalize = x)
    (hr : StickyEquiv x.toExpInt x.toRat r) :
    (x.blastSmtLibRound ep sp .RNE : EUnpackedFloat (exponentWidth ep sp) (sp + 1)).state = .Number →
      ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE sign (ExtRat.Number r)).isNaN
      ∧ ¬ ((SmtLibSemantics.smtLibRoundMethod (R := ExtRat) ep sp
            SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round .RNE sign (ExtRat.Number r)).isInfinite := by
  intro hstate
  have hq : x.toRat ≠ 0 := hr.ne_zero_of_ne_zero hrne
  have hmsb : x.sig.msb = true := by
    have hsig : ¬ (x.sig = 0#su) := by
      intro hcontra
      apply hq
      rw [UnpackedFloat.toRat_eq_toRat']
      apply UnpackedFloat.toRat'_eq_zero_of_isZero
      simp [UnpackedFloat.isZero, hcontra]
    exact (UnpackedFloat.normalize_eq_self_iff x hsig).mp hxnorm
  have hcongr := round_congr_of_RoundEquiv (e := ep) (s := sp) .RNE x.sign
    (roundEquiv_of_stickyEquiv he hs hsu x hmsb hr) hq
  rw [round_eq_round_of_ne_zero .RNE sign x.sign r hrne, ← hcongr]
  exact UnpackedFloat.blastSmtLibRound_finite_of_RNE he hep hs heu (by omega)
    x x.sign (Eq.refl _) x.toRat (Eq.refl _) hxnorm hmsb hstate

/-! ## Layer 4: rounding is the identity on representable values -/

/--
The PackedFloat order is total away from NaN.
-/
theorem PackedFloat.le_total_of_not_isNaN {e s : Nat} (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) : x ≤ y ∨ y ≤ x := by
  rw [← PackedFloat.le_def, ← PackedFloat.le_def, PackedFloat.le, PackedFloat.le]
  grind

/--
The PackedFloat order is antisymmetric away from NaN (different NaN
bit patterns compare `≤` both ways, but nothing else does — note `-0 < +0`
strictly in this order).
-/
theorem PackedFloat.eq_of_le_of_le_of_not_isNaN {e s : Nat} (x y : PackedFloat e s)
    (hx : ¬ x.isNaN) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rw [← PackedFloat.le_def, PackedFloat.le] at hxy hyx
  rcases x with ⟨xsign, xex, xsig⟩
  rcases y with ⟨ysign, yex, ysig⟩
  simp only [PackedFloat.mk.injEq]
  grind [BitVec.toNat_inj]

/--
For a non-NaN float, the embedded value is `Number 0` only for the two
zeros.
-/
theorem PackedFloat.isZero_of_toExtRat'_eq_zero {e s : Nat}
    (x : PackedFloat e s) (hx : ¬ x.isNaN)
    (h : x.toExtRat' = ExtRat.Number 0) : x.isZero := by
  by_cases hxinf : x.isInfinite
  · rw [PackedFloat.toExtRat'_eq_Infinity_of_isInfinite x hxinf] at h
    grind
  · by_cases hxz : x.isZero
    · exact hxz
    · have hnum : x.isNormOrNonzeroSubnorm := by
        grind [PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero]
      rw [PackedFloat.toExtRat'_eq_toRat_of hnum] at h
      have := PackedFloat.toRat_ne_zero hnum
      grind

/--
The PackedFloat order reflects the semantic (ExtRat) order: if the embedded
value of `x` is `≤` the embedded value of a non-NaN `y`, then `x ≤ y` —
provided not both are zeros (the order distinguishes `-0 < +0`, the
embedding does not).  (The converse of `toExtRat'_le_toExtRat'_of_le`.)
-/
theorem PackedFloat.le_of_toExtRat'_le_toExtRat' {e s : Nat}
    (he : 0 < e) (hs : 0 < s) (x y : PackedFloat e s)
    (hy : ¬ y.isNaN)
    (hnz : ¬ x.isZero ∨ ¬ y.isZero)
    (h : x.toExtRat' ≤ y.toExtRat') : x ≤ y := by
  have hx : ¬ x.isNaN := by
    intro hx
    rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN x hx] at h
    rw [ExtRat.ExtRat.NaN_le_iff] at h
    simp only [decide_eq_true_eq] at h
    exact hy (by grind [PackedFloat.toExtRat'_eq_NaN_iff_isNaN])
  by_cases hxz : x.isZero
  · -- `x = ±0` and `y` is nonzero with `0 ≤ y`, hence `y` is positive.
    have hyz : ¬ y.isZero := by grind
    rw [PackedFloat.toExtRat'_eq_zero_of_isZero x hxz] at h
    have hysign : y.sign = false := by
      by_cases hsign : y.sign
      · exfalso
        have hlt : y.toExtRat' < 0 :=
          (PackedFloat.toExtRat'_lt_zero_eq_decide y hy).mpr (by grind)
        grind [ExtRat.lt_eq_le_and_not_eq, ExtRat.ExtRat.eq_of_le_of_le, ExtRat.ExtRat.zero_def]
      · grind
    exact PackedFloat.le_of_lt
      (PackedFloat.isZero_lt_of_nonneg_of_not_isZero he hs x y hxz hysign hy hyz)
  · by_cases hyz : y.isZero
    · -- `y = ±0` and `x` is nonzero with `x ≤ 0`, hence `x` is negative.
      rw [PackedFloat.toExtRat'_eq_zero_of_isZero y hyz] at h
      have hxsign : x.sign = true := by
        by_cases hsign : x.sign
        · grind
        · exfalso
          have hnlt : ¬ (x.toExtRat' < 0) := by
            rw [PackedFloat.toExtRat'_lt_zero_eq_decide x hx]
            grind
          have heq : x.toExtRat' = ExtRat.Number 0 := by
            grind [ExtRat.lt_eq_le_and_not_eq, ExtRat.ExtRat.zero_def]
          exact hxz (PackedFloat.isZero_of_toExtRat'_eq_zero x hx heq)
      by_cases hysign : y.sign
      · rw [PackedFloat.le_of_ex_le_ex_or_sig_le_sig_of_neg_of_neg x y hxsign hysign hx hy]
        have hyfields := (PackedFloat.isZero_iff_ex_eq_zero_and_sig_eq_zero he).mp hyz
        grind
      · exact PackedFloat.le_of_nonneg_of_neg x y hxsign (by grind) hx hy
    · -- Both nonzero: totality plus strict monotonicity.
      rcases PackedFloat.le_total_of_not_isNaN x y hx hy with hle | hle
      · exact hle
      · by_cases heq : y = x
        · grind
        · exfalso
          have hlt : y < x := PackedFloat.lt_of_le_of_ne y x hle heq
          have := PackedFloat.toExtRat'_lt_toExtRat'_of_lt he hs y x hyz hxz hy hx hlt
          grind [ExtRat.lt_eq_le_and_not_eq, ExtRat.ExtRat.eq_of_le_of_le]

/-- `smtLibLower` of (the value of) a normal or nonzero-subnormal float is
the float itself. -/
theorem smtLibLower_number_toRat_eq_self {e s : Nat}
    (he : 0 < e) (hs : 0 < s)
    (b : PackedFloat e s) (hb : b.isNormOrNonzeroSubnorm) :
    (SmtLibSemantics.smtLibLower (X := PackedFloat e s) (R := ExtRat)).lower
      (ExtRat.Number b.toRat) = b := by
  have hbnan : ¬ b.isNaN := by grind
  have hbval : b.toExtRat' = ExtRat.Number b.toRat := b.toExtRat'_eq_toRat_of hb
  have hlaw : SmtLibSemantics.IsLawfulLower (ExtRat.Number b.toRat) b := by
    constructor
    · simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', hbval]
      exact ExtRat.ExtRat.le_refl
    · intro lower' hlower'
      simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat'] at hlower'
      apply PackedFloat.le_of_toExtRat'_le_toExtRat' he hs _ _ hbnan (Or.inr (by grind))
      rw [hbval]
      exact hlower'
  have huniq : ∀ pf : PackedFloat e s,
      SmtLibSemantics.IsLawfulLower (ExtRat.Number b.toRat) pf → pf = b := by
    intro pf hpf
    obtain ⟨h1, h2⟩ := hpf
    simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat'] at h1 h2
    have hb_le_pf : b ≤ pf := h2 b (by rw [hbval]; exact ExtRat.ExtRat.le_refl)
    have hpf_le_b : pf ≤ b := by
      apply PackedFloat.le_of_toExtRat'_le_toExtRat' he hs _ _ hbnan (Or.inr (by grind))
      rw [hbval]
      exact h1
    exact PackedFloat.eq_of_le_of_le_of_not_isNaN pf b
      (by intro hnan; rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN pf hnan, ExtRat.ExtRat.NaN_le_iff] at h1; grind)
      hpf_le_b hb_le_pf
  show Classical.epsilon (fun x => SmtLibSemantics.IsLawfulLower (ExtRat.Number b.toRat) x) = b
  exact Classical.epsilon_elim b hlaw huniq

/-- `smtLibUpper` of (the value of) a normal or nonzero-subnormal float is
the float itself. -/
theorem smtLibUpper_number_toRat_eq_self {e s : Nat}
    (he : 0 < e) (hs : 0 < s)
    (b : PackedFloat e s) (hb : b.isNormOrNonzeroSubnorm) :
    (SmtLibSemantics.smtLibUpper (X := PackedFloat e s) (R := ExtRat)).upper
      (ExtRat.Number b.toRat) = b := by
  have hbnan : ¬ b.isNaN := by grind
  have hbval : b.toExtRat' = ExtRat.Number b.toRat := b.toExtRat'_eq_toRat_of hb
  have hlaw : SmtLibSemantics.IsLawfulUpper (ExtRat.Number b.toRat) b := by
    constructor
    · simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat', hbval]
      exact ExtRat.ExtRat.le_refl
    · intro upper' hupper'
      simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat'] at hupper'
      have hnan' : ¬ upper'.isNaN := by
        intro hnan
        rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN upper' hnan, ExtRat.ExtRat.le_NaN_iff] at hupper'
        grind
      apply PackedFloat.le_of_toExtRat'_le_toExtRat' he hs _ _ hnan' (Or.inl (by grind))
      rw [hbval]
      exact hupper'
  have huniq : ∀ pf : PackedFloat e s,
      SmtLibSemantics.IsLawfulUpper (ExtRat.Number b.toRat) pf → pf = b := by
    intro pf hpf
    obtain ⟨h1, h2⟩ := hpf
    simp only [SmtLibSemantics.smtLibV_embed_eq, PackedFloat.toExtRat_eq_toExtRat'] at h1 h2
    have hpfnan : ¬ pf.isNaN := by
      intro hnan
      rw [PackedFloat.toExtRat'_eq_NaN_of_isNaN pf hnan, ExtRat.ExtRat.le_NaN_iff] at h1
      grind
    have hb_le_pf : b ≤ pf := by
      apply PackedFloat.le_of_toExtRat'_le_toExtRat' he hs _ _ hpfnan (Or.inl (by grind))
      rw [hbval]
      exact h1
    have hpf_le_b : pf ≤ b := h2 b (by rw [hbval]; exact ExtRat.ExtRat.le_refl)
    exact PackedFloat.eq_of_le_of_le_of_not_isNaN pf b hpfnan hpf_le_b hb_le_pf
  show Classical.epsilon (fun x => SmtLibSemantics.IsLawfulUpper (ExtRat.Number b.toRat) x) = b
  exact Classical.epsilon_elim b hlaw huniq

/--
For (the value of) a representable float, the SMT-LIB `lowerHalf` predicate
holds vacuously: the lower approximants at significand widths `s` and `s + 1`
are both the value itself, so their embeddings agree.  (Similarly `tieBreak`
is vacuously true; `roundRNE` therefore consults the tie-break branches
*before* `lowerHalf`, and both produce the value itself since
`lower = upper`.)
-/
theorem lowerHalf_number_toRat {e s : Nat} (he : 0 < e) (hs : 0 < s)
    (b : PackedFloat e s) (hb : b.isNormOrNonzeroSubnorm) :
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lowerHalf
      (ExtRat.Number b.toRat) := by
  rw [SmtLibSemantics.smtLibRoundMethod.lowerHalf_eq]
  obtain ⟨b', hb', hval⟩ := PackedFloat.exists_widen he hs b hb
  simp only [SmtLibSemantics.smtLibV_lower_eq, SmtLibSemantics.smtLibV_embed_eq]
  rw [smtLibLower_number_toRat_eq_self he hs b hb]
  rw [show (ExtRat.Number b.toRat) = (ExtRat.Number b'.toRat) by rw [hval]]
  rw [smtLibLower_number_toRat_eq_self he (by omega) b' hb']
  simp only [SmtLibSemantics.instExtendedRat.smtLibEq, PackedFloat.toExtRat_eq_toExtRat']
  rw [b.toExtRat'_eq_toRat_of hb, b'.toExtRat'_eq_toRat_of hb', hval]

/--
**Rounding is the identity on representable values**: rounding the exact
rational value of a normal or nonzero-subnormal float returns the float, in
every rounding mode.  (For representable values `lower = upper`, so every
branch of every rounding mode produces the same float; note that for such
values the SMT-LIB `lowerHalf` and `tieBreak` predicates are vacuously true,
which is why `roundRNE` consults `lowerHalf` *after* the tie-break branches.)
-/
theorem round_number_toRat_eq_self {e s : Nat}
    (he : 0 < e) (hs : 0 < s)
    (rm : RoundingMode) (sign : Bool)
    (b : PackedFloat e s) (hb : b.isNormOrNonzeroSubnorm) :
    (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).round
      rm sign (ExtRat.Number b.toRat) = b := by
  have hb0 : b.toRat ≠ 0 := PackedFloat.toRat_ne_zero hb
  have hlow : (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).lower (ExtRat.Number b.toRat) = b := by
    simp only [SmtLibSemantics.smtLibRoundMethod.lower_eq, SmtLibSemantics.smtLibV_lower_eq]
    exact smtLibLower_number_toRat_eq_self he hs b hb
  have hupp : (SmtLibSemantics.smtLibRoundMethod e s SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).upper (ExtRat.Number b.toRat) = b := by
    simp only [SmtLibSemantics.smtLibRoundMethod.upper_eq, SmtLibSemantics.smtLibV_upper_eq]
    exact smtLibUpper_number_toRat_eq_self he hs b hb
  have hlh := lowerHalf_number_toRat he hs b hb
  rcases rm
  case RNE =>
    simp only [SmtLibSemantics.RoundMethod.round_RNE_eq, SmtLibSemantics.RoundMethod.roundRNE]
    simp [hb0, hlow, hupp, hlh]
  case RNA =>
    simp only [SmtLibSemantics.RoundMethod.round_RNA_eq, SmtLibSemantics.RoundMethod.roundRNA]
    simp [hb0, hlow, hupp]
    grind
  case RTP =>
    simp only [SmtLibSemantics.RoundMethod.round_RTP_eq, SmtLibSemantics.RoundMethod.roundRTP]
    simp [hb0, hupp]
  case RTN =>
    simp only [SmtLibSemantics.RoundMethod.round_RTN_eq, SmtLibSemantics.RoundMethod.roundRTN]
    simp [hb0, hlow]
  case RTZ =>
    simp only [SmtLibSemantics.RoundMethod.round_RTZ_eq, SmtLibSemantics.RoundMethod.roundRTZ]
    simp [hb0, hlow, hupp]
    grind

/-! ## Layer 1 helpers -/

/--
Two structurally-distinguishable significands (one normalized, one zero)
are never `structBeq`.  Used to discharge the exact-cancellation branch when
one operand is zero and the other is a normalized number.
-/
theorem UnpackedFloat.structBeq_eq_false_of_msb_ne {e s : Nat} (x y : UnpackedFloat e s)
    (h : x.sig.msb ≠ y.sig.msb) : x.structBeq y = false := by
  grind [UnpackedFloat.structBeq]

/-- Negation does not change the significand. -/
@[simp]
theorem UnpackedFloat.sig_neg {e s : Nat} (x : UnpackedFloat e s) :
    x.neg.sig = x.sig := rfl

/-- Negation flips the sign. -/
@[simp]
theorem UnpackedFloat.sign_neg' {e s : Nat} (x : UnpackedFloat e s) :
    x.neg.sign = !x.sign := rfl

/-- The numeric payload of an extended zero is the unpacked zero. -/
@[simp]
theorem EUnpackedFloat.num_mkZero {e s : Nat} (sign : Bool) :
    (EUnpackedFloat.mkZero sign : EUnpackedFloat e s).num = UnpackedFloat.mkZero sign := rfl

/-- `structBeq` detects exactly the opposite-sign zero pairs. -/
theorem UnpackedFloat.structBeq_mkZero_neg_mkZero {e s : Nat} (sa sb : Bool) :
    (UnpackedFloat.mkZero (e := e) (s := s) sa).structBeq (UnpackedFloat.mkZero sb).neg =
      (sa == !sb) := by
  simp [UnpackedFloat.structBeq, UnpackedFloat.mkZero, UnpackedFloat.neg]

/--
The unpacked sum of two unpacked (norm/nonzero-subnorm) packed floats is a
sticky compression of the exact rational sum.
-/
theorem UnpackedFloat.unpackNum_add_unpackNum_stickyEquiv
    {e s : Nat} {a b : PackedFloat e s} (hs : 0 < s)
    (ha : a.isNormOrNonzeroSubnorm) (hb : b.isNormOrNonzeroSubnorm)
    (hne : a.toRat + b.toRat ≠ 0) :
    StickyEquiv ((a.unpackNum.add b.unpackNum).toExpInt)
      ((a.unpackNum.add b.unpackNum).toRat) (a.toRat + b.toRat) := by
  have hra := PackedFloat.unpackNum_toRat_eq_toRat (pf := a) ha
  have hrb := PackedFloat.unpackNum_toRat_eq_toRat (pf := b) hb
  rw [← hra, ← hrb] at hne ⊢
  exact UnpackedFloat.stickyEquiv_add a.unpackNum b.unpackNum (by omega)
    (PackedFloat.msb_unpackNum_eq_true ha) (PackedFloat.msb_unpackNum_eq_true hb) hne

/-! ## Layer 1: the big theorem

The statement mirrors `Fp.mul_eq_mul`: the SMT-LIB addition (exact rational
addition followed by SMT-LIB rounding) agrees with the bit-blasted
`PackedFloat.add` up to the NaN bit pattern, for RNE.
-/

set_option maxHeartbeats 1000000 in
theorem add_eq_add {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 2 < ein)
    (rm : RoundingMode) (hrm : rm = .RNE) (a b : PackedFloat ein sin) :
    (Fp.SmtLibSemantics.SmtLibFunctions.add (Fp.SmtLibSemanticsQ.smtLibRoundMethodQ ein sin) rm a b).EquivUptoNaN
      (PackedFloat.add rm a b) := by
  have he0 : 0 < ein := by grind
  simp only [SmtLibSemantics.SmtLibFunctions.add, SmtLibSemantics.smtLibV_embed_eq,
    PackedFloat.toExtRat_eq_toExtRat', roundQ_eq]
  rw [PackedFloat.add, EUnpackedFloat.add]
  cases a using PackedFloat.kindCasesNaNInfZeroNum
  case nanCase hnan =>
    simp only [hnan, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
      EUnpackedFloat.isNaN_mkNaN, Bool.true_or, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
      PackedFloat.EquivUptoNaN.of_mkNaN_iff]
    rw [ExtRat.ExtRat.NaN_add]
    exact isNaN_round_of_nan
  case infCase signa =>
    simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
      PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
      PackedFloat.unpack_getInfinity, ↓reduceIte]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
        EUnpackedFloat.isNaN_mkNaN, EUnpackedFloat.isNaN_mkInfinity, Bool.true_or, Bool.or_true,
        cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [ExtRat.ExtRat.add_NaN]
      exact isNaN_round_of_nan
    case infCase signb =>
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
        PackedFloat.unpack_getInfinity, ↓reduceIte, EUnpackedFloat.isNaN_mkInfinity,
        EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.sign_mkInfinity, Bool.false_or,
        Bool.true_and]
      by_cases hsign : signa = signb
      · subst hsign
        have hval : ExtRat.Infinity signa + ExtRat.Infinity signa = ExtRat.Infinity signa := by
          rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp
        rw [hval]
        simp only [bne_self_eq_false, Bool.and_false, cond_false, beq_self_eq_true,
          Bool.and_true, Bool.true_or, cond_true, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
        apply PackedFloat.EquivUptoNaN.of_eq
        simp [roundQ_eq_round_of_Infinity he0 hsin]
      · have hval : ExtRat.Infinity signa + ExtRat.Infinity signb = ExtRat.NaN := by
          rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp; grind
        rw [hval]
        have hbne : (signa != signb) = true := by grind
        have hbeq : (signa == signb) = false := by grind
        simp only [hbne, hbeq, Bool.and_true, Bool.and_false, Bool.false_or, cond_true,
          EUnpackedFloat.mkNaN_pack_eq_mkNaN, PackedFloat.EquivUptoNaN.of_mkNaN_iff]
        exact isNaN_round_of_nan
    case zeroCase signb =>
      simp only [PackedFloat.isZero_getZero, he, decide_true,
        PackedFloat.toExtRat'_eq_zero_of_isZero, PackedFloat.unpack_getZero, he0, ↓reduceIte,
        PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.isInfinite_mkZero, Bool.false_or,
        Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true,
        Bool.or_false, Bool.true_or, cond_true, cond_false,
        EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      have hval : ExtRat.Infinity signa + ExtRat.Number 0 = ExtRat.Infinity signa := by
        rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp
      rw [hval]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp [roundQ_eq_round_of_Infinity he0 hsin]
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        b.toExtRat'_eq_toRat_of hb]
      simp only [EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isNaN_mkNumber,
        EUnpackedFloat.isInfinite_mkInfinity, EUnpackedFloat.isInfinite_mkNumber, Bool.false_or,
        Bool.or_false, Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_false,
        Bool.and_true, Bool.true_or, cond_true, cond_false,
        EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      have hval : ExtRat.Infinity signa + ExtRat.Number b.toRat = ExtRat.Infinity signa := by
        rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp
      rw [hval]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp [roundQ_eq_round_of_Infinity he0 hsin]
  case zeroCase signa =>
    simp only [PackedFloat.isZero_getZero, he, decide_true,
      PackedFloat.toExtRat'_eq_zero_of_isZero, PackedFloat.unpack_getZero, he0, ↓reduceIte,
      PackedFloat.sign_getZero]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
        EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNaN, Bool.or_true, Bool.false_or,
        Bool.true_or, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
        PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [ExtRat.ExtRat.add_NaN]
      exact isNaN_round_of_nan
    case infCase signb =>
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
        PackedFloat.unpack_getInfinity, ↓reduceIte, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkZero,
        EUnpackedFloat.isInfinite_mkInfinity, Bool.false_or, Bool.or_false, Bool.false_and,
        Bool.and_true, Bool.not_false, Bool.true_and, Bool.and_false, Bool.true_or, Bool.or_true,
        cond_true, cond_false, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      have hval : ExtRat.Number 0 + ExtRat.Infinity signb = ExtRat.Infinity signb := by
        rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp
      rw [hval]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp [roundQ_eq_round_of_Infinity he0 hsin]
    case zeroCase signb =>
      simp only [PackedFloat.isZero_getZero, he, decide_true,
        PackedFloat.toExtRat'_eq_zero_of_isZero, PackedFloat.unpack_getZero, he0, ↓reduceIte,
        PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isInfinite_mkZero,
        Bool.false_or, Bool.or_self, Bool.false_and, Bool.and_false, cond_false,
        EUnpackedFloat.mkZero_num_sign]
      rw [ExtRat.ExtRat.add_Number]
      rw [show (0 : Rat) + 0 = 0 by grind]
      rw [round_eq_mkZero_of_mkZero he0]
      simp only [EUnpackedFloat.num_mkZero]
      rw [UnpackedFloat.structBeq_mkZero_neg_mkZero]
      subst hrm
      by_cases hsign : signa = !signb
      · simp only [hsign, beq_self_eq_true, cond_true, EUnpackedFloat.mkZero_pack_eq_getZero]
        apply PackedFloat.EquivUptoNaN.of_eq
        simp [SmtLibSemantics.SmtLibFunctions.addSign]
        grind
      · have : (signa == !signb) = false := by grind
        simp only [this, cond_false, EUnpackedFloat.isZero_mkZero, cond_true,
          EUnpackedFloat.mkZero_pack_eq_getZero]
        apply PackedFloat.EquivUptoNaN.of_eq
        simp [SmtLibSemantics.SmtLibFunctions.addSign]
        grind
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        b.toExtRat'_eq_toRat_of hb]
      simp only [EUnpackedFloat.isNaN_mkZero, EUnpackedFloat.isNaN_mkNumber,
        EUnpackedFloat.isInfinite_mkZero, EUnpackedFloat.isInfinite_mkNumber, Bool.or_self,
        Bool.false_and, Bool.and_false, Bool.false_or, cond_false, EUnpackedFloat.mkZero_num_sign,
        EUnpackedFloat.num_mkNumber, EUnpackedFloat.isZero_mkZero, cond_true]
      rw [ExtRat.ExtRat.add_Number]
      rw [show (0 : Rat) + b.toRat = b.toRat by grind]
      simp only [EUnpackedFloat.num_mkZero]
      rw [UnpackedFloat.structBeq_eq_false_of_msb_ne _ _
        (by simp [PackedFloat.msb_unpackNum_eq_true hb, UnpackedFloat.mkZero])]
      simp only [cond_false]
      rw [round_number_toRat_eq_self he0 hsin rm _ b hb]
      rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
      refine EUnpackedFloat.pack'_EquivUptoNaN_of_Rel he hsin _ _ ?_
        (by intro _; exact PackedFloat.unpackNum_packable he hsin b hb)
        (by intro _; exact ⟨by grind, by grind⟩)
      apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number _ _ (by simp [EUnpackedFloat.mkNumber])
      apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
      · rw [EUnpackedFloat.num_mkNumber]
        have h := PackedFloat.unpackNum_toRat_eq_toRat hb
        rw [UnpackedFloat.toRat_eq_toRat'] at h
        exact h
      · simp
  case numCase ha =>
    rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha,
      a.toExtRat'_eq_toRat_of ha]
    cases b using PackedFloat.kindCasesNaNInfZeroNum
    case nanCase hb =>
      simp only [hb, PackedFloat.toExtRat'_eq_NaN_of_isNaN, PackedFloat.unpack_eq_NaN_of_isNaN,
        EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isNaN_mkNaN, Bool.or_true, Bool.false_or,
        Bool.true_or, cond_true, EUnpackedFloat.mkNaN_pack_eq_mkNaN,
        PackedFloat.EquivUptoNaN.of_mkNaN_iff]
      rw [ExtRat.ExtRat.add_NaN]
      exact isNaN_round_of_nan
    case infCase signb =>
      simp only [hsin, PackedFloat.isInfinite_getInfinity, decide_true,
        PackedFloat.toExtRat'_eq_Infinity_of_isInfinite, PackedFloat.sign_getInfinity,
        PackedFloat.unpack_getInfinity, ↓reduceIte, EUnpackedFloat.isNaN_mkNumber,
        EUnpackedFloat.isNaN_mkInfinity, EUnpackedFloat.isInfinite_mkNumber,
        EUnpackedFloat.isInfinite_mkInfinity, Bool.false_or, Bool.or_false, Bool.false_and,
        Bool.and_true, Bool.not_false, Bool.true_and, Bool.and_false, Bool.true_or, Bool.or_true,
        cond_true, cond_false, EUnpackedFloat.mkInfinity_pack_eq_getInfinity]
      have hval : ExtRat.Number a.toRat + ExtRat.Infinity signb = ExtRat.Infinity signb := by
        rw [← ExtRat.ExtRat.add_def]; unfold ExtRat.add; simp
      rw [hval]
      apply PackedFloat.EquivUptoNaN.of_eq
      simp [roundQ_eq_round_of_Infinity he0 hsin]
    case zeroCase signb =>
      simp only [PackedFloat.isZero_getZero, he, decide_true,
        PackedFloat.toExtRat'_eq_zero_of_isZero, PackedFloat.unpack_getZero, he0, ↓reduceIte,
        PackedFloat.sign_getZero, EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isNaN_mkZero,
        EUnpackedFloat.isInfinite_mkNumber, EUnpackedFloat.isInfinite_mkZero, Bool.or_self,
        Bool.false_and, Bool.and_false, Bool.false_or, cond_false, EUnpackedFloat.num_mkNumber,
        EUnpackedFloat.mkZero_num_sign, EUnpackedFloat.isZero_mkNumber, EUnpackedFloat.isZero_mkZero,
        cond_true]
      rw [ExtRat.ExtRat.add_Number]
      rw [show a.toRat + 0 = a.toRat by grind]
      simp only [EUnpackedFloat.num_mkZero]
      rw [UnpackedFloat.structBeq_eq_false_of_msb_ne _ _
        (by simp [PackedFloat.msb_unpackNum_eq_true ha, UnpackedFloat.mkZero])]
      simp only [cond_false]
      have hazero : a.unpackNum.isZero = false :=
        PackedFloat.isZero_unpackNum_eq_false a (by grind)
      simp only [hazero, Bool.false_eq_true, cond_false]
      rw [round_number_toRat_eq_self he0 hsin rm _ a ha]
      rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
      refine EUnpackedFloat.pack'_EquivUptoNaN_of_Rel he hsin _ _ ?_
        (by intro _; exact PackedFloat.unpackNum_packable he hsin a ha)
        (by intro _; exact ⟨by grind, by grind⟩)
      apply EUnpackedFloat.Rel_of_Rel_of_state_eq_Number _ _ (by simp [EUnpackedFloat.mkNumber])
      apply UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign
      · rw [EUnpackedFloat.num_mkNumber]
        have h := PackedFloat.unpackNum_toRat_eq_toRat ha
        rw [UnpackedFloat.toRat_eq_toRat'] at h
        exact h
      · simp
    case numCase hb =>
      rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm hb,
        b.toExtRat'_eq_toRat_of hb]
      simp only [EUnpackedFloat.isNaN_mkNumber, EUnpackedFloat.isInfinite_mkNumber,
        Bool.or_self, Bool.false_and, Bool.and_false, Bool.false_or, cond_false,
        EUnpackedFloat.num_mkNumber]
      rw [ExtRat.ExtRat.add_Number]
      have hamsb := PackedFloat.msb_unpackNum_eq_true ha
      have hbmsb := PackedFloat.msb_unpackNum_eq_true hb
      by_cases hcancel : a.unpackNum.structBeq b.unpackNum.neg
      · -- Exact cancellation: the sum is exactly zero, both sides give a zero.
        have hsum0 : a.toRat + b.toRat = 0 := by
          have h := UnpackedFloat.toRat_add_toRat_eq_zero_of_structBeq_neg _ _ hcancel
          rwa [PackedFloat.unpackNum_toRat_eq_toRat ha,
            PackedFloat.unpackNum_toRat_eq_toRat hb] at h
        have hsigns : a.sign = !b.sign := by
          have hsign := hcancel
          simp only [UnpackedFloat.structBeq, Bool.and_eq_true, beq_iff_eq] at hsign
          have h1 := PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign a
          have h2 := PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign b
          grind
        rw [hsum0, round_eq_mkZero_of_mkZero he0]
        simp only [hcancel, cond_true, EUnpackedFloat.mkZero_pack_eq_getZero]
        apply PackedFloat.EquivUptoNaN.of_eq
        subst hrm
        simp [SmtLibSemantics.SmtLibFunctions.addSign, hsigns]
        rfl
      · -- The interesting case: a genuine nonzero sum, rounded by the circuit.
        have hsumne : a.toRat + b.toRat ≠ 0 := by
          have h := UnpackedFloat.toRat_add_toRat_ne_zero_of_not_structBeq_neg
            a.unpackNum b.unpackNum hamsb hbmsb (by grind)
          rwa [PackedFloat.unpackNum_toRat_eq_toRat ha,
            PackedFloat.unpackNum_toRat_eq_toRat hb] at h
        have hsumne' : a.unpackNum.toRat + b.unpackNum.toRat ≠ 0 := by
          rwa [PackedFloat.unpackNum_toRat_eq_toRat ha,
            PackedFloat.unpackNum_toRat_eq_toRat hb]
        have hazero : a.unpackNum.isZero = false :=
          PackedFloat.isZero_unpackNum_eq_false a (by grind)
        have hbzero : b.unpackNum.isZero = false :=
          PackedFloat.isZero_unpackNum_eq_false b (by grind)
        simp only [hcancel, cond_false, EUnpackedFloat.isZero_mkNumber, hazero, hbzero]
        rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
        subst hrm
        -- Mirror of the `div_eq_div` call site: the bit-blasted rounder output is `Packable`
        -- (normalized + in-range) and the SMT spec result is finite, both discharged by the
        -- `blastSmtLibRound` analogues of the lemmas used at sites 1/2.
        have hxnorm : (a.unpackNum.add b.unpackNum).normalize = a.unpackNum.add b.unpackNum :=
          UnpackedFloat.normalize_eq_self_of_msb_eq_true _
            (UnpackedFloat.msb_add_eq_true _ _ (by omega) hamsb hbmsb hsumne')
        have hsticky : StickyEquiv ((a.unpackNum.add b.unpackNum).toExpInt)
            ((a.unpackNum.add b.unpackNum).toRat) (a.toRat + b.toRat) :=
          UnpackedFloat.unpackNum_add_unpackNum_stickyEquiv hsin ha hb hsumne
        refine EUnpackedFloat.pack'_EquivUptoNaN_of_Rel he hsin _ _ ?hrel ?hpack ?hpf
        case hrel =>
          exact UnpackedFloat.blastSmtLibRound_Rel_round_of_RNE_of_stickyEquiv he hep hsin
            (eu := exponentWidth ein sin + 1) (su := sin + 1 + 2) (by omega) (by omega)
            (a.unpackNum.add b.unpackNum) _ _ hsumne hxnorm hsticky
        case hpack =>
          exact UnpackedFloat.blastSmtLibRound_Packable_of_RNE hep hsin (by omega) (by omega)
            (a.unpackNum.add b.unpackNum) hxnorm
        case hpf =>
          exact UnpackedFloat.blastSmtLibRound_finite_of_RNE_of_stickyEquiv he hep hsin
            (by omega) (by omega) (a.unpackNum.add b.unpackNum) _ _ hsumne hxnorm hsticky

/--
info: 'Fp.add_eq_add' depends on axioms: [propext, sorryAx, BitVec.toNat_clz_cons, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms add_eq_add

end Fp
