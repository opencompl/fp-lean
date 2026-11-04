import Fp.Theorems.SqrtFixed
import Fp.Theorems.Multiplication
import Fp.UnpackedFloat.Lemmas.Conversion

/-!
# Value characterization of `UnpackedFloat.sqrt`

Builds on `fixedPointSqrt_bracket` (`SqrtFixed.lean`): the unpacked square root's significand
is `2m + sticky` where `m = ⌊√Xa⌋` on the aligned, doubled-width input `Xa` and the sticky bit
records exactness. The exponent is halved (`sshiftRight 1`) and the sign is `+`.

Everything is stated at the `Nat` (`toNat`) level to avoid `BitVec` width bookkeeping
(the circuit mixes widths `1+s+1` and `s+2`).
-/

namespace Fp

open UnpackedFloat

/-- `((0#1 ++ sig) ++ 0#1).toNat = 2 * sig.toNat`. -/
theorem toNat_alignedSig {s : Nat} (sig : BitVec s) :
    (((0#1 ++ sig) ++ 0#1 : BitVec (1 + s + 1))).toNat = 2 * sig.toNat := by
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_or,
    Nat.or_zero, Nat.shiftLeft_eq, Nat.pow_one]
  omega

/-- `toNat` of `fixedPointSqrt aligned` in terms of its integer-sqrt `w` and sticky bit. -/
theorem toNat_fixedPointSqrt {n : Nat} {aligned : BitVec (n + 1)} {w : BitVec n}
    (hfp : fixedPointSqrt aligned = w ++ BitVec.ofBool (decide (w.toNat ^ 2 ≠ aligned.toNat * 2 ^ (n - 1)))) :
    (fixedPointSqrt aligned).toNat
      = 2 * w.toNat + (if w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) then 0 else 1) := by
  rw [hfp, BitVec.toNat_append, BitVec.toNat_ofBool, Nat.shiftLeft_eq]
  have hb : (decide (w.toNat ^ 2 ≠ aligned.toNat * 2 ^ (n - 1))).toNat
      = (if w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) then 0 else 1) := by
    by_cases h : w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) <;> simp [h]
  rw [hb]
  have hlt : (if w.toNat ^ 2 = aligned.toNat * 2 ^ (n - 1) then (0:Nat) else 1) < 2 ^ 1 := by
    split <;> omega
  rw [Nat.mul_comm w.toNat (2 ^ 1), ← Nat.two_pow_add_eq_or_of_lt hlt w.toNat]

/-- Splitting off the low bit and re-appending it rebuilds the value:
`(v.extractMsb' 0 len ++ ofBool (v.getLsbD 0)).toNat = v.toNat` when `len + 1 = W`. -/
theorem reconstruct_toNat {W len : Nat} (v : BitVec W) (h : len + 1 = W) :
    ((v.extractMsb' 0 len) ++ BitVec.ofBool (v.getLsbD 0)).toNat = v.toNat := by
  rw [BitVec.toNat_append, BitVec.toNat_ofBool, BitVec.toNat_extractMsb'_zero v (by omega)]
  have hWlen : W - len = 1 := by omega
  rw [hWlen, Nat.shiftLeft_eq, Nat.pow_one]
  have hbit : (v.getLsbD 0).toNat = v.toNat % 2 := by
    have : v.getLsbD 0 = decide (v.toNat % 2 = 1) := by
      rw [BitVec.getLsbD, Nat.testBit_zero]
    rw [this]; by_cases h2 : v.toNat % 2 = 1 <;> simp [h2] <;> omega
  rw [hbit]
  have hdlt : v.toNat % 2 < 2 ^ 1 := by omega
  rw [Nat.mul_comm (v.toNat / 2) 2, ← Nat.two_pow_add_eq_or_of_lt hdlt (v.toNat / 2)]
  omega

/-- Arithmetic-shifting the exponent right by one halves it (floor); the dropped bit is the
exponent's parity: `2 · ⌊E/2⌋ = E - (E mod 2)`. -/
theorem two_mul_sshiftRight_toInt {w : Nat} (hw : 0 < w) (x : BitVec w) :
    2 * (x.sshiftRight 1).toInt = x.toInt - (if x.getLsbD 0 then 1 else 0) := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  have hn : (2 : Nat) ^ w = 2 * 2 ^ (w - 1) := by
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.pow_succ]; omega
  have htn : x.toInt % 2 = (x.toNat : Int) % 2 := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hb : x.toInt % 2 = ((x.toNat % 2 : Nat) : Int) := by rw [htn]; exact_mod_cast rfl
  have hpar : x.toInt % 2 = (if x.getLsbD 0 then 1 else 0) := by
    rw [BitVec.getLsbD, Nat.testBit_zero]
    have hm : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
    rcases hm with h | h <;> rw [hb, h] <;> simp
  have h21 : (2 : Int) ^ 1 = 2 := rfl
  omega

/-- Value/bracket characterization of `UnpackedFloat.sqrt` on a normalized input.  `m = ⌊√Xa⌋`
where `Xa` is the doubled-width aligned significand; the significand is `2m + sticky`. -/
theorem UnpackedFloat.sqrt_bracket {e s : Nat} (hs : 0 < s) (x : UnpackedFloat e s)
    (hmsb : x.sig.msb = true) :
    ∃ (m Xa : Nat),
      Xa = (if x.ex.getLsbD 0 = false then 2 else 4) * x.sig.toNat * 2 ^ s ∧
      m ^ 2 ≤ Xa ∧ Xa < (m + 1) ^ 2 ∧
      (UnpackedFloat.sqrt x).sign = false ∧
      (UnpackedFloat.sqrt x).ex = x.ex.sshiftRight 1 ∧
      (UnpackedFloat.sqrt x).sig.toNat = 2 * m + (if m ^ 2 = Xa then 0 else 1) ∧
      (UnpackedFloat.sqrt x).sig.msb = true := by
  have hsiglo : 2 ^ (s - 1) ≤ x.sig.toNat := by
    have h := hmsb; rw [BitVec.msb_eq_decide] at h; simpa using h
  have hsig : x.sig.toNat < 2 ^ s := x.sig.isLt
  -- Common analysis for a given aligned significand with a leading bit.
  have core : ∀ (aligned : BitVec (1 + s + 1)) (C : Nat), aligned.toNat = C → 2 ^ s ≤ C →
      ∃ (m : Nat), m ^ 2 ≤ C * 2 ^ s ∧ C * 2 ^ s < (m + 1) ^ 2 ∧
        (fixedPointSqrt aligned).toNat = 2 * m + (if m ^ 2 = C * 2 ^ s then 0 else 1) ∧
        2 ^ s ≤ m := by
    intro aligned C hC hlead
    obtain ⟨w, hfp, hle, hgt⟩ := fixedPointSqrt_bracket (n := 1 + s) (by omega) aligned
      (by rw [hC, show 1 + s - 1 = s from by omega]; exact hlead)
    have hxc : aligned.toNat * 2 ^ (1 + s - 1) = C * 2 ^ s := by
      rw [hC, show 1 + s - 1 = s from by omega]
    have hval := toNat_fixedPointSqrt hfp
    rw [hxc] at hval hle hgt
    refine ⟨w.toNat, hle, hgt, hval, ?_⟩
    have h3 : (2 ^ s) ^ 2 ≤ C * 2 ^ s := by
      rw [Nat.pow_two]; exact Nat.mul_le_mul_right _ hlead
    have h4 : (2 ^ s) ^ 2 < (w.toNat + 1) ^ 2 := Nat.lt_of_le_of_lt h3 hgt
    rcases Nat.lt_or_ge (2 ^ s) (w.toNat + 1) with hlt | hge
    · omega
    · exact absurd h4 (Nat.not_lt.mpr (Nat.pow_le_pow_left hge 2))
  have hpow : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  -- unfold the significand structure and split on exponent parity
  simp only [UnpackedFloat.sqrt]
  by_cases hpar : x.ex.getLsbD 0 = false
  · obtain ⟨m, hle, hgt, hval, hm⟩ := core ((0#1 ++ x.sig) ++ 0#1) (2 * x.sig.toNat)
      (toNat_alignedSig x.sig) (by omega)
    have hrec := reconstruct_toNat (W := 1 + s + 1) (len := s + 1)
      (fixedPointSqrt ((0#1 ++ x.sig) ++ 0#1)) (by omega)
    refine ⟨m, 2 * x.sig.toNat * 2 ^ s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hpar]
    · simpa [hpar] using hle
    · simpa [hpar] using hgt
    · simp [hpar]
    · simp [hpar]
    · simp only [hpar, beq_self_eq_true, if_true]
      rw [hrec]; simpa [hpar] using hval
    · simp only [hpar, beq_self_eq_true, if_true]
      rw [BitVec.msb_eq_decide, hrec]
      have hb : 2 ^ (s + 1) ≤ (fixedPointSqrt ((0#1 ++ x.sig) ++ 0#1)).toNat := by
        rw [hval, Nat.pow_succ]; omega
      simpa using hb
  · have hpar' : x.ex.getLsbD 0 = true := by
      cases h : x.ex.getLsbD 0 <;> simp_all
    have h2pow : (2 : Nat) ^ (1 + s + 1) = 4 * 2 ^ s := by
      rw [show 1 + s + 1 = s + 2 from by omega, Nat.pow_add]; omega
    have hAsl : (((0#1 ++ x.sig) ++ 0#1 : BitVec (1 + s + 1)) <<< 1).toNat = 4 * x.sig.toNat := by
      rw [BitVec.toNat_shiftLeft, toNat_alignedSig, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨m, hle, hgt, hval, hm⟩ := core (((0#1 ++ x.sig) ++ 0#1) <<< 1) (4 * x.sig.toNat)
      hAsl (by omega)
    have hrec := reconstruct_toNat (W := 1 + s + 1) (len := s + 1)
      (fixedPointSqrt (((0#1 ++ x.sig) ++ 0#1) <<< 1)) (by omega)
    refine ⟨m, 4 * x.sig.toNat * 2 ^ s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hpar']
    · simpa [hpar'] using hle
    · simpa [hpar'] using hgt
    · simp [hpar']
    · simp [hpar']
    · simp only [hpar', Bool.true_eq_false, if_false, beq_iff_eq]
      rw [hrec]; simpa [hpar'] using hval
    · simp only [hpar', Bool.true_eq_false, if_false, beq_iff_eq]
      rw [BitVec.msb_eq_decide, hrec]
      have hb : 2 ^ (s + 1) ≤ (fixedPointSqrt (((0#1 ++ x.sig) ++ 0#1) <<< 1)).toNat := by
        rw [hval, Nat.pow_succ]; omega
      simpa using hb

/-- The unpacked square root faithfully represents `√(x.toRat)` via rational squared brackets:
either it is exact (`q·q = x.toRat`), or `x.toRat` lies strictly between the squares of the two
adjacent grid points around `q`.  This is the `StickyEquiv`-to-`√x` condition expressed rationally
(without naming the irrational `√x`), the key input to the rounding bridge. -/
theorem UnpackedFloat.sqrt_toRat_sq_bracket {e s : Nat} (hs : 0 < s) (he : 0 < e)
    (x : UnpackedFloat e s) (hmsb : x.sig.msb = true) (hsign : x.sign = false) :
    (UnpackedFloat.sqrt x).toRat * (UnpackedFloat.sqrt x).toRat = x.toRat ∨
      (let d : Rat := 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1));
       ((UnpackedFloat.sqrt x).toRat - d) * ((UnpackedFloat.sqrt x).toRat - d) < x.toRat ∧
       x.toRat < ((UnpackedFloat.sqrt x).toRat + d) * ((UnpackedFloat.sqrt x).toRat + d)) := by
  obtain ⟨m, Xa, hXa, hle, hgt, hsgn, hex, hsig, hmsb2⟩ := sqrt_bracket hs x hmsb
  have hne2 : (2 : Rat) ≠ 0 := by decide
  have hkexp : (UnpackedFloat.sqrt x).toExpInt = (x.ex.sshiftRight 1).toInt - ((s : Int) + 1) := by
    rw [UnpackedFloat.toExpInt, hex]
    have : ((s + 2 - 1 : Nat) : Int) = (s : Int) + 1 := by push_cast; omega
    rw [this]; omega
  -- `q = ↑(2m+st)·R`, `R = 2^K`, `st = if m²=Xa then 0 else 1`
  have hsqrat : (UnpackedFloat.sqrt x).toRat
      = ((2 * m + (if m ^ 2 = Xa then 0 else 1) : Nat) : Rat)
        * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)) := by
    rw [UnpackedFloat.toRat_eq_sign_sig_exp, hsgn, hsig, hkexp]; simp [Bool.toSign]
  -- `x.toRat = ↑(4·Xa)·(R·R)`
  have hRpos : (0 : Rat) < 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)) :=
    Rat.two_pow_pos _
  have hpar := two_mul_sshiftRight_toInt he x.ex
  have hcs : ((2 ^ s : Nat) : Rat) = (2 : Rat) ^ (s : Int) := by
    rw [Rat.zpow_natCast]; push_cast; grind
  have hxe : x.toRat = (x.sig.toNat : Rat) * 2 ^ (x.ex.toInt - ((s - 1 : Nat) : Int)) := by
    rw [UnpackedFloat.toRat_eq_sign_sig_exp, hsign, UnpackedFloat.toExpInt,
      show -(((s - 1 : Nat) : Int) - x.ex.toInt) = x.ex.toInt - ((s - 1 : Nat) : Int) from by omega]
    simp [Bool.toSign]
  have hQ : x.toRat = ((4 * Xa : Nat) : Rat)
      * (2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
        * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))) := by
    rw [hxe]
    by_cases hpe : x.ex.getLsbD 0 = false
    · have hEp : 2 * (x.ex.sshiftRight 1).toInt = x.ex.toInt := by
        simp only [hpe] at hpar; simpa using hpar
      have ha : ((4 * Xa : Nat) : Rat) = 8 * (x.sig.toNat : Rat) * (2 : Rat) ^ (s : Int) := by
        rw [hXa]; simp only [hpe, if_true]; push_cast; rw [← hcs]; push_cast; grind
      have hpw : (8 : Rat) * (2 : Rat) ^ (s : Int)
          * (2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
            * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)))
          = 2 ^ (x.ex.toInt - ((s - 1 : Nat) : Int)) := by
        rw [show (8 : Rat) = 2 ^ (3 : Int) from by decide, ← Rat.zpow_add hne2,
          ← Rat.zpow_add hne2, ← Rat.zpow_add hne2]
        congr 1; omega
      rw [ha]; grind
    · have hpe' : x.ex.getLsbD 0 = true := by cases h : x.ex.getLsbD 0 <;> simp_all
      have hEp : 2 * (x.ex.sshiftRight 1).toInt = x.ex.toInt - 1 := by
        simp only [hpe'] at hpar; simpa using hpar
      have ha : ((4 * Xa : Nat) : Rat) = 16 * (x.sig.toNat : Rat) * (2 : Rat) ^ (s : Int) := by
        rw [hXa]; simp only [hpe, hpe', if_false, Bool.true_eq_false]; push_cast
        rw [← hcs]; push_cast; grind
      have hpw : (16 : Rat) * (2 : Rat) ^ (s : Int)
          * (2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
            * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)))
          = 2 ^ (x.ex.toInt - ((s - 1 : Nat) : Int)) := by
        rw [show (16 : Rat) = 2 ^ (4 : Int) from by decide, ← Rat.zpow_add hne2,
          ← Rat.zpow_add hne2, ← Rat.zpow_add hne2]
        congr 1; omega
      rw [ha]; grind
  -- assemble the sticky disjunction
  simp only
  have hRR : (2 : Rat) ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
      * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)) > 0 := Rat.mul_positive hRpos hRpos
  by_cases hmx : m ^ 2 = Xa
  · left
    rw [hsqrat, hQ]
    simp only [hmx, if_true]
    have h4 : (4 * Xa : Nat) = (2 * m + 0) * (2 * m + 0) := by
      have := Nat.pow_two m; grind
    rw [h4]; push_cast; grind
  · right
    have hst : (if m ^ 2 = Xa then (0 : Nat) else 1) = 1 := by simp [hmx]
    have hmlt : m ^ 2 < Xa := Nat.lt_of_le_of_ne hle hmx
    refine ⟨?_, ?_⟩
    · rw [hsqrat, hQ, hst]
      have hexp1 : ((2 * m + 1 : Nat) : Rat) * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
          - 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
          = ((2 * m : Nat) : Rat) * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)) := by
        push_cast; grind
      rw [hexp1]
      have hlt : ((2 * m : Nat) * (2 * m) : Nat) < (4 * Xa : Nat) := by
        have := Nat.pow_two m; grind
      have hltR : (((2 * m) * (2 * m) : Nat) : Rat) < ((4 * Xa : Nat) : Rat) := by exact_mod_cast hlt
      have hkey := (Rat.mul_lt_mul_cancel_right_of_lt hRR).mpr hltR
      have hcast : (((2 * m) * (2 * m) : Nat) : Rat) = ((2 * m : Nat) : Rat) * ((2 * m : Nat) : Rat) := by
        push_cast; grind
      grind
    · rw [hsqrat, hQ, hst]
      have hexp2 : ((2 * m + 1 : Nat) : Rat) * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
          + 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1))
          = ((2 * m + 2 : Nat) : Rat) * 2 ^ ((x.ex.sshiftRight 1).toInt - ((s : Int) + 1)) := by
        push_cast; grind
      rw [hexp2]
      have hgt2 : (4 * Xa : Nat) < ((2 * m + 2) * (2 * m + 2) : Nat) := by
        have := Nat.pow_two (m + 1); grind
      have hgtR : ((4 * Xa : Nat) : Rat) < (((2 * m + 2) * (2 * m + 2) : Nat) : Rat) := by
        exact_mod_cast hgt2
      have hkey := (Rat.mul_lt_mul_cancel_right_of_lt hRR).mpr hgtR
      have hcast : (((2 * m + 2) * (2 * m + 2) : Nat) : Rat)
          = ((2 * m + 2 : Nat) : Rat) * ((2 * m + 2 : Nat) : Rat) := by push_cast; grind
      grind

end Fp

namespace Fp

/-- Squaring is monotone on nonnegative rationals: `a ≤ b ↔ a*a ≤ b*b`.
The rational engine behind the sqrt rounding bridge (`c ≤ √X ↔ c*c ≤ X`, never naming `√X`). -/
theorem Rat.mul_self_le_iff_of_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * a ≤ b * b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hab : a ≤ b
    · exact hab
    · have hba : b < a := by grind
      have h1 : b * b ≤ b * a := by apply Rat.mul_le_mul_of_nonneg_left <;> grind
      have h2 : b * a < a * a := by apply Rat.mul_lt_mul_of_pos_right <;> grind
      grind
  · intro h
    have h1 : a * a ≤ b * a := by apply Rat.mul_le_mul_of_nonneg_right <;> grind
    have h2 : b * a ≤ b * b := by apply Rat.mul_le_mul_of_nonneg_left <;> grind
    grind

end Fp

namespace Fp

open SmtLibSemanticsQ

/--
Internal SMT-LIB-style specification of the square-root circuit.

Because `√(rational)` is irrational, there is no exact `ExtRat` value to feed to `round`; instead
the number case rounds the *rational* value `(UnpackedFloat.sqrt a.unpackNum).toRat` produced by the
digit-by-digit fixed-point square root.  Its faithfulness — that this rational squares to bracket the
input `a` — is the separate theorem `UnpackedFloat.sqrt_toRat_sq_bracket`.  Together they say the
packed result is the correct rounding of a value whose square brackets the input.

The special-value branches mirror the circuit exactly (`Fp.sqrt`, `Fp/Sqrt.lean`).
-/
noncomputable def sqrtSpec (rm : RoundingMode) (a : PackedFloat e s) : PackedFloat e s :=
  if a.isZero then a
  else if (a.sign && !a.isZero) || a.isNaN then PackedFloat.getNaN e s
  else if (a.isInfinite && !a.sign) then PackedFloat.getInfinity e s false
  else (smtLibRoundMethodQ e s).round rm false
        (ExtRat.Number ((UnpackedFloat.sqrt a.unpack.num).toRat))

/--
The square-root circuit `Fp.sqrt` matches its SMT-LIB-style specification `sqrtSpec` (up to NaN
payloads), for every rounding mode.  Mirrors `mul_eq_mul`/`div_eq_div`: special-value branches
agree definitionally and the number leaf is discharged by the shared mode-generic rounding bridge
(`toExtRat_round_Rel_smtLibRound`) plus `pack'_EquivUptoNaN_of_Rel`.
-/
theorem sqrt_eq_sqrt {ein sin : Nat} (hsin : 0 < sin) (he : 1 < ein) (hep : 1 < ein)
    (rm : RoundingMode) (a : PackedFloat ein sin) :
    (sqrtSpec rm a).EquivUptoNaN (_root_.sqrt a rm) := by
  rw [sqrtSpec, _root_.sqrt]
  by_cases h1 : a.isZero = true
  · simp only [if_pos h1]; exact PackedFloat.EquivUptoNaN.refl _
  · simp only [if_neg h1]
    by_cases h2 : ((a.sign && !a.isZero) || a.isNaN) = true
    · simp only [if_pos h2]; exact PackedFloat.EquivUptoNaN.refl _
    · simp only [if_neg h2]
      by_cases h3 : (a.isInfinite && !a.sign) = true
      · simp only [if_pos h3]; exact PackedFloat.EquivUptoNaN.refl _
      · simp only [if_neg h3]
        -- Number leaf: `a` is a positive normal / nonzero-subnormal float.
        rw [Bool.not_eq_true] at h1 h2 h3
        have ha : a.isNormOrNonzeroSubnorm :=
          PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero
            (by grind) (by grind) (by grind)
        rw [PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm ha,
          EUnpackedFloat.num_mkNumber, roundQ_eq]
        obtain ⟨m, Xa, -, -, -, hvsign, -, -, hvmsb⟩ :=
          UnpackedFloat.sqrt_bracket (by omega) a.unpackNum (PackedFloat.msb_unpackNum_eq_true ha)
        have hxnorm : (UnpackedFloat.sqrt a.unpackNum).normalize
            = UnpackedFloat.sqrt a.unpackNum :=
          UnpackedFloat.normalize_eq_self_of_msb_eq_true _ hvmsb
        rw [PackedFloat.EquivUptoNaN_symm, EUnpackedFloat.pack_eq_pack']
        refine EUnpackedFloat.pack'_EquivUptoNaN_of_Rel (by grind) (by grind) _ _ ?hrel ?hpack ?hpf
        case hrel =>
          apply UnpackedFloat.toExtRat_round_Rel_smtLibRound rm
          · exact he
          · exact hep
          · exact hsin
          · exact Nat.le_refl _
          · omega
          · exact hvsign.symm
          · rfl
          · exact hxnorm
        case hpack =>
          exact UnpackedFloat.blastSmtLibRound_Packable rm hep hsin
            (Nat.le_refl _) (by omega) _ hxnorm
        case hpf =>
          apply UnpackedFloat.blastSmtLibRound_finite rm
          · exact he
          · exact hep
          · exact hsin
          · exact Nat.le_refl _
          · omega
          · exact hvsign.symm
          · rfl
          · exact hxnorm
          · exact hvmsb

/--
info: 'Fp.sqrt_eq_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sqrt_eq_sqrt

end Fp
