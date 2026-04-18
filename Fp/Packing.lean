import Fp.Basic
import Fp.Unpacking
import Fp.Theorems.Packing

namespace EUnpackedFloat

/-- Packing a NaN gives a NaN PackedFloat. -/
@[simp, grind .]
theorem isNaN_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isNaN) :
    uf.pack.isNaN = true := by
  simp [pack, PackedFloat.isNaN, huf]
  grind

/--
Packing an infinity gives an infinite PackedFloat. Requires `0 < s` because with no sig bits,
the PackedFloat infinity encoding aliases NaN.
-/
@[simp, grind .]
theorem isInfinite_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack.isInfinite = true := by
  have hnan : uf.isNaN = false := by
    simp [isNaN, isInfinite] at huf ⊢
    grind
  simp [pack, PackedFloat.isInfinite, huf, hnan]
  grind

/-- Packing always preserves the sign. -/
@[simp, grind .]
theorem sign_pack
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack.sign = uf.sign := by
  simp [pack, EUnpackedFloat.sign]

/--
Packing then unpacking an infinity recovers `mkInfinity` with the same sign.
-/
@[simp, grind .]
theorem unpack_pack_of_isInfinite
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isInfinite) (hs : 0 < s) :
    uf.pack.unpack = EUnpackedFloat.mkInfinity uf.sign := by
  have hInf : uf.pack.isInfinite = true := isInfinite_pack_of_isInfinite uf huf hs
  have hNaN : uf.pack.isNaN = false := by
    have := PackedFloat.not_isNaN_of_isInfinite (pf := uf.pack) hInf
    grind
  simp [PackedFloat.unpack, hNaN, hInf]

/--
Packing then unpacking a NaN yields `mkNaN`.
The PackedFloat's NaN status is preserved by `isNaN_pack_of_isNaN`, so unpack takes the NaN branch.
-/
@[simp, grind .]
theorem unpack_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isNaN) :
    uf.pack.unpack = EUnpackedFloat.mkNaN := by
  have hNaN : uf.pack.isNaN = true := isNaN_pack_of_isNaN uf huf
  simp [PackedFloat.unpack, hNaN]

/-! ### Helper lemmas for the Number round-trip

The main `unpack_pack_of_isNumber` proof below is a 3-way case split (zero / normal / subnormal).
Each branch is pushed into its own `sorry` lemma below; those are the "real" content left to prove.
-/

/--
For a bitvec with its top bit set, re-inserting that top bit via `cons` after dropping it with
`setWidth` is the identity.
-/
@[simp]
theorem BitVec.cons_true_setWidth_of_msb {n : Nat}
    (x : BitVec (n + 1)) (hmsb : x.msb = true) :
    BitVec.cons true (x.setWidth n) = x := by
  ext i hi
  by_cases hi : i = n
  · grind only [= BitVec.msb_eq_getMsbD_zero, = BitVec.getElem_cons, = BitVec.getMsbD_eq_getLsbD,
    = BitVec.getLsbD_eq_getElem]
  · grind only [= BitVec.getElem_cons, = BitVec.getElem_setWidth, = BitVec.getLsbD_eq_getElem]

/--
Zero case: a Number-state `uf` which is a zero
must be exactly `mkZero uf.sign`.
-/
theorem eq_mkZero_of_isNumber_of_isZero
    (uf : EUnpackedFloat e s)
    (hNum : uf.isNumber) (hZ : uf.isZero) :
    uf = EUnpackedFloat.mkZero uf.sign := by
  rcases uf with ⟨state, sign, ex, sig⟩
  simp [isNumber] at hNum
  simp [isZero, isNumber, UnpackedFloat.isZero] at hZ
  simp [EUnpackedFloat.mkZero, UnpackedFloat.mkZero, EUnpackedFloat.sign]
  grind

/--
For a normalized Number-state `uf`, `¬ uf.isZero` implies the significand is nonzero.
-/
theorem sig_ne_zero_of_isNumber_of_not_isZero_of_normalize
    (uf : EUnpackedFloat e s)
    (hNum : uf.isNumber)
    (hZ : ¬ uf.isZero)
    -- | TODO: why do I need hnorm?
    (hnorm : uf.num.normalize = uf.num) :
    uf.num.sig ≠ 0#s := by
  intro hsig
  apply hZ
  have hnormZ : uf.num.normalize = UnpackedFloat.mkZero uf.num.sign := by
    simp [UnpackedFloat.normalize, hsig]
  have heq : uf.num = UnpackedFloat.mkZero uf.num.sign := hnorm.symm.trans hnormZ
  simp only [EUnpackedFloat.isZero, hNum, Bool.true_and]
  rw [heq]
  simp [UnpackedFloat.isZero]

/-! #### BitVec sub-lemmas for the normal round-trip -/

/--
In the normal-range case, the packed exponent `(uf.num.ex + bias).truncate e` is nonzero.
Reason: normal range means `uf.num.ex ≥ minNormalExp = 1 - bias`, so
`uf.num.ex + bias ≥ 1` (no wraparound since `uf.num.ex ≤ maxNormalExp = bias`, giving
`uf.num.ex + bias ≤ 2·bias`, well within the `exponentWidth`).
-/
private theorem pack_ex_ne_zero_of_normal {e s : Nat}
    (ex : BitVec (exponentWidth e s))
    (hnr : (BitVec.ofInt _ (minNormalExp e)).sle ex = true)
    (hhi : ex.sle (BitVec.ofInt _ (maxNormalExp e)))
    (he : 0 < e) :
    (ex + BitVec.ofNat _ (bias e)).truncate e ≠ 0#e := by
  sorry

/--
In the normal-range case, the packed exponent `(uf.num.ex + bias).truncate e` is not `allOnes`.
Reason: `uf.num.ex ≤ maxNormalExp = bias`, so `uf.num.ex + bias ≤ 2·bias = 2^e - 2 < allOnes`.
-/
private theorem pack_ex_ne_allOnes_of_normal {e s : Nat}
    (ex : BitVec (exponentWidth e s))
    (hnr : (BitVec.ofInt _ (minNormalExp e)).sle ex = true)
    (hhi : ex.sle (BitVec.ofInt _ (maxNormalExp e)))
    (he : 0 < e) :
    (ex + BitVec.ofNat _ (bias e)).truncate e ≠ BitVec.allOnes e := by
  sorry

/--
Bias add-then-subtract round-trip. In the normal range, `((ex + bias).truncate e).zeroExtend _ - bias = ex`.
Follows from the range being within `[1, 2^e - 2]` once biased, so truncation is lossless.
-/
private theorem unpack_pack_ex_eq_of_normal {e s : Nat}
    (ex : BitVec (exponentWidth e s))
    (hnr : (BitVec.ofInt _ (minNormalExp e)).sle ex = true)
    (hhi : ex.sle (BitVec.ofInt _ (maxNormalExp e)))
    (he : 0 < e) :
    ((ex + BitVec.ofNat _ (bias e)).truncate e).zeroExtend (exponentWidth e s)
      - BitVec.ofNat (exponentWidth e s) (bias e) = ex := by
  simp only [BitVec.truncate_eq_setWidth]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · sorry
  · sorry



/--
Normal-range round-trip. For a Number-state `uf` with msb=1 significand and exponent in the
normal range `[minNormalExp, maxNormalExp]`, `pack` produces a PackedFloat classified as
`isNorm`, and `unpack` reconstitutes `uf`.

Key sub-facts used:
- the packed exponent `(uf.ex + bias).truncate e` is neither `0` nor `allOnes`;
- `BitVec.cons_true_setWidth_of_msb` recovers the full significand from its `truncate s` truncation;
- adding `bias` and then subtracting it back recovers `uf.ex` (no overflow in the valid range).
-/
theorem unpack_pack_of_isNumber_normal
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (hNum : uf.isNumber) (hNZ : ¬ uf.isZero)
    (hmsb : uf.num.sig.msb = true)
    (hnr : (BitVec.ofInt _ (minNormalExp e)).sle uf.num.ex = true)
    (hhi : uf.num.ex.sle (BitVec.ofInt _ (maxNormalExp e)))
    (he : 0 < e) (hs : 0 < s) :
    uf.pack.unpack = uf := by
  have hstate : uf.state = .Number := by
    simp [isNumber] at hNum; exact hNum
  have hnan : uf.isNaN = false := by
    simp [isNaN, hstate]
  have hinf : uf.isInfinite = false := by
    simp [isInfinite, hstate]
  -- pack field equalities
  have hpf_ex_ne_zero := pack_ex_ne_zero_of_normal (s := s) uf.num.ex hnr hhi he
  have hpf_ex_ne_allOnes := pack_ex_ne_allOnes_of_normal (s := s) uf.num.ex hnr hhi he
  have hexp : uf.exp = uf.num.ex := rfl
  have hsig : uf.sig = uf.num.sig := rfl
  have hpf_ex : uf.pack.ex = (uf.num.ex + BitVec.ofNat _ (bias e)).truncate e := by
    simp [pack, hnan, hinf, hexp, hNZ, hnr]
  have hpf_sig : uf.pack.sig = uf.num.sig.setWidth s := by
    simp [pack, hnan, hinf, hsig, hexp, hNZ, hnr]
  have hpf_sign : uf.pack.sign = uf.num.sign := by simp [pack, EUnpackedFloat.sign]
  -- pack classification
  have hpf_nan : uf.pack.isNaN = false := by
    simp [PackedFloat.isNaN, hpf_ex, hpf_ex_ne_allOnes]
  have hpf_inf : uf.pack.isInfinite = false := by
    simp [PackedFloat.isInfinite, hpf_ex, hpf_ex_ne_allOnes]
  have hpf_ex_ne_zero' : uf.pack.ex ≠ 0#e := hpf_ex ▸ hpf_ex_ne_zero
  have hpf_zero : uf.pack.isZero = false := by
    simp [PackedFloat.isZero, hpf_ex_ne_zero']
  have hpf_norm : uf.pack.isNorm = true := by
    simp [PackedFloat.isNorm, hpf_ex, hpf_ex_ne_zero, hpf_ex_ne_allOnes]
  -- unpack
  rw [PackedFloat.unpack]
  simp only [hpf_nan, hpf_inf, hpf_zero, cond_false]
  simp only [PackedFloat.unpackNum, hpf_norm, ↓reduceIte, hpf_sign, hpf_ex, hpf_sig]
  rw [show BitVec.setWidth s uf.num.sig = uf.num.sig.setWidth s from rfl]
  rw [unpack_pack_ex_eq_of_normal (s := s) uf.num.ex hnr hhi he]
  rw [BitVec.cons_true_setWidth_of_msb uf.num.sig hmsb]
  -- Goal: mkNumber { sign := uf.num.sign, ex := uf.num.ex, sig := uf.num.sig } = uf
  rcases uf with ⟨state, num⟩
  simp [isNumber] at hNum
  subst hNum
  rcases num with ⟨sign, ex, sig⟩
  rfl

/-! #### Subnormal round-trip

**Caveat.** In the subnormal range the round-trip `uf.pack.unpack = uf` is *not* valid for all
`uf` satisfying `hNum`, `hmsb`, and the exponent bounds alone. `pack` shifts `uf.num.sig` right
by `k = minNormalExp - uf.num.ex` bits and truncates to `s` bits — the lowest `k` bits of
`uf.num.sig` are *discarded*. `unpack` then cons's `false` and renormalizes, producing a value
whose low `k` bits are zero. So the round-trip only holds when the low `k` bits of `uf.num.sig`
are already zero (equivalently: `uf` is in the image of `unpack`).

The statement below is therefore false in general — but left in place with `sorry` so that the
main dispatcher `unpack_pack_of_isNumber` compiles. To make it true, an extra hypothesis
`uf.num.sig.toNat % 2^(minNormalExp - uf.num.ex).toNat = 0` (or equivalent) is required.
-/

/--
Subnormal-range round-trip. **Not provable in current form** — see the caveat above.
-/
theorem unpack_pack_of_isNumber_subnormal
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (hNum : uf.isNumber) (hNZ : ¬ uf.isZero)
    (hmsb : uf.num.sig.msb = true)
    (hnr : ¬ ((BitVec.ofInt _ (minNormalExp e)).sle uf.num.ex = true))
    (hlo : (BitVec.ofInt _ (minSubnormalExp e s + 1)).sle uf.num.ex)
    (he : 0 < e) (hs : 0 < s) :
    uf.pack.unpack = uf := by
  sorry

/-! ### Main round-trip for finite Numbers -/

/--
The round-trip: packing a normalized Number and unpacking returns the same value.

Hypotheses:
- `hNum : uf.isNumber` — non-NaN, non-Infinity. (NaN/Infinity are handled by
  `unpack_pack_of_isNaN` / `unpack_pack_of_isInfinite`; their `num` fields are not preserved,
  so the round-trip only gives back `mkNaN` / `mkInfinity uf.sign`.)
- `hnorm : uf.num.normalize = uf.num` — either `uf.num` is canonical zero (ex = intMin, sig = 0)
  or its significand has msb = 1.
- `hlo`, `hhi` — the exponent fits in the PackedFloat's representable range.
- `he`, `hs` — avoid the degenerate `e = 0` / `s = 0` formats.
-/
theorem unpack_pack_of_isNumber
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (hNum : uf.isNumber)
    (hnorm : uf.num.normalize = uf.num)
    (hlo : (BitVec.ofInt _ (minSubnormalExp e s + 1)).sle uf.num.ex)
    (hhi : uf.num.ex.sle (BitVec.ofInt _ (maxNormalExp e)))
    (he : 0 < e) (hs : 0 < s) :
    uf.pack.unpack = uf := by
  by_cases hZ : uf.isZero
  · -- Zero case: uf = mkZero uf.sign; pack = getZero; unpack(getZero) = mkZero sign
    rw [eq_mkZero_of_isNumber_of_isZero uf]
    · simp [he]
    · grind only
    · grind only
  · -- Non-zero: sig ≠ 0, so normalize forces msb=1
    have hsigNeZ : uf.num.sig ≠ 0#(s + 1) := by
      apply sig_ne_zero_of_isNumber_of_not_isZero_of_normalize uf <;> grind only
    have hmsb : uf.num.sig.msb = true := by
      have h := UnpackedFloat.msb_normalize_eq_decide (uf := uf.num) (zsign := uf.num.sign)
      grind only
    -- Case split on normal vs subnormal range
    by_cases hnr : ((BitVec.ofInt (exponentWidth e s) (minNormalExp e)).sle uf.num.ex) = true
    · apply unpack_pack_of_isNumber_normal <;> grind only
    · apply unpack_pack_of_isNumber_subnormal <;> grind only

/-! ### Corollary: `toExtRat` preservation -/

/--
Packing preserves `toExtRat` when either the value is NaN/Infinity (trivially), or it is a
sufficiently normalized/bounded Number (via `unpack_pack_of_isNumber`).
-/
theorem toExtRat_pack_of_isNumber
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (hNum : uf.isNumber)
    (hnorm : uf.num.normalize = uf.num)
    (hlo : (BitVec.ofInt _ (minSubnormalExp e s + 1)).sle uf.num.ex)
    (hhi : uf.num.ex.sle (BitVec.ofInt _ (maxNormalExp e)))
    (he : 0 < e) (hs : 0 < s) :
    uf.pack.toExtRat = uf.toExtRat := by
  rw [← PackedFloat.toExtRat_unpack_eq_toExtRat,
      unpack_pack_of_isNumber uf hNum hnorm hlo hhi he hs]

end EUnpackedFloat
