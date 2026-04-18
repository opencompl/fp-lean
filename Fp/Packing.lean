import Fp.Basic
import Fp.Unpacking
import Fp.Theorems.Packing

namespace EUnpackedFloat

/-- Packing a NaN gives a NaN PackedFloat. -/
@[simp]
theorem isNaN_pack_of_isNaN
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) (huf : uf.isNaN) :
    uf.pack.isNaN = true := by
  simp [pack, PackedFloat.isNaN, huf]
  grind

@[grind ., simp]
theorem two_pow_e_lt_two_pow_exponentWidth (he : 1 < e) (hs : 0 < s) :
    2 ^ e < 2 ^ exponentWidth e s := by
  apply Nat.pow_lt_pow_of_lt
  · decide
  · exact self_lt_exponentWidth e s he hs


@[simp]
theorem isNaN_of_isNaN_pack (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.pack.isNaN):
    uf.isNaN = true := by
  simp [pack, PackedFloat.isNaN] at huf ⊢
  by_cases hnan : uf.isNaN
  · simp [hnan]
  · simp [hnan] at huf
    by_cases hinf : uf.isInfinite
    · simp [hinf] at huf
      grind only
    · simp [hinf] at huf
      by_cases hzero : uf.isZero
      · simp [hzero] at huf
        grind only
      · simp [hzero] at huf
        split at huf
        case neg.isTrue hle =>
          simp [hle] at huf
          grind
        case neg.isFalse hle =>
          -- simp at hle
          simp [hle] at huf
          simp at hle
          obtain ⟨huf1, huf2⟩ := huf
          rcases huf2 with huf2 | huf2
          · grind only
          · rw [BitVec.sle_eq_decide] at hle
            simp at hle
            rw [Int.bmod_eq_of_le] at hle
            · sorry
            · norm_cast
              simp only [Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int]
              sorry
            · sorry

@[simp, grind .]
theorem pack_isNaN_eq_isNaN (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack.isNaN = uf.isNaN := by
  have h1 := isNaN_pack_of_isNaN uf
  have h2 := isNaN_of_isNaN_pack he hs uf
  grind only [= PackedFloat.isNaN_iff_toExtRat'_eq_NaN, #9c18]


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

theorem isInfinite_of_isInfinite_pack (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.pack.isInfinite):
    uf.isInfinite = true := by
  simp [pack, PackedFloat.isInfinite] at huf ⊢
  by_cases hinf : uf.isInfinite
  · simp [hinf]
  · simp [hinf] at huf
    by_cases hnan : uf.isNaN
    · simp [hnan] at huf
    · simp [hnan] at huf
      by_cases hzero : uf.isZero
      · simp [hzero] at huf
        grind only
      · simp [hzero] at huf
        split at huf
        case neg.isTrue hle =>
          simp [hle] at huf
          grind
        case neg.isFalse hle =>
          -- simp at hle
          simp [hle] at huf
          obtain ⟨huf1, huf2⟩ := huf
          sorry

@[simp, grind .]
theorem pack_isInfinite_eq_isInfinite (he : 1 < e) (hs : 0 < s)
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    uf.pack.isInfinite = uf.isInfinite := by
  have h1 := isInfinite_pack_of_isInfinite uf
  have h2 := isInfinite_of_isInfinite_pack he hs uf
  grind only [PackedFloat.eq_getInfinity_iff_isInfinity, #050c]

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

@[simp, grind =>]
theorem EUnpackedFloat.isNaN_iff_state_eq
  (uf : EUnpackedFloat e s) :
  uf.isNaN ↔ (uf.state = .NaN) := by simp [isNaN]

@[simp, grind =>]
theorem EUnpackedFloat.isInfinite_iff_state_eq
  (uf : EUnpackedFloat e s) :
  uf.isInfinite ↔ (uf.state = .Infinity) := by simp [isInfinite]

@[simp, grind =>]
theorem EUnpackedFloat.isNumber_iff_state_eq
  (uf : EUnpackedFloat e s) :
  uf.isNumber ↔ (uf.state = .Number) := by simp [isNumber]

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
    (hnormalize : uf.num.normalize = uf.num)
    (hlo : minSubnormalExp e s ≤ uf.num.ex.toInt)
    (hhi : uf.num.ex.toInt ≤ maxNormalExp e)
    (he : 1 < e) (hs : 0 < s) :
    uf.pack.unpack = uf := by
  simp [isNumber] at hNum
  have hnan : uf.isNaN = false := by grind only [=> EUnpackedFloat.isNaN_iff_state_eq]
  have hpacknan : uf.pack.isNaN = false := by
    sorry
  have hinf : uf.isInfinite = false := by sorry
  have hpackinf : uf.pack.isInfinite = false := by sorry
  by_cases hZ : uf.isZero
  · have : uf.pack.isZero = true := by sorry
    simp [this]
    sorry
  · have hpackzero : uf.pack.isZero = false := by sorry
    simp [PackedFloat.unpack]
    simp [hpackinf, hpacknan, hpackzero]
    simp [PackedFloat.unpackNum]
    by_cases hnorm : uf.pack.isNorm
    · simp [hnorm]
      ext1
      · simp [hNum]
      · ext1
        · simp [EUnpackedFloat.sign]
        · simp; sorry
        · simp; sorry
    · simp [hnorm]
      ext1
      · simp [hNum]
      · ext1
        · simp [EUnpackedFloat.sign]
        · simp; sorry
        · simp; sorry





/-! ### Corollary: `toExtRat` preservation -/

/--
Packing preserves `toExtRat` when either the value is NaN/Infinity (trivially), or it is a
sufficiently normalized/bounded Number (via `unpack_pack_of_isNumber`).
-/
theorem toExtRat_pack_of_isNumber
    (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (hNum : uf.isNumber)
    (hnorm : uf.num.normalize = uf.num)
    (hlo : minSubnormalExp e s ≤ uf.num.ex.toInt)
    (hhi : uf.num.ex.toInt ≤ maxNormalExp e)
    (he : 1 < e) (hs : 0 < s) :
    uf.pack.toExtRat = uf.toExtRat := by
  rw [← PackedFloat.toExtRat_unpack_eq_toExtRat]
  rw [unpack_pack_of_isNumber]
  · grind only
  · grind only
  · grind only
  · grind only
  · grind only
  · grind only

end EUnpackedFloat
