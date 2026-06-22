import Fp.PackedFloat.Basic
import Fp.Theorems.PackedFloat.Negation
import Fp.Theorems.PackedFloat.Packing
import Fp.UnpackedFloat.Basic
import Fp.Theorems.UnpackedFloat.ToRat
import Fp.EUnpackedFloat.Basic
import Fp.Basic
import Fp.Comparison
import Fp.Utils


/--
An unpacked float is related to a packed float
iff they have the same rational value and the same sign, when
the unpacked float is interpreted at the rational value.
-/
def UnpackedFloat.Rel (uf : UnpackedFloat e s) (pf : PackedFloat ep sp) :=
  uf.toRat' sp = pf.toRat ∧ uf.sign = pf.sign -- ∧ ¬ pf.isInfinite ∧ ¬ pf.isNaN


@[simp, grind .]
theorem sign_eq_sign_of_Rel (uf : UnpackedFloat e s) (pf : PackedFloat ep sp) (hRel : uf.Rel pf) :
  uf.sign = pf.sign := by
  simp only [UnpackedFloat.Rel] at hRel
  exact hRel.2

@[simp]
theorem toRat'_eq_toRat_of_Rel (uf : UnpackedFloat e s) (pf : PackedFloat ep sp) (hRel : uf.Rel pf) :
  uf.toRat' sp = pf.toRat := by
  simp only [UnpackedFloat.Rel] at hRel
  exact hRel.1

@[grind =>]
theorem UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign (uf : UnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (hToRat : uf.toRat' sp = pf.toRat) (hSign : uf.sign = pf.sign) :
  UnpackedFloat.Rel uf pf := by
  simp only [UnpackedFloat.Rel]
  simp [hToRat, hSign]

theorem UnpackedFloat.Rel_of_isZero_of_isZero
  (uf : UnpackedFloat ef uf)
  (pf : PackedFloat ep sp)
  (huf : uf.isZero) (hpf : pf.isZero) (hsign : uf.sign = pf.sign) :
  UnpackedFloat.Rel uf pf := by
  simp only [UnpackedFloat.Rel]
  simp [hpf, hsign, huf]

@[simp]
theorem UnpackedFloat.neg_Rel_neg
  (uf : UnpackedFloat e s) (pf : PackedFloat ep sp)
  (h : uf.Rel pf) :
  (- uf).Rel (-pf) := by
  constructor
  · simp
    apply toRat'_eq_toRat_of_Rel uf pf h
  · simp; grind only [sign_eq_sign_of_Rel]

/-- info: 'UnpackedFloat.neg_Rel_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UnpackedFloat.neg_Rel_neg

/--
An extended unpacked float is related to a packed float
iff they are both NaN, or they are both infinite with the same sign,
or they are either NaN and infinite, and have the same rational value and the same sign.
-/
def EUnpackedFloat.Rel (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp) :=
  (euf.state = .NaN ∧ pf.isNaN) ∨
  (euf.state = .Infinity ∧ pf.isInfinite ∧ euf.sign = pf.sign) ∨
  (euf.state = .Number ∧ euf.num.Rel pf)

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_state_eq_NaN_of_isNaN (euf : EUnpackedFloat ef uf)
  (pf : PackedFloat ep sp)
  (heuf : euf.state = .NaN)
  (hpf : pf.isNaN) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, hpf]

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_state_eq_Infinity_of_sign (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : euf.state = .Infinity)
  (hpf : pf.isInfinite)
  (hsign : euf.sign = pf.sign) :
  EUnpackedFloat.Rel euf pf := by
  simp only [EUnpackedFloat.Rel]
  simp [heuf, hpf, hsign]

@[simp, grind =>]
theorem EUnpackedFloat.Rel_of_Rel_of_state_eq_Number (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : euf.state = .Number) (hRel : euf.num.Rel pf) :
  EUnpackedFloat.Rel euf pf := by
  simp [EUnpackedFloat.Rel]
  simp [heuf, hRel]

@[simp, grind .]
theorem EUnpackedFloat.Rel_of_Rel_of_isZero_of_isZero_of_eq_sign
  (euf : EUnpackedFloat ef uf) (pf : PackedFloat ep sp)
  (heuf : euf.isZero) (hpf : pf.isZero) (hsign : euf.sign = pf.sign) :
  EUnpackedFloat.Rel euf pf := by
  simp [EUnpackedFloat.Rel]
  simp [heuf, hsign]
  apply UnpackedFloat.Rel_of_isZero_of_isZero
  · simp [isZero] at heuf
    grind only [=> UnpackedFloat.toRat'_ne_zero_iff_not_isZero]
  · grind only
  · simp only [sign] at hsign
    simp only [hsign]


@[simp, grind .]
theorem EUnpackedFloat.neg_Rel_neg {e s ep sp}
  (euf : EUnpackedFloat e s) (pf : PackedFloat ep sp)
  (h : euf.Rel pf) :
euf.neg.Rel (-pf) := by
  simp [EUnpackedFloat.Rel]
  rcases h with h | h | h
  · have heuf : euf.state = .NaN := by
      simp [h]
    have hpf : (pf).isNaN = true := by
      simp [h]
    grind only [=> EUnpackedFloat.isNaN_iff_state_eq]
  · simp [h]
  · obtain ⟨hnan, hinf, hnum⟩ := h
    simp [hnan]
    apply UnpackedFloat.neg_Rel_neg _ _
    grind only [=> UnpackedFloat.Rel_of_toRat_eq_toRat_and_sign]

@[grind .]
theorem EUnpackeDFloat.num_Rel_of_Rel_of_eq_Number {e s ep sp}
  (euf : EUnpackedFloat e s) (pf : PackedFloat ep sp)
  (hRel : euf.Rel pf) (heuf : euf.state = .Number) :
  euf.num.Rel pf := by
  simp [EUnpackedFloat.Rel] at hRel
  grind only

/-- info: 'EUnpackedFloat.neg_Rel_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EUnpackedFloat.neg_Rel_neg


-- ep sp eu su : Nat
-- he : 1 < ep
-- hs : 0 < sp
-- heu : exponentWidth ep sp ≤ eu
-- hsu : sp + 2 ≤ su
-- x : UnpackedFloat eu su
-- hxnorm : x.normalize = x
-- hzero : x.isZero = true
-- ⊢ (EUnpackedFloat.mkZero x.sign).Rel
--   ((SmtLibSemantics.smtLibRoundMethod ep sp SmtLibSemantics.smtLibV SmtLibSemantics.smtLibV).roundRNE x.sign
--     (ExtRat.Number 0))
theorem EUnpackedFloat.mkZero_Rel_of_isZero
  (ep sp eu su : Nat)
  (he : 1 < ep)
  (hsign : signUnpacked = signPacked) :
  (EUnpackedFloat.mkZero signUnpacked : EUnpackedFloat eu su).Rel
    (PackedFloat.getZero ep sp signPacked) := by
  simp [EUnpackedFloat.mkZero, EUnpackedFloat.Rel]
  constructor
  · simp only [UnpackedFloat.mkZero_isZero, UnpackedFloat.toRat'_eq_zero_of_isZero]
    rw [PackedFloat.toRat_getZero]
    grind only
  · simp [hsign]

/--
The Number-case content of `pack'_EquivUptoNaN_of_Rel`: packing a normalized,
in-range finite number `uf` that is related to a *finite* packed float `pf`
recovers exactly `pf`.

The `hpfNaN`/`hpfInf` hypotheses are necessary because `Rel` only fixes the rational
value and sign: an infinity has `toRat = 0` and a NaN has a nonzero `toRat`, so without
them `Rel` could wrongly relate a number to a NaN/Infinity bit pattern. The
`hnorm`/`hexp1`/`hexp2` hypotheses are exactly those of `toRat_pack_mkNumber_eq_toRat`.
-/
theorem EUnpackedFloat.packNumber'_eq_of_Rel
    (hep : 1 < ep) (hsp : 0 < sp)
    (uf : UnpackedFloat (exponentWidth ep sp) (sp + 1))
    (pf : PackedFloat ep sp)
    (hpfNaN : ¬ pf.isNaN) (hpfInf : ¬ pf.isInfinite)
    (hpack : uf.Packable)
    (hRel : uf.Rel pf) :
    (EUnpackedFloat.mkNumber uf).pack' = pf := by
  obtain ⟨hnorm, hexp1, hexp2⟩ := hpack
  obtain ⟨hval, hsign⟩ := hRel
  have hufRat : uf.toRat = pf.toRat := by
    rw [UnpackedFloat.toRat_eq_toRat']; exact hval
  by_cases hzero : uf.isZero
  · -- zero sub-case: `pack'` produces `getZero`, and `pf` (finite, value 0) is a zero too.
    have hpf0 : pf.toRat = 0 := by
      rw [← hufRat, UnpackedFloat.toRat_eq_toRat']
      exact uf.toRat'_eq_zero_of_isZero hzero
    have hpfZero : pf.isZero := by
      apply Classical.byContradiction
      intro hc
      exact PackedFloat.toRat_ne_zero
        (PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero hpfNaN hpfInf hc) hpf0
    rw [pack'_eq_getZero_of_isZero _ (by simp [EUnpackedFloat.isZero_mkNumber, hzero])]
    simp only [EUnpackedFloat.sign, EUnpackedFloat.num_mkNumber]
    exact ((PackedFloat.eq_mkZero_of_isZero' (sign := uf.sign) (by omega)).mp ⟨hpfZero, hsign⟩).symm
  · -- nonzero sub-case: both sides are finite numbers with equal value, so equal bits.
    have hpfRatNe : pf.toRat ≠ 0 := by
      rw [← hufRat, UnpackedFloat.toRat_eq_toRat']
      exact (uf.toRat'_ne_zero_iff_not_isZero).mp hzero
    have hpfZ : ¬ pf.isZero := by
      intro hc
      exact hpfRatNe (by simp [PackedFloat.toRat, PackedFloat.toRatSig_eq_zero_of_isZero pf hc])
    have hpfFin : pf.isNormOrNonzeroSubnorm :=
      PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero hpfNaN hpfInf hpfZ
    -- the packed value equals `uf.toRat = pf.toRat`
    have hpackRat : (EUnpackedFloat.mkNumber uf).pack'.toRat = pf.toRat := by
      rw [← EUnpackedFloat.pack_eq_pack',
        toRat_pack_mkNumber_eq_toRat hep hsp uf ⟨hnorm, hexp1, hexp2⟩, hufRat]
    -- unfold `pack'` to `packNumber'` for the non-zero case
    have hpackEq : (EUnpackedFloat.mkNumber uf).pack'
        = EUnpackedFloat.packNumber' uf.sign uf.sig uf.ex := by
      simp only [EUnpackedFloat.pack', EUnpackedFloat.isNaN_mkNumber,
        EUnpackedFloat.isInfinite_mkNumber, EUnpackedFloat.isZero_mkNumber, hzero,
        Bool.false_eq_true, ↓reduceIte, EUnpackedFloat.sign, EUnpackedFloat.sig,
        EUnpackedFloat.exp, EUnpackedFloat.num_mkNumber]
    -- the packed number is itself a finite number (not NaN, not Inf, not zero)
    have hLnaN : ¬ (EUnpackedFloat.mkNumber uf).pack'.isNaN := by
      rw [hpackEq]
      simp [EUnpackedFloat.not_isNaN_packNumber' hsp hep uf.sign uf.sig uf.ex hexp1]
    have hLinf : ¬ (EUnpackedFloat.mkNumber uf).pack'.isInfinite := by
      rw [hpackEq]
      simp only [PackedFloat.isInfinite, EUnpackedFloat.packNumber', Bool.and_eq_true,
        beq_iff_eq, not_and]
      intro hcontra
      exact absurd hcontra
        (EUnpackedFloat.packNumber'.exPacked_ne_allOnes hsp hep uf.ex hexp1)
    have hLzero : ¬ (EUnpackedFloat.mkNumber uf).pack'.isZero := by
      intro hc
      exact hpfRatNe (by rw [← hpackRat]; simp [PackedFloat.toRat,
        PackedFloat.toRatSig_eq_zero_of_isZero _ hc])
    have hLfin : (EUnpackedFloat.mkNumber uf).pack'.isNormOrNonzeroSubnorm :=
      PackedFloat.isNormOrNonzeroSubnorm_of_not_NaN_not_Infinite_not_Zero hLnaN hLinf hLzero
    apply PackedFloat.eq_of_toExtRat'_eq _ _ hLnaN hpfNaN hLzero hpfZ
    rw [PackedFloat.toExtRat'_eq_toRat_of hLfin, PackedFloat.toExtRat'_eq_toRat_of hpfFin,
      hpackRat]

/--
If an extended unpacked float is related to a packed float,
then packing the extended unpacked gives a packed float that is equal
to the related one according to SMT-LIB equality.
This allows the 'NaN' bit pattern to change, but requires all else to remain equal.
Thus, all our theorems will be stated in terms of SMT-LIB equality.

When `euf` is a finite number, `Rel` alone is too weak (it fixes only the value and sign),
so two extra hypotheses supply the missing facts: `hpack` says `euf` is `Packable` (its payload
is normalized and in range), and `hpf` says `pf` is finite. Both are vacuous when `euf` is
NaN/Infinity.
-/
theorem EUnpackedFloat.pack'_EquivUptoNaN_of_Rel
    (hep : 1 < ep) (hsp : 0 < sp)
    (euf : EUnpackedFloat (exponentWidth ep sp) (sp + 1))
    (pf : PackedFloat ep sp)
    (hRel : euf.Rel pf)
    (hpack : euf.Packable)
    (hpf : euf.state = .Number → ¬ pf.isNaN ∧ ¬ pf.isInfinite) :
    euf.pack'.EquivUptoNaN pf := by
  have hRel0 := hRel
  simp [EUnpackedFloat.Rel] at hRel
  simp [PackedFloat.EquivUptoNaN]
  rcases heuf : euf.state
  case NaN =>
    simp [heuf] at hRel ⊢
    simp [hRel]
  case Infinity =>
    simp [heuf] at hRel ⊢
    left
    simp [hRel, hsp]
    have := pf.eq_getInfinity_iff_isInfinity hsp |>.mp (by simp [hRel])
    rw [this]
    simp [hsp]
  case Number =>
    obtain ⟨hpfNaN, hpfInf⟩ := hpf heuf
    have hnumPack : euf.num.Packable := hpack heuf
    have hnumRel : euf.num.Rel pf :=
      EUnpackeDFloat.num_Rel_of_Rel_of_eq_Number euf pf hRel0 heuf
    left
    have heqMk : euf = EUnpackedFloat.mkNumber euf.num := by
      apply EUnpackedFloat.ext <;> simp [heuf, EUnpackedFloat.mkNumber]
    rw [heqMk]
    exact EUnpackedFloat.packNumber'_eq_of_Rel hep hsp euf.num pf
      hpfNaN hpfInf hnumPack hnumRel

-- theorem unpack_eq_of_Rel (euf : EUnpackedFloat ef uf) (pf : PackedFloat (exponentWidth ef uf) (uf + 1)) (hRel : euf.Rel pf) :
--   pf.unpack = euf := sorry
