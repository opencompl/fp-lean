import Fp.Basic

/--
Convert a packed float into an 'UnpackedFloat',
ignoring the possibility that it could be NaN/± infinity.
-/
@[bv_normalize]
def PackedFloat.unpackNum (pf : PackedFloat e s) :
  UnpackedFloat (exponentWidth e s) (s + 1) :=
  if pf.isNorm then
    {
      sign := pf.sign
      -- We cannot use `BitVec.signExtend` here because `pf.ex` is not in 2's complement representation.
      -- It should be safe to use `setWidth'`
      ex := pf.ex.zeroExtend _ - BitVec.ofNat _ (bias e) -- e - bias, but no adjustment for significand?
      sig := pf.sig.cons true
      : UnpackedFloat _ _
    }
  else -- bif pf.isSubnorm then
    {
      sign := pf.sign
      ex := BitVec.ofInt _ (minNormalExp e)
      sig := pf.sig.cons false
      : UnpackedFloat _ _
    }.normalize

/--
If we start with a packedFloat whose 'isZero' predicate says 'false',
then we know that the unpacked version of it is also not zero. This is a useful fact to have when we want to rewrite
-/
@[simp, grind! →]
axiom PackedFloat.unpackNormOrNonzeroSubnorm_isZero_eq_of_not_isZero (pf : PackedFloat e s) (hpf : ¬ pf.isZero := by grind) :
  pf.unpackNum.isZero = false

@[simp]
theorem PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign (pf : PackedFloat e s) :
    pf.unpackNum.sign = pf.sign := by
  simp [unpackNum]
  by_cases hpf : pf.isNorm <;> simp [hpf]


@[bv_normalize]
def PackedFloat.unpack (pf : PackedFloat e s)
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif pf.isNaN then
    EUnpackedFloat.mkNaN
  else bif pf.isInfinite then
    EUnpackedFloat.mkInfinity pf.sign
  else bif pf.isZero then
    EUnpackedFloat.mkZero pf.sign
  else EUnpackedFloat.mkNumber (pf.unpackNum)

@[simp, grind! .]
theorem PackedFloat.isNaN_unpack_eq_isNaN (pf : PackedFloat e s) :
    pf.unpack.isNaN = pf.isNaN := by
  simp [PackedFloat.unpack]
  by_cases hpf : pf.isNaN <;> simp [hpf]
  · by_cases hinf : pf.isInfinite <;> simp [hinf]
    · by_cases hzero : pf.isZero <;> simp [hzero]

@[simp, grind! .]
theorem PackedFloat.isInfinite_unpack_eq_isInfinite (pf : PackedFloat e s) :
    pf.unpack.isInfinite = pf.isInfinite := by
  simp [PackedFloat.unpack]
  by_cases hnan : pf.isNaN <;> simp [hnan]
  by_cases hpf : pf.isInfinite <;> simp [hpf]
  · grind
  · by_cases hinf : pf.isInfinite <;> simp [hinf]
    · by_cases hzero : pf.isZero <;> simp [hzero]

@[simp, grind! .]
theorem PackedFloat.isZero_unpack_eq_isZero (pf : PackedFloat e s) :
    pf.unpack.isZero = pf.isZero := by
  simp [PackedFloat.unpack]
  by_cases hnan : pf.isNaN <;> simp [hnan]
  · grind
  · by_cases hinf : pf.isInfinite <;> simp [hinf]
    · grind
    · by_cases hzero : pf.isZero <;> simp [hzero]


@[simp, grind =]
theorem PackedFloat.unpack_eq_unpackNum_of (pf : PackedFloat e s)
    (hpf : pf.isNormOrNonzeroSubnorm) :
     pf.unpack = EUnpackedFloat.mkNumber pf.unpackNum := by
  unfold unpack
  grind

/-- Unpacking a packed float always results in a normalized float. -/
@[simp, grind =]
theorem PackedFloat.msb_unpackNum_eq_true {pf : PackedFloat e s}
    (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.unpackNum.sig.msb = true := by
  simp only [unpackNum, BitVec.truncate_eq_setWidth]
  by_cases hf : pf.isNorm <;> simp only [hf, ↓reduceIte, BitVec.msb_cons]
  have : pf.sig ≠ 0#s := by grind
  simp [this]


@[bv_normalize]
def EUnpackedFloat.pack (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
  : PackedFloat e s :=
  -- min normal <= exp
  let inNormalRange := (BitVec.ofInt _ (minNormalExp e)).sle uf.exp
  {
    sign := bif uf.isNaN then false else uf.sign
    ex := bif uf.isNaN || uf.isInfinite then
            BitVec.allOnes e
          else if uf.isZero || !inNormalRange then
            0#e
          else -- bif uf.isNorm then
            -- Truncate msbs used to normalize subnormals
            (uf.exp + BitVec.ofNat _ (bias e)).signExtend _
    sig := bif uf.isNaN then
            BitVec.intMin s
           else bif uf.isInfinite || uf.isZero then
            0#s
           else bif inNormalRange then
            uf.sig.truncate s -- drop the leading 1 bit
           else -- bif uf.isSubnorm then
            -- shift right by #of subnormal bits.
            let shift := BitVec.ofInt _ (minNormalExp e) - uf.exp
            -- shift, and then truncate to significand width.
            (uf.sig >>> shift).truncate s
  }

/--
Alternative definition of `EUnpackedFloat.pack`
that isolates the number conversion.
-/
def EUnpackedFloat.packNumber' (sign : Bool) (sig : BitVec (s + 1)) (exp : BitVec (exponentWidth e s)) : PackedFloat e s :=
  {
    sign := sign
    ex := exPacked
    sig := sigPacked
   } where
      inNormalRange := (BitVec.ofInt _ (minNormalExp e)).sle exp
      shift := BitVec.ofInt _ (minNormalExp e) - exp
      exPacked := if !inNormalRange then 0#e else (exp + BitVec.ofNat _ (bias e)).signExtend e
      sigPacked := if inNormalRange then sig.truncate s else (sig >>> shift).truncate s


/--
we are in the normal range iff the exponent is greater than or equal to the minimum normal exponent.
Note that the minimum normal exponent is negative, so this is really saying that the exponent is "not too small". This is a useful fact to have when we want to rewrite using `minNormalExp` in the context of `packNumber'`.
-/
@[simp]
theorem EUnpackedFloat.packNumber'.inNormalRange_iff
    (he : 1 < e) (hs : 0 < s)
    (exp : BitVec (exponentWidth e s)) :
    EUnpackedFloat.packNumber'.inNormalRange exp ↔ ((minNormalExp e) ≤ exp.toInt) := by
  simp [EUnpackedFloat.packNumber'.inNormalRange]
  constructor
  · intros h
    rw [BitVec.sle_eq_decide] at h
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp he hs] at h
    grind only
  · intros h
    rw [BitVec.sle_eq_decide]
    rw [toInt_ofInt_minNormalExp_eq_minNormalExp he hs]
    grind only


/--
we never produce an 'allOnes' exponent,
since that would be reserved for NaN and infinity, and we only use `packNumber'` for normal/subnormal numbers.
-/
theorem EUnpackedFloat.packNumber'.exPacked_ne_allOnes
    (hs : 0 < s)
    (he : 1 < e)
    (sign : Bool)
    (exp : BitVec (exponentWidth e s))
    (hexp : exp.toInt ≤ maxNormalExp e) :
    EUnpackedFloat.packNumber'.exPacked exp ≠ BitVec.allOnes e := by
  simp [exPacked]
  by_cases hrange : inNormalRange exp
  · simp [hrange]
    apply BitVec.toInt_ne .. |>.mp
    rw [BitVec.toInt_signExtend]
    simp only [BitVec.toInt_add, BitVec.toInt_allOnes, show 0 < e by grind only, ↓reduceIte,
      Int.reduceNeg, ne_eq]
    rw [toInt_ofNat_bias_eq_bias he hs]
    have he : e < exponentWidth e s := by
      exact self_lt_exponentWidth e s he hs
    simp only [show min e (exponentWidth e s) = e by grind, Int.reduceNeg, ne_eq]
    rw [Int.bmod_bmod_of_dvd]
    · simp [maxNormalExp, bias] at hexp ⊢
      have : 0 < 2 ^ (e - 1) := by grind only [!Nat.two_pow_pos]
      have := exp.toInt_le
      sorry
    · refine (Nat.pow_dvd_pow_iff_le_right ?_).mpr ?_
      · decide
      · grind only

  · simp [hrange]
    grind only

@[simp, grind =]
theorem EUnpackedFloat.not_isNaN_packNumber'  (hs : 0 < s) (he : 1 < e)
    (sign : Bool) (sig : BitVec (s + 1))
    (exp : BitVec (exponentWidth e s))
    (hexplt : exp.toInt ≤ maxNormalExp e) :
    (EUnpackedFloat.packNumber' sign sig exp).isNaN = false := by
  simp [EUnpackedFloat.packNumber', PackedFloat.isNaN]
  intros hexp
  simp [show ¬ s = 0 by grind only]
  have := EUnpackedFloat.packNumber'.exPacked_ne_allOnes hs he sign exp hexplt
  grind only

/--
Alternative definition of `EUnpackedFloat.pack`
that isolates the cases for NaN, infinity, and zero.
-/
def EUnpackedFloat.pack' (uf : EUnpackedFloat (exponentWidth e s) (s + 1)) : PackedFloat e s :=
  if uf.isNaN then
    PackedFloat.getNaN e s
  else if uf.isInfinite then
    PackedFloat.getInfinity e s uf.sign
  else if uf.isZero then
    PackedFloat.getZero e s uf.sign
  else EUnpackedFloat.packNumber' uf.sign uf.sig uf.exp

@[simp, grind .]
theorem pack'_eq_getNaN_of_isNaN (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isNaN) :
    EUnpackedFloat.pack' uf = PackedFloat.getNaN e s := by
  rw [EUnpackedFloat.pack', huf]
  simp

@[simp, grind .]
theorem pack'_eq_getInfinity_of_isInfinite (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isInfinite)  :
    EUnpackedFloat.pack' uf = PackedFloat.getInfinity e s uf.sign := by
  rw [EUnpackedFloat.pack', huf]
  simp only [↓reduceIte, ite_eq_right_iff]
  intros hnan
  simp at hnan huf
  grind only

@[simp, grind .]
theorem pack'_eq_getZero_of_isZero (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
    (huf : uf.isZero) :
    EUnpackedFloat.pack' uf = PackedFloat.getZero e s uf.sign := by
  rw [EUnpackedFloat.pack', huf]
  simp [huf]

@[simp, grind .]
theorem pack'_mkZero_eq_getZero (sign : Bool) :
    EUnpackedFloat.pack' (EUnpackedFloat.mkZero sign) = PackedFloat.getZero e s sign := by
  rw [pack'_eq_getZero_of_isZero]
  · simp
  · simp

/-
`BitVec.ushiftRight_eq'` unfolds stuff into 'toNat' that then cascades
into an annoying set of rewrites, so we just disable this simp-lemma
entirely.
-/
attribute [- simp] BitVec.ushiftRight_eq'

@[simp]
theorem EUnpackedFloat.pack_eq_pack' (euf : EUnpackedFloat (exponentWidth e s) (s + 1)) :
    euf.pack = EUnpackedFloat.pack' euf := by
  by_cases hnan : euf.isNaN
  · simp at hnan
    simp [pack, pack', hnan]
    simp [PackedFloat.getNaN]
  · simp [pack, pack']
    by_cases hinf : euf.isInfinite
    · simp at hinf
      simp [hinf]
      simp [PackedFloat.getInfinity]
    · simp at hinf
      simp [hinf]
      by_cases hzero : euf.isZero
      · simp [hzero]
        simp [PackedFloat.getZero]
      · simp only [hzero, Bool.false_eq_true, false_or, cond_false, ↓reduceIte]
        simp only [packNumber']
        simp at hnan hinf hzero
        simp [hnan]
        by_cases hsle : (BitVec.ofInt _ (minNormalExp e)).sle euf.exp
        · simp [hsle]
          simp [packNumber'.exPacked, packNumber'.sigPacked, packNumber'.inNormalRange, packNumber'.shift]
          constructor
          · intros hcontra
            grind only
          · intros hcontra
            grind only
        · simp [hsle]
          simp [packNumber'.exPacked, packNumber'.sigPacked, packNumber'.inNormalRange, packNumber'.shift]
          constructor
          · intros hcontra
            grind only
          · intros hcontra
            grind only

attribute [bv_normalize] BitVec.zero

@[simp]
theorem PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm
  {pf : PackedFloat e s} (hpf : pf.isNormOrNonzeroSubnorm := by solve | simp | grind) :
    pf.unpack = EUnpackedFloat.mkNumber pf.unpackNum := by
  have hnan : ¬ pf.isNaN := by grind
  have hinf : ¬ pf.isInfinite := by grind
  have hzero : ¬ pf.isZero := by grind
  simp [PackedFloat.unpack, hnan, hinf, hzero]

@[simp, grind →]
theorem PackedFloat.unpack_eq_NaN_of_isNaN (pf : PackedFloat e s) (hpf : pf.isNaN) :
    pf.unpack = EUnpackedFloat.mkNaN := by
  simp [PackedFloat.unpack, hpf]

@[simp]
theorem EUnpackedFloat.mkNaN_pack_eq_mkNaN : (EUnpackedFloat.mkNaN : EUnpackedFloat _ _).pack =
  (PackedFloat.getNaN e s) := rfl

@[simp]
theorem EUnpackedFloat.mkInfinity_pack_eq_getInfinity (sign : Bool) :
    (EUnpackedFloat.mkInfinity sign).pack = PackedFloat.getInfinity e s sign := by
  simp [pack, PackedFloat.getInfinity]

@[simp]
theorem EUnpackedFloat.mkZero_pack_eq_getZero (sign : Bool) :
    (EUnpackedFloat.mkZero sign).pack = PackedFloat.getZero e s sign := by
  simp [pack, PackedFloat.getZero]

@[simp, grind! .]
theorem PackedFloat.unpack_getInfinity {sign : Bool}   :
    (PackedFloat.getInfinity e s sign).unpack = if (0 < s) then EUnpackedFloat.mkInfinity sign else EUnpackedFloat.mkNaN  := by
  simp [PackedFloat.unpack]
  by_cases hs : 0 < s
  · simp [hs]
  · simp [hs]

@[simp]
theorem PackedFloat.unpack_eq_mkZero_of_isZero (pf : PackedFloat e s) (hpf : pf.isZero) :
    pf.unpack = EUnpackedFloat.mkZero pf.sign := by
  simp [PackedFloat.unpack, hpf]
  grind

@[simp]
theorem PackedFloat.unpack_getZero {sign : Bool} :
    (PackedFloat.getZero e s sign).unpack =
      if 0 < e then EUnpackedFloat.mkZero sign else
      if s = 0 then EUnpackedFloat.mkNaN else EUnpackedFloat.mkInfinity sign := by
  by_cases he : 0 < e
  · simp [he]
  · simp [he]
    simp [PackedFloat.unpack]
    simp [show (e = 0) = true by grind]
    by_cases hs : s = 0
    · simp [hs]
    · simp [hs]

private theorem PackedFloat.isInfinite_pack_unpack_example (pf : PackedFloat 5 10) (hpf : pf.unpack.isInfinite) :
    pf.unpack.pack.isInfinite = pf.isInfinite ∧ pf.unpack.pack.sign = pf.sign := by
  bv_decide


private theorem PackedFloat.isNaN_pack_unpack_example (pf : PackedFloat 5 10) :
    pf.unpack.pack.isNaN = pf.isNaN := by
  bv_decide

private theorem PackedFloat.pack_unpack_example (pf : PackedFloat 5 10) (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.unpack.pack = pf := by
  bv_decide


private theorem PackedFloat.pack_unpack_e0m1_example (pf : PackedFloat 0 1) (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.unpack.pack = pf := by
  bv_decide

private theorem PackedFloat.pack_unpack_e1m0_example (pf : PackedFloat 1 0) (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.unpack.pack = pf := by
  bv_decide

example (pf : PackedFloat 0 0) (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.isNaN = true := by
  bv_decide

/-- info: { sign := +, ex := 0x00#5, sig := 0x001#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x00#5, sig := 0x001#10 : PackedFloat _ _ }.unpack.pack
/-- info: { sign := +, ex := 0x0f#5, sig := 0x3ff#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x0f#5, sig := 0x3ff#10 : PackedFloat _ _ }.unpack.pack
/-- info: { sign := +, ex := 0x00#5, sig := 0x000#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x00#5, sig := 0x000#10 : PackedFloat _ _ }.unpack.pack
