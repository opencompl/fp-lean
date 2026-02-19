import Fp.Basic

@[bv_normalize]
def PackedFloat.unpackNormOrNonzeroSubnorm (pf : PackedFloat e s) :
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
  pf.unpackNormOrNonzeroSubnorm.isZero = false

@[simp]
theorem PackedFloat.sign_unpackNormOrNonzeroSubnorm_eq_sign (pf : PackedFloat e s) :
    pf.unpackNormOrNonzeroSubnorm.sign = pf.sign := by
  simp [PackedFloat.unpackNormOrNonzeroSubnorm]
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
  else EUnpackedFloat.mkNumber (pf.unpackNormOrNonzeroSubnorm)

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



@[bv_normalize]
def EUnpackedFloat.pack (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
  : PackedFloat e s :=
  -- min normal <= exp
  let inNormalRange := (BitVec.ofInt _ (minNormalExp e)).sle uf.exp
  {
    sign := uf.sign
    ex := bif uf.isNaN || uf.isInfinite then
            BitVec.allOnes e
          else if uf.isZero || !inNormalRange then
            0#e
          else -- bif uf.isNorm then
            -- Truncate msbs used to normalize subnormals
            (uf.exp + BitVec.ofNat _ (bias e)).truncate _
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


attribute [bv_normalize] BitVec.zero

@[simp]
theorem PackedFloat.unpack_eq_mkNumber_of_isNormOrNonzeroSubnorm
  {pf : PackedFloat e s} (hpf : pf.isNormOrNonzeroSubnorm) :
    pf.unpack = EUnpackedFloat.mkNumber pf.unpackNormOrNonzeroSubnorm := by
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
