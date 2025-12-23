import Fp.Basic

@[bv_normalize]
def PackedFloat.unpack (pf : PackedFloat e s)
  : EUnpackedFloat (exponentWidth e s) (s + 1) :=
  bif pf.isNaN then
    EUnpackedFloat.mkNaN
  else bif pf.isInfinite then
    EUnpackedFloat.mkInfinity pf.sign
  else bif pf.isZero then
    EUnpackedFloat.mkZero pf.sign
  else bif pf.isNorm then
    ({
      sign := pf.sign
      -- We cannot use `BitVec.signExtend` here because `pf.ex` is not in 2's complement representation.
      -- It should be safe to use `setWidth'`
      ex := pf.ex.zeroExtend _ - BitVec.ofNat _ (bias e) -- e - bias, but no adjustment for significand?
      sig := pf.sig.cons true
      : UnpackedFloat _ _
    }).toEUnpackedFloat
  else -- bif pf.isSubnorm then
    ({
      sign := pf.sign
      ex := BitVec.ofInt _ (minNormalExp e)
      sig := pf.sig.cons false
      : UnpackedFloat _ _
    }).normalize.toEUnpackedFloat

@[bv_normalize]
def EUnpackedFloat.pack (uf : EUnpackedFloat (exponentWidth e s) (s + 1))
  : PackedFloat e s :=
  let inNormalRange := (BitVec.ofInt _ (minNormalExp e)).sle uf.exp
  {
    sign := uf.sign
    ex := bif uf.isNaN || uf.isInfinite then
            BitVec.allOnes e
          else if uf.isZero || !inNormalRange then
            (0#_)
          else -- bif uf.isNorm then
            -- Truncate msbs used to normalize subnormals
            (uf.exp + BitVec.ofNat _ (bias e)).truncate _
    sig := bif uf.isNaN then
            BitVec.ofNat _ (2 ^ (s - 1))
           else bif uf.isInfinite || uf.isZero then
            (0#_)
           else bif inNormalRange then
            uf.sig.truncate _
           else -- bif uf.isSubnorm then
            let shift := BitVec.ofInt _ (minNormalExp e) - uf.exp
            (uf.sig >>> shift).truncate _
  }

attribute [bv_normalize] BitVec.zero

theorem PackedFloat.isInfinite_pack_unpack (pf : PackedFloat 5 10) (hpf : pf.unpack.isInfinite) :
    pf.unpack.pack.isInfinite = pf.isInfinite ∧ pf.unpack.pack.sign = pf.sign := by
  bv_decide

theorem PackedFloat.isNaN_pack_unpack (pf : PackedFloat 5 10) :
    pf.unpack.pack.isNaN = pf.isNaN := by
  bv_decide

theorem PackedFloat.pack_unpack (pf : PackedFloat 5 10) (hpf : pf.isNormOrSubnorm) :
    pf.unpack.pack = pf := by
  bv_decide

theorem PackedFloat.pack_unpack' (pf : PackedFloat 0 1) (hpf : pf.isNormOrSubnorm) :
    pf.unpack.pack = pf := by
  bv_decide

theorem PackedFloat.pack_unpack'' (pf : PackedFloat 1 0) (hpf : pf.isNormOrSubnorm) :
    pf.unpack.pack = pf := by
  bv_decide

example (pf : PackedFloat 0 0) (hpf : pf.isNormOrSubnorm) :
    pf.isNaN = true := by
  bv_decide

/-- info: { sign := +, ex := 0x00#5, sig := 0x001#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x00#5, sig := 0x001#10 : PackedFloat _ _ }.unpack.pack
/-- info: { sign := +, ex := 0x0f#5, sig := 0x3ff#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x0f#5, sig := 0x3ff#10 : PackedFloat _ _ }.unpack.pack
/-- info: { sign := +, ex := 0x00#5, sig := 0x000#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x00#5, sig := 0x000#10 : PackedFloat _ _ }.unpack.pack
