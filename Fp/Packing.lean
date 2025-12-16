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
    EUnpackedFloat.mkNumber {
      sign := pf.sign
      ex := pf.ex.zeroExtend _ - BitVec.ofNat _ (bias e)
      sig := pf.sig.cons true
    }
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
            BitVec.zero _
          else -- bif uf.isNorm then
            -- Truncate msbs used to normalize subnormals
            (uf.exp + BitVec.ofNat _ (bias e)).truncate _
    sig := bif uf.isNaN then
            BitVec.ofNat _ (2 ^ (s - 1))
           else bif uf.isInfinite || uf.isZero then
            BitVec.zero _
           else bif inNormalRange then
            uf.sig.truncate _
           else -- bif uf.isSubnorm then
            let shift := BitVec.ofInt _ (minNormalExp e) - uf.exp
            (uf.sig >>> shift).truncate _
  }

/-- info: { sign := +, ex := 0x00#5, sig := 0x001#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x00#5, sig := 0x001#10 : PackedFloat _ _ }.unpack.pack
/-- info: { sign := +, ex := 0x0f#5, sig := 0x3ff#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x0f#5, sig := 0x3ff#10 : PackedFloat _ _ }.unpack.pack
/-- info: { sign := +, ex := 0x00#5, sig := 0x000#10 } -/
#guard_msgs in #eval { sign := false, ex := 0x00#5, sig := 0x000#10 : PackedFloat _ _ }.unpack.pack
