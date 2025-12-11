import Fp.Basic
import Fp.Rounding


-- 1 / (a *2^{-e}) = 2^e / a
/-- Compute the multiplicative inverse. -/
def f_mulinv (a : FixedPoint v e) : FixedPoint (v + v) e :=
  let hExOffset := a.hExOffset
  let aExt : BitVec (v + v) := a.val.zeroExtend _
  let twoPowV : BitVec (v + v) := BitVec.twoPow (v + v) v
  let divResult : BitVec (v + v) := twoPowV / aExt
  {
    sign := a.sign
    val := divResult
    hExOffset := by omega
  }
