import Fp.Basic
import Fp.Rounding
import Fp.Addition
import Fp.Multiplication

@[bv_normalize]
def fma (a b c : PackedFloat e s) (m : RoundingMode)
  : PackedFloat e s :=
  if a.isNaN || b.isNaN || c.isNaN ||
    (a.isInfinite && b.isZero) ||
    (b.isInfinite && a.isZero) then PackedFloat.getNaN _ _
  else if a.isInfinite || b.isInfinite then
    let interSign := (a.sign ^^ b.sign)
    if c.isInfinite && c.sign != interSign then
      PackedFloat.getNaN _ _
    else
      PackedFloat.getInfinity _ _ interSign
  else
    let sa := BitVec.ofBool (a.ex != 0) ++ a.sig
    let sb := BitVec.ofBool (b.ex != 0) ++ b.sig
    let shift : BitVec (e+1) :=
      (if a.ex == 0 then 0 else a.ex - 1).setWidth _ +
      (if b.ex == 0 then 0 else b.ex - 1).setWidth _
    let prod := sa.setWidth (2*(s+1)) * sb.setWidth (2*(s+1))
    let result : EFixedPoint (2*(2^e + s)) (2*(2^(e-1) + s - 2)) :=
      {
        state := .Number
        num := {
          sign := a.sign ^^ b.sign
          val := prod.setWidth _ <<< shift
          hExOffset := by
            have h := toEFixed_hExOffset e s
            omega
        }
      }
    -- Used for proving bounds
    have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
    let added_result := e_add m result (c.toEFixed.expand _ _ (by omega) (by omega))
    round _ _ m added_result
