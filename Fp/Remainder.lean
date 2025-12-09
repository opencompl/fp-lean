import Fp.Basic
import Fp.Rounding

@[bv_normalize]
def remainder (a b : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN || b.isNaN || a.isInfinite || b.isZero then PackedFloat.getNaN e s
  else if a.isZero || b.isInfinite then a
  else if a.ex + 1 < b.ex then a
  else
    let sa := BitVec.ofBool (a.ex != 0) ++ a.sig
    let sb := BitVec.ofBool (b.ex != 0) ++ b.sig ++ 0#1
    let shift :=
      if a.ex == 0 && b.ex != 0 then 2 - b.ex
      else if a.ex != 0 && b.ex == 0 then a.ex
      else a.ex + 1 - b.ex
    let bshift := if b.ex == 0 then 0 else b.ex - 1
    let dividend : BitVec (2^e + s) := sa.setWidth _ <<< shift
    let divisor : BitVec (s+3) := sb.setWidth _ <<< 1
    -- We are dividing a size 2^e + s number by a size s+2 number
    -- Here's hoping the solver will optimise out the redundant parts of
    -- the modulo here
    let rem : BitVec (s+3) := (dividend % divisor.setWidth _).setWidth _
    -- Simulate rounding-to-even.
    let odd := rem ≥ sb.setWidth _
    let rest : BitVec (1+s+1) :=
      (if odd then rem - sb.setWidth _ else rem).setWidth _
    let remSign :=
      (sb &&& 1 == 0 && rest ≥ sb/2 && odd) || (rest > sb/2)
    let val := if remSign then sb - rest else rest
    let result : EFixedPoint (2^e + s) (2 ^ (e-1) + s - 1) :=
      {
        state := .Number
        num := {
          sign := a.sign ^^ remSign
          val := val.setWidth _ <<< bshift
          hExOffset := by
            have hexp0 : 0 < 2^e := Nat.two_pow_pos _
            have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
            omega
        }
      }
    -- If all calculations are correct, the rounding mode should not
    -- matter here as the result is always exact
    round e s .RTZ result

/-- info: { sign := -, ex := 0x00#5, sig := 0x1#2 } -/
#guard_msgs in #eval remainder (PackedFloat.ofBits 5 2 0b00000011) (PackedFloat.ofBits 5 2 0b00000100)
