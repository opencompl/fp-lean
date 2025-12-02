import Fp.Basic
import Fp.Rounding
import Fp.Negation

/--
Multiplication of two fixed-point numbers.
-/
@[bv_float_normalize]
def f_mul (a : FixedPoint v e) (b : FixedPoint w f) : FixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.hExOffset b.hExOffset
  let a' : BitVec (v+w) := a.val.setWidth' (by omega)
  let b' : BitVec (v+w) := b.val.setWidth' (by omega)
  {
    sign := a.sign ^^ b.sign
    val := a' * b'
    hExOffset
  }

/--
Multiplication of two extended fixed-point numbers.
-/
@[bv_float_normalize]
def e_mul (a : EFixedPoint v e) (b : EFixedPoint w f) : EFixedPoint (v+w) (e+f) :=
  let hExOffset := Nat.add_lt_add a.num.hExOffset b.num.hExOffset
  open EFixedPoint in
  if hN : a.state = .NaN || b.state = .NaN ||
      (a.state = .Infinity && b.isZero) ||
      (b.state = .Infinity && a.isZero) then getNaN hExOffset
  else if hI1 : a.state = .Infinity || b.state = .Infinity then
    getInfinity (a.num.sign ^^ b.num.sign) hExOffset
  else
    let _ : a.state = .Number && b.state = .Number := by
      cases ha : a.state <;> cases hb : b.state <;> simp_all
    {
      state := .Number
      num := f_mul a.num b.num
    }

/--
Multiplication of two floating point numbers, rounded to a floating point
number using the provided rounding mode.

Implemented using `e_mul`, by conversion to extended fixed-point numbers.
-/
@[bv_float_normalize]
def mulfixed
  (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  round_to_packedFloat _ _ m (e_mul a.toEFixed b.toEFixed)

/--
Multiplication of two floating point numbers, rounded to a floating point
number using the provided rounding mode.

A bit-blastable version of multiplication, without using `e_mul`.
-/
@[bv_float_normalize]
def mul
  (a b : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  if a.isNaN || b.isNaN ||
    (a.isInfinite && b.isZero) ||
    (b.isInfinite && a.isZero) then PackedFloat.getNaN _ _
  else if a.isInfinite || b.isInfinite then
    PackedFloat.getInfinity _ _ (a.sign ^^ b.sign)
  else
    let sa := BitVec.ofBool (a.ex != 0) ++ a.sig
    let sb := BitVec.ofBool (b.ex != 0) ++ b.sig
    let shift : BitVec (e+1) :=
      (if a.ex == 0 then 0 else a.ex - 1).setWidth _ +
      (if b.ex == 0 then 0 else b.ex - 1).setWidth _
    let prod := sa.setWidth (2*(s+1)) * sb.setWidth (2*(s+1))
    let result : EFixedPoint (2*2^e + 2*s) (2^e + 2*s - 4) :=
      {
        state := .Number
        num := {
          sign := a.sign ^^ b.sign
          val := prod.setWidth _ <<< shift
          hExOffset := by
            have h : 0 < 2^e := Nat.two_pow_pos e
            omega
        }
      }
    round_to_packedFloat _ _ m result

/--
Doubles the given floating point number, rounding to infinity if applicable.
-/
@[bv_float_normalize]
def doubleRNE (a : PackedFloat e s) : PackedFloat e s :=
  if a.isNaN then PackedFloat.getNaN _ _
  else if a.isZeroOrSubnorm then
    let ex := if a.sig.msb then 1 else 0
    { sign := a.sign, ex, sig := a.sig <<< 1 }
  else
    let ex := if a.ex == BitVec.allOnes _ then BitVec.allOnes _ else a.ex + 1
    let sig := if ex == BitVec.allOnes _ then 0 else a.sig
    { sign := a.sign, ex, sig }
