import Fp.Basic
import Fp.Rounding
import Fp.UnpackedRound

#check Float
#check BitVec.mul_zero

attribute [grind] BitVec.mul_zero

/--
Implementation of integer square root. Remainder bit appended to the end of the result.
-/
@[bv_normalize]
def sqrt_iter (i : Nat) (x : BitVec n) (y : BitVec n) : BitVec (n+1) :=
  let yExtended := y.setWidth (2*n) ||| (1#_ <<< i)
  let flag := (BitVec.ofBool (yExtended * yExtended ≤ x.setWidth (2*n))).setWidth n <<< i
  let yNew := y ||| flag
  match i with
  | 0 => yNew ++ BitVec.ofBool (yNew.setWidth (2*n) * yNew.setWidth (2*n) ≠ x.setWidth (2*n))
  | j+1 => sqrt_iter j x yNew

@[bv_normalize]
def bit_sqrt (x : BitVec n) : BitVec (n+1) :=
  sqrt_iter (n - 1) x 0

/--
Inner loop for fixedPointSqrt. `i` counts down from `n-1` to `0`.
When `i > 0`: try setting bit `i-1` in the working result.
When `i = 0`: return the result with a sticky bit appended.
`xcomp` is the input padded to `2*n` bits (right-padded with zeros).
`working` is the `n`-bit result being built, with the MSB always set.
-/
@[bv_normalize]
def fixedPointSqrt_iter (i : Nat) (xcomp : BitVec (2 * n)) (working : BitVec n) : BitVec (n + 1) :=
  match i with
  | 0 =>
    let sq := working.setWidth (2 * n) * working.setWidth (2 * n)
    working ++ BitVec.ofBool (sq ≠ xcomp)
  | loc + 1 =>
    let candidate := working ||| ((1 : BitVec n) <<< loc)
    let candidateSq := candidate.setWidth (2 * n) * candidate.setWidth (2 * n)
    let addBit := candidateSq ≤ xcomp
    let newWorking := working ||| ((BitVec.ofBool addBit).setWidth n <<< loc)
    fixedPointSqrt_iter loc xcomp newWorking

/--
Fixed-point square root, ported from the C++ `fixedPointSqrt`.
Input `x` has `n+1` bits representing a fixed-point value in [1, 4).
Returns `n+1` bits: the top `n` bits are the sqrt in [1, 2),
and the bottom bit is the sticky/remainder bit.
-/
@[bv_normalize]
def fixedPointSqrt (x : BitVec (n + 1)) : BitVec (n + 1) :=
  -- Right-pad x by (n-1) zeros to get 2*n bits for comparison.
  -- This is equivalent to the C++ `x.append(ubv::zero(inputWidth - 2))`.
  let xcomp : BitVec (2 * n) := (x.setWidth (2 * n)) <<< (n - 1)
  -- Start with MSB set (the integer part is always 1 for inputs in [1,4))
  let working : BitVec n := (1 : BitVec n) <<< (n - 1)
  -- Iterate from bit n-2 down to bit 0
  fixedPointSqrt_iter (n - 1) xcomp working

def UnpackedFloat.sqrt (x : UnpackedFloat e s) :
    UnpackedFloat e ((s + 2)) :=
  let exponentEven : Bool := (x.ex.getLsbD 0 == false)
  -- sshiftRight does floor division:
  -- -3 = -4 + 1 = <101>
  -- <110> = -4 + 2 = -2
  -- -3 sshiftRight 1 = <110> = -2
  let exponentHalved : BitVec e := x.ex.sshiftRight 1
  let leadingOne_alignedSig : BitVec _ :=  ((0#1 ++ x.sig)) ++ 0#1
  -- if the exponent is even, then do nothing.
  -- Otherwise, if exponent is odd, say 9, then we write the
  -- number as 'sig * twoPow(2 * halfExp + 1)',
  -- which becomes (2 * sig) * twoPow(2 * halfExp)
  let leadingOne_alignedSig := if exponentEven then leadingOne_alignedSig else leadingOne_alignedSig <<< 1
  -- since 'leadingOne_alignedSig' is in [1, 4), its square root is in [1, 2)
  -- so no need for rounding.
  let leadingOne_result_stickyBit := fixedPointSqrt leadingOne_alignedSig
  -- Top (s+1) bits are the sqrt result, bottom bit is sticky.
  let result : BitVec (s + 1) := leadingOne_result_stickyBit.extractMsb' 0 (s + 1)
  let sticky := leadingOne_result_stickyBit.getLsbD 0

  let out : UnpackedFloat e _ :=
    { sign := false, ex := exponentHalved, sig := result ++ BitVec.ofBool sticky }
  out

@[bv_normalize]
def sqrt (x : PackedFloat e s) (m : RoundingMode) : PackedFloat e s :=
  if x.isZero then x
  else if (x.sign && !x.isZero) || x.isNaN then PackedFloat.getNaN e s
  else if (x.isInfinite && !x.sign) then PackedFloat.getInfinity e s false
  else (UnpackedFloat.sqrt x.unpack.num) |> UnpackedFloat.round (mode := m) |>.pack

theorem square_sqrt_is_id (x : BitVec 3)
  : bit_sqrt (x.setWidth 6 * x.setWidth _) = x.setWidth _ <<< 1 := by
  bv_normalize
  bv_decide

/-- info: ExtRat.Number (3 : Rat)/65536 -/
#guard_msgs in #eval (PackedFloat.ofBits 5 2 0b00000011#8).toExtRat
/-- info: ExtRat.Number (7 : Rat)/1024 -/
#guard_msgs in #eval (sqrt (PackedFloat.ofBits 5 2 0b00000011#8) .RNE).toExtRat

/-- info: { sign := +, ex := 0x07#5, sig := 0x0#2 } -/
#guard_msgs in #eval sqrt (PackedFloat.ofBits 5 2 0b00000001#8) .RNE
/-- info: { sign := +, ex := 0x07#5, sig := 0x3#2 } -/
#guard_msgs in #eval sqrt (PackedFloat.ofBits 5 2 0b00000011#8) .RNE
/-- info: { sign := +, ex := 0x16#5, sig := 0x0#2 } -/
#guard_msgs in #eval sqrt (PackedFloat.ofBits 5 2 0b01110100#8) .RNE
/-- info: { sign := +, ex := 0x0f#5, sig := 0x0#2 } -/
#guard_msgs in #eval sqrt (oneE5M2) .RNE
