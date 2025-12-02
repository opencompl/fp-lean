import Fp.Basic

/--
Rounding modes used in floating-point calculations.

Available modes:
* `RNA`: Round to nearest, tiebreak away from zero.
* `RNE`: Round to nearest, tiebreak to even significand.
* `RTN`: Round towards negative infinity.
* `RTP`: Round towards positive infinity.
* `RTZ`: Round towards zero.
-/
inductive RoundingMode : Type
| RNA : RoundingMode -- RoundNearestTiesToAway
| RNE : RoundingMode -- RoundNearestTiesToEven
| RTN : RoundingMode -- RoundTowardNegative
| RTP : RoundingMode -- RoundTowardPositive
| RTZ : RoundingMode -- RoundTowardZero
deriving DecidableEq

instance : Repr RoundingMode where
  reprPrec m _ := match m with
  | .RNA => "RNA"
  | .RNE => "RNE"
  | .RTN => "RTN"
  | .RTP => "RTP"
  | .RTZ => "RTZ"

@[simp, bv_float_normalize]
def fls' (m : Nat) (b : BitVec n) (hm : n ≤ m) : BitVec m := match n with
  | 0 => 0
  | n' + 1 =>
    if b.msb then n
    else fls' m (BitVec.truncate n' b) (by omega)


@[simp, bv_float_normalize]
def fls_log (m : Nat) (b : BitVec n) : BitVec n :=
  if m = 0 then
    0
  else if b >>> m == 0 then
    fls_log (m/2) b
  else
    BitVec.ofNat _ m ||| fls_log (m/2) (b >>> m)
  termination_by m

/--
Find the position of the last (most significant) set bit in a BitVec.

Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.

Implemented naively using a fold with $O(n)$ steps.
-/
@[simp, bv_float_normalize]
def fls (b : BitVec n) : BitVec n :=
  fls' n b (n.le_refl)

/--
Find the position of the last (most significant) set bit in a BitVec.

Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.
-/
@[simp, bv_float_normalize]
def flsLog (b : BitVec n) : BitVec n :=
  if b == 0 then 0 else 1#_ + fls_log (lastPowerOfTwo n) b

/--
`flsLog` and `fls` implement the same function.
-/
theorem flsIter_eq_fls (b : BitVec 8)
  : flsLog b = fls b := by
  simp
  bv_decide

/--
Gets the first `w` bits of the bitvector `v`.
-/
@[simp, bv_float_normalize]
def truncateRight (w : Nat) (v : BitVec n) : BitVec w :=
  if hw : n ≤ w then
    -- Have to show that hw ⊢ n + (w - n) = w
    have h : BitVec (n+(w-n)) = BitVec w := by
      congr
      omega

    h.mp (v ++ 0#(w-n))
  else
    BitVec.truncate w (v >>> (n-w))

@[simp, bv_float_normalize]
def shouldRoundAway (m : RoundingMode)
  (sign : Bool) (odd : Bool) (v : BitVec n) : Bool :=
  let guard := v.msb
  let sticky := v.truncate (n-1) ≠ 0
  match m with
  | .RNE => guard ∧ (sticky ∨ odd)
  | .RNA => guard
  | .RTP => (guard ∨ sticky) ∧ ¬sign
  | .RTN => (guard ∨ sticky) ∧ sign
  | .RTZ => False


def is_over (x : EFixedPoint width exOffset) (exWidth : Nat) : Bool :=
  let over := x.num.val >>> (exOffset + 2^(exWidth-1))
  over != 0

-- Round is less well-behaved when exWidth = 0. This shouldn't be an issue?
/--
Round an extended fixed-point number to its nearest floating point number of
the specified format, with the specified rounding mode.
-/
@[bv_float_normalize]
def round_to_packedFloat
  (exWidth sigWidth : Nat) (mode : RoundingMode) (x : EFixedPoint width exOffset)
  : PackedFloat exWidth sigWidth :=
  if x.state = .NaN then
    PackedFloat.getNaN _ _
  else if x.state = .Infinity then
    PackedFloat.getInfinity _ _ x.num.sign
  else
    let exOffset' := 2^(exWidth - 1) + sigWidth - 2
    -- trim bitvector
    let over := x.num.val >>> (exOffset + 2^(exWidth-1))
    let a := (x.num.val >>> exOffset).truncate (2^(exWidth-1))
    let b := truncateRight exOffset' (x.num.val.truncate exOffset)
    let underWidth := exOffset - exOffset'
    let under := x.num.val.truncate underWidth
    let trimmed := a ++ b
    if over != 0 then
      -- Overflow to Infinity
      -- Unless we're rounding RTN/RTP to the opposite sign, or RTZ
      -- in which case we overflow to MAX
      if (mode = .RTN ∧ ¬x.num.sign) ∨ (mode = .RTP ∧ x.num.sign) ∨ mode = .RTZ then
        PackedFloat.getMax _ _ x.num.sign
      else
        PackedFloat.getInfinity _ _ x.num.sign
    else
    let index := fls trimmed
    let sigWidthB := BitVec.ofNat _ sigWidth
    let ex : BitVec exWidth :=
      if index ≤ sigWidthB then
        0
      else
        (index - sigWidthB).truncate _
    let truncSig : BitVec sigWidth :=
      if ex = 0 then
        trimmed.truncate _
      else
        (trimmed >>> (ex - 1)).truncate _
    let rem : BitVec (2^exWidth + underWidth) :=
      if ex = 0 then
        under.truncate _ <<< (1<<<exWidth)
      else
        let totalShift : BitVec (exWidth+1) := ex.truncate _ - 1
        truncateRight _ (trimmed <<< ((1<<<exWidth) + sigWidth - 2 - totalShift)) |||
        (under.truncate _ <<< ((1<<<exWidth) - totalShift))
    if shouldRoundAway mode x.num.sign (truncSig.getLsbD 0) rem then
      if truncSig = BitVec.allOnes _ then
        -- overflow to next exponent
        {
          sign := x.num.sign
          ex := ex+1
          sig := 0
        }
      else
        -- add 1 to significand
        {
          sign := x.num.sign
          ex
          sig := truncSig + 1
        }
    else
    -- leave everything the same
    {
      sign := x.num.sign
      ex
      sig := truncSig
    }

/--
Determine if a fixed-point number has an exact representation in the
specified floating-point format.
-/
@[bv_float_normalize]
def isExactFloat (exWidth sigWidth : Nat)
  (x : EFixedPoint width exOffset) : Bool :=
  if x.state = .Number then
    let exOffset' := 2^(exWidth - 1) + sigWidth - 2
    -- trim bitvector
    let over := x.num.val >>> (exOffset + 2^(exWidth-1))
    let a := (x.num.val >>> exOffset).truncate (2^(exWidth-1))
    let b := truncateRight exOffset' (x.num.val.truncate exOffset)
    let underWidth := exOffset - exOffset'
    let under := x.num.val.truncate underWidth
    let trimmed := a ++ b
    if over != 0 || under != 0 then
      -- Overflow to Infinity, or under has values
      false
    else
    let index := fls trimmed
    let sigWidthB := BitVec.ofNat _ sigWidth
    let ex : BitVec exWidth :=
      if index ≤ sigWidthB then
        0
      else
        (index - sigWidthB).truncate _
    if ex = 0 then
      true
    else
      let totalShift : BitVec (exWidth+1) := ex.truncate _ - 1
      (trimmed &&& ((1#_ <<< totalShift) - 1#_)) == 0
  else
    true

@[bv_float_normalize]
def roundToInt (mode : RoundingMode) (x : PackedFloat e s) : PackedFloat e s :=
  if x.isNaN then PackedFloat.getNaN e s
  else if x.isInfinite then x
  else
    let ef := x.toEFixed.num.val
    let offset := 2 ^ (e - 1) + s - 2
    let before := ef >>> offset
    let after := ef <<< (2 ^ e + s - offset)
    let integral := before +
      (if shouldRoundAway mode x.sign (before.getLsbD 0) after then 1 else 0)
    let res : EFixedPoint (2^e + s) 0 := {
      state := .Number
      num := {
        sign := x.sign
        val := integral
        hExOffset := by
          have h := Nat.two_pow_pos e
          omega
      }
    }
    round_to_packedFloat e s mode res

namespace PackedFloat
def ofRat (e s : Nat) (mode : RoundingMode) (num : Int) (den : Nat) : PackedFloat e s :=
  let width := 2^e + s + 2
  let exOffset := 2^(e-1) + s
  let adjustedNum : Nat := num.natAbs <<< (exOffset - 1)
  let roundBit := if adjustedNum % den != 0 then 1 else 0
  let quot := (adjustedNum / den) * 2 + roundBit
  if quot.log2 ≥ width then
    PackedFloat.getInfinity e s (num < 0)
  else
    let result : EFixedPoint width exOffset := {
      state := .Number
      num := {
        sign := num < 0
        val := BitVec.ofNat width quot
        hExOffset := by
          have hexp0 : 0 < 2^e := Nat.two_pow_pos _
          have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
          omega
      }
    }
    round_to_packedFloat e s mode result
end PackedFloat

theorem ofRat_one_is_oneE5M2 : PackedFloat.ofRat 5 2 .RNE 1 1 = oneE5M2 := by
  simp [PackedFloat.ofRat, Nat.log2]
  decide

theorem ofRat_two_is_twoE5M2 : PackedFloat.ofRat 5 2 .RNE 2 1 = twoE5M2 := by
  simp [PackedFloat.ofRat, Nat.log2]
  decide

/-- info: { sign := +, ex := 0x0f#5, sig := 0x0#2 } -/
#guard_msgs in #eval PackedFloat.ofRat 5 2 .RNE 1 1
/-- info: 5#8 -/
#guard_msgs in #eval fls 0x10#8
/-- info: 0#8 -/
#guard_msgs in #eval fls 0#8
/-- info: 10#4 -/
#guard_msgs in #eval truncateRight 4 0xaf#8
/-- info: 44800#16 -/
#guard_msgs in #eval truncateRight 16 0xaf#8
