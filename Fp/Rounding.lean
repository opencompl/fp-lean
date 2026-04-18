import Fp.Basic
import Fp.Unpacking

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
/-- RoundNearestTiesToAway (Round to nearest, tiebreak away from zero) -/
| RNA : RoundingMode
/--  RoundNearestTiesToEven (Round to nearest, tiebreak to even significand) -/
| RNE : RoundingMode
/-- RoundTowardNegative (Round towards negative infinity) -/
| RTN : RoundingMode
/-- RoundTowardPositive (round towards +ve infinity) -/
| RTP : RoundingMode
/-- RoundTowardZero (round towards zero) -/
| RTZ : RoundingMode
deriving DecidableEq

attribute [bv_normalize] RoundingMode.eq_iff_enumToBitVec_eq

@[bv_normalize]
theorem RoundingMode.beq_iff_enumToBitVec_beq {x y : RoundingMode}
  : (x == y) = (x.enumToBitVec == y.enumToBitVec) := by
  cases h : (x == y) <;> simp_all [eq_iff_enumToBitVec_eq]

@[bv_normalize]
theorem RoundingMode.bne_to_beq {x y : RoundingMode}
  : (x != y) = !(x == y) := by
  cases h : (x != y) <;> simp_all [eq_iff_enumToBitVec_eq]

@[bv_normalize]
theorem RoundingMode.RNA_enumToBitVec_eq : enumToBitVec RNA = 0b000#3 := rfl
@[bv_normalize]
theorem RoundingMode.RNE_enumToBitVec_eq : enumToBitVec RNE = 0b001#3 := rfl
@[bv_normalize]
theorem RoundingMode.RTN_enumToBitVec_eq : enumToBitVec RTN = 0b010#3 := rfl
@[bv_normalize]
theorem RoundingMode.RTP_enumToBitVec_eq : enumToBitVec RTP = 0b011#3 := rfl
@[bv_normalize]
theorem RoundingMode.RTZ_enumToBitVec_eq : enumToBitVec RTZ = 0b100#3 := rfl

@[bv_normalize]
theorem RoundingMode.eq_cond_enumToBitVec {x y : RoundingMode} :
  (bif b then x else y).enumToBitVec = bif b then x.enumToBitVec else y.enumToBitVec := by
  cases b <;> rfl

instance : Repr RoundingMode where
  reprPrec m _ := match m with
  | .RNA => "RNA"
  | .RNE => "RNE"
  | .RTN => "RTN"
  | .RTP => "RTP"
  | .RTZ => "RTZ"

/-- The dyadic number 'd' is representable with a floating point number with exponent 'e', mantissa 's'. -/
def IsRepresentable (e : Nat) (s : Nat) (d : Dyadic) : Prop :=
  ∃ (f : PackedFloat e s),
    f.toDyadic? = some d

/-- The dyadic 'near' is closer than all representable dyadics to 'd'. -/
def IsCloserThanRepresentables (e : Nat) (s : Nat) (d : Dyadic) (near : Dyadic) : Prop :=
  ∀ (far : Dyadic), IsRepresentable e s far →
    d.distance near ≤ d.distance far
/--
Find the position of the last (most significant) set bit in a BitVec.
Returns zero if BitVec is zero. Otherwise, returns the index starting from 1.
Implemented in terms of bitblastable `clz`.

Given a BV `000111`, then `clz` returns `3` (the number of leading zeros),
and `fls` returns `6 - 3 = 3`, which is the index of the last set bit (counting from 1).
-/
@[simp, bv_normalize]
def fls (b : BitVec n) : BitVec n := BitVec.ofNat n n - b.clz


@[simp, bv_normalize]
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
-/
@[simp, bv_normalize]
def flsLog (b : BitVec n) : BitVec n :=
  if b == 0 then 0 else 1#_ + fls_log (lastPowerOfTwo n) b

/--
`flsLog` and `fls` implement the same function.
-/
theorem flsLog_eq_fls (b : BitVec 8)
  : flsLog b = fls b := by
  simp
  bv_decide

/--
Gets the first `w` bits of the bitvector `v`.
-/
@[simp, bv_normalize]
def truncateRight (w : Nat) (v : BitVec n) : BitVec w :=
  if hw : n ≤ w then
    -- Have to show that hw ⊢ n + (w - n) = w
    have h : BitVec (n+(w-n)) = BitVec w := by
      congr
      omega

    h.mp (v ++ 0#(w-n))
  else
    BitVec.truncate w (v >>> (n-w))

@[simp, bv_normalize]
def shouldRoundAway (m : RoundingMode)
  (sign : Bool) (odd : Bool) (v : BitVec n) : Bool :=
  let guard := v.msb
  let sticky := v.truncate (n-1) ≠ 0
  match m with
  | .RNE => guard && (sticky || odd)
  | .RNA => guard
  | .RTP => (guard || sticky) && ¬sign
  | .RTN => (guard || sticky) && sign
  | .RTZ => false

@[bv_normalize]
theorem shouldRoundAway.match_eq_cond :
  (shouldRoundAway.match_1 (fun _ => Bool) m a b c d e) =
  bif m = .RNE then a () else bif m = .RNA then b () else bif m = .RTP then c () else bif m = .RTN then d () else e () := by
  cases m <;> rfl


-- Round is less well-behaved when exWidth = 0. This shouldn't be an issue?
/--
Round an extended fixed-point number to its nearest floating point number of
the specified format, with the specified rounding mode.
-/
@[bv_normalize]
def EFixedPoint.round {width exOffset}
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
        PackedFloat.maxNormalNumber _ _ x.num.sign
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

@[grind =>]
theorem round_of_eq_nan {width exOffset}
  {exWidth sigWidth : Nat} {mode : RoundingMode} {x : EFixedPoint width exOffset}
  {hNaN : x.state = .NaN} :
  EFixedPoint.round exWidth sigWidth mode x = PackedFloat.getNaN exWidth sigWidth := by
  simp [EFixedPoint.round, hNaN]

@[grind =>]
theorem round_of_eq_infinity {width exOffset}
  {exWidth sigWidth : Nat} {mode : RoundingMode} {x : EFixedPoint width exOffset}
  {hInf : x.state = .Infinity} :
  EFixedPoint.round exWidth sigWidth mode x = PackedFloat.getInfinity exWidth sigWidth x.num.sign := by
  simp [EFixedPoint.round, hInf]


/-- IsRounded e s d closest iff closest is the closest representable dyadic that is closer than all other. -/
def IsRounded (e s : Nat) (perfect : Dyadic) (closest : Dyadic) : Prop :=
  IsRepresentable e s closest ∧
  IsCloserThanRepresentables e s perfect closest

/--
If there a choice between another number that is a rounded result, then our result is rounded.
-/
def IsNearestEven (e s : Nat) (perfect : Dyadic) (closest : Dyadic) : Prop :=
  ∀ (other : Dyadic), IsRounded e s perfect other →
    (other.numerator % 2 = 0 → other = closest)

/-- The result of the 'round' function is well-rounded. -/
axiom IsRounded_round_RNE {width exOffset}
  (exWidth sigWidth : Nat) (mode : RoundingMode)
  (x : EFixedPoint width exOffset) (xd : Dyadic) (hxd : x.toDyadic? = some xd)
  (f : PackedFloat exWidth sigWidth) (hf : EFixedPoint.round exWidth sigWidth .RNE x = f)
  (fd : Dyadic) (hfd : f.toDyadic? = some fd) :
  IsRounded exWidth sigWidth xd fd

/-- The result of the 'round' function is well-rounded. -/
axiom IsNearestEven_round_RNE {width exOffset}
  (exWidth sigWidth : Nat) (mode : RoundingMode)
  (x : EFixedPoint width exOffset) (xd : Dyadic) (hxd : x.toDyadic? = some xd)
  (f : PackedFloat exWidth sigWidth) (hf : EFixedPoint.round exWidth sigWidth .RNE x = f)
  (fd : Dyadic) (hfd : f.toDyadic? = some fd) :
  IsNearestEven exWidth sigWidth xd fd

/--
Determine if a fixed-point number has an exact representation in the
specified floating-point format.
-/
@[bv_normalize]
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

@[bv_normalize]
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
        hPrec := by
          have h := Nat.two_pow_pos e
          omega
      }
    }
    EFixedPoint.round e s mode res

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
        hPrec := by
          have hexp0 : 0 < 2^e := Nat.two_pow_pos _
          have hexp1 : 2^(e-1) ≤ 2^e := two_pow_sub_one_le_two_pow e
          omega
      }
    }
    EFixedPoint.round e s mode result
end PackedFloat

theorem ofRat_one_is_oneE5M2 : PackedFloat.ofRat 5 2 .RNE 1 1 = oneE5M2 := by
  simp [PackedFloat.ofRat]
  decide

theorem ofRat_two_is_twoE5M2 : PackedFloat.ofRat 5 2 .RNE 2 1 = twoE5M2 := by
  simp [PackedFloat.ofRat]
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

/-- info: 6#5 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).ex - BitVec.ofNat 5 (bias 5)
/-- info: 1408#11 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).sig.cons true
/-- info: 6#6 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).unpack.num.ex
/-- info: 1408#11 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).unpack.num.sig
/-- info: 88 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).toEFixed.num.toDyadic.toRat
/-- info: 88 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).unpack.num.toDyadic.toRat
/-- info: 88 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).unpack.num.toRat
/-- info: 88 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE 88 1).unpack.pack.toEFixed.num.toDyadic.toRat

/-- info: -88 -/
#guard_msgs in #eval (PackedFloat.ofRat 5 (11 - 1) .RNE (-88) 1).unpack.pack.toEFixed.num.toDyadic.toRat
